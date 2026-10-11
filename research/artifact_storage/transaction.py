"""Bounded, same-path artifact replacement; never roll back installed bytes."""
import argparse
import ctypes
import json
import os
import stat
import sys
import time
import uuid
from contextlib import ExitStack
from dataclasses import dataclass

from .filesystem import (RootFS, Error, fingerprint, digest, metadata,
                         apply_metadata, verify_metadata, fsync_directory)
from .journal import MaintenanceLock, Journal, reconcile, _journal_path

_MANIFEST_LIMIT = 8 << 20
_CHUNK = 1 << 20
_AGE_NS = 24 * 60 * 60 * 1_000_000_000


def _path(value):
    if (not isinstance(value, str) or not value or chr(0) in value
            or any(p in ('', '.', '..') for p in value.split('/'))):
        raise Error('paths must be normalized, root-relative paths')
    return value


def _relative(root, value):
    return _path(os.path.relpath(value, os.path.abspath(root))
                 if os.path.isabs(value) else value)


def _verified(directory):
    if directory.verified() is False:
        raise Error('directory identity changed')


def _matches(current, expected, renamed=False):
    return (isinstance(expected, dict)
            and all(k in expected for k in current)
            and all(v == expected[k] for k, v in current.items()
                    if not (renamed and k == 'ctime_ns')))


def _named_fp(directory, name):
    _verified(directory)
    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=directory.fd)
    try:
        return fingerprint(fd)
    finally:
        os.close(fd)


def _safe(fp, root, size):
    if (not stat.S_ISREG(fp['mode']) or fp['dev'] != root.device
            or fp['nlink'] != 1 or (fp['flags'] & ~0x8040) != 0
            or fp['size'] != size):
        raise Error('candidate must be regular, have approved flags, nlink1, same-volume and exact-size')


def _load_manifest(root, relative, max_files, max_bytes):
    with ExitStack() as stack:
        parent, leaf = os.path.split(relative)
        directory = root.directory(parent)
        stack.callback(directory.close)
        _verified(directory)
        fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=directory.fd)
        stack.callback(os.close, fd)
        before = fingerprint(fd)
        if not stat.S_ISREG(before['mode']) or before['size'] > _MANIFEST_LIMIT:
            raise Error('manifest must be a regular file of at most 8 MiB')
        raw = bytearray()
        while len(raw) <= _MANIFEST_LIMIT:
            chunk = os.read(fd, min(_CHUNK, _MANIFEST_LIMIT + 1 - len(raw)))
            if not chunk:
                break
            raw.extend(chunk)
        if (len(raw) > _MANIFEST_LIMIT or fingerprint(fd) != before
                or _named_fp(directory, leaf) != before):
            raise Error('manifest changed or exceeded its bound')
    value = json.loads(raw)
    if not isinstance(value, dict) or not isinstance(value.get('groups'), list):
        raise Error('manifest requires a groups list')
    groups, seen, total = [], set(), 0
    for group in value['groups']:
        if not isinstance(group, dict):
            raise Error('invalid manifest group')
        sha, size, files = group.get('sha256'), group.get('size'), group.get('files')
        if (not isinstance(sha, str) or len(sha) != 64
                or any(c not in '0123456789abcdef' for c in sha)
                or type(size) is not int or size < 0
                or not isinstance(files, list) or not files):
            raise Error('invalid group hash, size or files')
        for item in files:
            if not isinstance(item, dict):
                raise Error('invalid manifest file')
            path = _path(item.get('path'))
            if path in seen:
                raise Error('duplicate manifest path: ' + path)
            for key in ('size', 'mtime_ns', 'ctime_ns', 'inode', 'device'):
                if type(item.get(key)) is not int or item[key] < 0:
                    raise Error('invalid manifest fingerprint: ' + path)
            if item['size'] != size:
                raise Error('group/file size disagreement: ' + path)
            seen.add(path)
            total += size
            if len(seen) > max_files or total > max_bytes:
                raise Error('manifest exceeds --max-files or --max-bytes')
        groups.append((sha, files))
    return groups, seen


def _managed(states, file, fp, sha):
    for state in reversed(states):
        if state['target'] != file.relative:
            continue
        if state['state'] in ('superseded', 'abandoned', 'prepared'):
            continue
        if state['state'] == 'uncertain':
            raise Error('uncertain journal state: ' + file.relative)
        if not state.get('restoration_eligible'):
            return None
        record = state['record']
        expected = record.get('after') or record.get('temp_fp')
        if record['hash'] != sha or not _matches(fp, expected, renamed=record.get('after') is None):
            raise Error('journal-managed target changed: ' + file.relative)
        verify_metadata(file.fd, record['metadata'])
        return record
    return None


@dataclass
class _Candidate:
    file: object
    fp: dict
    meta: dict
    sha: str
    evidence: object = None


def _check(candidate):
    _verified(candidate.file.parent)
    if candidate.file.current() != candidate.fp:
        raise Error('candidate changed: ' + candidate.file.relative)
    verify_metadata(candidate.file.fd, candidate.meta)


def _cloner():
    if sys.platform != 'darwin':
        raise Error('clonefileat requires Darwin; there is no copy fallback')
    library = ctypes.CDLL(None, use_errno=True)
    try:
        function = library.clonefileat
    except AttributeError as exc:
        raise Error('clonefileat unavailable; there is no fallback') from exc
    function.argtypes = (ctypes.c_int, ctypes.c_char_p, ctypes.c_int,
                         ctypes.c_char_p, ctypes.c_uint32)
    function.restype = ctypes.c_int
    return function


def _copy(source_fd, target_fd, size):
    offset = 0
    while offset < size:
        block = os.pread(source_fd, min(_CHUNK, size - offset), offset)
        if not block:
            raise Error('source shortened during ordinary copy')
        view = memoryview(block)
        while view:
            written = os.write(target_fd, view)
            if written <= 0:
                raise Error('ordinary copy made no write progress')
            view = view[written:]
        offset += len(block)


def _cleanup(directory, name, owned):
    if owned is None:
        return
    _verified(directory)
    try:
        current = os.stat(name, dir_fd=directory.fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    if (stat.S_ISREG(current.st_mode) and current.st_nlink == 1
            and (current.st_dev, current.st_ino) == (owned['dev'], owned['ino'])):
        os.unlink(name, dir_fd=directory.fd)
        fsync_directory(directory)


def _replace(root, journal, source, target, restoring, clone):
    ident = uuid.uuid4().hex
    name = '.artifact-storage-' + ident + '.tmp'
    directory = target.file.parent
    fd, owned, installed, prepared = None, None, False, False
    record = dict(transaction_id=ident, event='prepared',
                  operation='restore' if restoring else 'clone', target=target.file.relative,
                  source=source.file.relative, hash=target.sha, before=target.fp,
                  temp_name=name, temp_fp=None, metadata=target.meta, after=None,
                  before_hash=target.sha, before_metadata=target.meta)
    try:
        _check(source)
        _check(target)
        if restoring:
            fd = os.open(name, os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600, dir_fd=directory.fd)
            owned = fingerprint(fd)
            record['temp_fp'] = owned
            _safe(owned, root, 0)
            _copy(source.file.fd, fd, target.fp['size'])
        else:
            result = clone(source.file.parent.fd, os.fsencode(source.file.leaf),
                           directory.fd, os.fsencode(name), 1)  # CLONE_NOFOLLOW
            if result != 0:
                code = ctypes.get_errno()
                raise OSError(code, os.strerror(code), name)
            fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | os.O_CLOEXEC, dir_fd=directory.fd)
            owned = fingerprint(fd)
            record['temp_fp'] = owned
        current = fingerprint(fd)
        _safe(current, root, target.fp['size'])
        if any((current['dev'], current['ino']) == (c.fp['dev'], c.fp['ino'])
               for c in (source, target)):
            raise Error('replacement inode is not distinct')
        metadata(fd)  # Filesystem layer rejects ACL-bearing temporary files.
        if digest(fd) != target.sha:
            raise Error('replacement hash mismatch')
        apply_metadata(fd, target.meta)
        if digest(fd) != target.sha:
            raise Error('final replacement hash mismatch')
        apply_metadata(fd, target.meta)  # Restore atime after hashing.
        verify_metadata(fd, target.meta)
        os.fsync(fd)
        record['temp_fp'] = fingerprint(fd)
        _safe(record['temp_fp'], root, target.fp['size'])
        prepared = True  # append itself can fail after becoming durable.
        journal.append(record.copy())
        _check(source)
        _check(target)
        if (fingerprint(fd) != record['temp_fp']
                or _named_fp(directory, name) != record['temp_fp']):
            raise Error('temporary inode changed before rename')
        verify_metadata(fd, target.meta)
        _verified(directory)
        os.replace(name, target.file.leaf, src_dir_fd=directory.fd,
                   dst_dir_fd=directory.fd)
        installed = True  # Must precede every fallible post-rename operation.
        after = fingerprint(fd)
        if (not _matches(after, record['temp_fp'], True)
                or _named_fp(directory, target.file.leaf) != after):
            raise Error('installed replacement identity changed')
        verify_metadata(fd, target.meta)
        record['after'] = after
        fsync_directory(directory)
        journal.append({**record, 'event': 'restored' if restoring else 'completed'})
    except Exception as exc:
        failures = []
        error_record = {**record, 'event': 'error', 'renamed': installed,
                        'error': str(exc)}
        try:
            journal.append(error_record)
        except Exception as logging_error:
            failures.append('error append failed: ' + str(logging_error))
        if prepared or installed:
            try:
                reconcile(root, journal)
            except Exception as recovery_error:
                failures.append('reconciliation failed: ' + str(recovery_error))
        detail = '; '.join(failures) or 'error state recorded/reconciled'
        raise Error(f'{target.file.relative}: {exc}; {detail}; '
                    'installed bytes are never rolled back') from exc
    finally:
        try:
            if not installed:
                _cleanup(directory, name, owned)
        finally:
            if fd is not None:
                os.close(fd)


def _run(args):
    with ExitStack() as stack:
        root = RootFS(args.root)
        stack.callback(root.close)
        manifest = _relative(args.root, args.manifest)
        journal_path = _journal_path(_relative(args.root, args.journal))
        groups, paths = _load_manifest(root, manifest, args.max_files, args.max_bytes)
        if manifest == journal_path or manifest in paths or journal_path in paths:
            raise Error('manifest, journal and candidate paths must be distinct')
        if args.apply:
            stack.enter_context(MaintenanceLock(root))
        journal, states = None, []
        if args.apply or args.restore_unique:
            journal = Journal(root, journal_path, read_only=not args.apply)
            stack.callback(journal.close)
            if args.apply:
                journal.repair_tail()
            states = reconcile(root, journal)
            if any(s['state'] == 'uncertain' and s['target'] in paths for s in states):
                raise Error('uncertain journal state affects this manifest')
        batches, cutoff = [], time.time_ns() - _AGE_NS
        identities = set()
        for sha, entries in groups:
            batch = []
            for entry in entries:
                file = root.open_compiled(entry['path'])
                stack.callback(file.close)
                fp = file.current()
                _safe(fp, root, entry['size'])
                identity = (fp['dev'], fp['ino'])
                if identity in identities:
                    raise Error('duplicate candidate inode')
                identities.add(identity)
                if fp['mtime_ns'] > cutoff:
                    raise Error('candidate is younger than 24 hours: ' + file.relative)
                evidence = _managed(states, file, fp, sha)
                if evidence is not None and not args.restore_unique:
                    raise Error('already managed target; refresh manifest or restore first: ' + file.relative)
                keys = [('size', 'size'), ('mtime_ns', 'mtime_ns'), ('dev', 'device')]
                if evidence is None:
                    keys += [('ctime_ns', 'ctime_ns'), ('ino', 'inode')]
                if any(fp[a] != entry[b] for a, b in keys):
                    raise Error('stale manifest fingerprint: ' + file.relative)
                attrs = metadata(file.fd)
                if digest(file.fd) != sha or file.current() != fp:
                    raise Error('candidate hash or identity changed: ' + file.relative)
                verify_metadata(file.fd, attrs)
                batch.append(_Candidate(file, fp, attrs, sha, evidence))
            batches.append(batch)
        if args.restore_unique:
            plan = [(c, c) for batch in batches for c in batch
                    if c.evidence is not None
                    and c.evidence.get('operation', 'clone') == 'clone']
        else:
            plan = [(batch[0], c) for batch in batches for c in batch[1:]]
        # Recheck the entire validated set before the first replacement.
        for batch in batches:
            for candidate in batch:
                _check(candidate)
        if args.apply:
            clone = _cloner() if plan and not args.restore_unique else None
            for source, target in plan:
                _replace(root, journal, source, target, args.restore_unique, clone)
        return dict(dry_run=not args.apply,
                    operation='restore-unique' if args.restore_unique else 'clone',
                    candidate_files=len(paths), replacement_files=len(plan),
                    completed=len(plan) if args.apply else 0,
                    planned_logical_bytes=sum(c.fp['size'] for _, c in plan),
                    targets=[c.file.relative for _, c in plan])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--manifest', required=True)
    parser.add_argument('--journal', default='build/file-management/artifact-storage.jsonl')
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--exclusive-maintenance', action='store_true')
    parser.add_argument('--restore-unique', action='store_true')
    parser.add_argument('--max-files', type=int)
    parser.add_argument('--max-bytes', type=int)
    args = parser.parse_args(argv)
    if args.apply and not args.exclusive_maintenance:
        parser.error('--apply requires --exclusive-maintenance')
    if args.apply and (args.max_files is None or args.max_bytes is None):
        parser.error('--apply requires explicit --max-files and --max-bytes')
    args.max_files = 128 if args.max_files is None else args.max_files
    args.max_bytes = 1 << 30 if args.max_bytes is None else args.max_bytes
    if args.max_files <= 0 or args.max_bytes <= 0:
        parser.error('bounds must be positive')
    try:
        result = _run(args)
    except (Error, OSError, ValueError, TypeError, KeyError, RecursionError) as exc:
        print(json.dumps({'error': str(exc)}, ensure_ascii=True), file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
