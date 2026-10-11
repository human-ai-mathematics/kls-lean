import errno
import hashlib
import json
import os
import posixpath
import secrets
import stat

from .filesystem import Error, digest, fingerprint, fsync_directory, metadata


_EVENTS = {"prepared", "completed", "error", "restored"}
_OPERATIONS = {"clone", "restore"}
_FIELDS = (
    "transaction_id", "operation", "event", "target", "source", "hash",
    "before", "before_hash", "before_metadata", "temp_name", "temp_fp",
    "metadata", "after",
)
_FLAGS = os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
_MAX_JOURNAL = 64 * 1024 * 1024


def _path(value, name="path"):
    if not isinstance(value, str) or not value or value.startswith("/") or "\\" in value or "\x00" in value:
        raise Error("invalid %s" % name)
    parts = value.split("/")
    if any(not part or part in (".", "..") for part in parts):
        raise Error("invalid %s" % name)
    return "/".join(parts)


def _journal_path(value):
    value = _path(value, "journal path")
    parts = value.split("/")
    if len(parts) < 2 or parts[0] != "build":
        raise Error("journal must be below build")
    if parts[1].casefold() in ("review", "reviews", "verification", "verifications"):
        raise Error("journal is in a protected tree")
    return value


def _same_inode(a, b):
    return a.st_dev == b.st_dev and a.st_ino == b.st_ino


def _write_all(fd, data):
    view = memoryview(data)
    while view:
        count = os.write(fd, view)
        if count <= 0:
            raise OSError(errno.EIO, "short write")
        view = view[count:]


def _stable_fp_equal(first, second):
    if not isinstance(first, dict) or not isinstance(second, dict):
        return False
    fields = ("dev", "ino", "mode", "uid", "gid", "nlink", "size", "mtime_ns", "flags", "birthtime_hex")
    return all(first.get(field) == second.get(field) for field in fields)


class MaintenanceLock:
    """A non-stealing, root-scoped maintenance lock."""

    def __init__(self, root_fs):
        self.root_fs = root_fs
        self._dir = None
        self._fd = None
        self._stat = None
        self._parent_stat = None
        self._token = None
        self._root_token = False

    def __enter__(self):
        if getattr(self.root_fs, "_storage_lock_held", False):
            raise Error("maintenance lock already held")
        try:
            self._dir = self.root_fs.directory("build/file-management", create=False)
            if self._dir.verified() is False:
                raise Error("unverified maintenance-lock directory")
            self._parent_stat = os.fstat(self._dir.fd)
            try:
                self._fd = os.open(
                    ".artifact-storage.lock",
                    os.O_RDWR | os.O_CREAT | os.O_EXCL | _FLAGS,
                    0o600,
                    dir_fd=self._dir.fd,
                )
            except FileExistsError as exc:
                raise Error("maintenance lock exists; stale locks are not stolen") from exc
            self._stat = os.fstat(self._fd)
            if not stat.S_ISREG(self._stat.st_mode) or self._stat.st_nlink != 1:
                raise Error("invalid maintenance lock inode")
            named = os.stat(".artifact-storage.lock", dir_fd=self._dir.fd, follow_symlinks=False)
            if not _same_inode(named, self._stat):
                raise Error("maintenance lock entry changed")
            self._token = secrets.token_hex(24).encode("ascii") + b"\n"
            _write_all(self._fd, self._token)
            os.fsync(self._fd)
            fsync_directory(self._dir)
            setattr(self.root_fs, "_storage_lock_held", True)
            self._root_token = True
            return self
        except Exception:
            try:
                self._remove_owned()
            finally:
                self._close()
            raise

    def _check_parent(self):
        if self._dir is None or self._parent_stat is None:
            raise Error("maintenance lock is closed")
        if not self._dir.verified():
            raise Error("maintenance-lock directory namespace changed")
        current = os.fstat(self._dir.fd)
        if not _same_inode(current, self._parent_stat):
            raise Error("maintenance-lock directory changed")

    def _remove_owned(self):
        if self._fd is None or self._dir is None or self._stat is None:
            return
        self._check_parent()
        current = os.fstat(self._fd)
        named = os.stat(".artifact-storage.lock", dir_fd=self._dir.fd, follow_symlinks=False)
        if not _same_inode(current, self._stat) or not _same_inode(named, self._stat):
            raise Error("maintenance lock ownership changed; refusing removal")
        if current.st_nlink != 1 or not stat.S_ISREG(current.st_mode):
            raise Error("maintenance lock inode changed; refusing removal")
        os.unlink(".artifact-storage.lock", dir_fd=self._dir.fd)
        fsync_directory(self._dir)

    def _close(self):
        fd, directory = self._fd, self._dir
        owned = self._root_token
        self._fd = self._dir = None
        self._stat = self._parent_stat = None
        self._root_token = False
        if fd is not None:
            os.close(fd)
        if directory is not None:
            directory.close()
        if owned:
            setattr(self.root_fs, "_storage_lock_held", False)

    def release(self):
        try:
            self._remove_owned()
        finally:
            self._close()

    def __exit__(self, exc_type, exc, tb):
        self.release()
        return False


class Journal:
    def __init__(self, root_fs, journal_relative, read_only=False):
        self.root_fs = root_fs
        self.relative = _journal_path(journal_relative)
        parent_name, self.leaf = posixpath.split(self.relative)
        self.read_only = bool(read_only)
        self._parent = None
        self._fd = None
        self._parent_stat = None
        self._journal_stat = None
        self._tail = b""
        self._tail_offset = 0
        self._created = False
        try:
            self._parent = root_fs.directory(parent_name, create=False)
            if self._parent.verified() is False:
                raise Error("unverified journal directory")
            self._parent_stat = os.fstat(self._parent.fd)
            exists = True
            try:
                os.stat(self.leaf, dir_fd=self._parent.fd, follow_symlinks=False)
            except FileNotFoundError:
                exists = False
            if self.read_only and not exists:
                raise Error("journal does not exist")
            if exists:
                flags = os.O_RDONLY if self.read_only else os.O_RDWR | os.O_APPEND
                self._fd = os.open(self.leaf, flags | _FLAGS, dir_fd=self._parent.fd)
            else:
                try:
                    self._fd = os.open(
                        self.leaf,
                        os.O_RDWR | os.O_APPEND | os.O_CREAT | os.O_EXCL | _FLAGS,
                        0o600,
                        dir_fd=self._parent.fd,
                    )
                    self._created = True
                except FileExistsError:
                    self._fd = os.open(self.leaf, os.O_RDWR | os.O_APPEND | _FLAGS, dir_fd=self._parent.fd)
            self._journal_stat = os.fstat(self._fd)
            self._check_binding()
            if self._created:
                fsync_directory(self._parent)
        except Exception:
            if self._fd is not None:
                os.close(self._fd)
                self._fd = None
            if self._parent is not None:
                self._parent.close()
                self._parent = None
            raise

    def _check_fd(self):
        if self._fd is None or self._journal_stat is None:
            raise Error("closed journal")
        current = os.fstat(self._fd)
        if not stat.S_ISREG(current.st_mode) or current.st_nlink != 1:
            raise Error("journal is not an unlinked regular file")
        if not _same_inode(current, self._journal_stat):
            raise Error("journal inode changed")
        if self._parent_stat is not None and current.st_dev != self._parent_stat.st_dev:
            raise Error("journal is on the wrong volume")
        try:
            fp = fingerprint(self._fd)
        except (OSError, Error, ValueError) as exc:
            raise Error("journal fingerprint unavailable") from exc
        if fp.get("flags", -1) & ~0x40:
            raise Error("journal has unsafe flags")

    def _check_binding(self):
        self._check_fd()
        if self._parent is None or self._parent_stat is None:
            raise Error("closed journal")
        if not self._parent.verified():
            raise Error("journal directory namespace changed")
        parent = os.fstat(self._parent.fd)
        if not _same_inode(parent, self._parent_stat):
            raise Error("journal directory changed")
        named = os.stat(self.leaf, dir_fd=self._parent.fd, follow_symlinks=False)
        current = os.fstat(self._fd)
        if not _same_inode(named, current) or named.st_nlink != 1:
            raise Error("journal entry changed")

    def close(self):
        fd, parent = self._fd, self._parent
        self._fd = self._parent = None
        self._journal_stat = self._parent_stat = None
        if fd is not None:
            os.close(fd)
        if parent is not None:
            parent.close()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        self.close()
        return False

    @staticmethod
    def _record(record, require_operation=False):
        if not isinstance(record, dict):
            raise Error("journal record is not an object")
        record = dict(record)
        for key in _FIELDS:
            record.setdefault(key, None)
        if not isinstance(record["transaction_id"], str) or not record["transaction_id"]:
            raise Error("journal record has no transaction id")
        if record["event"] not in _EVENTS:
            raise Error("invalid journal event")
        operation = record["operation"]
        if require_operation and operation not in _OPERATIONS:
            raise Error("journal record has invalid operation")
        if operation is not None and operation not in _OPERATIONS:
            raise Error("invalid journal operation")
        for key in ("target", "source"):
            if record[key] is not None:
                record[key] = _path(record[key], key)
        temp_name = record["temp_name"]
        if temp_name is not None and (not isinstance(temp_name, str) or not temp_name or "/" in temp_name or temp_name in (".", "..")):
            raise Error("invalid temporary name")
        value = record["hash"]
        if value is not None and (not isinstance(value, str) or len(value) != 64 or any(ch not in "0123456789abcdef" for ch in value)):
            raise Error("invalid artifact hash")
        for key in ("before", "temp_fp", "after"):
            if record[key] is not None and not isinstance(record[key], dict):
                raise Error("invalid %s fingerprint" % key)
        for key in ("before_metadata", "metadata"):
            if record[key] is not None and not isinstance(record[key], dict):
                raise Error("invalid metadata")
        return record

    def append(self, record):
        if self._fd is None:
            raise Error("closed journal")
        if self.read_only:
            raise Error("read-only journal")
        self._check_binding()
        self.records()
        if self._tail:
            raise Error("journal has an unrepaired torn tail")
        record = self._record(record, require_operation=True)
        try:
            data = (json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode("utf-8")
        except (TypeError, ValueError) as exc:
            raise Error("journal record is not serializable") from exc
        size = os.fstat(self._fd).st_size
        if size + len(data) > _MAX_JOURNAL:
            raise Error("journal is too large")
        self._check_binding()
        _write_all(self._fd, data)
        os.fsync(self._fd)
        self._check_binding()

    @staticmethod
    def _parse(data):
        if len(data) > _MAX_JOURNAL:
            raise Error("journal is too large")
        if not data:
            return [], 0, b""
        complete_end = len(data) if data.endswith(b"\n") else data.rfind(b"\n") + 1
        complete = data[:complete_end]
        tail = data[complete_end:]
        result = []
        for line in complete.split(b"\n")[:-1]:
            if not line:
                raise Error("journal has a blank complete record")
            try:
                item = json.loads(line.decode("utf-8"))
            except (UnicodeError, ValueError) as exc:
                raise Error("journal contains invalid JSON") from exc
            result.append(Journal._record(item))
        return result, complete_end, tail

    def _read_raw(self):
        self._check_binding()
        before = fingerprint(self._fd)
        size = before["size"]
        if size > _MAX_JOURNAL:
            raise Error("journal is too large")
        chunks = []
        offset = 0
        while offset < size:
            block = os.pread(self._fd, min(65536, size - offset), offset)
            if not block:
                raise Error("journal read changed unexpectedly")
            chunks.append(block)
            offset += len(block)
        data = b"".join(chunks)
        self._check_binding()
        if fingerprint(self._fd) != before:
            raise Error("journal changed while reading")
        return data

    def records(self):
        data = self._read_raw()
        result, end, tail = self._parse(data)
        self._tail = tail
        self._tail_offset = end
        return result

    @property
    def torn_tail(self):
        return self._tail

    @property
    def raw_tail(self):
        return self._tail

    @property
    def tail_offset(self):
        return self._tail_offset

    def repair_tail(self):
        if self._fd is None:
            raise Error("closed journal")
        if self.read_only:
            raise Error("cannot repair a read-only journal")
        if getattr(self.root_fs, "_storage_lock_held", False) is not True:
            raise Error("journal repair requires the storage lock")
        self._check_binding()
        original_fp = fingerprint(self._fd)
        original = self._read_raw()
        records, end, tail = self._parse(original)
        self._tail = tail
        self._tail_offset = end
        if not tail:
            return None
        name = None
        artifact_fd = None
        try:
            for _ in range(16):
                candidate = ".%s.recovery.%s" % (self.leaf, secrets.token_hex(16))
                try:
                    artifact_fd = os.open(candidate, os.O_WRONLY | os.O_CREAT | os.O_EXCL | _FLAGS, 0o600, dir_fd=self._parent.fd)
                    name = candidate
                    break
                except FileExistsError:
                    continue
            if artifact_fd is None:
                raise Error("cannot create journal recovery artifact")
            header = json.dumps({"before": original_fp, "sha256": hashlib.sha256(original).hexdigest(), "valid_prefix_bytes": end}, sort_keys=True).encode("ascii")
            payload = b"ARTIFACT-STORAGE-JOURNAL-RECOVERY-1\n" + header + b"\n" + len(original).to_bytes(8, "big") + original
            _write_all(artifact_fd, payload)
            os.fsync(artifact_fd)
            artifact_stat = os.fstat(artifact_fd)
            if not stat.S_ISREG(artifact_stat.st_mode) or artifact_stat.st_nlink != 1:
                raise Error("invalid recovery artifact")
            fsync_directory(self._parent)
        finally:
            if artifact_fd is not None:
                os.close(artifact_fd)
        self._check_binding()
        backup_fd = os.open(name, os.O_RDONLY | _FLAGS, dir_fd=self._parent.fd)
        try:
            backup = os.fstat(backup_fd)
            named = os.stat(name, dir_fd=self._parent.fd, follow_symlinks=False)
            if (not _same_inode(backup, artifact_stat) or not _same_inode(named, artifact_stat)
                    or backup.st_nlink != 1 or digest(backup_fd) != hashlib.sha256(payload).hexdigest()):
                raise Error("journal recovery backup changed")
        finally:
            os.close(backup_fd)
        current = self._read_raw()
        if current != original or fingerprint(self._fd) != original_fp:
            raise Error("journal changed before repair")
        os.ftruncate(self._fd, end)
        os.fsync(self._fd)
        self._check_binding()
        fsync_directory(self._parent)
        self._tail = b""
        self._tail_offset = end
        return posixpath.join(posixpath.dirname(self.relative), name)

    def reconcile(self, root_fs=None):
        return reconcile(root_fs or self.root_fs, self)


def _snapshot(ref):
    try:
        first = ref.current() if hasattr(ref, "current") else fingerprint(ref.fd)
        flags = first.get("flags")
        if (not stat.S_ISREG(first.get("mode", 0)) or first.get("nlink") != 1
                or flags is None or (flags & ~0x8040) != 0):
            return None, "unsafe"
        saved_metadata = metadata(ref.fd)
        saved_hash = digest(ref.fd)
        last = ref.current() if hasattr(ref, "current") else fingerprint(ref.fd)
        if first != last or metadata(ref.fd) != saved_metadata:
            return None, "changed"
        return {"fp": first, "hash": saved_hash, "metadata": saved_metadata}, "ok"
    except (OSError, Error, ValueError):
        return None, "unreadable"


def _target_snapshot(root_fs, path):
    if not isinstance(path, str):
        return None, "unavailable"
    try:
        ref = root_fs.open_compiled(path)
    except FileNotFoundError:
        return None, "missing"
    except (OSError, Error, ValueError):
        return None, "unavailable"
    try:
        return _snapshot(ref)
    finally:
        ref.close()


def _temp_snapshot(root_fs, target, name):
    if name is None:
        return None, "missing"
    if not isinstance(name, str) or not name or "/" in name or name in (".", ".."):
        return None, "invalid"
    try:
        target = _path(target, "target")
        parent_name = posixpath.dirname(target)
        directory = root_fs.directory(parent_name, create=False)
    except (OSError, Error, ValueError):
        return None, "unavailable"
    fd = None
    try:
        if directory.verified() is False:
            return None, "unavailable"
        try:
            fd = os.open(name, os.O_RDONLY | _FLAGS, dir_fd=directory.fd)
        except FileNotFoundError:
            return None, "missing"
        class Ref:
            pass
        ref = Ref()
        ref.fd = fd
        result = _snapshot(ref)
        named = os.stat(name, dir_fd=directory.fd, follow_symlinks=False)
        if not _same_inode(named, os.fstat(fd)):
            return None, "changed"
        return result
    except (OSError, Error, ValueError):
        return None, "unavailable"
    finally:
        if fd is not None:
            os.close(fd)
        directory.close()


def _same_install_fp(actual, expected):
    return _stable_fp_equal(actual, expected)


def _installed(snapshot, record):
    return snapshot is not None and _same_install_fp(snapshot["fp"], record.get("temp_fp")) and snapshot["hash"] == record.get("hash") and snapshot["metadata"] == record.get("metadata")


def _completed(snapshot, record):
    after = record.get("after")
    return snapshot is not None and isinstance(after, dict) and snapshot["fp"] == after and snapshot["hash"] == record.get("hash") and snapshot["metadata"] == record.get("metadata")


def _before_expected(record):
    before = record.get("before")
    if isinstance(before, dict) and isinstance(before.get("fp"), dict):
        return before.get("fp"), before.get("hash"), before.get("metadata")
    return before, record.get("before_hash"), record.get("before_metadata")


def _original(snapshot, record):
    fp, value_hash, value_metadata = _before_expected(record)
    return snapshot is not None and isinstance(fp, dict) and value_hash is not None and isinstance(value_metadata, dict) and snapshot["fp"] == fp and snapshot["hash"] == value_hash and snapshot["metadata"] == value_metadata


def _copy_record(record, actual=None):
    result = dict(record)
    if actual is not None:
        result["after"] = actual["fp"]
    return result


def reconcile(root_fs, journal):
    records = journal.records()
    groups = {}
    positions = {}
    for index, record in enumerate(records):
        transaction_id = record["transaction_id"]
        groups.setdefault(transaction_id, []).append(record)
        positions.setdefault(transaction_id, []).append(index)
    items = []
    latest_by_target = {}
    for transaction_id, history in groups.items():
        prepared_index = max((index for index, record in enumerate(history) if record["event"] == "prepared"), default=-1)
        prepared = history[prepared_index] if prepared_index >= 0 else None
        terminal_index = max((index for index, record in enumerate(history) if record["event"] in ("completed", "restored", "error") and index > prepared_index), default=-1)
        terminal = history[terminal_index] if terminal_index >= 0 else None
        base = prepared or terminal or history[-1]
        target = base.get("target")
        item = {
            "transaction_id": transaction_id,
            "operation": base.get("operation"),
            "target": target,
            "source": base.get("source"),
            "record": _copy_record(base),
            "restoration_eligible": False,
        }
        if isinstance(target, str):
            latest_by_target[target] = (positions[transaction_id][-1], transaction_id)
        if prepared is None:
            if terminal is not None and terminal["event"] == "error":
                prepared = terminal
            else:
                item.update(state="uncertain", classification="uncertain", reason="no prepared record")
                items.append(item)
                continue
        operation = prepared.get("operation")
        if operation not in _OPERATIONS:
            item.update(state="uncertain", classification="uncertain", reason="unknown operation")
            items.append(item)
            continue
        if terminal is not None and terminal["event"] != "error":
            current, reason = _target_snapshot(root_fs, terminal.get("target"))
            valid = _completed(current, terminal)
            if valid and terminal["event"] == "restored":
                item.update(state="restored", classification="restored", record=_copy_record(terminal))
            elif valid and terminal["event"] == "completed":
                item.update(state="completed", classification="completed", record=_copy_record(terminal), restoration_eligible=(operation == "clone"))
            else:
                item.update(state="uncertain", classification="uncertain", reason=reason or "current target does not match completion")
            items.append(item)
            continue
        target_snapshot, target_state = _target_snapshot(root_fs, prepared.get("target"))
        temp_snapshot, temp_state = _temp_snapshot(root_fs, prepared.get("target"), prepared.get("temp_name"))
        known_after = next((r for r in reversed(history) if isinstance(r.get('after'), dict)), None)
        if known_after is not None and (not _completed(target_snapshot, known_after) or temp_state != 'missing'):
            item.update(state='uncertain', classification='uncertain', reason='known installed fingerprint changed')
            items.append(item)
            continue
        original = _original(target_snapshot, prepared)
        installed = _installed(temp_snapshot, prepared)
        if original and temp_state == "missing":
            item.update(state="abandoned", classification="abandoned", record=_copy_record(prepared))
        elif original and temp_state == "ok" and installed:
            item.update(state="prepared", classification="prepared", record=_copy_record(prepared))
        elif _installed(target_snapshot, prepared) and temp_state == "missing":
            if operation == "restore":
                item.update(state="restored", classification="restored", phase="installed", record=_copy_record(prepared, target_snapshot))
            else:
                item.update(state="installed", classification="installed", record=_copy_record(prepared, target_snapshot), restoration_eligible=True)
        else:
            item.update(state="uncertain", classification="uncertain", reason="target=%s,temp=%s" % (target_state, temp_state))
        items.append(item)
    # A failed pre-rename operation must not supersede a still-installed clone.
    latest_by_target = {}
    for item in items:
        if item['state'] in ('completed', 'restored', 'installed'):
            key = item['target']
            index = max(positions[item['transaction_id']])
            if key not in latest_by_target or index > latest_by_target[key][0]:
                latest_by_target[key] = (index, item['transaction_id'])
    for item in items:
        latest = latest_by_target.get(item.get('target'))
        if latest is not None and latest[1] != item['transaction_id'] and latest[0] > max(positions[item['transaction_id']]):
            item['state'] = 'superseded'
            item['classification'] = 'superseded'
            item['superseded_by'] = latest[1]
            item['restoration_eligible'] = False
    return items
