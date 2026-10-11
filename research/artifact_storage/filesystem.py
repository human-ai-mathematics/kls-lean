import base64
import ctypes
import errno
import hashlib
import os
import stat
import sys


class Error(Exception):
    pass


class _FSID(ctypes.Structure):
    _fields_ = [('val', ctypes.c_int32 * 2)]


class _StatFS64(ctypes.Structure):
    _fields_ = [
        ('f_bsize', ctypes.c_uint32),
        ('f_iosize', ctypes.c_int32),
        ('f_blocks', ctypes.c_uint64),
        ('f_bfree', ctypes.c_uint64),
        ('f_bavail', ctypes.c_uint64),
        ('f_files', ctypes.c_uint64),
        ('f_ffree', ctypes.c_uint64),
        ('f_fsid', _FSID),
        ('f_owner', ctypes.c_uint32),
        ('f_type', ctypes.c_uint32),
        ('f_flags', ctypes.c_uint32),
        ('f_fssubtype', ctypes.c_uint32),
        ('f_fstypename', ctypes.c_char * 16),
        ('f_mntonname', ctypes.c_char * 1024),
        ('f_mntfromname', ctypes.c_char * 1024),
        ('f_flags_ext', ctypes.c_uint32),
        ('f_reserved', ctypes.c_uint32 * 7),
    ]


def _statfs_fd(fd):
    if ctypes.sizeof(_StatFS64) != 2168 or _StatFS64.f_fstypename.offset != 72:
        raise Error('unsupported statfs64 ABI')
    if sys.platform != 'darwin':
        raise Error('only Darwin APFS is supported')
    libc = ctypes.CDLL(None, use_errno=True)
    fn = getattr(libc, 'fstatfs', None)
    if fn is None:
        raise Error('fd-based fstatfs is unavailable')
    fn.argtypes = [ctypes.c_int, ctypes.POINTER(_StatFS64)]
    fn.restype = ctypes.c_int
    value = _StatFS64()
    if fn(fd, ctypes.byref(value)) != 0:
        e = ctypes.get_errno()
        raise Error('fstatfs failed: ' + os.strerror(e))
    if bytes(value.f_fstypename).split(b'\0', 1)[0] != b'apfs':
        raise Error('only APFS is supported')


def _flags():
    if not hasattr(os, 'O_NOFOLLOW') or not hasattr(os, 'O_DIRECTORY'):
        raise Error('required descriptor flags unavailable')
    return os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK


def _parts(value, empty=False):
    if not isinstance(value, str) or '\x00' in value or value.startswith('/'):
        raise Error('invalid relative path')
    if not value:
        if empty:
            return []
        raise Error('empty relative path')
    result = value.split('/')
    if any(not p or p in ('.', '..') for p in result):
        raise Error('unsafe relative path')
    return result


def _stat_tuple(st):
    return (st.st_dev, st.st_ino, st.st_mode, st.st_uid, st.st_gid,
            st.st_atime_ns, st.st_mtime_ns, st.st_ctime_ns)


def fingerprint(fd):
    try:
        first = os.fstat(fd)
        second = os.fstat(fd)
    except OSError as exc:
        raise Error(str(exc)) from exc
    if _stat_tuple(first) != _stat_tuple(second):
        raise Error('file changed while fingerprinting')
    return {
        'dev': int(first.st_dev), 'ino': int(first.st_ino),
        'mode': int(first.st_mode), 'uid': int(first.st_uid),
        'gid': int(first.st_gid), 'nlink': int(first.st_nlink),
        'size': int(first.st_size), 'mtime_ns': int(first.st_mtime_ns),
        'ctime_ns': int(first.st_ctime_ns),
        'flags': int(getattr(first, 'st_flags', 0)),
        'birthtime_hex': float(first.st_birthtime).hex(),
    }


def digest(fd):
    before = fingerprint(fd)
    if not stat.S_ISREG(before['mode']):
        raise Error('digest requires a regular file')
    h = hashlib.sha256()
    offset = 0
    total = 0
    while total < before['size']:
        try:
            block = os.pread(fd, min(1024 * 1024, before['size'] - total), offset)
        except OSError as exc:
            raise Error(str(exc)) from exc
        if not block:
            raise Error('short read while hashing')
        h.update(block)
        total += len(block)
        offset += len(block)
    after = fingerprint(fd)
    if before != after or total != before['size']:
        raise Error('file changed while hashing')
    return h.hexdigest()


def _acl_check(fd):
    if sys.platform != 'darwin':
        raise Error('Darwin extended ACL API required')
    libc = ctypes.CDLL(None, use_errno=True)
    try:
        get_acl, get_entry, free_acl = libc.acl_get_fd_np, libc.acl_get_entry, libc.acl_free
    except AttributeError as exc:
        raise Error('extended ACL API unavailable') from exc
    get_acl.argtypes = [ctypes.c_int, ctypes.c_int]
    get_acl.restype = ctypes.c_void_p
    get_entry.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.POINTER(ctypes.c_void_p)]
    get_entry.restype = ctypes.c_int
    free_acl.argtypes = [ctypes.c_void_p]
    free_acl.restype = ctypes.c_int
    ctypes.set_errno(0)
    acl = get_acl(fd, 0x100)  # SDK ACL_TYPE_EXTENDED.
    if not acl:
        code = ctypes.get_errno()
        # Apple Libc reads FILESEC_ACL from a successful fstatx_np; absent
        # extended ACL properties return ENOENT. This held regular fd is
        # checked again by metadata(), so missing path errors are excluded.
        if code == errno.ENOENT and stat.S_ISREG(os.fstat(fd).st_mode):
            return
        raise Error('unable to read extended ACL: ' + os.strerror(code))
    try:
        entry = ctypes.c_void_p()
        ctypes.set_errno(0)
        result = get_entry(acl, 0, ctypes.byref(entry))  # SDK ACL_FIRST_ENTRY.
        if result == 0:
            raise Error('ACL-bearing files are not supported')
        if result != -1 or ctypes.get_errno() != errno.EINVAL:
            raise Error('unable to inspect ACL entries')
    finally:
        free_acl(acl)


def _xattr_api(name):
    # Darwin sys/xattr.h descriptor APIs; Python os exposes these only on Linux.
    if sys.platform != 'darwin':
        raise Error('Darwin descriptor xattr API required')
    libc = ctypes.CDLL(None, use_errno=True)
    fn = getattr(libc, name)
    signatures = {
        'flistxattr': ([ctypes.c_int, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int], ctypes.c_ssize_t),
        'fgetxattr': ([ctypes.c_int, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_uint32, ctypes.c_int], ctypes.c_ssize_t),
        'fsetxattr': ([ctypes.c_int, ctypes.c_char_p, ctypes.c_void_p, ctypes.c_size_t, ctypes.c_uint32, ctypes.c_int], ctypes.c_int),
        'fremovexattr': ([ctypes.c_int, ctypes.c_char_p, ctypes.c_int], ctypes.c_int),
    }
    fn.argtypes, fn.restype = signatures[name]
    return fn


def _xattr_read(fn, prefix, suffix, bound):
    size = fn(*prefix, None, 0, *suffix)
    if size < 0 or size > bound:
        raise Error('xattr read failed or exceeded bound')
    buffer = ctypes.create_string_buffer(max(size, 1))
    got = fn(*prefix, buffer, size, *suffix)
    if got != size:
        raise Error('xattr changed while reading')
    return buffer.raw[:size]


def _xattrs(fd):
    raw = _xattr_read(_xattr_api('flistxattr'), [fd], [0], 1 << 20)
    if raw and not raw.endswith(b'\0'):
        raise Error('invalid xattr name list')
    names = raw[:-1].split(b'\0') if raw else []
    if len(names) != len(set(names)) or any(not n for n in names):
        raise Error('duplicate or empty xattr name')
    result = {}
    for raw_name in names:
        try:
            name = raw_name.decode('utf-8')
        except UnicodeDecodeError as exc:
            raise Error('non-UTF-8 extended attribute name') from exc
        lower = name.lower()
        if (lower.startswith('com.apple.acl') or lower.startswith('system.posix_acl_')
                or lower in ('security.acl', 'user.acl')):
            raise Error('ACL-bearing files are not supported')
        value = _xattr_read(_xattr_api('fgetxattr'), [fd, raw_name], [0, 0], 16 << 20)
        result[name] = base64.b64encode(value).decode('ascii')
    return dict(sorted(result.items()))


def _remove_xattr(fd, name):
    if _xattr_api('fremovexattr')(fd, name.encode('utf-8'), 0) != 0:
        raise Error('unable to remove extended attribute')


def _set_xattr(fd, name, value):
    buffer = ctypes.create_string_buffer(value, max(1, len(value)))
    if _xattr_api('fsetxattr')(fd, name.encode('utf-8'), buffer, len(value), 0, 0) != 0:
        raise Error('unable to set extended attribute')


def _fchflags(fd, flags):
    if type(flags) is not int or flags < 0 or flags & ~0x8040:
        raise Error('invalid flags')
    import ctypes
    native = ctypes.CDLL(None, use_errno=True).fchflags
    native.argtypes = (ctypes.c_int, ctypes.c_uint32)
    native.restype = ctypes.c_int
    if native(fd, flags) != 0:
        raise OSError(ctypes.get_errno(), 'fchflags failed')


def metadata(fd):
    try:
        before = os.fstat(fd)
        _acl_check(fd)
        values = _xattrs(fd)
        after = os.fstat(fd)
    except OSError as exc:
        raise Error(str(exc)) from exc
    if _stat_tuple(before) != _stat_tuple(after):
        raise Error('metadata changed while reading')
    flags = int(after.st_flags)
    if flags < 0 or flags & ~0x8040:
        raise Error('unsupported flags')
    return {
        'mode': int(stat.S_IMODE(after.st_mode)),
        'uid': int(after.st_uid), 'gid': int(after.st_gid),
        'atime_ns': int(after.st_atime_ns), 'mtime_ns': int(after.st_mtime_ns),
        'flags': flags,
        'xattrs': values,
    }


def _decode_metadata(value):
    if not isinstance(value, dict) or set(value) != {
            'mode', 'uid', 'gid', 'atime_ns', 'mtime_ns', 'flags', 'xattrs'}:
        raise Error('invalid metadata dictionary')
    result = {}
    for key in ('mode', 'uid', 'gid', 'atime_ns', 'mtime_ns', 'flags'):
        item = value[key]
        if type(item) is not int or item < 0:
            raise Error('invalid metadata integer')
        result[key] = item
    if result['mode'] & ~0o7777:
        raise Error('invalid metadata mode')
    if result['flags'] & ~0x8040:
        raise Error('invalid metadata flags')
    if not isinstance(value['xattrs'], dict):
        raise Error('invalid xattrs dictionary')
    attrs = {}
    for name, encoded in value['xattrs'].items():
        if not isinstance(name, str) or not name or '\x00' in name:
            raise Error('invalid xattr name')
        if not isinstance(encoded, str):
            raise Error('invalid xattr value')
        try:
            raw = base64.b64decode(encoded.encode('ascii'), validate=True)
        except (ValueError, UnicodeEncodeError) as exc:
            raise Error('invalid base64 xattr') from exc
        if base64.b64encode(raw).decode('ascii') != encoded:
            raise Error('non-canonical base64 xattr')
        attrs[name] = encoded
    result['xattrs'] = dict(sorted(attrs.items()))
    return result


def verify_metadata(fd, expected):
    expected = _decode_metadata(expected)
    actual = metadata(fd)
    if actual != expected:
        raise Error('metadata mismatch')


def apply_metadata(fd, value):
    value = _decode_metadata(value)
    _acl_check(fd)
    try:
        current = metadata(fd)
        if current['uid'] != value['uid'] or current['gid'] != value['gid']:
            os.fchown(fd, value['uid'], value['gid'])
        os.fchmod(fd, 0o600)  # Own temporary inode; xattr writes require owner write.
        current_names = set(current['xattrs'])
        wanted_names = set(value['xattrs'])
        for name in current_names - wanted_names:
            _remove_xattr(fd, name)
        for name, encoded in value['xattrs'].items():
            _set_xattr(fd, name, base64.b64decode(encoded))
        os.utime(fd, ns=(value['atime_ns'], value['mtime_ns']))
        _fchflags(fd, value['flags'])
        os.fchmod(fd, value['mode'])
    except OSError as exc:
        raise Error(str(exc)) from exc
    verify_metadata(fd, value)


class DirRef:
    def __init__(self, root, relative, owned_fds):
        self.root = root
        self.relative = relative
        self.owned_fds = list(owned_fds)
        self.fd = self.owned_fds[-1]
        self._closed = False

    def verified(self):
        if self._closed or not self.root.verified():
            return False
        try:
            parts = _parts(self.relative, empty=True)
            if len(self.owned_fds) != len(parts) + 1:
                return False
            for index, fd in enumerate(self.owned_fds):
                st = os.fstat(fd)
                if not stat.S_ISDIR(st.st_mode) or st.st_dev != self.root.device:
                    return False
                named = os.fstat(self.root.fd) if index == 0 else os.stat(
                    parts[index - 1], dir_fd=self.owned_fds[index - 1], follow_symlinks=False)
                if (st.st_dev, st.st_ino) != (named.st_dev, named.st_ino) or not stat.S_ISDIR(named.st_mode):
                    return False
            return True
        except OSError:
            return False

    def close(self):
        if self._closed:
            return
        self._closed = True
        fds = self.owned_fds
        self.owned_fds = []
        for fd in reversed(fds):
            try:
                os.close(fd)
            except OSError:
                pass


class FileRef:
    def __init__(self, fd, parent, leaf, relative):
        self.fd = fd
        self.parent = parent
        self.leaf = leaf
        self.relative = relative
        self._closed = False

    def current(self):
        if self._closed or not self.parent.verified():
            raise Error('file anchor is closed or unverified')
        current = fingerprint(self.fd)
        named = os.stat(self.leaf, dir_fd=self.parent.fd, follow_symlinks=False)
        if not stat.S_ISREG(named.st_mode) or (named.st_dev, named.st_ino) != (current['dev'], current['ino']):
            raise Error('named file identity changed')
        return current

    def close(self):
        if self._closed:
            return
        self._closed = True
        try:
            os.close(self.fd)
        except OSError:
            pass
        finally:
            self.parent.close()


class RootFS:
    def __init__(self, root_path):
        absolute = os.path.abspath(os.fspath(root_path))
        parts = absolute.split(os.sep)[1:]
        self._anchors = []
        self._root_parts = parts
        self._closed = False
        try:
            current = os.open('/', _flags() | os.O_DIRECTORY)
            self._anchors.append(current)
            for part in parts:
                child = os.open(part, _flags() | os.O_DIRECTORY, dir_fd=current)
                self._anchors.append(child)
                current = child
            self.fd = current
            self.device = os.fstat(current).st_dev
            _statfs_fd(current)
            if not self.verified():
                raise Error('root namespace changed')
        except Exception:
            for fd in reversed(self._anchors):
                os.close(fd)
            self._anchors = []
            raise

    def verified(self):
        if self._closed:
            return False
        try:
            for index, part in enumerate(self._root_parts, 1):
                held = os.fstat(self._anchors[index])
                named = os.stat(part, dir_fd=self._anchors[index - 1], follow_symlinks=False)
                if not stat.S_ISDIR(named.st_mode) or (held.st_dev, held.st_ino) != (named.st_dev, named.st_ino):
                    return False
            return True
        except OSError:
            return False

    def directory(self, relative_dir, create=False):
        if self._closed:
            raise Error('root is closed')
        parts = _parts(relative_dir, empty=True)
        owned = []
        try:
            current = os.dup(self.fd)
            owned.append(current)
            for part in parts:
                try:
                    child = os.open(part, _flags() | getattr(os, 'O_DIRECTORY', 0),
                                    dir_fd=current)
                except FileNotFoundError:
                    if not create:
                        raise
                    os.mkdir(part, 0o755, dir_fd=current)
                    child = os.open(part, _flags() | getattr(os, 'O_DIRECTORY', 0),
                                    dir_fd=current)
                owned.append(child)
                current = child
        except OSError as exc:
            for fd in reversed(owned):
                try:
                    os.close(fd)
                except OSError:
                    pass
            raise Error(str(exc)) from exc
        return DirRef(self, relative_dir, owned)

    def open_compiled(self, relative_file):
        parts = _parts(relative_file)
        suffixes = ('.olean.private', '.olean.server', '.olean', '.ir.sig', '.ilean', '.ir', '.c', '.o')
        if (len(parts) < 3 or parts[:2] not in (['build', 'reviews'], ['build', 'verification'])
                or not relative_file.endswith(suffixes)
                or [p.casefold() for p in parts[:3]] == ['build', 'reviews', '2026-10-11-file-management']):
            raise Error('file outside approved compiled-artifact scope')
        parent_name = '/'.join(parts[:-1])
        leaf = parts[-1]
        parent = self.directory(parent_name, create=False)
        try:
            fd = os.open(leaf, _flags(), dir_fd=parent.fd)
            st = os.fstat(fd)
            if not stat.S_ISREG(st.st_mode):
                os.close(fd)
                raise Error('compiled artifact is not a regular file')
        except Error:
            parent.close()
            raise
        except OSError as exc:
            parent.close()
            raise Error(str(exc)) from exc
        return FileRef(fd, parent, leaf, relative_file)

    def close(self):
        if self._closed:
            return
        self._closed = True
        for fd in reversed(self._anchors):
            try:
                os.close(fd)
            except OSError:
                pass
        self._anchors = []


def fsync_directory(dirref):
    if not isinstance(dirref, DirRef) or not dirref.verified():
        raise Error('unverified directory anchor')
    try:
        os.fsync(dirref.fd)
    except OSError as exc:
        raise Error(str(exc)) from exc


__all__ = [
    'RootFS', 'DirRef', 'FileRef', 'Error', 'fingerprint', 'digest',
    'metadata', 'apply_metadata', 'verify_metadata', 'fsync_directory',
]
