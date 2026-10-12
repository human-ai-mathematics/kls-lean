"""Provenance lock of the vendored Lean libraries (formalization/vendor/README.md).

The lock binds every vendored file to its upstream blob at the pinned commit, its vendored hash and
`port.patch`. The default check is offline; `--upstream`/`--fetch` also compare the upstream Git objects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

VENDOR_DIR = "formalization/vendor"
LOCK_NAME = "vendor-lock.json"
PATCH_NAME = "port.patch"

PINS: dict[str, dict[str, str]] = {
    "LevyStochCalc": {
        "repository": "https://github.com/cgarryZA/LevyStochCalc",
        "commit": "984dbf0b790031eac05d56fe5a84b65e15e1e932",
        "upstream_toolchain": "leanprover/lean4:v4.32.0",
        "upstream_mathlib": "81a5d257c8e410db227a6665ed08f64fea08e997",
        "license": "Apache-2.0",
    },
    "BrownianMotion": {
        "repository": "https://github.com/RemyDegenne/brownian-motion",
        "commit": "4d52fa776130a29d4ad7d6eda2035a919c0b4696",
        "upstream_toolchain": "leanprover/lean4:v4.32.0",
        "upstream_mathlib": "81a5d257c8e410db227a6665ed08f64fea08e997",
        "license": "Apache-2.0",
    },
    "KolmogorovExtension4": {
        "repository": "https://github.com/RemyDegenne/kolmogorov_extension4",
        "commit": "f33cbc388e5d444606dffa7eec507a26b62c15bb",
        "upstream_toolchain": "leanprover/lean4:v4.32.0",
        "upstream_mathlib": "81a5d257c8e410db227a6665ed08f64fea08e997",
        "license": "Apache-2.0",
    },
    "MathFin": {
        "repository": "https://github.com/raphaelrrcoelho/formal-mathfin",
        "commit": "784a8311f75a1519a23717856df9982bd6a9a370",
        "upstream_toolchain": "leanprover/lean4:v4.32.0",
        "upstream_mathlib": "81a5d257c8e410db227a6665ed08f64fea08e997",
        "license": "Apache-2.0",
    },
}

_DESCRIPTION = (
    "Vendored Lean libraries with machine-checkable upstream provenance and port metadata."
)
_HEX = re.compile(r"^[0-9a-f]+$")
_HUNK = re.compile(
    r"^@@ -([0-9]+)(?:,([0-9]+))? \+([0-9]+)(?:,([0-9]+))? @@(?: .*)?$"
)


@dataclass
class PatchLine:
    kind: str
    data: bytes
    no_newline: bool = False


@dataclass
class Hunk:
    old_start: int
    old_count: int
    new_start: int
    new_count: int
    lines: list[PatchLine]


def git_blob_sha1(data: bytes) -> str:
    """Return Git's SHA-1 for a blob."""
    header = b"blob %d\0" % len(data)
    return hashlib.sha1(header + data).hexdigest()


def _lines(data: bytes) -> list[bytes]:
    """Split on LF only, keeping line endings, so CR and Unicode separators stay in their line."""
    parts = data.split(b"\n")
    lines = [part + b"\n" for part in parts[:-1]]
    if parts[-1]:
        lines.append(parts[-1])
    return lines


def _safe_patch_path(path: str) -> bool:
    if not path or path.startswith("/") or "\\" in path:
        return False
    return all(part not in {"", ".", ".."} for part in path.split("/"))


_NO_NEWLINE = b"\\ No newline at end of file"


def parse_patch(text: bytes | str) -> dict[str, list[Hunk]]:
    """Parse a strict unified diff of existing files (no creation, deletion or stray lines)."""
    data = text.encode("utf-8") if isinstance(text, str) else text
    lines = _lines(data)
    result: dict[str, list[Hunk]] = {}
    index = 0

    def header_path(prefix: bytes, side: bytes) -> str:
        line = lines[index].rstrip(b"\n") if index < len(lines) else b""
        if not line.startswith(prefix + b" " + side + b"/"):
            raise ValueError(f"expected {prefix.decode()} {side.decode()}/<path> at line {index + 1}")
        path = line[len(prefix) + 3:].decode("utf-8")
        if not _safe_patch_path(path):
            raise ValueError(f"invalid patch path at line {index + 1}: {path!r}")
        return path

    while index < len(lines):
        old_rel = header_path(b"---", b"a")
        index += 1
        new_rel = header_path(b"+++", b"b")
        index += 1
        if old_rel != new_rel:
            raise ValueError(f"mismatched patch paths: {old_rel!r} and {new_rel!r}")
        if old_rel in result:
            raise ValueError(f"duplicate patch file: {old_rel}")
        hunks: list[Hunk] = []
        while index < len(lines) and not lines[index].startswith(b"--- "):
            match = _HUNK.fullmatch(lines[index].rstrip(b"\n").decode("utf-8", "replace"))
            if match is None:
                raise ValueError(f"malformed hunk header or stray line at line {index + 1}")
            old_start, new_start = int(match.group(1)), int(match.group(3))
            old_count, new_count = int(match.group(2) or "1"), int(match.group(4) or "1")
            if (old_count and not old_start) or (new_count and not new_start):
                raise ValueError(f"nonempty hunk side cannot start at line zero at line {index + 1}")
            index += 1
            body: list[PatchLine] = []
            old_seen = new_seen = 0
            while old_seen < old_count or new_seen < new_count or (
                    index < len(lines) and lines[index].rstrip(b"\n") == _NO_NEWLINE):
                if index >= len(lines):
                    raise ValueError(f"hunk body is truncated for {old_rel}")
                raw = lines[index]
                index += 1
                if raw.rstrip(b"\n") == _NO_NEWLINE:
                    if not body or body[-1].no_newline or not body[-1].data.endswith(b"\n"):
                        raise ValueError(f"misplaced no-newline marker in {old_rel}")
                    body[-1].data = body[-1].data[:-1]
                    body[-1].no_newline = True
                    continue
                kind = raw[:1].decode("latin-1")
                if kind not in {" ", "-", "+"} or not raw.endswith(b"\n"):
                    raise ValueError(f"invalid hunk body line at line {index}")
                old_seen += kind in " -"
                new_seen += kind in " +"
                if old_seen > old_count or new_seen > new_count:
                    raise ValueError(f"hunk line counts exceed header for {old_rel}")
                body.append(PatchLine(kind, raw[1:]))
            hunks.append(Hunk(old_start, old_count, new_start, new_count, body))
        if not hunks:
            raise ValueError(f"file section has no hunks: {old_rel}")
        result[old_rel] = hunks
    return result


def _apply(data: bytes, hunks: Iterable[Hunk], *, reverse: bool) -> bytes:
    """Apply hunks at exactly their header positions, copying the unchanged lines between them."""
    source = _lines(data)
    output: list[bytes] = []
    position = 0
    for hunk in hunks:
        start = hunk.new_start if reverse else hunk.old_start
        count = hunk.new_count if reverse else hunk.old_count
        # A zero-count side `l,0` denotes the empty range after line `l`.
        at = start if count == 0 else start - 1
        if at < position or at > len(source):
            raise ValueError(f"hunk at line {start} overlaps or lies outside the file")
        expected = [line.data for line in hunk.lines if line.kind in ("+ " if reverse else "- ")]
        replacement = [line.data for line in hunk.lines if line.kind in ("- " if reverse else "+ ")]
        if source[at:at + count] != expected:
            raise ValueError(f"hunk context does not match at line {at + 1}")
        output.extend(source[position:at])
        output.extend(replacement)
        position = at + count
    output.extend(source[position:])
    if any(not line.endswith(b"\n") for line in output[:-1]):
        raise ValueError("a line without a final newline is not the last line")
    return b"".join(output)


def apply_reverse(new: bytes, hunks: Iterable[Hunk]) -> bytes:
    """Strictly reverse-apply hunks to the patched (vendored) content."""
    return _apply(new, hunks, reverse=True)


def apply_forward(old: bytes, hunks: Iterable[Hunk]) -> bytes:
    """Strictly apply hunks to the original (upstream) content."""
    return _apply(old, hunks, reverse=False)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _is_hex(value: Any, length: int) -> bool:
    return isinstance(value, str) and len(value) == length and _HEX.fullmatch(value) is not None


def _collect_files(base: Path) -> tuple[dict[str, bytes], list[str]]:
    files: dict[str, bytes] = {}
    errors: list[str] = []

    def visit(directory: Path) -> None:
        try:
            entries = sorted(directory.iterdir(), key=lambda item: item.name)
        except OSError as exc:
            errors.append(f"cannot read {directory}: {exc}")
            return

        for entry in entries:
            relative = entry.relative_to(base).as_posix()
            shown = f"{base.name}/{relative}"
            if entry.is_symlink():
                errors.append(f"symlink in vendor tree: {shown}")
                continue
            if entry.is_dir():
                visit(entry)
                continue
            if not entry.is_file():
                errors.append(f"non-regular file in vendor tree: {shown}")
                continue
            try:
                files[relative] = entry.read_bytes()
            except OSError as exc:
                errors.append(f"cannot read vendored file {shown}: {exc}")

    if base.is_symlink():
        errors.append(f"symlink in vendor tree: {base}")
    elif base.is_dir():
        visit(base)
    else:
        errors.append(f"missing vendor directory: {base}")
    return files, errors


def _empty_summary(lock_sha256: str = "", patch_sha256: str = "") -> dict[str, Any]:
    return {
        "lock_sha256": lock_sha256,
        "patch_sha256": patch_sha256,
        "roots": {},
        "total_files": 0,
    }


def _valid_path(path: str) -> bool:
    return bool(path) and _safe_patch_path(path)


def check_lock(root: Path, roots: set[str] | None = None) -> tuple[dict[str, Any], list[str]]:
    """Validate the offline provenance lock."""
    errors: list[str] = []
    lock_path = root / VENDOR_DIR / LOCK_NAME
    patch_path = root / VENDOR_DIR / PATCH_NAME
    summary = _empty_summary()

    try:
        lock_bytes = lock_path.read_bytes()
        summary["lock_sha256"] = _sha256(lock_bytes)
    except OSError:
        errors.append(f"missing lock file: {lock_path}")
        return summary, errors

    try:
        patch_bytes = patch_path.read_bytes()
        summary["patch_sha256"] = _sha256(patch_bytes)
    except OSError:
        patch_bytes = b""
        errors.append(f"missing patch file: {patch_path}")

    expected_roots = set(PINS) if roots is None else set(roots)
    if roots is not None and set(roots) != set(PINS):
        errors.append("expected roots do not equal PINS keys")

    try:
        data = json.loads(lock_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        errors.append(f"invalid lock JSON: {exc}")
        return summary, errors

    if not isinstance(data, dict):
        errors.append("lock top level must be an object")
        return summary, errors

    top_keys = {"schema", "description", "port", "patch", "libraries"}
    if set(data) != top_keys:
        errors.append("lock top-level keys are incorrect")

    if data.get("schema") != 1 or isinstance(data.get("schema"), bool):
        errors.append("lock schema must be integer 1")
    if not isinstance(data.get("description"), str) or not data["description"].endswith("."):
        errors.append("lock description must be a sentence")
    port = data.get("port")
    if not isinstance(port, dict) or set(port) != {"lean", "mathlib"}:
        errors.append("lock port fields are incorrect")
        port = {}
    if port.get("lean") != "v4.33.0" or port.get("mathlib") != "db584cd":
        errors.append("lock port does not match the port pin")

    patch_info = data.get("patch")
    if not isinstance(patch_info, dict) or set(patch_info) != {"path", "sha256", "files"}:
        errors.append("lock patch fields are incorrect")
        patch_info = {}
    if patch_info.get("path") != PATCH_NAME:
        errors.append("lock patch path is incorrect")
    if not _is_hex(patch_info.get("sha256"), 64):
        errors.append("lock patch sha256 is invalid")
    elif patch_info["sha256"] != summary["patch_sha256"]:
        errors.append("patch sha256 does not match port.patch")
    patch_files_value = patch_info.get("files")
    patch_files: set[str] = set()
    if not isinstance(patch_files_value, list) or any(
        not isinstance(item, str) for item in patch_files_value
    ):
        errors.append("lock patch files must be a list of strings")
    else:
        patch_files = set(patch_files_value)
        if len(patch_files) != len(patch_files_value):
            errors.append("lock patch files contain duplicates")
        if patch_files_value != sorted(patch_files_value):
            errors.append("lock patch files are not sorted")
        for item in patch_files:
            if not _valid_path(item):
                errors.append(f"invalid path in lock patch files: {item!r}")

    libraries = data.get("libraries")
    if not isinstance(libraries, dict):
        errors.append("lock libraries must be an object")
        libraries = {}
    elif set(libraries) != expected_roots:
        errors.append("lock library roots do not match expected roots")

    if patch_bytes:
        try:
            parsed_patch = parse_patch(patch_bytes)
        except ValueError as exc:
            parsed_patch = {}
            errors.append(f"invalid port.patch: {exc}")
    else:
        parsed_patch = {}
    actual_patch_files = set(parsed_patch)
    if actual_patch_files != patch_files:
        errors.append("patch file set does not match lock patch.files")

    vendor_dir = root / VENDOR_DIR
    expected_top = expected_roots | {"README.md", ".gitattributes", PATCH_NAME, LOCK_NAME}
    actual_top: set[str] = set()
    if vendor_dir.is_dir() and not vendor_dir.is_symlink():
        try:
            for entry in vendor_dir.iterdir():
                actual_top.add(entry.name)
                if entry.is_symlink():
                    errors.append(f"symlink at vendor top level: {entry.name}")
        except OSError as exc:
            errors.append(f"cannot read vendor directory: {exc}")
    else:
        errors.append(f"missing vendor directory: {vendor_dir}")
    if actual_top != expected_top:
        errors.append("vendor top-level inventory does not match expected files and roots")

    all_entries: dict[str, dict[str, Any]] = {}
    root_files: dict[str, dict[str, bytes]] = {}
    for name in expected_roots:
        library = libraries.get(name)
        if not isinstance(library, dict):
            errors.append(f"library entry is missing or invalid: {name}")
            library = {}
        expected_library_keys = {
            "repository",
            "commit",
            "upstream_toolchain",
            "upstream_mathlib",
            "license",
            "modules",
            "files",
        }
        if set(library) != expected_library_keys:
            errors.append(f"library fields are incorrect: {name}")
        pin = PINS.get(name)
        if pin is None:
            errors.append(f"root is absent from PINS: {name}")
        else:
            for field in (
                "repository",
                "commit",
                "upstream_toolchain",
                "upstream_mathlib",
                "license",
            ):
                if library.get(field) != pin[field]:
                    errors.append(f"{name} {field} does not match PINS")
        if not _is_hex(library.get("commit"), 40):
            errors.append(f"{name} commit is invalid")
        if not _is_hex(library.get("upstream_mathlib"), 40):
            errors.append(f"{name} upstream_mathlib is invalid")
        if not isinstance(library.get("repository"), str):
            errors.append(f"{name} repository must be a string")
        if not isinstance(library.get("upstream_toolchain"), str):
            errors.append(f"{name} upstream_toolchain must be a string")
        if not isinstance(library.get("license"), str):
            errors.append(f"{name} license must be a string")
        if (
            not isinstance(library.get("modules"), int)
            or isinstance(library.get("modules"), bool)
            or library.get("modules", -1) < 0
        ):
            errors.append(f"{name} modules must be a nonnegative integer")

        file_info = library.get("files")
        if not isinstance(file_info, dict):
            errors.append(f"{name} files must be an object")
            file_info = {}
        root_base = vendor_dir / name
        actual, inventory_errors = _collect_files(root_base)
        errors.extend(inventory_errors)
        root_files[name] = actual
        on_disk = {f"{name}/{path}" for path in actual}
        errors.extend(f"extra vendored file not in the lock: {key}"
                      for key in sorted(on_disk - set(file_info)))
        errors.extend(f"missing vendored file listed in the lock: {key}"
                      for key in sorted(set(file_info) - on_disk))

        root_patch_count = 0
        root_module_count = 0
        for key, entry in file_info.items():
            if not isinstance(key, str) or not key.startswith(f"{name}/"):
                errors.append(f"file key is outside library root {name}: {key!r}")
                continue
            if not isinstance(entry, dict):
                errors.append(f"file entry is not an object: {key}")
                continue
            expected_file_keys = {
                "upstream_path",
                "module",
                "upstream_sha256",
                "upstream_git_blob",
                "vendored_sha256",
                "patched",
            }
            if set(entry) != expected_file_keys:
                errors.append(f"file fields are incorrect: {key}")
            rel = key[len(name) + 1 :]
            expected_module = (
                key[:-5].replace("/", ".") if key.endswith(".lean") else None
            )
            if entry.get("upstream_path") != rel:
                errors.append(f"upstream_path is incorrect: {key}")
            if entry.get("module") != expected_module:
                errors.append(f"module name is incorrect: {key}")
            if key.endswith(".lean"):
                root_module_count += 1
                if not isinstance(entry.get("module"), str) or not entry["module"].startswith(
                    f"{name}."
                ):
                    errors.append(f"Lean module does not start with {name}.: {key}")
            elif entry.get("module") is not None:
                errors.append(f"non-Lean file has a module name: {key}")
            for field in ("upstream_sha256", "vendored_sha256"):
                if not _is_hex(entry.get(field), 64):
                    errors.append(f"{field} is invalid: {key}")
            if not _is_hex(entry.get("upstream_git_blob"), 40):
                errors.append(f"upstream_git_blob is invalid: {key}")
            if not isinstance(entry.get("patched"), bool):
                errors.append(f"patched must be boolean: {key}")
            if entry.get("patched") is True:
                root_patch_count += 1
            all_entries[key] = entry

        if isinstance(library.get("modules"), int) and not isinstance(library.get("modules"), bool):
            if library["modules"] != root_module_count:
                errors.append(f"module count is incorrect: {name}")

        summary["roots"][name] = {
            "files": len(actual),
            "modules": sum(path.endswith(".lean") for path in actual),
            "patched": root_patch_count,
        }

    summary["total_files"] = sum(item["files"] for item in summary["roots"].values())

    actual_all = {
        f"{name}/{relative}": data
        for name, files in root_files.items()
        for relative, data in files.items()
    }
    patched_entries = {key for key, entry in all_entries.items() if entry.get("patched") is True}
    differing_entries = {
        key
        for key, entry in all_entries.items()
        if entry.get("upstream_sha256") != entry.get("vendored_sha256")
    }
    if actual_patch_files != patched_entries or patch_files != patched_entries:
        errors.append("patch file set does not match patched lock entries")
    if patched_entries != differing_entries:
        errors.append("patched entries do not match differing upstream and vendored hashes")

    for key, entry in all_entries.items():
        actual = actual_all.get(key)
        if actual is None:
            continue
        if _is_hex(entry.get("vendored_sha256"), 64) and _sha256(actual) != entry["vendored_sha256"]:
            errors.append(f"vendored_sha256 mismatch: {key}")

        patched = entry.get("patched") is True
        if not patched:
            if entry.get("upstream_sha256") != entry.get("vendored_sha256"):
                errors.append(f"unpatched file has differing hashes: {key}")
            if (
                _is_hex(entry.get("upstream_git_blob"), 40)
                and git_blob_sha1(actual) != entry["upstream_git_blob"]
            ):
                errors.append(f"upstream_git_blob mismatch for unpatched file: {key}")
            continue

        hunks = parsed_patch.get(key)
        if hunks is None:
            errors.append(f"patched file is absent from parsed patch: {key}")
            continue
        try:
            reconstructed = apply_reverse(actual, hunks)
        except ValueError as exc:
            errors.append(f"reverse application failed for {key}: {exc}")
            continue
        if _is_hex(entry.get("upstream_sha256"), 64) and _sha256(reconstructed) != entry[
            "upstream_sha256"
        ]:
            errors.append(f"upstream_sha256 mismatch after reverse application: {key}")
        if (
            _is_hex(entry.get("upstream_git_blob"), 40)
            and git_blob_sha1(reconstructed) != entry["upstream_git_blob"]
        ):
            errors.append(f"upstream_git_blob mismatch after reverse application: {key}")
        try:
            if apply_forward(reconstructed, hunks) != actual:
                errors.append(f"forward application does not reproduce vendored file: {key}")
        except ValueError as exc:
            errors.append(f"forward application failed for {key}: {exc}")

    return summary, errors


def _git_env() -> dict[str, str]:
    env = os.environ.copy()
    for variable in ("GIT_DIR", "GIT_INDEX_FILE", "GIT_WORK_TREE"):
        env.pop(variable, None)
    return env


def _run_git(arguments: list[str]) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        arguments,
        capture_output=True,
        check=False,
        env=_git_env(),
    )


def _git_blob(clone: Path, commit: str, path: str) -> bytes:
    result = _run_git(["git", "-C", str(clone), "cat-file", "blob", f"{commit}:{path}"])
    if result.returncode:
        raise ValueError(result.stderr.decode("utf-8", "replace").strip())
    return result.stdout


def _git_text(clone: Path, commit: str, path: str) -> str:
    return _git_blob(clone, commit, path).decode("utf-8")


def check_upstream(root: Path, clones: dict[str, Path]) -> list[str]:
    """Compare the lock with local upstream Git repositories."""
    errors: list[str] = []
    lock_path = root / VENDOR_DIR / LOCK_NAME
    try:
        data = json.loads(lock_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        return [f"cannot read lock for upstream check: {exc}"]

    _, lock_errors = check_lock(root, set(PINS))
    errors.extend(lock_errors)
    libraries = data.get("libraries", {}) if isinstance(data, dict) else {}

    for name, library in libraries.items():
        if not isinstance(library, dict):
            continue
        clone = clones.get(name)
        if clone is None:
            errors.append(f"missing upstream clone: {name}")
            continue
        commit = library.get("commit")
        if not isinstance(commit, str):
            continue
        exists = _run_git(["git", "-C", str(clone), "cat-file", "-e", f"{commit}^{{commit}}"])
        if exists.returncode:
            errors.append(f"pinned commit is absent from upstream clone: {name}")
            continue

        files = library.get("files", {})
        if isinstance(files, dict):
            for vendor_path, entry in files.items():
                if not isinstance(entry, dict):
                    continue
                upstream_path = entry.get("upstream_path")
                expected_blob = entry.get("upstream_git_blob")
                expected_sha = entry.get("upstream_sha256")
                if not isinstance(upstream_path, str):
                    continue
                revision = _run_git(
                    ["git", "-C", str(clone), "rev-parse", f"{commit}:{upstream_path}"]
                )
                actual_blob = revision.stdout.decode("ascii", "replace").strip()
                if revision.returncode or actual_blob != expected_blob:
                    errors.append(f"upstream blob mismatch: {name}/{upstream_path}")
                    continue
                try:
                    blob = _git_blob(clone, commit, upstream_path)
                except ValueError as exc:
                    errors.append(f"cannot read upstream blob {name}/{upstream_path}: {exc}")
                    continue
                if _sha256(blob) != expected_sha:
                    errors.append(f"upstream sha256 mismatch: {name}/{upstream_path}")

        try:
            toolchain = _git_text(clone, commit, "lean-toolchain").rstrip()
        except (ValueError, UnicodeDecodeError) as exc:
            errors.append(f"cannot read lean-toolchain for {name}: {exc}")
        else:
            if toolchain != library.get("upstream_toolchain"):
                errors.append(f"lean-toolchain mismatch: {name}")

    levy = libraries.get("LevyStochCalc")
    levy_clone = clones.get("LevyStochCalc")
    if isinstance(levy, dict) and levy_clone is not None:
        try:
            manifest = json.loads(
                _git_text(levy_clone, levy["commit"], "lake-manifest.json")
            )
        except (ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            errors.append(f"cannot read LevyStochCalc lake-manifest.json: {exc}")
        else:
            packages = manifest.get("packages") if isinstance(manifest, dict) else None
            package_map = {
                package.get("name"): package
                for package in packages or []
                if isinstance(package, dict) and isinstance(package.get("name"), str)
            }
            required = {
                "BrownianMotion": "BrownianMotion",
                "MathFin": "MathFin",
                "kolmogorov_extension4": "KolmogorovExtension4",
                "mathlib": "LevyStochCalc",
            }
            for package_name, pin_root in required.items():
                package = package_map.get(package_name)
                expected = (
                    PINS.get(pin_root, {}).get("commit")
                    if package_name != "mathlib"
                    else levy.get("upstream_mathlib")
                )
                if package is None:
                    errors.append(f"LevyStochCalc manifest lacks package: {package_name}")
                elif package.get("rev") != expected:
                    errors.append(f"LevyStochCalc manifest pin mismatch: {package_name}")

    return errors


def fetch_upstream(destination: Path) -> dict[str, Path]:
    """Fetch all pinned repositories into fresh Git directories."""
    destination.mkdir(parents=True, exist_ok=True)
    clones: dict[str, Path] = {}
    for name, pin in PINS.items():
        clone = destination / name
        if clone.exists():
            raise ValueError(f"fetch destination already exists: {clone}")
        clone.mkdir()
        initialized = _run_git(["git", "init", str(clone)])
        if initialized.returncode:
            raise RuntimeError(
                f"git init failed for {name}: {initialized.stderr.decode('utf-8', 'replace')}"
            )
        fetched = _run_git(
            [
                "git",
                "-C",
                str(clone),
                "fetch",
                "--depth",
                "1",
                "--filter=blob:none",
                pin["repository"],
                pin["commit"],
            ]
        )
        if fetched.returncode:
            raise RuntimeError(
                f"git fetch failed for {name}: {fetched.stderr.decode('utf-8', 'replace')}"
            )
        clones[name] = clone
    return clones


def _vendored_files_for_generation(root: Path, name: str) -> dict[str, bytes]:
    files, errors = _collect_files(root / VENDOR_DIR / name)
    if errors:
        raise ValueError("\n".join(errors))
    return {f"{name}/{relative}": data for relative, data in files.items()}


def generate_lock(root: Path, clones: dict[str, Path]) -> dict[str, Any]:
    """Generate a provenance lock from vendored files and upstream Git objects."""
    vendor = root / VENDOR_DIR
    patch_path = vendor / PATCH_NAME
    problems: list[str] = []

    try:
        patch_bytes = patch_path.read_bytes()
        parsed_patch = parse_patch(patch_bytes)
    except (OSError, ValueError) as exc:
        raise ValueError(f"cannot parse port.patch: {exc}") from exc

    patch_files = set(parsed_patch)
    libraries: dict[str, Any] = {}

    for name, pin in PINS.items():
        clone = clones.get(name)
        if clone is None:
            problems.append(f"missing upstream clone: {name}")
            continue
        try:
            files = _vendored_files_for_generation(root, name)
        except ValueError as exc:
            problems.append(str(exc))
            continue

        entries: dict[str, Any] = {}
        for key in sorted(files):
            vendored = files[key]
            upstream_path = key[len(name) + 1 :]
            try:
                upstream = _git_blob(clone, pin["commit"], upstream_path)
            except ValueError as exc:
                problems.append(f"cannot read upstream {name}/{upstream_path}: {exc}")
                continue

            patched = key in patch_files
            if patched:
                try:
                    reconstructed = apply_reverse(vendored, parsed_patch[key])
                except ValueError as exc:
                    problems.append(f"patch does not reverse-apply for {key}: {exc}")
                    reconstructed = b""
                if reconstructed != upstream:
                    problems.append(f"patched file does not reconstruct upstream bytes: {key}")
            elif vendored != upstream:
                problems.append(f"unpatched file differs from upstream: {key}")

            entries[key] = {
                "upstream_path": upstream_path,
                "module": key[:-5].replace("/", ".") if key.endswith(".lean") else None,
                "upstream_sha256": _sha256(upstream),
                "upstream_git_blob": git_blob_sha1(upstream),
                "vendored_sha256": _sha256(vendored),
                "patched": patched,
            }

        libraries[name] = {
            "repository": pin["repository"],
            "commit": pin["commit"],
            "upstream_toolchain": pin["upstream_toolchain"],
            "upstream_mathlib": pin["upstream_mathlib"],
            "license": pin["license"],
            "modules": sum(key.endswith(".lean") for key in entries),
            "files": entries,
        }

    if set(patch_files) != {
        key for library in libraries.values() for key, entry in library["files"].items()
        if entry["patched"]
    }:
        problems.append("patch file set does not match generated patched entries")

    lock = {
        "schema": 1,
        "description": _DESCRIPTION,
        "port": {"lean": "v4.33.0", "mathlib": "db584cd"},
        "patch": {
            "path": PATCH_NAME,
            "sha256": _sha256(patch_bytes),
            "files": sorted(patch_files),
        },
        "libraries": libraries,
    }
    if problems:
        raise ValueError("\n".join(problems))
    return lock


def _print_summary(summary: dict[str, Any]) -> None:
    for name in sorted(summary.get("roots", {})):
        counts = summary["roots"][name]
        print(
            f"{name}: files={counts['files']} modules={counts['modules']} "
            f"patched={counts['patched']}"
        )
    print(f"total files: {summary.get('total_files', 0)}")


def _write_lock(root: Path, lock: dict[str, Any]) -> None:
    path = root / VENDOR_DIR / LOCK_NAME
    path.write_text(json.dumps(lock, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _check_all(root: Path, clones: dict[str, Path] | None, write: bool) -> int:
    if write and clones is not None:
        _write_lock(root, generate_lock(root, clones))
    summary, errors = check_lock(root, set(PINS))
    if clones is not None:
        # check_upstream repeats the offline check; report each error once.
        errors.extend(e for e in check_upstream(root, clones) if e not in errors)
    _print_summary(summary)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("vendor lock: OK" + (" (offline and upstream)" if clones is not None else " (offline)"))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--upstream", type=Path, help="directory holding <Root> clones of the upstreams")
    parser.add_argument("--fetch", action="store_true", help="fetch the pinned upstreams into a temporary directory")
    parser.add_argument("--write", action="store_true", help="regenerate the lock from the upstreams first")
    args = parser.parse_args(argv)
    if args.write and not (args.upstream or args.fetch):
        parser.error("--write requires --upstream or --fetch")
    if args.upstream and args.fetch:
        parser.error("--upstream and --fetch are exclusive")
    root = args.root.resolve()
    try:
        if args.fetch:
            with tempfile.TemporaryDirectory() as temporary:
                return _check_all(root, fetch_upstream(Path(temporary)), args.write)
        clones = {name: args.upstream / name for name in PINS} if args.upstream else None
        return _check_all(root, clones, args.write)
    except (OSError, RuntimeError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
