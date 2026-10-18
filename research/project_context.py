from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import subprocess
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

MAX_FILE = 8 * 1024 * 1024
MAX_TOTAL = 64 * 1024 * 1024
MAX_FILES = 4000
MAX_API = 32 * 1024 * 1024
MAX_JSON_NODES = 250000
MAX_HANDLES = 4
MAX_PAGE = 50
HEX40 = re.compile(r"^[0-9a-fA-F]{40}$")
HEX64 = re.compile(r"^[0-9a-fA-F]{64}$")
SCOPES = {"full", "lean-only", "downstream"}
EXCLUDED = {".git", ".cursor", ".clinerules", ".claude", "build",
            "config", "configuration", "secret", "secrets"}
ROOT_FILES = {"README.md", "HANDOFF.md", "LEAN_DESIGN.md", "AGENTS.md", "LICENSE"}
REGISTRY_FILES = {
    "research/tasks.json", "research/a-series/ledger.yaml",
    "research/progress/literature.json", "research/progress/nodes.json",
    "research/progress/proof-path.json", "research/progress/proof-path.yaml",
    "research/progress/current.json", "research/progress/current.yaml",
    "research/workflow.md", "research/naming.md", "research/verification.md",
    "research/context-mcp.md",
}

class ContextError(Exception):
    pass

def _digest(files: dict[str, Any]) -> str:
    raw = json.dumps(files, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()

def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def _bounded_json(data: bytes, *, limit: int = MAX_FILE, nodes: int = MAX_JSON_NODES) -> Any:
    if len(data) > limit:
        raise ContextError("JSON source exceeds the read bound")
    try:
        def pairs(items):
            result = dict(items)
            if len(result) != len(items):
                raise ContextError("JSON source has duplicate keys")
            return result
        value = json.loads(data.decode("utf-8"), object_pairs_hook=pairs,
                           parse_constant=lambda _: (_ for _ in ()).throw(ContextError("nonfinite JSON number")))
        seen = 0

        def visit(x: Any, depth: int = 0) -> None:
            nonlocal seen
            seen += 1
            if depth > 32 or seen > nodes:
                raise ContextError("JSON source is too deep or large")
            if isinstance(x, dict):
                for k, v in x.items():
                    if not isinstance(k, str) or len(k) > 1000:
                        raise ContextError("JSON object key is not text")
                    visit(v, depth + 1)
            elif isinstance(x, list):
                for v in x:
                    visit(v, depth + 1)

        visit(value)
        return value
    except (UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise ContextError("recorded JSON source is malformed") from exc

class ProjectContext:
    def __init__(self, repo: Path):
        self.repo = self._discover_root(Path(repo))
        self._handles: dict[str, dict[str, Any]] = {}

    @staticmethod
    def _env() -> dict[str, str]:
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        env.update({"GIT_OPTIONAL_LOCKS": "0", "GIT_NO_LAZY_FETCH": "1",
                    "GIT_TERMINAL_PROMPT": "0", "GIT_NO_REPLACE_OBJECTS": "1", "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_CONFIG_GLOBAL": os.devnull, "LC_ALL": "C"})
        return env

    @classmethod
    def _discover_root(cls, path: Path) -> Path:
        try:
            candidate = path.expanduser().resolve(strict=True)
            out = subprocess.run(
                ["git", "-C", str(candidate), "rev-parse", "--show-toplevel"],
                env=cls._env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=10, check=True,
            ).stdout.decode("utf-8", "strict").strip()
            root = Path(out).resolve(strict=True)
            if not root.is_dir():
                raise ValueError
            return root
        except (OSError, UnicodeError, ValueError, subprocess.SubprocessError) as exc:
            raise ContextError("repository is not a usable local Git worktree") from exc

    def _git(self, args: list[str], *, data: bytes | None = None) -> bytes:
        if not args or any(not isinstance(x, str) or "\x00" in x for x in args):
            raise ContextError("invalid Git request")
        try:
            result = subprocess.run(
                ["git", "-c", "core.fsmonitor=false", "-c", "core.hooksPath=" + os.devnull,
                 "-C", str(self.repo), *args], input=data, env=self._env(),
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20, check=True).stdout
        except (OSError, subprocess.SubprocessError) as exc:
            raise ContextError("Git read failed") from exc
        if len(result) > MAX_TOTAL + MAX_FILES * 128:
            raise ContextError("Git response exceeds the read bound")
        return result

    def _head(self) -> str:
        value = self._git(["rev-parse", "HEAD"]).decode().strip()
        if not HEX40.fullmatch(value):
            raise ContextError("repository HEAD is not a full commit ID")
        return value.lower()

    def _index_path(self) -> Path:
        raw = self._git(["rev-parse", "--git-path", "index"]).decode().strip()
        path = Path(raw)
        return path if path.is_absolute() else self.repo / path

    def _index_sha(self) -> str:
        try:
            with self._index_path().open("rb") as stream:
                data = stream.read(MAX_FILE + 1)
        except OSError as exc:
            raise ContextError("Git index is unavailable") from exc
        if len(data) > MAX_FILE:
            raise ContextError("Git index exceeds the read bound")
        return _sha(data)

    @staticmethod
    def _safe_rel(path: str) -> bool:
        if not isinstance(path, str) or not path or len(path) > 1000 or "\\" in path:
            return False
        parts = path.split("/")
        if any(not x or x in {".", ".."} or "\x00" in x for x in parts):
            return False
        for i, part in enumerate(parts):
            low = part.lower()
            public_hidden = part in {".gitignore", ".gitattributes"} or (i == 0 and part in {".github", ".githooks"})
            if low in EXCLUDED or (part.startswith(".") and not public_hidden):
                return False
            if low.endswith((".env", ".pem", ".key")) or any(x in low for x in ("credential", "secret")):
                return False
        history = ("research/decisions/", "research/handoffs/", "research/explorations/",
                   "research/weekly/", "research/api-migration/")
        if path.startswith(history) or path == "research/proof-corrections-and-improvements.md":
            return False
        if path.startswith("research/technical-debt/") and re.match(r"[0-9]{4}-", parts[-1]):
            return False
        return True

    @classmethod
    def allowed(cls, path: str) -> bool:
        if not cls._safe_rel(path) or any(x.startswith(".") for x in path.split("/")):
            return False
        if path in ROOT_FILES or path in REGISTRY_FILES:
            return True
        if path == "formalization/FunctionalInequalities.lean":
            return True
        if path.startswith("formalization/FunctionalInequalities/"):
            return path.endswith(".lean") or Path(path).name == "README.md"
        if path in {
            "formalization/lean-toolchain",
            "formalization/lakefile.toml",
            "formalization/lakefile.lean",
            "formalization/lake-manifest.json",
            "formalization/blueprint/route-composition.yaml",
        }:
            return True
        if path.startswith("formalization/blueprint/src/") and path.endswith(".tex"):
            return True
        for prefix in ("solutions/", "examples/"):
            if path.startswith(prefix) and "/" not in path[len(prefix):]:
                return path.endswith(".lean") or Path(path).name == "README.md"
        return False

    def _tree(self, commit: str) -> dict[str, str]:
        if not isinstance(commit, str) or not HEX40.fullmatch(commit):
            raise ContextError("revision must be a full 40-hex commit ID")
        if self._git(["cat-file", "-t", commit]).strip() != b"commit":
            raise ContextError("revision must identify a commit")
        result = {}
        for row in self._git(["ls-tree", "-r", "-z", "--full-tree", commit]).split(b"\0"):
            if not row:
                continue
            try:
                left, raw_path = row.split(b"\t", 1)
                mode, kind, oid = left.decode().split()
                path = raw_path.decode("utf-8", "strict")
            except (ValueError, UnicodeError) as exc:
                raise ContextError("unreadable Git tree") from exc
            if self._safe_rel(path) and (kind != "blob" or mode not in {"100644", "100755"}):
                raise ContextError("safe source tree contains a symlink or nonregular file")
            if not HEX40.fullmatch(oid):
                raise ContextError("invalid Git object ID")
            result[path] = oid.lower()
        if len(result) > MAX_FILES:
            raise ContextError("source file count exceeds the bound")
        return result

    def _index_entries(self) -> dict[str, str]:
        result = {}
        for row in self._git(["ls-files", "--cached", "--stage", "-z"]).split(b"\0"):
            if not row:
                continue
            try:
                left, raw_path = row.split(b"\t", 1)
                mode, oid, stage = left.decode().split()
                path = raw_path.decode("utf-8", "strict")
            except (ValueError, UnicodeError) as exc:
                raise ContextError("unreadable Git index") from exc
            if self._safe_rel(path) and (stage != "0" or mode not in {"100644", "100755"}):
                raise ContextError("safe source has unresolved or nonregular index entries")
            if not HEX40.fullmatch(oid):
                raise ContextError("invalid index object ID")
            result[path] = oid.lower()
        if len(result) > MAX_FILES:
            raise ContextError("source file count exceeds the bound")
        return result

    def _blobs(self, oids: dict[str, str]) -> dict[str, bytes]:
        if len(oids) > MAX_FILES or any(not HEX40.fullmatch(x) for x in oids.values()):
            raise ContextError("invalid or excessive blob set")
        if not oids:
            return {}
        payload = "".join(x + "\n" for x in oids.values()).encode()
        headers = self._git(["cat-file", "--batch-check"], data=payload).splitlines()
        if len(headers) != len(oids):
            raise ContextError("incomplete blob size inspection")
        sizes = []
        for expected, header in zip(oids.values(), headers):
            parts = header.split()
            if len(parts) != 3 or parts[0].decode() != expected or parts[1] != b"blob":
                raise ContextError("immutable Git blob is unavailable")
            try:
                size = int(parts[2])
            except ValueError as exc:
                raise ContextError("invalid blob size") from exc
            if not 0 <= size <= MAX_FILE:
                raise ContextError("source blob exceeds the read bound")
            sizes.append(size)
        if sum(sizes) > MAX_TOTAL:
            raise ContextError("source blobs exceed the total read bound")
        raw = self._git(["cat-file", "--batch"], data=payload)
        values, cursor = {}, 0
        for (path, oid), size in zip(oids.items(), sizes):
            end = raw.find(b"\n", cursor)
            if end < 0 or raw[cursor:end].split() != [oid.encode(), b"blob", str(size).encode()]:
                raise ContextError("Git blob changed during capture")
            cursor = end + 1
            values[path] = raw[cursor:cursor + size]
            cursor += size
            if len(values[path]) != size or raw[cursor:cursor + 1] != b"\n":
                raise ContextError("short immutable Git blob")
            cursor += 1
        if cursor != len(raw):
            raise ContextError("unexpected Git blob response")
        return values

    def _open_read(self, rel: str, limit: int = MAX_FILE) -> bytes:
        parts = rel.split("/")
        try:
            root_fd = os.open(self.repo, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        except OSError as exc:
            raise ContextError("repository directory is unavailable") from exc
        fd = root_fd
        try:
            for part in parts[:-1]:
                nxt = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
                if fd != root_fd:
                    os.close(fd)
                fd = nxt
            final = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=fd)
            try:
                before = os.fstat(final)
                if not stat.S_ISREG(before.st_mode) or before.st_size > limit:
                    raise ContextError("file is not a bounded regular file")
                data = bytearray()
                while len(data) <= limit:
                    chunk = os.read(final, min(1024 * 1024, limit + 1 - len(data)))
                    if not chunk:
                        break
                    data.extend(chunk)
                after = os.fstat(final)
                identity = lambda x: (x.st_dev, x.st_ino, x.st_size, x.st_mtime_ns, x.st_ctime_ns)
                if len(data) > limit or identity(before) != identity(after):
                    raise ContextError("file changed during read")
                return bytes(data)
            finally:
                os.close(final)
        except OSError as exc:
            if isinstance(exc, FileNotFoundError):
                raise FileNotFoundError(rel) from exc
            raise ContextError("safe regular file cannot be read") from exc
        finally:
            os.close(fd)
            if fd != root_fd:
                os.close(root_fd)

    def _read_rel(self, rel: str) -> bytes:
        if not self._safe_rel(rel):
            raise ContextError("path is outside the safe source binding boundary")
        try:
            return self._open_read(rel)
        except FileNotFoundError as exc:
            raise ContextError("source file is unavailable") from exc

    def _fixed_file(self, path: Path) -> bytes:
        try:
            rel = path.relative_to(self.repo) if path.is_absolute() else path
        except ValueError as exc:
            raise ContextError("fixed artifact escapes repository") from exc
        text = rel.as_posix()
        receipt = re.fullmatch(r"build/verification/[A-Za-z0-9_.-]+/report\.json", text)
        api = text in {"build/api-index/" + x for x in ("manifest.json", "public-api.json", "compiler.json", "index.html", "Observe.lean")}
        if not (receipt or api) or any(x in {"", ".", ".."} for x in rel.parts):
            raise ContextError("artifact is outside the fixed layout")
        try:
            return self._open_read(text, MAX_API if api and rel.name != "manifest.json" else MAX_FILE)
        except FileNotFoundError as exc:
            raise ContextError("fixed artifact is unavailable") from exc

    def _work_paths(self) -> list[str]:
        try:
            rows = self._git(["ls-files", "--cached", "--others", "--exclude-standard", "-z"])
            paths = sorted({x.decode("utf-8", "strict") for x in rows.split(b"\0") if x})
        except UnicodeError as exc:
            raise ContextError("source path is not UTF-8") from exc
        if len(paths) > MAX_FILES:
            raise ContextError("source file count exceeds the bound")
        return paths

    def _work_capture(self) -> tuple[dict[str, Any], dict[str, bytes], int]:
        paths = self._work_paths()
        safe = [p for p in paths if self._safe_rel(p)]
        def capture():
            files, content, total = {}, {}, 0
            for path in safe:
                try:
                    data = self._open_read(path)
                except FileNotFoundError:
                    files[path] = None
                    continue
                total += len(data)
                if total > MAX_TOTAL:
                    raise ContextError("worktree source exceeds total read bound")
                files[path] = _sha(data)
                if self.allowed(path):
                    content[path] = data
            return files, content
        first, content = capture()
        if self._work_paths() != paths or capture()[0] != first:
            raise ContextError("worktree source changed during capture")
        return first, content, len(paths) - len(safe)

    def _source_map(self, view: str, commit: str) -> tuple[dict[str, str], dict[str, str], int]:
        tree = self._tree(commit) if view == "head" else self._index_entries()
        oids = {p: oid for p, oid in tree.items() if self._safe_rel(p)}
        blobs = self._blobs(oids)
        return oids, {p: _sha(v) for p, v in blobs.items()}, len(tree) - len(oids)

    def _dirty(self) -> list[str]:
        try:
            rows = self._git(["diff-index", "--cached", "--no-ext-diff", "--no-textconv", "--name-only", "-z", "HEAD", "--"])
            rows += self._git(["diff-files", "--no-ext-diff", "--no-textconv", "--name-only", "-z", "--"])
            rows += self._git(["ls-files", "--others", "--exclude-standard", "-z"])
            return sorted({p.decode("utf-8") for p in rows.split(b"\0") if p and self.allowed(p.decode("utf-8"))})[:100]
        except (ContextError, UnicodeError):
            return ["<unavailable>"]

    def _metadata(self, rec: dict[str, Any]) -> dict[str, Any]:
        refs = [{"path": p, "sha256": h} for p, h in sorted(rec["files"].items())]
        return {"fingerprint": rec["fingerprint"], "head": self._head(),
                "snapshot_head": rec["head"], "view": rec["view"],
                "observationUTC": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
                "real_index_sha256": self._index_sha(), "snapshot_index_sha256": rec["index_sha"],
                "binding_complete": rec["excluded_count"] == 0,
                "excluded_path_count": rec["excluded_count"], "dirty_paths": self._dirty(),
                "source_refs": refs[:20], "source_ref_count": len(refs),
                "source_refs_truncated": len(refs) > 20,
                "text_truncation": "Record strings/collections use explicit <truncated> markers."}

    def _record(self, sid: str) -> dict[str, Any]:
        if not isinstance(sid, str) or sid not in self._handles:
            raise ContextError("unknown or stale snapshot handle")
        return self._handles[sid]

    def _validate(self, sid: str) -> dict[str, Any]:
        rec = self._record(sid)
        self._fresh(rec)
        return rec

    def _fresh(self, rec: dict[str, Any]) -> None:
        if rec["view"] not in {"index", "worktree"}:
            return
        if self._head() != rec["head"] or self._index_sha() != rec["index_sha"]:
            raise ContextError("snapshot handle is stale: HEAD or index changed")
        if rec["view"] == "worktree":
            current, _, excluded = self._work_capture()
            if current != rec["files"] or excluded != rec["excluded_count"]:
                raise ContextError("snapshot handle is stale: worktree changed")

    def _read_record(self, rec: dict[str, Any], path: str) -> bytes:
        if not self.allowed(path) or rec["files"].get(path) is None:
            raise ContextError("public text is unavailable in this snapshot")
        if rec["view"] == "worktree":
            return rec["content"][path]
        data = self._blobs({path: rec["oids"][path]})[path]
        if _sha(data) != rec["files"][path]:
            raise ContextError("source binding changed")
        return data

    def project_snapshot(self, view: str = "head", revision: str | None = None) -> dict[str, Any]:
        if not isinstance(view, str) or view not in {"head", "index", "worktree"}:
            raise ContextError("view must be head, index, or worktree")
        if revision is not None and (view != "head" or not isinstance(revision, str) or not HEX40.fullmatch(revision)):
            raise ContextError("revision must be a full 40-hex commit ID")
        before_head, before_index = self._head(), self._index_sha()
        selected = revision.lower() if revision is not None else before_head
        if view == "worktree":
            files, content, excluded = self._work_capture()
            oids, actual = {}, "worktree"
        else:
            oids, files, excluded = self._source_map(view, selected)
            content, actual = {}, "revision" if revision is not None else view
        if self._head() != before_head or self._index_sha() != before_index:
            raise ContextError("HEAD or index changed during snapshot capture")
        rec = {"view": actual, "head": selected, "oids": oids, "files": files,
               "content": content, "index_sha": before_index, "fingerprint": _digest(files),
               "excluded_count": excluded}
        self._fresh(rec)
        sid = "s_" + uuid.uuid4().hex
        if len(self._handles) >= MAX_HANDLES:
            self._handles.pop(next(iter(self._handles)))
        self._handles[sid] = rec
        return {"snapshot": sid, "metadata": self._metadata(rec),
                "content_binding": {"sha256": rec["fingerprint"], "file_count": len(files),
                                    "complete": excluded == 0}}

    @staticmethod
    def _page(values: list[Any], offset: int, limit: int) -> tuple[list[Any], dict[str, int]]:
        if isinstance(offset, bool) or isinstance(limit, bool) or not isinstance(offset, int):
            raise ContextError("offset must be a nonnegative integer")
        if not isinstance(limit, int) or offset < 0 or not 1 <= limit <= MAX_PAGE:
            raise ContextError("limit must be between 1 and 50")
        return values[offset:offset + limit], {
            "offset": offset, "limit": limit, "total": len(values),
        }

    @staticmethod
    def _clip(value: Any, depth: int = 0) -> Any:
        budget = [300, 6000]
        def clip(x, level):
            budget[0] -= 1
            if level > 5 or budget[0] < 0 or budget[1] <= 0:
                return "<truncated>"
            if isinstance(x, str):
                size = min(2000, budget[1])
                budget[1] -= min(len(x), size)
                return x if len(x) <= size else x[:size] + "<truncated>"
            if isinstance(x, list):
                rows = [clip(v, level + 1) for v in x[:50]]
                return rows + (["<truncated>"] if len(x) > 50 else [])
            if isinstance(x, dict):
                rows = {k[:200]: clip(v, level + 1) for k, v in list(x.items())[:50]}
                if len(x) > 50:
                    rows["<truncated>"] = True
                return rows
            return x
        return clip(value, depth)

    def _json_file(self, rec: dict[str, Any], path: str) -> Any:
        return _bounded_json(self._read_record(rec, path))

    def _ref(self, rec: dict[str, Any], path: str, pointer: str) -> dict[str, str]:
        return {"source_path": path, "sha256": rec["files"][path], "json_pointer": pointer}

    def _registries(self, rec):
        tasks = self._json_file(rec, "research/tasks.json") if "research/tasks.json" in rec["files"] else {"nodes": {}}
        literature = self._json_file(rec, "research/progress/literature.json") if "research/progress/literature.json" in rec["files"] else {"papers": [], "priorities": []}
        ledger = self._json_file(rec, "research/a-series/ledger.yaml") if "research/a-series/ledger.yaml" in rec["files"] else {"nodes": []}
        if not isinstance(tasks, dict) or not isinstance(tasks.get("nodes", {}), dict):
            raise ContextError("tasks registry has an invalid nodes object")
        if not isinstance(literature, dict) or not isinstance(literature.get("papers", []), list) or not isinstance(literature.get("priorities", []), list):
            raise ContextError("literature registry has invalid list fields")
        if not isinstance(ledger, dict) or not isinstance(ledger.get("nodes", []), list):
            raise ContextError("ledger registry has an invalid nodes list")
        if any(not isinstance(v, dict) for v in tasks.get("nodes", {}).values()) or any(not isinstance(v, dict) for v in ledger.get("nodes", [])) or any(not isinstance(v, dict) for v in literature.get("papers", [])):
            raise ContextError("registry records must be objects")
        return tasks, literature, ledger

    def project_status(self, snapshot: str, offset: int = 0, limit: int = 20) -> dict[str, Any]:
        rec = self._validate(snapshot)
        tasks, literature, ledger = self._registries(rec)
        task_items = [
            {"id": key, "record": self._clip(value),
             "source": self._ref(rec, "research/tasks.json", "/nodes/" + key.replace("~", "~0").replace("/", "~1"))}
            for key, value in list(tasks.get("nodes", {}).items())
        ]
        cert_items = [
            {"id": self._clip(row.get("id")), "record": self._clip(row),
             "source": self._ref(rec, "research/a-series/ledger.yaml", f"/nodes/{i}")}
            for i, row in enumerate(ledger.get("nodes", [])) if isinstance(row, dict)
        ]
        papers = [
            {"record": self._clip(row),
             "source": self._ref(rec, "research/progress/literature.json", f"/papers/{i}")}
            for i, row in enumerate(literature.get("papers", []))
        ]
        task_page, task_paging = self._page(task_items, offset, limit)
        cert_page, cert_paging = self._page(cert_items, offset, limit)
        paper_page, paper_paging = self._page(papers, offset, limit)
        result = {
            "metadata": self._metadata(rec), "papers": paper_page,
            "paper_coverage": paper_page, "paper_paging": paper_paging,
            "priorities": self._clip(literature.get("priorities", [])),
            "task_nodes": task_page, "task_paging": task_paging,
            "certificate_records": cert_page, "certificate_paging": cert_paging,
            "interpretation": "Recorded facts only; no status is independently verified.",
        }
        self._fresh(rec)
        return result

    def _scope_files(self, files: dict[str, str], scope: str) -> tuple[dict[str, str], list[str]]:
        if not isinstance(scope, str) or scope not in SCOPES:
            raise ContextError("scope must be full, lean-only, or downstream")
        if scope == "full":
            return dict(files), []
        if scope == "downstream":
            return {}, ["No supported downstream receipt schema is defined."]
        expected = {
            p: h for p, h in files.items()
            if p.endswith(".lean")
            or p in {
                "formalization/lean-toolchain", "formalization/lakefile.toml",
                "formalization/lake-manifest.json", "research/verify.py",
                "research/atlas.py",
            }
            or p.startswith("research/audits/KLS/Classical/")
        }
        required = {
            "formalization/lean-toolchain", "formalization/lakefile.toml",
            "formalization/lake-manifest.json", "research/verify.py", "research/atlas.py",
        }
        missing = sorted(required - set(expected))
        return expected, (["Lean verification binding is incomplete: " + ", ".join(missing)]
                          if missing else [])

    def _receipt_paths(self, explicit: Iterable[Path] | None = None) -> tuple[list[Path], bool]:
        if explicit is not None:
            paths = list(explicit)
            complete = len(paths) <= 50
        else:
            base = self.repo / "build" / "verification"
            try:
                info = base.lstat()
                if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
                    raise ContextError("verification directory is not regular")
                fd = os.open(self.repo, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
                try:
                    for part in ("build", "verification"):
                        nxt = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
                        os.close(fd); fd = nxt
                    with os.scandir(fd) as entries:
                        names = sorted(entry.name for entry in entries if entry.is_dir(follow_symlinks=False) or entry.is_symlink())
                finally:
                    os.close(fd)
                complete = len(names) <= 50
                names = names[-50:]
                paths = [base / name / "report.json" for name in names]
            except FileNotFoundError:
                return [], True
            except OSError as exc:
                raise ContextError("verification receipt directory cannot be read") from exc
        result: list[Path] = []
        for path in paths[:50]:
            try:
                rel = path if not path.is_absolute() else path.relative_to(self.repo)
                text = Path(rel).as_posix()
            except ValueError as exc:
                raise ContextError("receipt path escapes repository") from exc
            if not re.fullmatch(r"build/verification/[^/]+/report\.json", text):
                raise ContextError("receipt path is outside the fixed receipt layout")
            result.append(self.repo / text)
        return sorted(result, key=lambda p: p.as_posix()), complete

    @staticmethod
    def _report_schema(value: Any) -> tuple[bool, str]:
        if not isinstance(value, dict):
            return False, "receipt is not an object"
        if type(value.get("version")) is not int or value["version"] != 1:
            return False, "receipt version is invalid"
        if not isinstance(value.get("started_utc"), str) or not re.fullmatch(r"[0-9]{8}T[0-9]{6}(?:\.[0-9]+)?Z", value["started_utc"]):
            return False, "receipt started_utc is missing or invalid"
        if not isinstance(value.get("scope"), str) or value["scope"] not in SCOPES:
            return False, "receipt scope is unknown"
        snap = value.get("snapshot")
        if not isinstance(snap, dict) or not isinstance(snap.get("files"), dict) or not snap["files"]:
            return False, "receipt snapshot.files is missing or empty"
        if not isinstance(snap.get("sha256"), str) or not HEX64.fullmatch(snap["sha256"]):
            return False, "receipt snapshot digest is invalid"
        for path, digest in snap["files"].items():
            if not isinstance(path, str) or path.startswith("/") or "\\" in path or any(x in {"", ".", ".."} for x in path.split("/")):
                return False, "receipt contains an invalid relative path"
            if digest is not None and (not isinstance(digest, str) or not HEX64.fullmatch(digest)):
                return False, "receipt contains an invalid file digest"
        gates = value.get("gates")
        if not isinstance(gates, list) or not gates:
            return False, "receipt gates are missing or empty"
        for gate in gates:
            if not isinstance(gate, dict) or not isinstance(gate.get("name"), str) or not gate["name"] or type(gate.get("exit_code")) is not int:
                return False, "receipt gate is malformed or unfinished"
        if not isinstance(value.get("errors"), list) or not isinstance(value.get("status"), str):
            return False, "receipt terminal fields are malformed"
        trust = value.get("trust_scope")
        if not isinstance(trust, str) or not trust:
            return False, "receipt trust_scope is missing"
        return True, ""

    def verification_status(
        self, snapshot: str, scope: str = "full", offset: int = 0, limit: int = 20,
        _receipt_paths: Iterable[Path] | None = None,
    ) -> dict[str, Any]:
        rec = self._validate(snapshot)
        self._page([], offset, limit)
        selected, scope_limits = self._scope_files(rec["files"], scope)
        if scope == "downstream":
            return {
                "metadata": self._metadata(rec), "scope": scope, "accepted": False,
                "availability": "unavailable", "remote": {"status": "unavailable"},
                "limitations": scope_limits, "receipts": [], "paging": {
                    "offset": offset, "limit": limit, "total": 0,
                },
            }
        paths, complete = self._receipt_paths(_receipt_paths)
        reports: list[dict[str, Any]] = []
        for path in paths:
            rel = path.relative_to(self.repo).as_posix()
            try:
                value = _bounded_json(self._fixed_file(path))
                valid, issue = self._report_schema(value)
                row = value if isinstance(value, dict) else {}
                row = dict(row)
                row.update({"path": rel, "schema_valid": valid, "schema_error": issue})
            except ContextError as exc:
                row = {"path": rel, "schema_valid": False, "schema_error": str(exc)}
            reports.append(row)
        reports.sort(key=lambda x: (x["path"].split("/")[-2] if re.fullmatch(r"[0-9]{8}T[0-9]{6}(?:\.[0-9]+)?Z", x["path"].split("/")[-2]) else x.get("started_utc", x["path"].split("/")[-2]) if x.get("schema_valid") else x["path"].split("/")[-2], x["path"]))
        latest_observed = reports[-1] if reports else None
        compatible = [r for r in reports if r.get("scope") == scope]

        def assess(report: dict[str, Any]) -> dict[str, Any]:
            if not report.get("schema_valid"):
                return {"accepted": False, "limitation": report.get("schema_error")}
            given = report["snapshot"]["files"]
            original_digest_ok = report["snapshot"]["sha256"] == _digest(given)
            missing = sorted(set(selected) - set(given))
            extra = sorted(set(given) - set(selected))
            different = sorted(
                p for p in set(selected) & set(given)
                if given[p] != selected[p]
            )
            gates_ok = all(g["exit_code"] == 0 for g in report["gates"])
            accepted = (
                original_digest_ok and not missing and not extra and not different
                and report.get("status") == "passed" and gates_ok
                and report.get("errors") == [] and not scope_limits
                and rec["excluded_count"] == 0 and complete
            )
            return {
                "accepted": accepted,
                "digest_valid": original_digest_ok,
                "missing": missing[:100], "extra": extra[:100],
                "different": different[:100],
                "difference_count": len(missing) + len(extra) + len(different),
                "missing_count": len(missing), "extra_count": len(extra), "different_count": len(different),
                "differences_truncated": max(len(missing), len(extra), len(different)) > 100,
                "failed_gates": [
                    g["name"][:200] for g in report["gates"] if g["exit_code"] != 0
                ][:50],
                "failed_gate_count": sum(g["exit_code"] != 0 for g in report["gates"]),
            }

        latest = compatible[-1] if compatible else None
        assessment = assess(latest) if latest else None
        newer = reports[reports.index(latest) + 1:] if latest else reports
        unresolved_newer = [r for r in newer if not r.get("schema_valid")]
        limitations = list(scope_limits)
        if unresolved_newer:
            limitations.append("A newer malformed or unfinished attempt has unknown acceptance scope; a later valid attempt of the requested scope is required.")
        if not complete:
            limitations.append("Receipt scan is bounded to 50 directories; current exact acceptance is unavailable.")
        if rec["excluded_count"]:
            limitations.append("Source binding omits excluded paths; exact acceptance is unavailable.")
        if not reports:
            limitations.append("No local verification receipt was found.")
        if latest_observed and not latest_observed.get("schema_valid"):
            limitations.append("The most recent observed receipt is malformed or incomplete.")
        elif latest_observed and latest_observed.get("scope") not in SCOPES:
            limitations.append("The most recent observed receipt has an unknown scope.")
        if latest and assessment and not assessment["accepted"]:
            limitations.append("The latest scope-compatible receipt is not an exact accepted match.")
        receipt_page, paging = self._page(
            [{"path": r["path"], "scope": self._clip(r.get("scope")), "status": self._clip(r.get("status")),
              "started_utc": self._clip(r.get("started_utc")), "schema_valid": r.get("schema_valid")}
             for r in reports], offset, limit)
        result = {
            "metadata": self._metadata(rec), "scope": scope,
            "accepted": bool(assessment and assessment["accepted"]
                             and latest_observed and latest_observed.get("schema_valid")
                             and not unresolved_newer),
            "unresolved_newer_attempts": [r["path"] for r in unresolved_newer[:20]],
            "unresolved_newer_attempt_count": len(unresolved_newer),
            "latest_observed": (
                {"path": latest_observed["path"], "scope": self._clip(latest_observed.get("scope")),
                 "status": self._clip(latest_observed.get("status")), "errors": self._clip(latest_observed.get("errors")),
                 "schema_valid": latest_observed.get("schema_valid"), "schema_error": latest_observed.get("schema_error")}
                if latest_observed else None
            ),
            "latest": ({"path": latest["path"], "assessment": assessment} if latest else None),
            "latest_scope_compatible": (
                {"path": latest["path"], "assessment": assessment} if latest else None
            ),
            "historical_matching_evidence": [
                {"path": r["path"], "assessment": assess(r)}
                for r in compatible[:-1] if assess(r)["accepted"]
            ][:20],
            "receipts": receipt_page, "paging": paging,
            "scan_complete": complete, "limitations": limitations,
            "remote": {"status": "unavailable"},
            "trust_boundary": "Receipts are local trust-bound claims, not fresh proof.",
        }
        self._fresh(rec)
        return result

    def _api_expected(self, files: dict[str, Any]) -> set[str]:
        fixed = {"formalization/FunctionalInequalities.lean", "formalization/lean-toolchain",
                 "formalization/lakefile.toml", "formalization/lake-manifest.json",
                 "research/APIIndex.lean", "research/api_index.py", "research/module_inventory.py"}
        return fixed | {p for p in files if p.startswith("formalization/FunctionalInequalities/") and p.endswith(".lean") and files[p] is not None}

    def _manifest_api(self, rec: dict[str, Any], claim: str) -> tuple[dict[str, Any] | None, str | None]:
        base = self.repo / "build/api-index"
        try:
            manifest_bytes = self._fixed_file(base / "manifest.json")
            manifest = _bounded_json(manifest_bytes)
            api_bytes = self._fixed_file(base / "public-api.json")
            api = _bounded_json(api_bytes, limit=MAX_API, nodes=500000)
        except ContextError as exc:
            return None, str(exc)
        if not isinstance(manifest, dict) or type(manifest.get("format")) is not int or manifest["format"] != 1:
            return None, "API manifest format is missing or unsupported."
        inputs, outputs = manifest.get("inputs"), manifest.get("outputs")
        expected = self._api_expected(rec["files"])
        if not isinstance(inputs, dict) or set(inputs) != expected or any(rec["files"].get(p) != h or h is None for p, h in inputs.items()):
            return None, "API manifest inputs do not exactly match the selected library and producer inputs."
        producer_digest = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        if manifest.get("input_digest") != producer_digest:
            return None, "API manifest input_digest is stale."
        if not isinstance(outputs, dict) or set(outputs) != {"compiler.json", "public-api.json", "index.html", "Observe.lean"} or any(not isinstance(h, str) or not HEX64.fullmatch(h) for h in outputs.values()):
            return None, "API manifest output set is invalid."
        if outputs["public-api.json"] != _sha(api_bytes):
            return None, "API manifest output binding is stale."
        library = {p for p in expected if p.startswith("formalization/FunctionalInequalities/")}
        modules = sorted(p[len("formalization/"):-5].replace("/", ".") for p in library | {"formalization/FunctionalInequalities.lean"})
        counts = ("source_modules", "public_declarations", "with_source_ranges", "with_docstrings")
        if any(type(manifest.get(k)) is not int for k in counts) or not isinstance(api, list) or not api:
            return None, "API manifest producer counts or declaration rows are invalid."
        if manifest["source_modules"] != len(library) or manifest.get("imported_modules") != modules or manifest["public_declarations"] != len(api):
            return None, "API manifest inventory differs from its selected source inventory."
        for row in api:
            if not isinstance(row, dict) or not isinstance(row.get("name"), str) or not isinstance(row.get("type"), str):
                return None, "API declaration row is malformed."
        if manifest["with_source_ranges"] != sum(r.get("source_line") is not None for r in api) or manifest["with_docstrings"] != sum(r.get("docstring") is not None for r in api):
            return None, "API manifest observation counts are inconsistent."
        if not isinstance(manifest.get("source_head"), str) or not HEX40.fullmatch(manifest["source_head"]) or not isinstance(manifest.get("source_binding"), str) or not manifest["source_binding"] or not isinstance(manifest.get("trust_scope"), str) or not manifest["trust_scope"]:
            return None, "API manifest producer metadata is incomplete."
        if manifest.get("toolchain") != self._read_record(rec, "formalization/lean-toolchain").decode("utf-8").strip():
            return None, "API manifest toolchain differs."
        found = next((r for r in api if r["name"] == claim), None)
        if found is None:
            return None, "No exact compiler declaration was found."
        path, line = found.get("source_path"), found.get("source_line")
        end = found.get("source_end_line", line)
        if path not in library | {"formalization/FunctionalInequalities.lean"} or type(line) is not int or line < 1 or type(end) is not int or end < line:
            return None, "Compiler declaration has no valid bound source origin."
        if self._fixed_file(base / "manifest.json") != manifest_bytes or _sha(self._fixed_file(base / "public-api.json")) != outputs["public-api.json"]:
            return None, "API artifacts changed during observation."
        return {"name": claim, "type": found["type"][:10000], "type_truncated": len(found["type"]) > 10000,
                "origin": {"source_path": path, "source_sha256": rec["files"][path], "source_line": line, "source_end_line": end,
                           "module": str(found.get("module", ""))[:300], "output_sha256": outputs["public-api.json"]}}, None

    def claim_explain(self, snapshot: str, claim: str) -> dict[str, Any]:
        rec = self._validate(snapshot)
        if not isinstance(claim, str) or not claim or len(claim) > 300 or "\x00" in claim:
            raise ContextError("claim must be a bounded literal")
        tasks, literature, ledger = self._registries(rec)
        task_matches = []
        if isinstance(tasks, dict) and isinstance(tasks.get("nodes"), dict) and claim in tasks["nodes"]:
            task_matches.append({
                "id": claim, "record": self._clip(tasks["nodes"][claim]),
                "source": self._ref(rec, "research/tasks.json", "/nodes/" + claim.replace("~", "~0").replace("/", "~1")),
            })
        cert_matches = []
        if isinstance(ledger, dict) and isinstance(ledger.get("nodes"), list):
            for i, row in enumerate(ledger.get("nodes", [])):
                if isinstance(row, dict) and row.get("id") == claim:
                    cert_matches.append({
                        "record": self._clip(row),
                        "source": self._ref(rec, "research/a-series/ledger.yaml", f"/nodes/{i}"),
                    })
        literature_matches = []

        def search(value: Any, pointer: str = "") -> None:
            if len(literature_matches) >= 20:
                return
            if isinstance(value, dict):
                for key, child in value.items():
                    here = pointer + "/" + str(key).replace("~", "~0").replace("/", "~1")
                    if child == claim:
                        literature_matches.append({
                            "pointer": here, "value": claim,
                            "source": self._ref(rec, "research/progress/literature.json", here),
                        })
                    search(child, here)
            elif isinstance(value, list):
                for i, child in enumerate(value):
                    search(child, pointer + "/" + str(i))
        search(literature)
        try:
            compiler, limitation = self._manifest_api(rec, claim)
        except (ContextError, UnicodeError, TypeError, ValueError) as exc:
            compiler, limitation = None, "Compiler artifact unavailable: " + str(exc)[:200]
        result = {
            "metadata": self._metadata(rec), "claim": claim,
            "task_matches": task_matches, "certificate_records": cert_matches,
            "literature_matches": literature_matches, "compiler": compiler,
            "limitations": [limitation] if limitation else [],
            "note": "Recorded maps and compiler observations are not proof verification.",
        }
        self._fresh(rec)
        return result

    def changes_review(self, base: str, snapshot: str) -> dict[str, Any]:
        if not isinstance(base, str) or not HEX40.fullmatch(base):
            raise ContextError("base must be a full 40-hex commit ID")
        rec = self._validate(snapshot)
        old_oids = self._tree(base.lower())
        old_blobs = self._blobs({p: h for p, h in old_oids.items() if self._safe_rel(p)})
        old = {p: _sha(v) for p, v in old_blobs.items()}
        changes = []
        for path in sorted(set(old) | set(rec["files"])):
            if path in old and path in rec["files"] and old[path] == rec["files"][path]:
                continue
            suffix = Path(path).suffix
            kind = "Lean" if suffix == ".lean" else (
                "documentation" if suffix in {".md", ".tex"} else
                "metadata" if suffix in {".json", ".yaml", ".toml"} or path.endswith("lean-toolchain")
                else "tool/configuration"
            )
            changes.append({
                "path": path, "class": kind,
                "base_sha256": old.get(path), "snapshot_sha256": rec["files"].get(path),
            })
        classes = sorted({x["class"] for x in changes})
        result = {
            "metadata": self._metadata(rec), "base": base.lower(),
            "changes": changes[:300], "changes_truncated": len(changes) > 300, "change_count": len(changes), "classes": classes,
            "recommended_recorded_checks": ([{"check": "strict Lean/client/axiom checks for proof changes", "ref": "research/verification.md"}] if "Lean" in classes else []) + [
                {"check": "follow the recorded project workflow", "ref": "research/workflow.md"}
            ] if classes else [],
            "limitation": "Digest comparison only; no build or semantic verification was run.",
        }
        self._fresh(rec)
        return result

    def work_next(self, snapshot: str) -> dict[str, Any]:
        rec = self._validate(snapshot)
        text = self._read_record(rec, "HANDOFF.md").decode("utf-8", "replace") if "HANDOFF.md" in rec["files"] else ""
        lines = text.splitlines()
        selected: list[str] = []
        level: int | None = None
        for line in lines:
            match = re.match(r"^(#{1,6})\s+(.+?)\s*#*\s*$", line)
            if match:
                title = match.group(2).strip().lower()
                current = len(match.group(1))
                if level is None and title in {"current work and next step", "current work", "work"}:
                    level = current
                    selected.append(line)
                    continue
                if level is not None and current <= level:
                    break
                if level is not None:
                    selected.append(line)
            elif level is not None:
                selected.append(line)
        section = "\n".join(selected).strip()
        has_body = any(x.strip() and not x.startswith("#") for x in selected)
        handoff = section[:12000] if has_body else ""
        result = {
            "metadata": self._metadata(rec), "handoff_work": handoff, "handoff_truncated": len(section) > 12000,
            "literature_priorities": [],
            "limitations": [] if handoff else ["Current work section is absent or empty."],
            "interpretation": "Recorded human intent, not an invented assignment or proof goal.",
        }
        if "research/progress/literature.json" in rec["files"]:
            literature = self._json_file(rec, "research/progress/literature.json")
            if not isinstance(literature, dict) or not isinstance(literature.get("priorities", []), list):
                raise ContextError("literature priorities have an invalid type")
            result["literature_priorities"] = self._clip(literature.get("priorities", []))
        self._fresh(rec)
        return result

    def handoff_resource(self, commit: str) -> str:
        if not isinstance(commit, str) or not HEX40.fullmatch(commit):
            raise ContextError("resource commit must be a full 40-hex ID")
        tree = self._tree(commit.lower())
        oid = tree.get("HANDOFF.md")
        if not oid:
            raise ContextError("HANDOFF.md is unavailable at this commit")
        text = self._blobs({"HANDOFF.md": oid})["HANDOFF.md"].decode("utf-8", "replace")
        return text[:12000] + ("\n<truncated>" if len(text) > 12000 else "")
