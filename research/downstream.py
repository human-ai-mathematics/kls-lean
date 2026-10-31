#!/usr/bin/env python3
"""Downstream acceptance runner.

Builds three narrow Lean clients against one exact commit of this repository in a
fresh Lake fixture, audits every local declaration of the imported primary closure,
replays the compiled primary and client modules in `leanchecker`, and writes a
receipt.  A PASSED receipt is downstream acceptance evidence for that commit; it is
not a mathematical certificate and it does not replay trusted third-party caches.

The runner never reads the caller's working tree as Lean source, never touches the
caller's Git index, and never resumes or overwrites an existing output directory.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import urlsplit

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CLIENTS = ("MatrixIntegral", "GeneratedSemigroup", "FiniteProductCovariance")
DEFAULT_REPOSITORY = "https://github.com/human-ai-mathematics/kls-lean.git"
PACKAGE_NAME = "functional-inequalities"
PRIMARY_ROOT = "FunctionalInequalities"
FORBIDDEN_MODULE_PREFIXES = ("FunctionalInequalities.KLS", "solutions", "examples")
RUNNER_ROOT = Path(__file__).resolve().parents[1]

# Environment variables that can redirect which Git objects or Lake packages are
# fetched.  Their presence aborts the run before an output directory exists.
REJECTED_ENVIRONMENT = {
    "GIT_CONFIG", "GIT_CONFIG_PARAMETERS", "GIT_CONFIG_COUNT", "GIT_CONFIG_GLOBAL",
    "GIT_CONFIG_SYSTEM", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_OBJECT_DIRECTORY",
    "GIT_REPLACE_REF_BASE", "GIT_EXEC_PATH", "LAKE_PKG_URL_MAP",
}
REJECTED_ENVIRONMENT_PATTERN = re.compile(r"^GIT_CONFIG_(?:KEY|VALUE)_\d+$")
# Everything else in these families (index/worktree overrides, search paths,
# toolchain overrides, tracing) is stripped; the names are recorded, never values.
STRIPPED_PREFIXES = ("GIT_", "LEAN", "LAKE", "PYTHON", "ELAN_TOOLCHAIN")

TOOLCHAIN_PATTERN = re.compile(r"^leanprover/lean4:v(\d+\.\d+\.\d+(?:-rc\d+)?)$")
LEAN_VERSION_PATTERN = re.compile(r"Lean \(version ([0-9][^,\s)]*)")
MODULE_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
HEADER_KEYWORDS = {"module", "prelude", "public", "meta", "private", "import", "all"}
INVENTORY_PREFIX = "DECL_INVENTORY "
INVENTORY_FOOTER = re.compile(r"(?m)^INVENTORY_COUNT (\d+)\s*$")
AUDIT_FOOTER = re.compile(r"(?m)^Audited (\d+) local declarations\.\s*$")
REPLAY_LINE = re.compile(r"(?m)^replaying:?\s+(\S+)\s*$")


class DownstreamFailure(RuntimeError):
    def __init__(self, message: str, stage: str = "validation") -> None:
        super().__init__(message)
        self.stage = stage


class StepFailure(DownstreamFailure):
    def __init__(self, stage: str, code: int, tail: str) -> None:
        super().__init__(f"subprocess exited {code}: {tail[-1200:]}", stage)
        self.code = code


@dataclass(frozen=True)
class RunSettings:
    revision: str
    repository: str
    cache_packages: Path | None
    threads: int


# --------------------------------------------------------------------------- hashing

def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


# ------------------------------------------------------------------------ validation

def normalize_manifest_name(name: str) -> str:
    """Lake writes hyphenated package names as «name»; accept only path-safe names."""
    value = name.strip()
    if value.startswith("«") and value.endswith("»"):
        value = value[1:-1]
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", value) or value in {".", ".."}:
        raise DownstreamFailure(f"unsafe package name: {name!r}")
    return value


def validate_revision(value: str) -> str:
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-fA-F]{40}", value):
        raise DownstreamFailure("--rev must be exactly 40 hexadecimal digits")
    return value.lower()


def validate_repository(value: str) -> str:
    """Accept http(s)/file URLs without credentials, query or fragment, or a local Git directory."""
    if not value:
        raise DownstreamFailure("repository must not be empty")
    parsed = urlsplit(value)
    if parsed.scheme in {"http", "https", "file"}:
        if parsed.username is not None or parsed.password is not None:
            raise DownstreamFailure("credential-bearing repository URLs are refused")
        if parsed.query or parsed.fragment or "?" in value or "#" in value:
            raise DownstreamFailure("repository URLs with a query or fragment are refused")
        return value
    if parsed.scheme or value.startswith("git@") or ":" in value.split("/", 1)[0]:
        raise DownstreamFailure("only http(s), file:// and local Git directories are supported")
    path = Path(value).expanduser().resolve()
    if not path.is_dir():
        raise DownstreamFailure(f"local repository does not exist: {path}")
    return str(path)


def redact(text: str, repository: str | None = None) -> str:
    result = text
    if repository:
        result = result.replace(repository, "<repository>")
    return re.sub(r"(\w+://)[^/@\s]+@", r"\1<credentials>@", result)


def scrub_environment(source: dict[str, str] | None = None, threads: int = 2) -> tuple[dict[str, str], dict]:
    """Build the fixture environment; reject redirection, strip overrides, pin locks and threads."""
    inherited = dict(os.environ if source is None else source)
    rejected = sorted(k for k in inherited if k in REJECTED_ENVIRONMENT or REJECTED_ENVIRONMENT_PATTERN.match(k))
    if rejected:
        raise DownstreamFailure("environment variables that can redirect Git or Lake are present: "
                                + ", ".join(rejected), "environment")
    removed = sorted(k for k in inherited if k.startswith(STRIPPED_PREFIXES))
    env = {k: v for k, v in inherited.items() if k not in removed}
    env.update({"GIT_OPTIONAL_LOCKS": "0", "GIT_TERMINAL_PROMPT": "0",
                "LEAN_NUM_THREADS": str(threads), "MATHLIB_NO_CACHE_ON_UPDATE": "1"})
    report = {"removed_variables": removed,
              "set_variables": {k: env[k] for k in ("GIT_OPTIONAL_LOCKS", "GIT_TERMINAL_PROMPT",
                                                     "LEAN_NUM_THREADS", "MATHLIB_NO_CACHE_ON_UPDATE")}}
    return env, report


def parse_toolchain(text: str) -> tuple[str, str]:
    """Return (version, prefix basename) for an exact release or release-candidate toolchain."""
    declared = text.strip()
    match = TOOLCHAIN_PATTERN.match(declared)
    if not match:
        raise DownstreamFailure(f"unsupported lean-toolchain format: {declared!r}", "toolchain")
    return match.group(1), declared.replace("/", "--").replace(":", "---")


def check_toolchain(declared: str, version_output: str, prefix_output: str, stage: str) -> dict:
    version, prefix_name = parse_toolchain(declared)
    found = LEAN_VERSION_PATTERN.search(version_output)
    if not found:
        raise DownstreamFailure(f"unrecognised Lean version output: {version_output.strip()[:200]!r}", stage)
    if found.group(1) != version:
        raise DownstreamFailure(f"Lean version {found.group(1)} does not match declared toolchain v{version}", stage)
    lines = [line for line in prefix_output.strip().splitlines() if line.strip()]
    prefix = Path(lines[-1].strip()) if lines else None
    if prefix is None or not prefix.is_absolute() or not prefix.is_dir() or prefix.name != prefix_name:
        raise DownstreamFailure(f"Lean prefix {prefix} is not the declared toolchain {prefix_name}", stage)
    return {"declared": declared.strip(), "version": found.group(1), "prefix": str(prefix.resolve())}


# --------------------------------------------------------------- Lean header parsing

def _skip_trivia(source: str, i: int) -> int:
    """Skip whitespace, line comments and nested block comments."""
    n = len(source)
    while i < n:
        if source[i].isspace():
            i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = n if j < 0 else j
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise DownstreamFailure("unterminated block comment in module header")
        else:
            break
    return i


def _skip_directive_trivia(source: str, i: int) -> int:
    """Lean v4.35 import-header `whitespace` inside one directive (ParseImportsFast.lean:97-119).

    Newlines, `--` comments and nested `/- -/` comments are skipped; a tab fails (line 103) and
    a doc comment ends the trivia because it is a token there (line 116). Kept in step with
    `research/lean_header.py`; this runner deliberately stays standalone.
    """
    n = len(source)
    while i < n:
        if source[i] == "\t":
            raise DownstreamFailure("tabs are not allowed in an import directive")
        if source[i].isspace():
            i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            i = n if j < 0 else j
        elif source.startswith("/-", i) and not source.startswith(("/--", "/-!"), i):
            depth, i = 1, i + 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise DownstreamFailure("unterminated block comment in an import directive")
        else:
            break
    return i


def parse_imports(source: str) -> list[str]:
    """Imported module names from a Lean module header, without lexing declaration bodies.

    Supports `module`/`prelude`, `public`/`meta` modifiers and `import all`. As in Lean's
    `keywordCore` (ParseImportsFast.lean:121-134), trivia including newlines and nested
    comments may separate the keywords from the mandatory first module name. Further modules
    on the same line as the first are accepted for older sources only. Anything else after
    `import` fails closed.
    """
    imports: list[str] = []
    i = 0
    while True:
        i = _skip_trivia(source, i)
        word = MODULE_IDENT.match(source, i)
        if not word:
            break
        token = word.group()
        if token in {"module", "prelude"}:
            i = word.end()
            continue
        while token in {"public", "meta", "private"}:
            i = _skip_directive_trivia(source, word.end())
            word = MODULE_IDENT.match(source, i)
            token = word.group() if word else ""
        if token != "import":
            break
        k = _skip_directive_trivia(source, word.end())
        keyword = MODULE_IDENT.match(source, k)
        if keyword and keyword.group() == "all":
            k = _skip_directive_trivia(source, keyword.end())
        name = MODULE_IDENT.match(source, k)
        if not name:
            raise DownstreamFailure("import directive without a module name")
        if name.group() in HEADER_KEYWORDS:
            raise DownstreamFailure(f"unsupported import syntax: {source[k:k + 40]!r}")
        modules, j = [name.group()], name.end()
        while True:  # legacy: further modules on the first module's line only
            k = _skip_trivia(source, j)
            if k >= len(source) or "\n" in source[j:k]:
                break
            name = MODULE_IDENT.match(source, k)
            if not name or name.group() in HEADER_KEYWORDS:
                raise DownstreamFailure(f"unsupported import syntax: {source[k:k + 40]!r}")
            modules.append(name.group())
            j = name.end()
        imports.extend(modules)
        i = j
    return imports


def forbidden_import(name: str) -> bool:
    return any(name == prefix or name.startswith(prefix + ".") for prefix in FORBIDDEN_MODULE_PREFIXES)


def is_primary(name: str) -> bool:
    return name == PRIMARY_ROOT or name.startswith(PRIMARY_ROOT + ".")


def module_path(formalization: Path, name: str) -> Path:
    return formalization / (name.replace(".", "/") + ".lean")


def compute_source_closure(formalization: Path, client_sources: dict[str, bytes]) -> tuple[list[str], list[str]]:
    """Transitive primary closure of the clients from source headers, plus direct Mathlib imports."""
    expected: set[str] = set()
    direct_mathlib: set[str] = set()
    pending: list[str] = []

    def consider(imports: list[str]) -> None:
        for name in imports:
            if forbidden_import(name):
                raise DownstreamFailure(f"forbidden downstream import: {name}")
            if name == "Mathlib" or name.startswith("Mathlib."):
                direct_mathlib.add(name)
            if is_primary(name):
                pending.append(name)

    for client, data in sorted(client_sources.items()):
        try:
            imports = parse_imports(data.decode("utf-8"))
        except UnicodeDecodeError as exc:
            raise DownstreamFailure(f"client {client} is not UTF-8: {exc}")
        if not any(is_primary(name) for name in imports):
            raise DownstreamFailure(f"client {client} imports no {PRIMARY_ROOT} module")
        consider(imports)
    while pending:
        name = pending.pop()
        if name in expected:
            continue
        path = module_path(formalization, name)
        if not path.is_file():
            raise DownstreamFailure(f"missing primary module {name}: {path}")
        ensure_plain_file(formalization, path, name)
        expected.add(name)
        consider(parse_imports(path.read_text(encoding="utf-8")))  # a leaf may have no imports
    return sorted(expected), sorted(direct_mathlib)


def compare_coverage(expected, actual, label: str = "coverage") -> None:
    missing = sorted(set(expected) - set(actual))
    extra = sorted(set(actual) - set(expected))
    if missing or extra:
        raise DownstreamFailure(f"{label} mismatch; missing={missing}, unexpected={extra}")


# ------------------------------------------------------------- audit and inventory

def declaration_inventory_code(modules: list[str]) -> str:
    """Lean program listing every constant owned by `modules`, with the audit producer's ownership rule."""
    imports = "\n".join("import " + module for module in sorted(set(modules) | {"Lean"}))
    names = ", ".join(json.dumps(module) for module in modules)
    return imports + f'''
run_cmd do
  let env ← Lean.getEnv
  let modules : Array String := #[{names}]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let localDecl := match env.getModuleIdxFor? name with
      | some idx => modules.contains env.header.moduleNames[idx.toNat]!.toString
      | none => (`FunctionalInequalities).isPrefixOf name ||
          (`solutions).isPrefixOf name || (`examples).isPrefixOf name
    if !localDecl then continue
    count := count + 1
    Lean.logInfo m!"{INVENTORY_PREFIX}{{(Lean.Json.str name.toString).compress}}"
  if count == 0 then throwError "No local declarations found"
  Lean.logInfo m!"INVENTORY_COUNT {{count}}"
'''


def parse_inventory(output: str) -> set[str]:
    names: list[str] = []
    errors: list[str] = []
    for line in output.splitlines():
        if not line.startswith(INVENTORY_PREFIX):
            continue
        try:
            value = json.loads(line[len(INVENTORY_PREFIX):])
        except ValueError:
            value = None
        if not isinstance(value, str) or not value:
            errors.append(f"unparsed inventory line: {line[:120]!r}")
            continue
        names.append(value)
    footers = INVENTORY_FOOTER.findall(output)
    if len(footers) != 1:
        errors.append(f"expected exactly one inventory footer, found {len(footers)}")
    elif int(footers[0]) != len(names):
        errors.append(f"inventory footer counts {footers[0]} declarations but {len(names)} were listed")
    if len(set(names)) != len(names):
        errors.append("duplicate declaration in inventory")
    if not names:
        errors.append("empty declaration inventory")
    if errors:
        raise DownstreamFailure("; ".join(errors), "declaration-inventory")
    return set(names)


def validate_axiom_reports(output: str, expected_names: set[str], parser) -> dict[str, list[str]]:
    """Fail closed unless the audit reports exactly `expected_names` with standard axioms only."""
    reports, errors = parser(output, set(expected_names), structured=True)
    errors = list(errors)
    if not reports:
        errors.append("empty axiom report")
    extra = sorted(set(reports) - set(expected_names))
    if extra:
        errors.append(f"axiom reports outside the declaration inventory: {extra[:5]}")
    for name, axioms in reports.items():
        if not isinstance(name, str) or not isinstance(axioms, list):
            errors.append(f"malformed axiom report: {name!r}")
        elif set(axioms) - STANDARD_AXIOMS:
            errors.append(f"{name}: nonstandard axioms {sorted(set(axioms) - STANDARD_AXIOMS)}")
    footers = AUDIT_FOOTER.findall(output)
    if len(footers) != 1:
        errors.append(f"expected exactly one audit footer, found {len(footers)}")
    elif int(footers[0]) != len(reports):
        errors.append(f"audit footer counts {footers[0]} declarations but {len(reports)} reports were parsed")
    if errors:
        raise DownstreamFailure("; ".join(sorted(set(errors))), "axiom-audit")
    return reports


# ------------------------------------------------------------------------ Git helpers

def _git(args: list[str], cwd: Path, env: dict[str, str], ok_codes=(0,)) -> subprocess.CompletedProcess:
    proc = subprocess.run(["git", *args], cwd=cwd, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if proc.returncode not in ok_codes:
        raise DownstreamFailure(f"git {args[0]} failed in {cwd.name}: {redact(proc.stderr[-800:])}")
    return proc


def git_head_and_clean(path: Path, env: dict[str, str]) -> tuple[str, bool]:
    """HEAD and tracked-clean state; GIT_OPTIONAL_LOCKS=0 keeps the inspection read-only."""
    head = _git(["rev-parse", "HEAD"], path, env).stdout.strip().lower()
    status = _git(["status", "--porcelain", "--untracked-files=no", "--ignore-submodules"], path, env)
    return head, not status.stdout.strip()


def check_git_self_contained(path: Path, env: dict[str, str]) -> None:
    """The copied package must not reference any Git directory or worktree outside itself."""
    resolved = path.resolve()
    if (path / ".git").is_symlink() or not (path / ".git").is_dir():
        raise DownstreamFailure(f"{path.name}: .git is not a plain directory (link, worktree or submodule pointer)")
    git_dir = (path / _git(["rev-parse", "--git-dir"], path, env).stdout.strip()).resolve()
    if git_dir != resolved / ".git":
        raise DownstreamFailure(f"{path.name}: Git directory {git_dir} is outside the copied package")
    top = Path(_git(["rev-parse", "--show-toplevel"], path, env).stdout.strip()).resolve()
    if top != resolved:
        raise DownstreamFailure(f"{path.name}: worktree {top} is not the copied package")
    worktree = _git(["config", "--get", "core.worktree"], path, env, ok_codes=(0, 1))
    if worktree.returncode == 0:
        raise DownstreamFailure(f"{path.name}: core.worktree redirection is refused")


def check_cache_symlinks(root: Path, name: str) -> int:
    """Allow symlinks that resolve strictly inside `root`; refuse escapes, broken/cyclic links and Git metadata links."""
    resolved_root = root.resolve()
    count = 0
    for directory, dirnames, filenames in os.walk(root, followlinks=False):
        for entry in dirnames + filenames:
            link = Path(directory) / entry
            if not link.is_symlink():
                continue
            relative = link.relative_to(root)
            if relative.parts[0] == ".git":
                raise DownstreamFailure(f"cache {name}: symlink in Git metadata is refused: {relative}", "cache")
            try:
                target = link.resolve(strict=True)
            except (OSError, RuntimeError):
                raise DownstreamFailure(f"cache {name}: broken or cyclic symlink is refused: {relative}", "cache")
            if not target.is_relative_to(resolved_root):
                raise DownstreamFailure(f"cache {name}: symlink escapes the cache root: {relative} -> {os.readlink(link)}", "cache")
            count += 1
    return count


def copy_tree(source: Path, destination: Path, env: dict[str, str]) -> str:
    """Whole-tree copy; copy-on-write where the platform offers it, shutil otherwise."""
    command = None
    if sys.platform == "darwin":
        command = ["cp", "-R", "-p", "-c", str(source), str(destination)]
    elif sys.platform.startswith("linux"):
        command = ["cp", "-R", "-p", "--reflink=always", str(source), str(destination)]
    if command:
        proc = subprocess.run(command, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        if proc.returncode == 0:
            return "copy-on-write"
        if destination.exists():
            shutil.rmtree(destination)
    shutil.copytree(source, destination, symlinks=True)
    return "shutil.copytree"


def validate_cache(cache_root: Path, manifest_packages: list[dict], target_root: Path,
                   env: dict[str, str]) -> list[dict]:
    """Copy every pinned third-party package of the manifest from a clean cache; fail otherwise."""
    records: list[dict] = []
    cache_root = cache_root.resolve()
    for item in manifest_packages:
        if not isinstance(item, dict):
            raise DownstreamFailure("malformed package manifest entry", "cache")
        name = normalize_manifest_name(str(item.get("name", "")))
        if name == PACKAGE_NAME:
            continue
        if item.get("type", "git") != "git":
            raise DownstreamFailure(f"non-Git dependency cannot be cached: {name}", "cache")
        pin = str(item.get("rev", "")).lower()
        if not re.fullmatch(r"[0-9a-f]{40}", pin):
            raise DownstreamFailure(f"dependency {name} is not pinned to a full commit", "cache")
        source = cache_root / name
        if source.is_symlink() or not source.is_dir() or source.resolve().parent != cache_root:
            raise DownstreamFailure(f"cache lacks a plain directory for {name}", "cache")
        if (source / ".git").is_symlink() or not (source / ".git").is_dir():
            raise DownstreamFailure(f"cache {name}: .git is not a plain directory", "cache")
        internal_links = check_cache_symlinks(source, name)
        head, clean = git_head_and_clean(source, env)
        if head != pin or not clean:
            raise DownstreamFailure(f"cache {name} is not tracked-clean at manifest pin {pin}", "cache")
        destination = target_root / name
        if destination.exists():
            raise DownstreamFailure(f"cache destination already exists: {destination}", "cache")
        destination.parent.mkdir(parents=True, exist_ok=True)
        copy_mode = copy_tree(source, destination, env)
        if check_cache_symlinks(destination, name) != internal_links:
            raise DownstreamFailure(f"copied cache {name} does not preserve its internal symlinks", "cache")
        check_git_self_contained(destination, env)
        copied_head, copied_clean = git_head_and_clean(destination, env)
        if copied_head != pin or not copied_clean:
            raise DownstreamFailure(f"copied cache {name} failed its pin/clean recheck", "cache")
        records.append({"package": name, "revision": pin, "source": str(source), "copy_mode": copy_mode,
                        "internal_symlinks_preserved": internal_links,
                        "tracked_source_clean": True, "compiled_cache_trusted_not_replayed": True})
    return records


def recheck_cache_pins(records: list[dict], target_root: Path, env: dict[str, str]) -> None:
    for record in records:
        head, clean = git_head_and_clean(target_root / record["package"], env)
        if head != record["revision"] or not clean:
            raise DownstreamFailure(f"copied cache {record['package']} changed during the run", "recheck")


# ------------------------------------------------------------------- Lake inspection

def inventory_primary_oleans(formalization: Path) -> dict[str, Path]:
    root = formalization / ".lake" / "build" / "lib" / "lean"
    found: dict[str, Path] = {}
    if root.is_dir():
        for path in root.rglob("*.olean"):
            name = ".".join(path.relative_to(root).with_suffix("").parts)
            found[name] = path
    return found


def path_is_allowed(value: str, project: Path, prefix: Path) -> bool:
    path = Path(value)
    path = (path if path.is_absolute() else project / path).resolve()
    return any(path == root or root in path.parents for root in (project.resolve(), prefix.resolve()))


SEARCH_PATH_PROBE = ("import json, os; print('SEARCH_PATHS ' + json.dumps({k: os.environ.get(k) "
                     "for k in ('LEAN_PATH', 'LEAN_SRC_PATH')}))")


def parse_search_paths(output: str) -> dict[str, list[str]]:
    """Lean search paths as `lake env` exports them; LEAN_PATH must be present, others may be unset."""
    lines = [line for line in output.splitlines() if line.startswith("SEARCH_PATHS ")]
    try:
        values = json.loads(lines[0][len("SEARCH_PATHS "):]) if len(lines) == 1 else None
    except ValueError:
        values = None
    if not isinstance(values, dict) or not values.get("LEAN_PATH"):
        raise DownstreamFailure("could not read LEAN_PATH from the fixture environment", "recheck")
    return {k: [v for v in (value or "").split(os.pathsep) if v] for k, value in values.items()}


def load_manifest_packages(path: Path, stage: str = "validation") -> list[dict]:
    try:
        packages = json.loads(path.read_text(encoding="utf-8"))["packages"]
    except (OSError, ValueError, KeyError, TypeError) as exc:
        raise DownstreamFailure(f"invalid lake manifest {path.name}: {exc}", stage)
    if not isinstance(packages, list):
        raise DownstreamFailure("lake manifest packages is not a list", stage)
    return packages


def toml_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def fixture_lakefile(repository: str, revision: str) -> str:
    lines = ['name = "downstream-acceptance"', 'version = "0.1.0"',
             "defaultTargets = [" + ", ".join(toml_string(x) for x in CLIENTS) + "]", "",
             "[[require]]", f"name = {toml_string(PACKAGE_NAME)}", f"git = {toml_string(repository)}",
             f"rev = {toml_string(revision)}", 'subDir = "formalization"', ""]
    for name in CLIENTS:
        lines += ["[[lean_lib]]", f"name = {toml_string(name)}", ""]
    return "\n".join(lines)


def verify_clients_unchanged(project: Path, clients_bytes: dict[str, bytes]) -> None:
    for name, data in clients_bytes.items():
        path = project / f"{name}.lean"
        if not path.is_file() or path.read_bytes() != data:
            raise DownstreamFailure(f"client bytes changed or missing: {name}", "recheck")


def ensure_plain_file(root: Path, path: Path, label: str, stage: str = "git-checkout") -> None:
    """`path` must be a regular file below `root` with no symlink component (no escape from the checkout)."""
    current = root
    for part in path.relative_to(root).parts:
        current = current / part
        if current.is_symlink():
            raise DownstreamFailure(f"{label}: symlink component {current} is refused", stage)
    if not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise DownstreamFailure(f"{label}: {path} is not a plain file inside the checkout", stage)


def compare_dependency_manifests(target: list[dict], fixture: list[dict], repository: str, revision: str) -> dict[str, dict]:
    """Exact third-party pin comparison between the target's manifest and the resolved fixture manifest."""
    def table(items: list[dict], label: str) -> dict[str, dict]:
        out: dict[str, dict] = {}
        for item in items:
            if not isinstance(item, dict):
                raise DownstreamFailure(f"malformed entry in {label} manifest", "lake-update")
            name = normalize_manifest_name(str(item.get("name", "")))
            if name in out:
                raise DownstreamFailure(f"duplicate package {name} in {label} manifest", "lake-update")
            out[name] = item
        return out

    wanted, resolved = table(target, "target"), table(fixture, "fixture")
    primary = resolved.pop(PACKAGE_NAME, None)
    if (primary is None or primary.get("type") != "git" or primary.get("subDir") != "formalization"
            or str(primary.get("rev", "")).lower() != revision or primary.get("url") != repository):
        raise DownstreamFailure("fixture manifest does not pin the requested Git dependency", "lake-update")
    if set(wanted) != set(resolved):
        raise DownstreamFailure(f"fixture manifest packages differ from target manifest; missing={sorted(set(wanted) - set(resolved))}, "
                                f"unexpected={sorted(set(resolved) - set(wanted))}", "lake-update")
    pins: dict[str, dict] = {}
    for name, item in wanted.items():
        other = resolved[name]
        pin = str(item.get("rev", "")).lower()
        if item.get("type", "git") != "git" or other.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", pin):
            raise DownstreamFailure(f"dependency {name} is not a fully pinned Git package", "lake-update")
        if (str(other.get("rev", "")).lower() != pin or other.get("url") != item.get("url")
                or other.get("subDir") != item.get("subDir")):
            raise DownstreamFailure(f"dependency {name} resolved to a different pin, URL or subDir than the target manifest", "lake-update")
        pins[name] = {"revision": pin, "url": item.get("url"), "subDir": item.get("subDir")}
    return pins


def check_dependency_checkouts(pins: dict[str, dict], packages_dir: Path, env: dict[str, str], stage: str) -> None:
    """Every resolved third-party package must be a tracked-clean checkout at its pin (cache or cold mode)."""
    for name, info in sorted(pins.items()):
        path = packages_dir / name
        if path.is_symlink() or not path.is_dir():
            raise DownstreamFailure(f"dependency {name} is not materialised as a plain directory", stage)
        head, clean = git_head_and_clean(path, env)
        if head != info["revision"] or not clean:
            raise DownstreamFailure(f"dependency {name} is {head} (clean={clean}), not a clean {info['revision']}", stage)


def tool_hashes(verify) -> dict[str, str]:
    verify_path = Path(verify.__file__).resolve()
    return {"research/downstream.py": sha256_file(Path(__file__).resolve()),
            "research/verify.py": sha256_file(verify_path), "verify_path": str(verify_path)}


def summarise_failed_audit(output: str, verify) -> list[str] | None:
    """Nonstandard axioms named by a failed audit's parsable reports, or None if nothing parsed."""
    found, _ = verify.axiom_reports(output, structured=True) if hasattr(verify, "axiom_reports") else ([], [])
    observed = sorted({axiom for _, axioms in found for axiom in axioms} - STANDARD_AXIOMS)
    return observed if found else None


def companion_artifacts(path: Path) -> list[Path]:
    """A module's .olean plus the companions this Lean version writes next to it."""
    candidates = [path, Path(str(path) + ".private"), Path(str(path) + ".server"), path.with_suffix(".ilean")]
    return [p for p in candidates if p.is_file()]


def load_verify():
    """Import the trusted research.verify helpers (sibling module, or via PYTHONPATH in candidate mode)."""
    try:
        import verify  # type: ignore
    except ImportError:
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        try:
            import verify  # type: ignore
        except ImportError as exc:
            raise DownstreamFailure(f"cannot import research.verify: {exc}", "axiom-audit")
    for attr in ("library_axiom_audit_code", "parse_axioms"):
        if not callable(getattr(verify, attr, None)):
            raise DownstreamFailure(f"research.verify lacks {attr}", "axiom-audit")
    return verify


# --------------------------------------------------------------------------- runner

def write_json(path: Path, data) -> None:
    """Atomic replace within the run directory; never a second run in the same directory."""
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


class StepRunner:
    def __init__(self, output: Path, env: dict[str, str], repository: str,
                 spawn=subprocess.run, on_step=None) -> None:
        self.output, self.env, self.repository = output, env, repository
        self.spawn, self.on_step = spawn, on_step
        self.steps: list[dict] = []
        self.current = "initialization"

    def run(self, name: str, args: list[str], cwd: Path, input_text: str | None = None) -> str:
        self.current = name
        log = self.output / f"{name}.log"
        if log.exists():
            raise DownstreamFailure(f"refusing to overwrite step log {log.name}", name)
        started = time.monotonic()
        command = " ".join(redact(str(x), self.repository) for x in args)
        completed = self.spawn(args, cwd=cwd, env=self.env, input=input_text, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False)
        output = redact(completed.stdout or "", self.repository)
        log.write_text(f"COMMAND {command}\nEXIT {completed.returncode}\n{output}", encoding="utf-8")
        self.steps.append({"name": name, "command": command, "exit_code": completed.returncode,
                           "seconds": round(time.monotonic() - started, 3), "log": log.name,
                           "status": "PASSED" if completed.returncode == 0 else "FAILED"})
        write_json(self.output / "steps.json", self.steps)
        if self.on_step:
            self.on_step(self.steps)
        if completed.returncode != 0:
            raise StepFailure(name, completed.returncode, output)
        return output


def start_run(settings: RunSettings, output: Path, env_report: dict, verify) -> dict:
    """Create the run directory, config and an initial FAILED/incomplete receipt."""
    output.parent.mkdir(parents=True, exist_ok=True)
    output.mkdir()
    hashes = tool_hashes(verify)
    write_json(output / "run-config.json", {
        "schema_version": 1, "requested_commit": settings.revision, "repository": settings.repository,
        "cache_packages": str(settings.cache_packages) if settings.cache_packages else None,
        "threads": settings.threads, "output": str(output), "environment": env_report,
        "python": platform.python_version(), "platform": platform.platform(),
        "started_utc": _dt.datetime.now(_dt.timezone.utc).isoformat()})
    write_json(output / "runner-hashes.json", hashes)
    receipt = {
        "schema_version": 1, "status": "FAILED", "failed_stage": "incomplete",
        "error": "run started; no terminal status recorded yet",
        "meaning": "Downstream acceptance of three narrow clients; not a mathematical certificate.",
        "requested_commit": settings.revision, "resolved_commit": None, "repository": settings.repository,
        "effective_repository_url": None, "fixture_location": str(output / "project"),
        "toolchain": {}, "tool_versions": {}, "tool_hashes": hashes, "environment": env_report,
        "client_modules": list(CLIENTS), "client_hashes": {}, "expected_primary_modules": [],
        "direct_mathlib_imports": [], "source_hashes": {}, "config_hashes": {},
        "built_primary_modules": [], "replayed_modules": [], "declaration_inventory_count": 0,
        "declaration_report_count": 0, "allowed_axioms": sorted(STANDARD_AXIOMS),
        "audit_status": "not-run", "nonstandard_axioms": None,
        "third_party_packages": {}, "resolved_manifest_hash": None,
        "cache_mode": "explicit-cache" if settings.cache_packages else "cold",
        "cache_provenance": [], "trust_boundary": None, "search_paths_isolated": False,
        "steps": [], "evidence_hashes": {},
    }
    write_json(output / "receipt.json", receipt)
    return receipt


def evidence_hashes(output: Path, project: Path, built: dict[str, Path]) -> dict[str, str]:
    """Hashes of the run's own evidence only; trusted dependencies are represented by pins."""
    files = [p for p in output.iterdir() if p.is_file() and p.suffix in {".log", ".lean"}]
    files += [output / n for n in ("run-config.json", "runner-hashes.json", "steps.json")]
    files += [project / n for n in ("lakefile.toml", "lean-toolchain", "lake-manifest.json", "target-lake-manifest.json")]
    files += [project / f"{c}.lean" for c in CLIENTS]
    for olean in [project / ".lake" / "build" / "lib" / "lean" / f"{c}.olean" for c in CLIENTS] + list(built.values()):
        files += companion_artifacts(olean)
    return {str(p.relative_to(output)): sha256_file(p) for p in sorted(set(files)) if p.is_file()}


def execute(settings: RunSettings, output: Path, env: dict[str, str], receipt: dict,
            spawn=subprocess.run) -> int:
    project = output / "project"
    package = project / ".lake" / "packages" / PACKAGE_NAME
    formalization = package / "formalization"
    repository, revision = settings.repository, settings.revision

    def checkpoint(steps=None):
        if steps is not None:
            receipt["steps"] = steps
        write_json(output / "receipt.json", receipt)

    runner = StepRunner(output, env, repository, spawn, checkpoint)
    clients_bytes: dict[str, bytes] = {}
    built: dict[str, Path] = {}
    try:
        package.mkdir(parents=True)
        runner.run("git-init", ["git", "init", "--quiet"], package)
        effective = _git(["ls-remote", "--get-url", repository], package, env).stdout.strip()
        receipt["effective_repository_url"] = redact(effective)
        if effective != repository:
            raise DownstreamFailure("Git configuration rewrites the repository URL (insteadOf); refusing", "git-init")
        runner.run("git-remote", ["git", "remote", "add", "origin", repository], package)
        runner.run("git-fetch", ["git", "fetch", "--depth=1", "origin", revision], package)
        runner.run("git-checkout", ["git", "checkout", "--detach", "--quiet", "FETCH_HEAD"], package)
        head, clean = git_head_and_clean(package, env)
        if head != revision or not clean:
            raise DownstreamFailure(f"checkout is {head} (clean={clean}), not a clean {revision}", "git-checkout")
        receipt["resolved_commit"] = head

        def commit_bytes(path: str) -> bytes:
            proc = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=package, env=env,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
            if proc.returncode:
                raise DownstreamFailure(f"target commit lacks {path}", "git-checkout")
            return proc.stdout

        for relative in ("formalization/lean-toolchain", "formalization/lake-manifest.json", "formalization/lakefile.toml"):
            ensure_plain_file(package, package / relative, relative)
        toolchain_bytes = commit_bytes("formalization/lean-toolchain")
        manifest_bytes = commit_bytes("formalization/lake-manifest.json")
        for name in CLIENTS:
            clients_bytes[name] = commit_bytes(f"examples/{name}.lean")
            ensure_plain_file(package, package / "examples" / f"{name}.lean", f"examples/{name}.lean")
            if (package / "examples" / f"{name}.lean").read_bytes() != clients_bytes[name]:
                raise DownstreamFailure(f"checked-out examples/{name}.lean differs from the commit blob", "git-checkout")
            receipt["client_hashes"][name] = sha256_bytes(clients_bytes[name])
            (project / f"{name}.lean").write_bytes(clients_bytes[name])
        if list(formalization.rglob("*.olean")):
            raise DownstreamFailure("primary checkout already contains compiled .olean output", "git-checkout")
        parse_toolchain(toolchain_bytes.decode("utf-8"))  # exact release tag required before any Lake call
        (project / "lean-toolchain").write_bytes(toolchain_bytes)
        (project / "target-lake-manifest.json").write_bytes(manifest_bytes)
        manifest_packages = load_manifest_packages(project / "target-lake-manifest.json")
        for item in manifest_packages:
            if normalize_manifest_name(str(item.get("name", ""))) == PACKAGE_NAME:
                raise DownstreamFailure("primary package appears in its own manifest")
            if item.get("type", "git") != "git":
                raise DownstreamFailure(f"path dependency is unsupported: {item.get('name')}")

        expected, direct_mathlib = compute_source_closure(formalization, clients_bytes)
        receipt["expected_primary_modules"], receipt["direct_mathlib_imports"] = expected, direct_mathlib
        source_hashes = {str(module_path(formalization, m).relative_to(package)): sha256_file(module_path(formalization, m))
                         for m in expected}
        receipt["source_hashes"] = source_hashes
        (project / "lakefile.toml").write_text(fixture_lakefile(repository, revision), encoding="utf-8")
        config_hashes = {n: sha256_file(project / n) for n in ("lakefile.toml", "lean-toolchain", "target-lake-manifest.json")}
        receipt["config_hashes"] = config_hashes
        checkpoint()

        # Toolchain before any build: elan selects it from the fixture's lean-toolchain.
        declared = toolchain_bytes.decode("utf-8")
        version_out = runner.run("toolchain-version", ["lean", "--version"], project)
        prefix_out = runner.run("toolchain-prefix", ["lean", "--print-prefix"], project)
        receipt["toolchain"] = check_toolchain(declared, version_out, prefix_out, "toolchain-version")
        receipt["tool_versions"] = {"lean": version_out.strip(), "git": _git(["--version"], project, env).stdout.strip(),
                                    "lake": runner.run("lake-version", ["lake", "--version"], project).strip()}

        if settings.cache_packages:
            receipt["cache_provenance"] = validate_cache(settings.cache_packages, manifest_packages,
                                                         project / ".lake" / "packages", env)
            receipt["trust_boundary"] = ("Exact target commit freshly compiled; pinned third-party source/compiled "
                                         "caches copied from a clean explicit cache and trusted, not rebuilt or replayed.")
        else:
            receipt["trust_boundary"] = ("Exact target commit freshly compiled; third-party dependencies materialised "
                                         "by Lake at their pins and built or fetched from the Mathlib cache server, "
                                         "trusted, not replayed. Cold mode is not a fresh Mathlib replay.")
        checkpoint()
        runner.run("lake-update", ["lake", "update"], project)
        fixture_manifest = project / "lake-manifest.json"
        if not fixture_manifest.is_file():
            raise DownstreamFailure("lake update produced no fixture manifest", "lake-update")
        pins = compare_dependency_manifests(manifest_packages, load_manifest_packages(fixture_manifest, "lake-update"),
                                            repository, revision)
        check_dependency_checkouts(pins, project / ".lake" / "packages", env, "lake-update")
        receipt["third_party_packages"] = pins
        receipt["resolved_manifest_hash"] = sha256_file(fixture_manifest)
        checkpoint()
        if not settings.cache_packages and direct_mathlib:
            runner.run("mathlib-cache-get", ["lake", "exe", "cache", "get", *direct_mathlib], project)

        runner.run("lake-build", ["lake", "build", *CLIENTS], project)
        built = inventory_primary_oleans(formalization)
        compare_coverage(expected, built, "fresh primary build")
        for name in sorted(built):
            if forbidden_import(name):
                raise DownstreamFailure(f"forbidden module was compiled: {name}", "lake-build")
        receipt["built_primary_modules"] = sorted(built)
        for name in CLIENTS:
            runner.run(f"strict-{name}", ["lake", "env", "lean", "-DwarningAsError=true", f"{name}.lean"], project)

        verify = load_verify()
        audited = sorted(set(expected) | set(CLIENTS))
        (output / "declaration-inventory.lean").write_text(declaration_inventory_code(audited), encoding="utf-8")
        (output / "axiom-audit.lean").write_text(verify.library_axiom_audit_code(audited), encoding="utf-8")
        inventory = parse_inventory(runner.run("declaration-inventory",
                                               ["lake", "env", "lean", str(output / "declaration-inventory.lean")], project))
        receipt["declaration_inventory_count"] = len(inventory)
        receipt["audit_status"] = "running"
        try:
            audit_output = runner.run("axiom-audit", ["lake", "env", "lean", "-DwarningAsError=true",
                                                      str(output / "axiom-audit.lean")], project)
        except StepFailure:
            receipt["audit_status"] = "failed"
            receipt["nonstandard_axioms"] = summarise_failed_audit((output / "axiom-audit.log").read_text(encoding="utf-8"), verify)
            raise
        try:
            reports = validate_axiom_reports(audit_output, inventory, verify.parse_axioms)
        except DownstreamFailure:
            receipt["audit_status"] = "failed"
            receipt["nonstandard_axioms"] = summarise_failed_audit(audit_output, verify)
            raise
        receipt["declaration_report_count"] = len(reports)
        receipt["audit_status"] = "completed-standard-only"
        receipt["nonstandard_axioms"] = []

        replay = runner.run("kernel-replay", ["lake", "env", "leanchecker", "--verbose", *sorted(built), *CLIENTS], project)
        replayed = sorted(set(REPLAY_LINE.findall(replay)))
        compare_coverage(set(built) | set(CLIENTS), replayed, "kernel replay")
        receipt["replayed_modules"] = replayed

        # Rechecks before PASSED.
        receipt["toolchain"] = check_toolchain(declared, runner.run("toolchain-version-recheck", ["lake", "env", "lean", "--version"], project),
                                               runner.run("toolchain-prefix-recheck", ["lake", "env", "lean", "--print-prefix"], project),
                                               "toolchain-version-recheck")
        prefix = Path(receipt["toolchain"]["prefix"])
        search_paths = parse_search_paths(runner.run("search-paths", ["lake", "env", sys.executable, "-I", "-c", SEARCH_PATH_PROBE], project))
        for variable, values in search_paths.items():
            for value in values:
                if not path_is_allowed(value, project, prefix):
                    raise DownstreamFailure(f"{variable} entry escapes fixture and toolchain: {value}", "recheck")
        receipt["search_paths_isolated"] = True
        head, clean = git_head_and_clean(package, env)
        if head != revision or not clean:
            raise DownstreamFailure("primary checkout is no longer a clean checkout of the requested commit", "recheck")
        verify_clients_unchanged(project, clients_bytes)
        if {n: sha256_file(project / n) for n in config_hashes} != config_hashes:
            raise DownstreamFailure("fixture configuration changed during the run", "recheck")
        if {k: sha256_file(package / k) for k in source_hashes} != source_hashes:
            raise DownstreamFailure("primary source changed during the run", "recheck")
        recheck_cache_pins(receipt["cache_provenance"], project / ".lake" / "packages", env)
        check_dependency_checkouts(pins, project / ".lake" / "packages", env, "recheck")
        if sha256_file(fixture_manifest) != receipt["resolved_manifest_hash"]:
            raise DownstreamFailure("fixture manifest changed after lake update", "recheck")
        if compute_source_closure(formalization, clients_bytes) != (expected, direct_mathlib):
            raise DownstreamFailure("source closure changed during the run", "recheck")
        compare_coverage(expected, inventory_primary_oleans(formalization), "final primary build inventory")
        if tool_hashes(verify) != receipt["tool_hashes"]:
            raise DownstreamFailure("runner or verify helper changed during the run", "recheck")
        receipt.update(status="PASSED", failed_stage=None, error=None)
    except DownstreamFailure as exc:
        receipt.update(status="FAILED", failed_stage=exc.stage, error=redact(str(exc), repository))
    except Exception as exc:  # unexpected: still a terminal FAILED receipt
        receipt.update(status="FAILED", failed_stage=runner.current, error=redact(f"{type(exc).__name__}: {exc}", repository))
    finally:
        receipt["steps"] = runner.steps
        receipt["finished_utc"] = _dt.datetime.now(_dt.timezone.utc).isoformat()
        receipt["evidence_hashes"] = evidence_hashes(output, project, built)
        checkpoint()
    return 0 if receipt["status"] == "PASSED" else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Downstream acceptance of one exact commit in a fresh Lake fixture.")
    parser.add_argument("--rev", required=True, help="full 40-hex commit")
    parser.add_argument("--repository", default=DEFAULT_REPOSITORY, help="http(s)/file URL or local Git directory")
    parser.add_argument("--cache-packages", help="directory of clean pinned third-party package caches")
    parser.add_argument("--output", help="new directory for this run (default: build/downstream/<utc>)")
    parser.add_argument("--threads", type=int, default=2)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        settings = RunSettings(validate_revision(args.rev), validate_repository(args.repository),
                               Path(args.cache_packages).expanduser().resolve() if args.cache_packages else None,
                               args.threads)
        if settings.threads <= 0:
            raise DownstreamFailure("--threads must be positive")
        if settings.cache_packages and not settings.cache_packages.is_dir():
            raise DownstreamFailure("--cache-packages must name an existing directory")
        if args.output:
            output = Path(args.output).expanduser().resolve()
        else:
            stamp = _dt.datetime.now(_dt.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
            output = RUNNER_ROOT / "build" / "downstream" / stamp
        if output.exists():
            raise DownstreamFailure(f"output directory already exists: {output}")
        env, env_report = scrub_environment(threads=settings.threads)
        verify = load_verify()
    except DownstreamFailure as exc:
        parser.error(str(exc))
    receipt = start_run(settings, output, env_report, verify)
    return execute(settings, output, env, receipt)


if __name__ == "__main__":
    raise SystemExit(main())
