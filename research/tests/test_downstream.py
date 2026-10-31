"""Regression tests for research/downstream.py.

Every test calls the runner's own functions.  Git fixtures are disposable
repositories under a temporary directory; Lake/Lean commands are replaced by a
controlled fake so no Lean build runs here.  Real acceptance against Lean is a
separate, independent step.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import downstream  # noqa: E402

verify = downstream.load_verify()

GIT_ENV = {k: v for k, v in os.environ.items() if not k.startswith(("GIT_", "LEAN", "LAKE", "PYTHON"))}
GIT_ENV.update({"GIT_OPTIONAL_LOCKS": "0", "GIT_TERMINAL_PROMPT": "0"})
CLEAN_ENV = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"), "HOME": os.environ.get("HOME", "/tmp")}
TOOLCHAIN = "leanprover/lean4:v4.33.0\n"
PRIMARY = "import Mathlib.Data.Real.Basic\nnamespace DownstreamFixture\ndef value : Nat := 7\nend DownstreamFixture\n"


def git(path: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(path), *args], env=GIT_ENV, text=True,
                                   stderr=subprocess.STDOUT).strip()


def make_repository(root: Path, *, clients_import: str = "FunctionalInequalities.Analysis.Probe",
                    primary: str = PRIMARY, with_examples: bool = True, toolchain: str = TOOLCHAIN,
                    packages: list | None = None, symlink_primary_to: Path | None = None) -> str:
    (root / "formalization" / "FunctionalInequalities" / "Analysis").mkdir(parents=True)
    probe = root / "formalization" / "FunctionalInequalities" / "Analysis" / "Probe.lean"
    if symlink_primary_to is None:
        probe.write_text(primary)
    else:
        probe.symlink_to(symlink_primary_to)
    (root / "formalization" / "lean-toolchain").write_text(toolchain)
    (root / "formalization" / "lakefile.toml").write_text('name = "functional-inequalities"\n')
    (root / "formalization" / "lake-manifest.json").write_text(json.dumps(
        {"version": "1.2.0", "packagesDir": ".lake/packages", "packages": packages or [], "name": "functional-inequalities"}))
    if with_examples:
        (root / "examples").mkdir()
        for name in downstream.CLIENTS:
            (root / "examples" / f"{name}.lean").write_text(
                f"import {clients_import}\nnamespace {name}\ntheorem smoke : (7 : Nat) = 7 := rfl\nend {name}\n")
    subprocess.check_call(["git", "init", "-q", "--initial-branch=main", str(root)], env=GIT_ENV)
    git(root, "add", ".")
    git(root, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "fixture")
    return git(root, "rev-parse", "HEAD")


def make_package(root: Path) -> str:
    """A disposable Git package standing in for a third-party cache entry."""
    root.mkdir(parents=True)
    (root / "source.txt").write_text("clean\n")
    subprocess.check_call(["git", "init", "-q", str(root)], env=GIT_ENV)
    git(root, "add", "source.txt")
    git(root, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "pkg")
    return git(root, "rev-parse", "HEAD")


class FakeLean:
    """Stand-in for lake/lean/leanchecker: real git runs, everything else is scripted."""

    def __init__(self, prefix: Path, build_oleans: bool = True, manifest_url: str | None = None) -> None:
        self.prefix, self.build_oleans, self.manifest_url = prefix, build_oleans, manifest_url

    def __call__(self, args, cwd, env, input=None, text=True, stdout=None, stderr=None, check=False):
        if args[0] == "git":
            return subprocess.run(args, cwd=cwd, env=env, input=input, text=text, stdout=stdout, stderr=stderr, check=check)
        tail = args[2:] if args[:2] == ["lake", "env"] else args
        out, code = "", 0
        if tail[:1] == ["lean"] and "--version" in tail:
            out = "Lean (version 4.33.0, arm64-apple-darwin24.6.0, commit abcdef, Release)\n"
        elif tail[:1] == ["lean"] and "--print-prefix" in tail:
            out = f"{self.prefix}\n"
        elif tail[:2] == ["lake", "--version"]:
            out = "Lake version 5.0.0 (Lean version 4.33.0)\n"
        elif tail[:2] == ["lake", "update"]:
            url = self.manifest_url or json.loads(
                (Path(cwd) / "lakefile.toml").read_text().split("git = ")[1].splitlines()[0])
            rev = json.loads((Path(cwd) / "lakefile.toml").read_text().split("rev = ")[1].splitlines()[0])
            target = json.loads((Path(cwd) / "target-lake-manifest.json").read_text())["packages"]
            (Path(cwd) / "lake-manifest.json").write_text(json.dumps({"packages": [
                {"name": "«functional-inequalities»", "type": "git", "url": url, "rev": rev, "subDir": "formalization"},
                *[{**item, "type": "git", "subDir": item.get("subDir")} for item in target]]}))
        elif tail[:2] == ["lake", "build"] and self.build_oleans:
            lib = Path(cwd) / ".lake" / "packages" / "functional-inequalities" / "formalization" / ".lake" / "build" / "lib" / "lean"
            (lib / "FunctionalInequalities" / "Analysis").mkdir(parents=True)
            for suffix in ("olean", "olean.private", "ilean"):
                (lib / "FunctionalInequalities" / "Analysis" / f"Probe.{suffix}").write_bytes(suffix.encode())
        elif tail[:1] == [sys.executable]:
            out = "SEARCH_PATHS " + json.dumps({"LEAN_PATH": str(Path(cwd) / ".lake") + os.pathsep + str(self.prefix / "lib" / "lean"),
                                                "LEAN_SRC_PATH": None}) + "\n"
        elif tail[:1] == ["lean"] and tail[-1].endswith("declaration-inventory.lean"):
            out = 'DECL_INVENTORY "DownstreamFixture.value"\nINVENTORY_COUNT 1\n'
        elif tail[:1] == ["lean"] and tail[-1].endswith("axiom-audit.lean"):
            out = 'AXIOM_REPORT {"name":"DownstreamFixture.value","axioms":[]}\nAudited 1 local declarations.\n'
        elif tail[:1] == ["leanchecker"]:
            out = "".join(f"replaying {m}\n" for m in tail[2:])
        return subprocess.CompletedProcess(args, code, out, "")


class ValidationTests(unittest.TestCase):
    def test_revision_is_full_and_case_normalised(self):
        self.assertEqual(downstream.validate_revision("A" * 40), "a" * 40)
        for bad in ("a" * 39, "g" * 40, "", "HEAD"):
            with self.assertRaises(downstream.DownstreamFailure):
                downstream.validate_revision(bad)

    def test_repository_transports_and_credentials(self):
        self.assertEqual(downstream.validate_repository(downstream.DEFAULT_REPOSITORY), downstream.DEFAULT_REPOSITORY)
        for bad in ("https://user:secret@example.invalid/repo.git", "https://token@example.invalid/repo.git",
                    "https://example.invalid/repo.git?token=abc", "https://example.invalid/repo.git#frag",
                    "git@example.invalid:repo.git", "ssh://example.invalid/repo.git", "example.invalid:repo.git",
                    "/definitely/not/a/directory/" + "x" * 8, ""):
            with self.subTest(url=bad), self.assertRaises(downstream.DownstreamFailure):
                downstream.validate_repository(bad)
        with tempfile.TemporaryDirectory() as directory:
            self.assertEqual(downstream.validate_repository(directory), str(Path(directory).resolve()))

    def test_cli_rejections_create_no_run(self):
        with tempfile.TemporaryDirectory() as directory:
            existing = Path(directory) / "existing"
            existing.mkdir()
            with mock.patch.dict(os.environ, CLEAN_ENV, clear=True):
                for argv in (["--rev", "a" * 40, "--output", str(existing)],
                             ["--rev", "a" * 40, "--threads", "0", "--output", str(Path(directory) / "t")],
                             ["--rev", "a" * 39, "--output", str(Path(directory) / "r")],
                             ["--rev", "a" * 40, "--cache-packages", str(Path(directory) / "nope"), "--output", str(Path(directory) / "c")]):
                    with self.subTest(argv=argv), self.assertRaises(SystemExit) as raised:
                        downstream.main(argv)
                    self.assertEqual(raised.exception.code, 2)
            self.assertEqual(sorted(p.name for p in Path(directory).iterdir()), ["existing"])
            self.assertEqual(list(existing.iterdir()), [])
            self.assertEqual(downstream.build_parser().parse_args(["--rev", "a" * 40]).threads, 2)

    def test_poisoned_environment_rejected_before_any_run(self):
        with tempfile.TemporaryDirectory() as directory:
            poisoned = {**CLEAN_ENV, "GIT_CONFIG_PARAMETERS": "'url.https://evil/.insteadOf=https://github.com/'"}
            with mock.patch.dict(os.environ, poisoned, clear=True), self.assertRaises(SystemExit) as raised:
                downstream.main(["--rev", "a" * 40, "--output", str(Path(directory) / "run")])
            self.assertEqual(raised.exception.code, 2)
            self.assertFalse((Path(directory) / "run").exists())

    def test_environment_rejection_strips_and_pins(self):
        for name in ("GIT_CONFIG_PARAMETERS", "GIT_CONFIG_KEY_3", "GIT_CONFIG_GLOBAL",
                     "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_OBJECT_DIRECTORY", "LAKE_PKG_URL_MAP", "GIT_EXEC_PATH"):
            with self.subTest(name=name), self.assertRaises(downstream.DownstreamFailure) as raised:
                downstream.scrub_environment({**CLEAN_ENV, name: "SECRET-VALUE"})
            self.assertIn(name, str(raised.exception))
            self.assertNotIn("SECRET-VALUE", str(raised.exception))
        stripped = {"GIT_INDEX_FILE": "x", "GIT_DIR": "x", "GIT_WORK_TREE": "x", "GIT_TRACE": "1", "GIT_SSH_COMMAND": "x",
                    "LEAN_PATH": "x", "LEAN_SRC_PATH": "x", "LEAN_SYSROOT": "x", "ELAN_TOOLCHAIN": "x",
                    "PYTHONPATH": "x", "LAKE_HOME": "x", "LEAN_NUM_THREADS": "99", "MATHLIB_NO_CACHE_ON_UPDATE": "0"}
        env, report = downstream.scrub_environment({**CLEAN_ENV, "ELAN_HOME": "/elan", **stripped}, threads=3)
        for name in stripped:
            if name not in ("LEAN_NUM_THREADS", "MATHLIB_NO_CACHE_ON_UPDATE"):
                self.assertNotIn(name, env)
                self.assertIn(name, report["removed_variables"])
        self.assertEqual(env["PATH"], CLEAN_ENV["PATH"])
        self.assertEqual(env["ELAN_HOME"], "/elan")
        self.assertEqual((env["GIT_OPTIONAL_LOCKS"], env["LEAN_NUM_THREADS"], env["MATHLIB_NO_CACHE_ON_UPDATE"]), ("0", "3", "1"))

    def test_manifest_names_normalised_and_unsafe_rejected(self):
        self.assertEqual(downstream.normalize_manifest_name("«functional-inequalities»"), "functional-inequalities")
        self.assertEqual(downstream.normalize_manifest_name("mathlib"), "mathlib")
        for name in ("../x", "/tmp/x", "", ".", "..", "a/b", "a\\b", "«»", "-x"):
            with self.subTest(name=name), self.assertRaises(downstream.DownstreamFailure):
                downstream.normalize_manifest_name(name)

    def test_toolchain_exact_release_match(self):
        with tempfile.TemporaryDirectory() as directory:
            prefix = Path(directory) / "leanprover--lean4---v4.33.0"
            prefix.mkdir()
            version = "Lean (version 4.33.0, arm64-apple-darwin24.6.0, commit d8b1897, Release)\n"
            info = downstream.check_toolchain(TOOLCHAIN, version, f"{prefix}\n", "t")
            self.assertEqual(info["version"], "4.33.0")
            for declared, observed, where in ((TOOLCHAIN, version.replace("4.33.0", "4.33.0-rc1"), prefix),
                                              ("leanprover/lean4:v4.33.0-rc1\n", version, prefix),
                                              (TOOLCHAIN, version, Path(directory)),
                                              (TOOLCHAIN, version, prefix / "missing"),
                                              (TOOLCHAIN, "lean: command not found\n", prefix),
                                              ("leanprover/lean4:nightly\n", version, prefix),
                                              ("4.33.0\n", version, prefix)):
                with self.subTest(declared=declared, observed=observed, where=where):
                    with self.assertRaises(downstream.DownstreamFailure):
                        downstream.check_toolchain(declared, observed, f"{where}\n", "t")


class HeaderParsingTests(unittest.TestCase):
    def test_header_forms_without_lexing_bodies(self):
        source = (
            "module\n/-! doc /- nested import Fake.One -/ import Fake.Two -/\n"
            "-- import Fake.Three\n"
            "public import FunctionalInequalities.One FunctionalInequalities.Two\n"
            "meta import all FunctionalInequalities.Three -- trailing comment\n"
            "import Mathlib.Data.Real.Basic\n\n"
            "namespace X\ntheorem h' (f' : Nat) : f' = f' := rfl\n"
            "def c : Char := '\"'\ndef s := \"import Fake.Four\"\ndef t := 'a'\n"
            "/- unbalanced in body is irrelevant: import Fake.Five\nend X\n")
        self.assertEqual(downstream.parse_imports(source), [
            "FunctionalInequalities.One", "FunctionalInequalities.Two",
            "FunctionalInequalities.Three", "Mathlib.Data.Real.Basic"])
        self.assertEqual(downstream.parse_imports("namespace Leaf\ndef x := 1\n"), [])
        self.assertEqual(downstream.parse_imports(""), [])
        self.assertEqual(downstream.parse_imports("import A.B'\nprivate def x := 1\n"), ["A.B'"])

    def test_newline_and_comment_trivia_before_the_first_module(self):
        # Matches Lean v4.35's fast import parser (ParseImportsFast.lean:97-134) and lean_header.
        cases = {"import\nFoo\n": ["Foo"],
                 "module\nimport /-\n  header comment\n-/ Mathlib\n": ["Mathlib"],
                 "module\nimport all\n  /- a /- nested -/ b -/\n  -- line\n  A.B\n": ["A.B"],
                 "module\npublic\n  meta /- c -/\n import\n A.B\n": ["A.B"],
                 "import\n  A B\nimport C\n": ["A", "B", "C"],
                 "import A\n  B\n": ["A"]}
        for source, expected in cases.items():
            with self.subTest(source=source):
                self.assertEqual(downstream.parse_imports(source), expected)

    def test_each_module_system_import_form_is_an_edge(self):
        forms = {"import A.Plain": "A.Plain", "public import A.Public": "A.Public",
                 "meta import A.Meta": "A.Meta", "public meta import A.PublicMeta": "A.PublicMeta",
                 "import all A.All": "A.All"}
        for directive, module in forms.items():
            with self.subTest(directive=directive):
                self.assertEqual(downstream.parse_imports(
                    "/- Copyright -/\nmodule\n\n" + directive + "\n\n@[expose] public section\n"), [module])
        self.assertEqual(downstream.parse_imports("import Mathlib\nimport A.B\n"), ["Mathlib", "A.B"])
        self.assertEqual(downstream.parse_imports("module\n\n/-! doc -/\n\npublic section\n"), [])

    def test_header_fails_closed(self):
        for source in ("import «Weird Name»\n", "import Foo.\n", "import Foo, Bar\n",
                       "/- never closed\nimport Foo\n", "import all\n", "import\n/-! doc -/ Foo\n",
                       "import\tFoo\n", "import /- open\nFoo\n", "module\nimport all\n\n"):
            with self.subTest(source=source), self.assertRaises(downstream.DownstreamFailure):
                downstream.parse_imports(source)

    def test_closure_forbidden_missing_leaf_and_client_rules(self):
        with tempfile.TemporaryDirectory() as directory:
            formalization = Path(directory)
            lib = formalization / "FunctionalInequalities"
            (lib / "KLS").mkdir(parents=True)
            (lib / "Leaf.lean").write_text("def leaf := 1\n")
            (lib / "Mid.lean").write_text("import FunctionalInequalities.Leaf\nimport Mathlib.Order.Basic\n")
            (lib / "KLS" / "Target.lean").write_text("import FunctionalInequalities.Leaf\n")
            clients = {"MatrixIntegral": b"import FunctionalInequalities.Mid\nimport Mathlib.Data.Nat.Basic\n"}
            expected, mathlib = downstream.compute_source_closure(formalization, clients)
            self.assertEqual(expected, ["FunctionalInequalities.Leaf", "FunctionalInequalities.Mid"])
            self.assertEqual(mathlib, ["Mathlib.Data.Nat.Basic", "Mathlib.Order.Basic"])
            for bad in (b"import FunctionalInequalities.KLS.Target\n", b"import FunctionalInequalities.Missing\n",
                        b"import Mathlib.Data.Nat.Basic\n", b"import solutions.Thm\n", b"\xff\xfe"):
                with self.subTest(client=bad), self.assertRaises(downstream.DownstreamFailure):
                    downstream.compute_source_closure(formalization, {"MatrixIntegral": bad})
            (lib / "Mid.lean").write_text("import FunctionalInequalities.KLS.Target\n")
            with self.assertRaises(downstream.DownstreamFailure):
                downstream.compute_source_closure(formalization, clients)

    def test_coverage_rejects_omissions_and_unexpected(self):
        downstream.compare_coverage(["A", "B"], {"B", "A"})
        for expected, actual in ((["A", "B"], ["A"]), (["A"], ["A", "Unexpected"]), ([], ["X"])):
            with self.assertRaises(downstream.DownstreamFailure):
                downstream.compare_coverage(expected, actual)


class AuditTests(unittest.TestCase):
    GOOD = ('AXIOM_REPORT {"name":"P.a","axioms":["propext"]}\n'
            'AXIOM_REPORT {"name":"P.b","axioms":["Classical.choice","Quot.sound"]}\n'
            'Audited 2 local declarations.\n')

    def test_audit_accepts_exact_standard_inventory(self):
        reports = downstream.validate_axiom_reports(self.GOOD, {"P.a", "P.b"}, verify.parse_axioms)
        self.assertEqual(sorted(reports), ["P.a", "P.b"])

    def test_audit_fails_closed_with_real_parser(self):
        cases = {
            "empty": ("", {"P.a"}),
            "malformed": ('AXIOM_REPORT {"name":"P.a"}\nAudited 1 local declarations.\n', {"P.a"}),
            "not json": ('AXIOM_REPORT {oops\nAudited 1 local declarations.\n', {"P.a"}),
            "duplicate": (self.GOOD.replace('"P.b"', '"P.a"'), {"P.a"}),
            "nonstandard": (self.GOOD.replace('"propext"', '"sorryAx"'), {"P.a", "P.b"}),
            "missing": (self.GOOD, {"P.a", "P.b", "P.c"}),
            "extra": (self.GOOD, {"P.a"}),
            "truncated": (self.GOOD.replace("Audited 2", "Audited 3"), {"P.a", "P.b"}),
            "no footer": (self.GOOD.splitlines()[0] + "\n" + self.GOOD.splitlines()[1] + "\n", {"P.a", "P.b"}),
            "two footers": (self.GOOD + "Audited 2 local declarations.\n", {"P.a", "P.b"}),
            "unstructured": (self.GOOD + "'x' depends on axioms: [propext]\n", {"P.a", "P.b"}),
        }
        for label, (output, inventory) in cases.items():
            with self.subTest(case=label), self.assertRaises(downstream.DownstreamFailure) as raised:
                downstream.validate_axiom_reports(output, inventory, verify.parse_axioms)
            self.assertEqual(raised.exception.stage, "axiom-audit")

    def test_inventory_parsing(self):
        good = 'DECL_INVENTORY "P.a"\nDECL_INVENTORY "P.b"\nINVENTORY_COUNT 2\n'
        self.assertEqual(downstream.parse_inventory(good), {"P.a", "P.b"})
        for bad in ("", good.replace("COUNT 2", "COUNT 3"), good.replace('"P.b"', '"P.a"'),
                    good.replace('"P.b"', "P.b"), good.replace("INVENTORY_COUNT 2\n", ""),
                    good + "INVENTORY_COUNT 2\n", 'DECL_INVENTORY ""\nINVENTORY_COUNT 1\n'):
            with self.subTest(output=bad), self.assertRaises(downstream.DownstreamFailure):
                downstream.parse_inventory(bad)

    def test_inventory_program_mirrors_producer_ownership(self):
        modules = ["FunctionalInequalities.X", "MatrixIntegral"]
        inventory = downstream.declaration_inventory_code(modules)
        producer = verify.library_axiom_audit_code(modules)
        for fragment in ("env.getModuleIdxFor? name", "(`FunctionalInequalities).isPrefixOf name",
                         "(`solutions).isPrefixOf name", "(`examples).isPrefixOf name",
                         'import FunctionalInequalities.X', 'import MatrixIntegral', 'import Lean'):
            self.assertIn(fragment, inventory)
            self.assertIn(fragment, producer)


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        root = Path(self.directory.name)
        self.cache = root / "cache"
        self.package = self.cache / "mathlib"
        self.pin = make_package(self.package)
        self.manifest = [{"name": "mathlib", "type": "git", "rev": self.pin},
                         {"name": "«functional-inequalities»", "type": "git", "rev": "f" * 40}]
        self.target = root / "project" / ".lake" / "packages"
        self.env, _ = downstream.scrub_environment(CLEAN_ENV)
        self.env["PATH"] = os.environ.get("PATH", self.env["PATH"])

    def tearDown(self):
        self.directory.cleanup()

    def test_clean_pinned_cache_is_copied_and_origin_untouched(self):
        index_before = (self.package / ".git" / "index").read_bytes()
        records = downstream.validate_cache(self.cache, self.manifest, self.target, self.env)
        self.assertEqual([r["package"] for r in records], ["mathlib"])
        self.assertEqual(records[0]["revision"], self.pin)
        self.assertIn(records[0]["copy_mode"], {"copy-on-write", "shutil.copytree"})
        self.assertTrue((self.target / "mathlib" / "source.txt").is_file())
        self.assertEqual((self.package / ".git" / "index").read_bytes(), index_before)
        downstream.recheck_cache_pins(records, self.target, self.env)
        (self.target / "mathlib" / "source.txt").write_text("later\n")
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.recheck_cache_pins(records, self.target, self.env)

    def test_tracked_modification_mismatched_pin_and_missing_cache_fail(self):
        (self.package / "source.txt").write_text("tracked edit\n")
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.validate_cache(self.cache, self.manifest, self.target, self.env)
        (self.package / "source.txt").write_text("clean\n")
        downstream.validate_cache(self.cache, self.manifest, Path(self.directory.name) / "ok", self.env)
        wrong = [{"name": "mathlib", "type": "git", "rev": "0" * 40}]
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.validate_cache(self.cache, wrong, self.target, self.env)
        for bad in ([{"name": "aesop", "type": "git", "rev": self.pin}],
                    [{"name": "mathlib", "type": "path", "dir": "../x"}],
                    [{"name": "mathlib", "type": "git", "rev": "main"}],
                    [{"name": "../mathlib", "type": "git", "rev": self.pin}]):
            with self.subTest(manifest=bad), self.assertRaises(downstream.DownstreamFailure):
                downstream.validate_cache(self.cache, bad, Path(self.directory.name) / "bad", self.env)

    def test_cache_pointing_outside_itself_is_refused(self):
        git(self.package, "config", "core.worktree", "/elsewhere")
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.validate_cache(self.cache, self.manifest, self.target, self.env)
        git(self.package, "config", "--unset", "core.worktree")
        real = self.package / ".git"
        real.rename(self.cache / "detached.git")
        (self.package / ".git").write_text(f"gitdir: {self.cache / 'detached.git'}\n")
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.validate_cache(self.cache, self.manifest, Path(self.directory.name) / "t2", self.env)
        (self.package / ".git").unlink()
        (self.cache / "detached.git").rename(real)
        for label, target in (("escape", self.cache), ("outside-file", Path(self.directory.name)),
                              ("absolute-outside", Path("/etc/hosts"))):
            link = self.package / "link"
            link.symlink_to(target)
            with self.subTest(link=label), self.assertRaises(downstream.DownstreamFailure) as raised:
                downstream.validate_cache(self.cache, self.manifest, Path(self.directory.name) / f"t-{label}", self.env)
            self.assertIn("escapes", str(raised.exception))
            link.unlink()
        (self.package / "broken").symlink_to(self.package / "nowhere")
        with self.assertRaises(downstream.DownstreamFailure) as raised:
            downstream.validate_cache(self.cache, self.manifest, Path(self.directory.name) / "t-broken", self.env)
        self.assertIn("broken", str(raised.exception))
        (self.package / "broken").unlink()
        (self.package / "loop").symlink_to("loop")
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.validate_cache(self.cache, self.manifest, Path(self.directory.name) / "t-loop", self.env)
        (self.package / "loop").unlink()
        (self.package / ".git" / "evil").symlink_to("../source.txt")
        with self.assertRaises(downstream.DownstreamFailure) as raised:
            downstream.validate_cache(self.cache, self.manifest, Path(self.directory.name) / "t-gitlink", self.env)
        self.assertIn("Git metadata", str(raised.exception))
        (self.package / ".git" / "evil").unlink()
        elsewhere = Path(self.directory.name) / "elsewhere-git"
        real.rename(elsewhere)
        (self.package / ".git").symlink_to(elsewhere)
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.validate_cache(self.cache, self.manifest, Path(self.directory.name) / "t-gitsym", self.env)
        (self.package / ".git").unlink()
        elsewhere.rename(real)

    def test_tracked_internal_symlinks_are_accepted_and_preserved(self):
        (self.package / "docs").mkdir()
        (self.package / "README.md").write_text("readme\n")
        (self.package / "docs" / "README.md").symlink_to("../README.md")
        (self.package / "scripts").mkdir()
        (self.package / "scripts" / "run").write_text("#!/bin/sh\n")
        (self.package / "scripts" / "run.py").symlink_to("run")
        (self.package / "alias").symlink_to("docs")
        git(self.package, "add", ".")
        git(self.package, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "links")
        pin = git(self.package, "rev-parse", "HEAD")
        manifest = [{"name": "mathlib", "type": "git", "rev": pin}]
        index_before = (self.package / ".git" / "index").read_bytes()
        records = downstream.validate_cache(self.cache, manifest, self.target, self.env)
        self.assertEqual(records[0]["internal_symlinks_preserved"], 3)
        copied = self.target / "mathlib"
        for link, target in (("docs/README.md", "../README.md"), ("scripts/run.py", "run"), ("alias", "docs")):
            self.assertTrue((copied / link).is_symlink(), link)
            self.assertEqual(os.readlink(copied / link), target)
        self.assertEqual((copied / "docs" / "README.md").read_text(), "readme\n")
        self.assertEqual((self.package / ".git" / "index").read_bytes(), index_before)
        self.assertEqual(git(copied, "status", "--porcelain", "--untracked-files=no"), "")
        self.assertEqual(git(copied, "rev-parse", "HEAD"), pin)
        downstream.recheck_cache_pins(records, self.target, self.env)
        # The shutil fallback must preserve links too.
        fallback = Path(self.directory.name) / "fallback"
        with mock.patch.object(downstream.sys, "platform", "unknown-os"):
            self.assertEqual(downstream.copy_tree(self.package, fallback, self.env), "shutil.copytree")
        self.assertTrue((fallback / "docs" / "README.md").is_symlink())
        self.assertEqual(os.readlink(fallback / "alias"), "docs")
        self.assertEqual(downstream.check_cache_symlinks(fallback, "mathlib"), 3)


class RunTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = Path(self.directory.name)
        self.prefix = self.root / "toolchains" / "leanprover--lean4---v4.33.0"
        (self.prefix / "lib" / "lean").mkdir(parents=True)
        self.env, self.report = downstream.scrub_environment(CLEAN_ENV)
        self.env["PATH"] = os.environ.get("PATH", self.env["PATH"])

    def tearDown(self):
        self.directory.cleanup()

    def run_fixture(self, repository: Path, revision: str, spawn, cache: Path | None = None) -> tuple[int, dict, Path]:
        output = self.root / "runs" / repository.name
        settings = downstream.RunSettings(revision, str(repository), cache, 2)
        receipt = downstream.start_run(settings, output, self.report, verify)
        initial = json.loads((output / "receipt.json").read_text())
        self.assertEqual((initial["status"], initial["failed_stage"]), ("FAILED", "incomplete"))
        self.assertTrue((output / "run-config.json").is_file() and (output / "runner-hashes.json").is_file())
        code = downstream.execute(settings, output, self.env, receipt, spawn)
        final = json.loads((output / "receipt.json").read_text())
        self.assertEqual(code, 0 if final["status"] == "PASSED" else 1)
        return code, final, output

    def test_full_run_passes_with_dynamic_coverage(self):
        repository = self.root / "good"
        revision = make_repository(repository)
        code, receipt, output = self.run_fixture(repository, revision, FakeLean(self.prefix))
        self.assertEqual(code, 0, receipt["error"])
        self.assertEqual(receipt["resolved_commit"], revision)
        self.assertEqual(receipt["expected_primary_modules"], ["FunctionalInequalities.Analysis.Probe"])
        self.assertEqual(receipt["built_primary_modules"], receipt["expected_primary_modules"])
        self.assertEqual(receipt["replayed_modules"], sorted(["FunctionalInequalities.Analysis.Probe", *downstream.CLIENTS]))
        self.assertEqual((receipt["declaration_inventory_count"], receipt["declaration_report_count"]), (1, 1))
        self.assertEqual((receipt["audit_status"], receipt["nonstandard_axioms"]), ("completed-standard-only", []))
        self.assertEqual(receipt["third_party_packages"], {})
        self.assertEqual(receipt["resolved_manifest_hash"], downstream.sha256_file(output / "project" / "lake-manifest.json"))
        self.assertEqual(receipt["tool_hashes"], json.loads((output / "runner-hashes.json").read_text()))
        self.assertEqual(receipt["tool_hashes"]["verify_path"], str(Path(verify.__file__).resolve()))
        lib = "project/.lake/packages/functional-inequalities/formalization/.lake/build/lib/lean/FunctionalInequalities/Analysis/"
        for companion in ("Probe.olean", "Probe.olean.private", "Probe.ilean"):
            self.assertIn(lib + companion, receipt["evidence_hashes"])
        self.assertEqual(receipt["toolchain"]["version"], "4.33.0")
        self.assertTrue(receipt["search_paths_isolated"])
        self.assertEqual(receipt["cache_mode"], "cold")
        self.assertEqual(receipt["effective_repository_url"], str(repository))
        self.assertEqual(set(receipt["client_hashes"]), set(downstream.CLIENTS))
        names = [s["name"] for s in receipt["steps"]]
        self.assertEqual(names[:4], ["git-init", "git-remote", "git-fetch", "git-checkout"])
        self.assertTrue(all(s["status"] == "PASSED" for s in receipt["steps"]))
        for evidence in ("axiom-audit.lean", "declaration-inventory.lean", "lake-build.log", "steps.json",
                         "project/lakefile.toml", "project/lean-toolchain", "project/MatrixIntegral.lean",
                         "project/.lake/packages/functional-inequalities/formalization/.lake/build/lib/lean/FunctionalInequalities/Analysis/Probe.olean"):
            self.assertIn(evidence, receipt["evidence_hashes"])
        self.assertNotIn("receipt.json", receipt["evidence_hashes"])
        self.assertLess(len(receipt["evidence_hashes"]), 60)
        self.assertEqual(receipt["source_hashes"],
                         {"formalization/FunctionalInequalities/Analysis/Probe.lean": downstream.sha256_bytes(PRIMARY.encode())})
        self.assertEqual(git(output / "project" / ".lake" / "packages" / "functional-inequalities", "status", "--porcelain", "--untracked-files=no"), "")

    def test_missing_examples_and_unavailable_revision_fail_with_receipts(self):
        repository = self.root / "noexamples"
        revision = make_repository(repository, with_examples=False)
        code, receipt, _ = self.run_fixture(repository, revision, FakeLean(self.prefix))
        self.assertEqual((code, receipt["status"], receipt["failed_stage"]), (1, "FAILED", "git-checkout"))
        self.assertIn("examples/MatrixIntegral.lean", receipt["error"])
        other = self.root / "unavailable"
        make_repository(other)
        code, receipt, output = self.run_fixture(other, "0123456789abcdef" * 2 + "01234567", FakeLean(self.prefix))
        self.assertEqual((code, receipt["failed_stage"]), (1, "git-fetch"))
        self.assertEqual([s["status"] for s in receipt["steps"]][-1], "FAILED")
        self.assertTrue((output / "git-fetch.log").is_file())
        self.assertIn("git-fetch.log", receipt["evidence_hashes"])

    def test_forbidden_import_and_bad_toolchain_fail_before_build(self):
        repository = self.root / "forbidden"
        revision = make_repository(repository, clients_import="FunctionalInequalities.KLS.Probe")
        (repository / "formalization" / "FunctionalInequalities" / "KLS").mkdir()
        (repository / "formalization" / "FunctionalInequalities" / "KLS" / "Probe.lean").write_text(PRIMARY)
        git(repository, "add", "."); git(repository, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "kls")
        revision = git(repository, "rev-parse", "HEAD")
        code, receipt, _ = self.run_fixture(repository, revision, FakeLean(self.prefix))
        self.assertEqual(code, 1)
        self.assertIn("forbidden downstream import", receipt["error"])
        self.assertNotIn("lake-build", [s["name"] for s in receipt["steps"]])
        nightly = self.root / "nightly"
        revision = make_repository(nightly, toolchain="leanprover/lean4:nightly-2026-01-01\n")
        code, receipt, _ = self.run_fixture(nightly, revision, FakeLean(self.prefix))
        self.assertEqual((code, receipt["failed_stage"]), (1, "toolchain"))

    def test_build_without_artifacts_or_wrong_manifest_cannot_pass(self):
        repository = self.root / "noartifacts"
        revision = make_repository(repository)
        code, receipt, output = self.run_fixture(repository, revision, FakeLean(self.prefix, build_oleans=False))
        self.assertEqual((code, receipt["status"]), (1, "FAILED"))
        self.assertIn("fresh primary build", receipt["error"])
        self.assertIn("lake-build.log", receipt["evidence_hashes"])
        redirected = self.root / "redirected"
        revision = make_repository(redirected)
        code, receipt, _ = self.run_fixture(redirected, revision, FakeLean(self.prefix, manifest_url="https://elsewhere.invalid/x.git"))
        self.assertEqual((code, receipt["failed_stage"]), (1, "lake-update"))

    def test_axiom_and_replay_failures_recorded(self):
        class BadAxioms(FakeLean):
            def __call__(self, args, **kw):
                result = super().__call__(args, **kw)
                if args[-1].endswith("axiom-audit.lean"):
                    return subprocess.CompletedProcess(args, 1, result.stdout.replace('"axioms":[]', '"axioms":["sorryAx"]')
                                                       + "error: DownstreamFixture.value: unexpected axioms [sorryAx]\n", "")
                return result

        class ShortReplay(FakeLean):
            def __call__(self, args, **kw):
                result = super().__call__(args, **kw)
                if args[2:3] == ["leanchecker"]:
                    return subprocess.CompletedProcess(args, 0, "replaying MatrixIntegral\n", "")
                return result

        repository = self.root / "badaxioms"
        revision = make_repository(repository)
        code, receipt, _ = self.run_fixture(repository, revision, BadAxioms(self.prefix))
        self.assertEqual((code, receipt["failed_stage"]), (1, "axiom-audit"))
        self.assertEqual(receipt["steps"][-1]["exit_code"], 1)
        self.assertEqual((receipt["audit_status"], receipt["nonstandard_axioms"]), ("failed", ["sorryAx"]))
        self.assertEqual(receipt["declaration_report_count"], 0)
        other = self.root / "shortreplay"
        revision = make_repository(other)
        code, receipt, _ = self.run_fixture(other, revision, ShortReplay(self.prefix))
        self.assertEqual(code, 1)
        self.assertIn("kernel replay mismatch", receipt["error"])

    def test_primary_or_example_symlink_escape_is_refused(self):
        outside = self.root / "outside"
        outside.mkdir()
        (outside / "Probe.lean").write_text(PRIMARY)
        repository = self.root / "symlinked"
        revision = make_repository(repository, symlink_primary_to=outside / "Probe.lean")
        code, receipt, output = self.run_fixture(repository, revision, FakeLean(self.prefix))
        self.assertEqual(code, 1)
        self.assertIn("symlink", receipt["error"])
        self.assertNotIn("lake-build", [s["name"] for s in receipt["steps"]])
        other = self.root / "symlinked-example"
        make_repository(other)
        (other / "examples" / "MatrixIntegral.lean").unlink()
        (other / "examples" / "MatrixIntegral.lean").symlink_to(outside / "Probe.lean")
        git(other, "add", "."); git(other, "-c", "user.name=t", "-c", "user.email=t@example.invalid", "commit", "-qm", "link")
        code, receipt, _ = self.run_fixture(other, git(other, "rev-parse", "HEAD"), FakeLean(self.prefix))
        self.assertEqual((code, receipt["failed_stage"]), (1, "git-checkout"))
        self.assertIn("symlink", receipt["error"])

    def test_third_party_pins_checked_in_both_modes(self):
        cache = self.root / "cache"
        pin = make_package(cache / "mathlib")
        entry = {"name": "mathlib", "type": "git", "url": "https://example.invalid/mathlib4.git", "rev": pin, "subDir": None}
        repository = self.root / "withdep"
        revision = make_repository(repository, packages=[entry])
        code, receipt, _ = self.run_fixture(repository, revision, FakeLean(self.prefix))
        self.assertEqual((code, receipt["failed_stage"]), (1, "lake-update"))
        self.assertIn("not materialised", receipt["error"])
        self.assertEqual(receipt["cache_mode"], "cold")
        cached = self.root / "withdep-cached"
        revision = make_repository(cached, packages=[entry])
        code, receipt, output = self.run_fixture(cached, revision, FakeLean(self.prefix), cache=cache)
        self.assertEqual(code, 0, receipt["error"])
        self.assertEqual(receipt["third_party_packages"], {"mathlib": {"revision": pin, "url": entry["url"], "subDir": None}})
        self.assertEqual(receipt["cache_provenance"][0]["revision"], pin)
        self.assertEqual(receipt["cache_mode"], "explicit-cache")
        self.assertNotIn("project/.lake/packages/mathlib/source.txt", receipt["evidence_hashes"])

    def test_dependency_manifest_comparison(self):
        rev, repo = "a" * 40, "https://example.invalid/kls.git"
        primary = {"name": "«functional-inequalities»", "type": "git", "url": repo, "rev": rev, "subDir": "formalization"}
        dep = {"name": "mathlib", "type": "git", "url": "https://example.invalid/m.git", "rev": "b" * 40, "subDir": None}
        pins = downstream.compare_dependency_manifests([dep], [primary, dep], repo, rev)
        self.assertEqual(pins, {"mathlib": {"revision": "b" * 40, "url": dep["url"], "subDir": None}})
        self.assertEqual(downstream.compare_dependency_manifests([], [primary], repo, rev), {})
        for target, fixture in (([dep], [primary]), ([], [primary, dep]), ([dep], [primary, {**dep, "rev": "c" * 40}]),
                                ([dep], [primary, {**dep, "url": "https://evil.invalid/m.git"}]),
                                ([dep], [primary, {**dep, "subDir": "sub"}]), ([dep], [primary, dep, dep]),
                                ([dep], [dep]), ([dep], [{**primary, "rev": "d" * 40}, dep]),
                                ([dep], [{**primary, "url": "https://evil.invalid/kls.git"}, dep]),
                                ([{**dep, "rev": "main"}], [primary, {**dep, "rev": "main"}]),
                                ([{**dep, "type": "path"}], [primary, dep])):
            with self.subTest(target=target, fixture=fixture), self.assertRaises(downstream.DownstreamFailure):
                downstream.compare_dependency_manifests(target, fixture, repo, rev)
        packages = self.root / "pkgs"
        pin = make_package(packages / "mathlib")
        good = {"mathlib": {"revision": pin, "url": None, "subDir": None}}
        downstream.check_dependency_checkouts(good, packages, self.env, "t")
        (packages / "mathlib" / "source.txt").write_text("edited\n")
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.check_dependency_checkouts(good, packages, self.env, "t")
        for bad in ({"mathlib": {"revision": "0" * 40}}, {"aesop": {"revision": pin}}):
            with self.assertRaises(downstream.DownstreamFailure):
                downstream.check_dependency_checkouts(bad, packages, self.env, "t")

    def test_failed_audit_summary_and_companions(self):
        text = 'AXIOM_REPORT {"name":"P.a","axioms":["propext","sorryAx"]}\nerror: P.a: unexpected axioms\n'
        self.assertEqual(downstream.summarise_failed_audit(text, verify), ["sorryAx"])
        self.assertIsNone(downstream.summarise_failed_audit("lean: crashed\n", verify))
        olean = self.root / "M.olean"
        for name in ("M.olean", "M.olean.server", "M.ilean", "M.trace"):
            (self.root / name).write_bytes(b"x")
        self.assertEqual(sorted(p.name for p in downstream.companion_artifacts(olean)), ["M.ilean", "M.olean", "M.olean.server"])

    def test_step_runner_records_failures_and_refuses_log_overwrite(self):
        output = self.root / "steps"
        output.mkdir()
        runner = downstream.StepRunner(output, self.env, "repo")
        with self.assertRaises(downstream.StepFailure) as raised:
            runner.run("failing", [sys.executable, "-c", "print('boom'); raise SystemExit(7)"], output)
        self.assertEqual(raised.exception.code, 7)
        record = json.loads((output / "steps.json").read_text())[0]
        self.assertEqual((record["status"], record["exit_code"]), ("FAILED", 7))
        self.assertIn("boom", (output / "failing.log").read_text())
        with self.assertRaises(downstream.DownstreamFailure):
            runner.run("failing", [sys.executable, "-c", "pass"], output)

    def test_client_bytes_recheck(self):
        project = self.root / "clients"
        project.mkdir()
        data = {name: f"import X.{name}\n".encode() for name in downstream.CLIENTS}
        for name, content in data.items():
            (project / f"{name}.lean").write_bytes(content)
        downstream.verify_clients_unchanged(project, data)
        (project / "MatrixIntegral.lean").write_bytes(b"changed\n")
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.verify_clients_unchanged(project, data)
        (project / "MatrixIntegral.lean").unlink()
        with self.assertRaises(downstream.DownstreamFailure):
            downstream.verify_clients_unchanged(project, data)

    def test_search_path_probe_parsing(self):
        good = 'noise\nSEARCH_PATHS {"LEAN_PATH": "/a:/b", "LEAN_SRC_PATH": null}\n'
        self.assertEqual(downstream.parse_search_paths(good), {"LEAN_PATH": ["/a", "/b"], "LEAN_SRC_PATH": []})
        for bad in ("", "SEARCH_PATHS {}\n", 'SEARCH_PATHS {"LEAN_PATH": ""}\n', "SEARCH_PATHS nope\n", good + good):
            with self.subTest(output=bad), self.assertRaises(downstream.DownstreamFailure):
                downstream.parse_search_paths(bad)
        probe = subprocess.run([sys.executable, "-I", "-c", downstream.SEARCH_PATH_PROBE], text=True, capture_output=True,
                               env={**CLEAN_ENV, "LEAN_PATH": "/x"}, check=True).stdout
        self.assertEqual(downstream.parse_search_paths(probe)["LEAN_PATH"], ["/x"])

    def test_lakefile_quotes_awkward_paths(self):
        text = downstream.fixture_lakefile('/tmp/odd "quote" \\ path', "a" * 40)
        self.assertIn('git = "/tmp/odd \\"quote\\" \\\\ path"', text)
        self.assertIn('subDir = "formalization"', text)
        self.assertTrue(downstream.path_is_allowed("./.lake/x", self.root, self.prefix))
        self.assertTrue(downstream.path_is_allowed(str(self.prefix / "lib"), self.root / "p", self.prefix))
        self.assertFalse(downstream.path_is_allowed("/usr/lib/lean", self.root / "p", self.prefix))


if __name__ == "__main__":
    unittest.main()
