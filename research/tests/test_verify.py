"""Exercise the generated axiom audit against Lean, including its failure boundary."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import (axiom_audit_code, build_replay_inputs, check_research_audits,
                    parse_axioms, prepare_replay, undiscovered_lean_sources)

ROOT = Path(__file__).resolve().parents[2]


class ResearchAuditTests(unittest.TestCase):
    def check_sources(self, sources):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "formalization").mkdir()
            (root / "formalization/lean-toolchain").write_text(
                (ROOT / "formalization/lean-toolchain").read_text())
            (root / "formalization/lakefile.toml").write_text('name = "audit-fixture"\n')
            snapshot = {"files": {"research/audits/Deleted.lean": None,
                                  "research/scratch/Excluded.lean": "outside"}}
            for name, code in sources.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(code)
                snapshot["files"][name] = "live"

            def run(name, command, *, cwd, lean_path=None):
                env = {**os.environ, "LEAN_NUM_THREADS": "2"}
                env.pop("LEAN_PATH", None)
                if lean_path is not None:
                    env["LEAN_PATH"] = lean_path
                result = subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                                        timeout=60, env=env)
                if result.returncode:
                    raise RuntimeError(result.stdout + result.stderr)
                return result.stdout

            prefix = subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                             cwd=ROOT / "formalization", text=True).strip()
            return check_research_audits(root, snapshot, run,
                                        lean=str(Path(prefix) / "bin/lean"),
                                        lean_path=str(root / "empty-view"))

    def test_live_and_nested_clients_are_checked_independently(self):
        sources = {"research/audits/A.lean": "theorem duplicate : True := trivial\n",
                   "research/audits/nested/A.lean": "theorem duplicate : True := trivial\n"}
        self.assertEqual(self.check_sources(sources), sorted(sources))

    def test_unsolved_goal_rejects_verification(self):
        with self.assertRaisesRegex(RuntimeError, "unsolved goals"):
            self.check_sources({"research/audits/Broken.lean": "example : False := by skip\n"})

    def test_sorry_warning_rejects_verification(self):
        with self.assertRaisesRegex(RuntimeError, "sorry"):
            self.check_sources({"research/audits/Hole.lean": "example : True := by sorry\n"})

    def test_nonstandard_reported_axiom_rejects_verification(self):
        with self.assertRaisesRegex(RuntimeError, "unexpected axioms"):
            self.check_sources({"research/audits/Axiom.lean":
                                "axiom bad : False\n#print axioms bad\n"})


class CheckedViewTests(unittest.TestCase):
    def test_stale_and_orphan_modules_cannot_satisfy_audits(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            formalization = root / "formalization"
            library = formalization / "FunctionalInequalities"
            library.mkdir(parents=True)
            (formalization / "lean-toolchain").write_text(
                (ROOT / "formalization/lean-toolchain").read_text())
            (formalization / "lakefile.toml").write_text(
                'name = "checked-view-fixture"\n'
                'defaultTargets = ["FunctionalInequalities"]\n'
                '[[lean_lib]]\nname = "FunctionalInequalities"\n')
            (formalization / "FunctionalInequalities.lean").write_text('def base := 0\n')
            for name in ["Outside", "Deleted"]:
                (library / f"{name}.lean").write_text(f'def {name.lower()} := 1\n')
            audits = root / "research/audits"
            audits.mkdir(parents=True)
            live_audit = audits / "Live.lean"
            live_audit.write_text('import FunctionalInequalities.Outside\n#check outside\n')
            snapshot = {"files": {
                "formalization/FunctionalInequalities.lean": "live",
                "formalization/FunctionalInequalities/Outside.lean": "live",
                "formalization/FunctionalInequalities/Deleted.lean": "live",
                "research/audits/Live.lean": "live"}}

            def run(name, command, *, cwd, lean_path=None):
                env = {**os.environ, "LEAN_NUM_THREADS": "2"}
                env.pop("LEAN_PATH", None)
                if lean_path is not None:
                    env["LEAN_PATH"] = lean_path
                result = subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                                        timeout=60, env=env)
                if result.returncode:
                    raise RuntimeError(result.stdout + result.stderr)
                return result.stdout

            run("default", ["lake", "build"], cwd=formalization)
            view = root / "initial-view"
            build_replay_inputs(root, snapshot, view, run)
            prefix = run("prefix", ["lake", "env", "lean", "--print-prefix"],
                         cwd=formalization).strip()
            lean = str(Path(prefix) / "bin/lean")
            self.assertEqual(check_research_audits(root, snapshot, run,
                             lean=lean, lean_path=str(view)), ["research/audits/Live.lean"])

            # A stale .olean exists, but rebuilding the full scope must reject broken source.
            (library / "Outside.lean").write_text('theorem outside : False := by skip\n')
            run("stale-control", ["lake", "env", "lean", str(live_audit)], cwd=formalization)
            with self.assertRaisesRegex(RuntimeError, "unsolved goals"):
                build_replay_inputs(root, snapshot, root / "broken-view", run)

            (library / "Outside.lean").write_text('def outside := 2\n')
            (library / "Deleted.lean").unlink()
            snapshot["files"]["formalization/FunctionalInequalities/Deleted.lean"] = None
            live_audit.write_text('import FunctionalInequalities.Deleted\n#check deleted\n')
            run("orphan-control", ["lake", "env", "lean", str(live_audit)], cwd=formalization)
            fresh = root / "fresh-view"
            build_replay_inputs(root, snapshot, fresh, run)
            self.assertFalse((fresh / "FunctionalInequalities/Deleted.olean").exists())
            with self.assertRaises(RuntimeError):
                check_research_audits(root, snapshot, run, lean=lean, lean_path=str(fresh))
            with self.assertRaisesRegex(RuntimeError, "must be empty"):
                prepare_replay(root, snapshot, view)


class SourceDiscoveryTests(unittest.TestCase):
    def test_packaging_patterns_do_not_hide_lean_families(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "config", "core.ignorecase", "true"], cwd=root, check=True)
            (root / ".gitignore").write_text((ROOT / ".gitignore").read_text())
            (root / ".git/info/exclude").write_text("/output/\n")
            paths = [f"{base}/{name}/Basic.lean"
                     for base in ["formalization/FunctionalInequalities/KLS", "research/audits", "solutions"]
                     for name in ["Target", "Lib", "Var", "Parts", "Build", "Manifest", "Output"]]
            result = subprocess.run(["git", "check-ignore", "--stdin", "--no-index"],
                                    cwd=root, input="\n".join(paths)+"\n", text=True,
                                    capture_output=True)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            artifacts = subprocess.run(["git", "check-ignore", "--stdin", "--no-index"],
                                       cwd=root, input="MANIFEST\noutput/generated.txt\n",
                                       text=True, capture_output=True)
            self.assertEqual(artifacts.returncode, 0, artifacts.stderr)
            self.assertEqual(set(artifacts.stdout.splitlines()),
                             {"MANIFEST", "output/generated.txt"})
            hidden = root / paths[0]
            hidden.parent.mkdir(parents=True)
            hidden.write_text('example : True := trivial\n')
            (root / ".gitignore").write_text('Target/\n')
            listed = subprocess.check_output(
                ["git", "ls-files", "--others", "--exclude-standard"], cwd=root, text=True)
            snapshot = {"files": {p: "live" for p in listed.splitlines()}}
            self.assertEqual(undiscovered_lean_sources(root, snapshot), [paths[0]])


class ReplayBuildTests(unittest.TestCase):
    def test_clean_default_build_leaves_wip_unbuilt_but_replay_build_covers_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            formalization = root / "formalization"
            wip = formalization / "FunctionalInequalities/WIP"
            wip.mkdir(parents=True)
            (formalization / "lean-toolchain").write_text(
                (ROOT / "formalization/lean-toolchain").read_text())
            (formalization / "lakefile.toml").write_text(
                'name = "replay-fixture"\n'
                'defaultTargets = ["FunctionalInequalities"]\n'
                '[[lean_lib]]\nname = "FunctionalInequalities"\n')
            (formalization / "FunctionalInequalities.lean").write_text(
                'theorem certified : True := trivial\n')
            (wip / "Retained.lean").write_text('theorem unfinished : True := by sorry\n')
            snapshot = {"files": {
                "formalization/FunctionalInequalities.lean": "root",
                "formalization/FunctionalInequalities/WIP/Retained.lean": "wip",
                "formalization/FunctionalInequalities/WIP/Deleted.lean": None,
                "formalization/Dev/Search.lean": "scratch",
            }}

            def run(name, command, *, cwd):
                result = subprocess.run(command, cwd=cwd, text=True, capture_output=True,
                                        timeout=60, env={**os.environ, "LEAN_PATH": ""})
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                return result.stdout

            run("default", ["lake", "build"], cwd=formalization)
            with self.assertRaisesRegex(RuntimeError, "Retained.lean has no built module"):
                prepare_replay(root, snapshot, root / "default-view")
            result = build_replay_inputs(root, snapshot, root / "replay-view", run)
            self.assertEqual(set(result["modules"]), {
                "FunctionalInequalities", "FunctionalInequalities.WIP.Retained"})
            self.assertTrue((root / "replay-view/FunctionalInequalities/WIP/Retained.olean").is_file())
            audit = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=formalization,
                                   input="import FunctionalInequalities\n#print axioms certified\n",
                                   text=True, capture_output=True, timeout=60,
                                   env={**os.environ, "LEAN_PATH": ""})
            self.assertEqual(audit.returncode, 0, audit.stdout + audit.stderr)
            self.assertNotIn("sorryAx", audit.stdout)


class AxiomAuditTests(unittest.TestCase):
    def run_audit(self, source, names):
        env = {**os.environ, "LEAN_NUM_THREADS": "2"}
        env.pop("LEAN_PATH", None)
        return subprocess.run(
            ["lake", "env", "lean", "--stdin"], cwd=ROOT / "formalization",
            input="import Lean\n" + source + "\n" + axiom_audit_code(names),
            text=True, capture_output=True, env=env, timeout=60,
        )

    def test_generated_proof_is_audited_without_identifier_warning(self):
        names = {"AuditFixture", "AuditFixture._proof_1"}
        result = self.run_audit(
            "def AuditFixture : {x : Nat // x = 0} := ⟨0, by rfl⟩", names)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("warning:", result.stdout + result.stderr)
        reports, errors = parse_axioms(result.stdout, names)
        self.assertEqual(errors, [])
        self.assertEqual(reports, {name: [] for name in names})

    def test_transitive_nonstandard_axiom_is_rejected(self):
        names = {"auditDependency"}
        result = self.run_audit(
            "axiom auditForbidden : False\n"
            "theorem auditDependency : False := auditForbidden", names)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        reports, errors = parse_axioms(result.stdout, names)
        self.assertEqual(reports["auditDependency"], ["auditForbidden"])
        self.assertTrue(any("unexpected axioms" in error for error in errors))

    def test_missing_declaration_fails_before_collection(self):
        names = {"AuditMissing"}
        result = self.run_audit("", names)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Axiom audit declaration not found: AuditMissing", result.stdout)
        reports, errors = parse_axioms(result.stdout, names)
        self.assertEqual(reports, {})
        self.assertIn("missing axiom report: AuditMissing", errors)


if __name__ == "__main__":
    unittest.main()
