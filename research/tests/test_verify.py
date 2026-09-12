"""Exercise the generated axiom audit against Lean, including its failure boundary."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import axiom_audit_code, build_replay_inputs, parse_axioms, prepare_replay

ROOT = Path(__file__).resolve().parents[2]


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
