"""Exercise the generated axiom audit against Lean, including its failure boundary."""
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import axiom_audit_code, parse_axioms

ROOT = Path(__file__).resolve().parents[2]


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
