"""Regressions for the classical KLS specification gate (research/audits/KLS/Classical), without running Lean."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "research/audits/KLS/Classical"
sys.path.insert(0, str(ROOT / "research"))
spec = importlib.util.spec_from_file_location("classical_kls_check", HERE / "check.py")
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)
import verify  # noqa: E402
from verify import CLASSICAL_KLS_DIR, verification_snapshot  # noqa: E402

CONFIG = json.loads((HERE / "config.json").read_text())
SPECIFICATION = (HERE / "Specification.lean.in").read_text()
CLIENT = (HERE / "Client.lean.in").read_text()
SPEC_MODULE = CONFIG["templates"]["specification"]["module"]
REPORTS = CONFIG["expected_axiom_reports"]
STANDARD = "[propext, Classical.choice, Quot.sound]"


def clean_git_env():
    return {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}


class GuardTests(unittest.TestCase):
    def test_pinned_templates_pass_their_guards(self):
        self.assertTrue(all(name.startswith("Mathlib.") for name in check.specification_guard(SPECIFICATION)))
        self.assertIn(SPEC_MODULE, check.client_guard(CLIENT, SPEC_MODULE, REPORTS))

    def test_specification_rejects_project_imports_and_names(self):
        with self.assertRaises(ValueError):
            check.specification_guard("import FunctionalInequalities.KLS.Statement\n" + SPECIFICATION)
        with self.assertRaises(ValueError):
            check.specification_guard(SPECIFICATION + "\ndef X : Prop := FunctionalInequalities.KLS.Conjecture\n")

    def test_specification_rejects_escapes(self):
        for addition in ["theorem fake : False := by sorry", "axiom fake : False", "opaque fake : Nat",
                         "elab \"x\" : term => pure default", "#eval 1", "unsafe def f : Nat := 0"]:
            with self.subTest(addition=addition), self.assertRaises(ValueError):
                check.specification_guard(SPECIFICATION + "\n" + addition + "\n")

    def test_comments_and_strings_do_not_trigger_guards(self):
        quoted = SPECIFICATION + '\n/- an outer /- nested sorry -/ axiom -/\n-- sorry here\ndef s : String := "axiom sorry"\n'
        self.assertTrue(check.specification_guard(quoted))

    def test_unterminated_comment_fails_closed(self):
        with self.assertRaises(ValueError):
            check.specification_guard(SPECIFICATION + "\n/- open")

    def test_client_rejects_foreign_imports_escapes_and_missing_reports(self):
        with self.assertRaises(ValueError):
            check.client_guard("import BKLIndependentChecks\n" + CLIENT, SPEC_MODULE, REPORTS)
        with self.assertRaises(ValueError):
            check.client_guard(CLIENT.replace("import " + SPEC_MODULE + "\n", ""), SPEC_MODULE, REPORTS)
        with self.assertRaises(ValueError):
            check.client_guard(CLIENT + "\ntheorem fake : False := by sorry\n", SPEC_MODULE, REPORTS)
        with self.assertRaises(ValueError):
            check.client_guard(CLIENT.replace("#print axioms uniformConvexBodyKls\n", ""), SPEC_MODULE, REPORTS)


class PinTests(unittest.TestCase):
    def test_templates_match_reviewed_pins(self):
        pins = check.check_pins(CONFIG)
        self.assertEqual(check.sha(pins["specification"]), "f52663e2398d7eb45433dbad4edd808ae02a03fb8167467f937a9e12205a8d0f")
        self.assertEqual(check.sha(pins["client"]), "d7e762f9ddd616d37a98d5e80f8fea40b5972507b76989dad8b4a12055b8f864")

    def test_drifted_template_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            here = Path(directory)
            for template in CONFIG["templates"].values():
                (here / template["path"]).write_bytes((HERE / template["path"]).read_bytes())
            (here / "Specification.lean.in").write_text(SPECIFICATION + "\n")
            with self.assertRaises(ValueError):
                check.check_pins(CONFIG, here)


class MutationTests(unittest.TestCase):
    def test_three_mutations_apply_exactly_once(self):
        self.assertEqual([m["name"] for m in CONFIG["mutations"]],
                         ["drop-logconcavity", "drop-gradient-energy", "strict-inequality"])
        for mutation in CONFIG["mutations"]:
            with self.subTest(mutation=mutation["name"]):
                self.assertEqual(SPECIFICATION.count(mutation["old"]), 1)
                mutated = check.apply_mutation(SPECIFICATION, mutation)
                self.assertNotEqual(mutated, SPECIFICATION)
                self.assertTrue(check.specification_guard(mutated))

    def test_absent_or_repeated_anchor_is_rejected(self):
        mutation = CONFIG["mutations"][0]
        with self.assertRaises(ValueError):
            check.apply_mutation(SPECIFICATION.replace(mutation["old"], ""), mutation)
        with self.assertRaises(ValueError):
            check.apply_mutation(SPECIFICATION + mutation["old"], mutation)


class AxiomReportTests(unittest.TestCase):
    def output(self, names, axioms=STANDARD):
        return "".join(f"'{name}' depends on axioms: {axioms}\n" for name in names)

    def test_gate_uses_the_verifier_parser(self):
        self.assertIs(check.load_verify(ROOT), verify)

    def test_complete_standard_reports_pass_including_wrapped_lists(self):
        wrapped = self.output(REPORTS).replace("[propext, ", "[propext,\n ")
        for output in (self.output(REPORTS), wrapped):
            reports, errors = check.axiom_reports(output, REPORTS, verify)
            self.assertEqual(errors, [])
            self.assertEqual(sorted(reports), sorted(REPORTS))

    def test_missing_duplicate_unexpected_and_nonstandard_reports_fail(self):
        cases = {"missing": (self.output(REPORTS[:-1]), "missing axiom report"),
                 "duplicate": (self.output(REPORTS + REPORTS[:1]), "duplicate axiom report"),
                 "unexpected": (self.output(REPORTS + ["SecondIndependentReview.extra"]), "unexpected axiom report"),
                 "nonstandard": (self.output(REPORTS[:-1]) + self.output(REPORTS[-1:], "[propext, sorryAx]"), "unexpected axioms")}
        for case, (output, message) in cases.items():
            with self.subTest(case=case):
                errors = check.axiom_reports(output, REPORTS, verify)[1]
                self.assertTrue(any(message in error for error in errors), errors)


class RejectionTests(unittest.TestCase):
    CLIENT_FILE = "/tmp/run/mutation-x/OriginalAnalyticClient.lean"

    def error(self, message, file=None):
        return f"{file or self.CLIENT_FILE}:21:2: error: {message}\n"

    def test_each_configured_mutation_names_a_known_elaboration_error(self):
        for mutation in CONFIG["mutations"]:
            self.assertIn(mutation["expected_error"], check.ERROR_KINDS)

    def test_expected_client_elaboration_error_counts(self):
        cases = {"type-mismatch": "Type mismatch\n  h\nhas type", "application-type-mismatch": "Application type mismatch: x",
                 "unsolved-goals": "unsolved goals\nC : ℝ",
                 "change-not-defeq": "'change' tactic failed, pattern\n  a ≤ b\nis not definitionally equal to target\n  a < b"}
        for kind, message in cases.items():
            with self.subTest(kind=kind):
                self.assertTrue(check.rejected_by_client(self.error(message), 1, self.CLIENT_FILE, kind))

    def test_other_failures_do_not_count(self):
        cases = {
            "exit zero": (self.error("Type mismatch"), 0, "type-mismatch"),
            "wrong kind": (self.error("unsolved goals"), 1, "type-mismatch"),
            "error in specification": (self.error("Type mismatch", "/tmp/run/mutation-x/OriginalAnalyticSpecification.lean"), 1, "type-mismatch"),
            "warning as error": (self.error("Type mismatch") + self.error("unused variable `h`\nNote: This linter can be disabled with"), 1, "type-mismatch"),
            "import": (self.error("unknown module prefix 'OriginalAnalyticSpecification'"), 1, "type-mismatch"),
            "syntax": (self.error("Type mismatch") + self.error("unexpected token 'theorem'; expected term"), 1, "type-mismatch"),
            "unknown name": (self.error("Type mismatch") + self.error("Unknown identifier `kls`"), 1, "type-mismatch"),
            "heartbeats": (self.error("(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached"), 1, "type-mismatch"),
            "recursion": (self.error("maximum recursion depth has been reached"), 1, "type-mismatch"),
            "tool": ("lean: No such file or directory\n", 1, "type-mismatch"),
            "no error": ("", 1, "type-mismatch"),
            "change without the defeq failure": (self.error("'change' tactic failed, pattern\n  a ≤ b"), 1, "change-not-defeq"),
        }
        for case, (output, code, kind) in cases.items():
            with self.subTest(case=case):
                self.assertFalse(check.rejected_by_client(output, code, self.CLIENT_FILE, kind))


class LeanOnlySnapshotTests(unittest.TestCase):
    def test_every_classical_input_binds_the_lean_only_receipt(self):
        env = clean_git_env()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True, env=env)
            subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.org",
                            "commit", "--allow-empty", "-qm", "fixture"], cwd=root, check=True, env=env)
            gate = root / CLASSICAL_KLS_DIR
            gate.mkdir(parents=True)
            inputs = [p.name for p in HERE.iterdir() if p.is_file()]
            self.assertEqual(sorted(inputs), sorted(["README.md", "Specification.lean.in", "Client.lean.in", "config.json", "check.py"]))
            for name in inputs:
                (gate / name).write_text("draft\n")
            (root / "README.md").write_text("prose\n")
            saved = dict(os.environ)
            try:
                os.environ.clear(); os.environ.update(env)
                before = verification_snapshot(root, lean_only=True)["sha256"]
                (root / "README.md").write_text("updated prose\n")
                self.assertEqual(verification_snapshot(root, lean_only=True)["sha256"], before)
                for name in inputs:
                    with self.subTest(name=name):
                        (gate / name).write_text("changed " + name + "\n")
                        self.assertNotEqual(verification_snapshot(root, lean_only=True)["sha256"], before)
                        (gate / name).write_text("draft\n")
            finally:
                os.environ.clear(); os.environ.update(saved)


if __name__ == "__main__":
    unittest.main()
