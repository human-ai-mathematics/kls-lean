"""Real-tool acceptance and rejection probes; explicitly opt in with tool path.

These probes use only Lean's prelude and the pinned Comparator. They exercise
the actual statement/axiom boundary rather than mocking a successful process.
"""
import datetime as dt
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research"))
import comparator

TOOLS = os.environ.get("KLS_COMPARATOR_TOOLS")


class ComparatorConfigurationTests(unittest.TestCase):
    def config(self, target="kls"):
        config = json.loads((ROOT / "research/audits/KLS/Comparator/config.json").read_text())
        if target == "openai":
            config["theorem_names"] = ["KLSOpenAI.kls", "KLSOpenAI.of_conjecture"]
        return config

    def test_complete_target_lists_are_accepted(self):
        for target in ["kls", "openai"]:
            comparator.validate_config(self.config(target), target)

    def test_empty_or_partial_target_list_is_rejected(self):
        for target, names in [("kls", []), ("openai", ["KLSOpenAI.kls"])]:
            config = self.config(target)
            config["theorem_names"] = names
            with self.assertRaisesRegex(RuntimeError, "exactly these declarations"):
                comparator.validate_config(config, target)

    def test_different_module_or_theorem_is_rejected(self):
        for key, value in [("challenge_module", "Other"), ("solution_module", "Other"),
                           ("theorem_names", ["Other.theorem"])]:
            config = self.config()
            config[key] = value
            with self.assertRaises(RuntimeError):
                comparator.validate_config(config, "kls")

    def test_extra_axiom_or_definition_hole_is_rejected(self):
        for key, value in [("permitted_axioms", ["propext", "Classical.choice", "Quot.sound", "sorryAx"]),
                           ("definition_names", ["answer"])]:
            config = self.config()
            config[key] = value
            with self.assertRaisesRegex(RuntimeError, "standard axioms"):
                comparator.validate_config(config, "kls")

    def test_unreported_external_kernel_mode_is_rejected(self):
        config = self.config()
        config["enable_nanoda"] = True
        with self.assertRaisesRegex(RuntimeError, "separate setup"):
            comparator.validate_config(config, "kls")

    def test_missing_or_duplicate_axiom_report_is_rejected(self):
        one = "'KLSOpenAI.kls' depends on axioms: [propext, Classical.choice, Quot.sound]"
        for output in [one, one + "\n" + one]:
            with self.assertRaisesRegex(RuntimeError, "every configured declaration"):
                comparator.validate_axiom_reports(output, "openai")

    def test_nonstandard_axiom_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "unexpected solution axioms"):
            comparator.validate_axiom_reports(
                "'FunctionalInequalities.KLS.kls' depends on axioms: [sorryAx]", "kls")

    def test_sandbox_mode_executes_no_unsandboxed_solution_preflight(self):
        with patch.object(comparator, "run", side_effect=AssertionError("unsandboxed execution")):
            result = comparator.check_solution_client("sandbox", ROOT, {}, "kls")
        self.assertIsNone(result)

    def test_build_log_allows_dependency_reports_but_requires_unique_complete_targets(self):
        dependency = "'Dependency.lemma' depends on axioms: [propext]"
        first = "'KLSOpenAI.kls' depends on axioms: [propext, Classical.choice, Quot.sound]"
        second = "'KLSOpenAI.of_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]"
        reports = comparator.validate_axiom_reports(
            dependency + "\n" + first + "\n" + second, "openai", build_log=True)
        self.assertEqual(set(reports), {"KLSOpenAI.kls", "KLSOpenAI.of_conjecture"})
        for output in [dependency + "\n" + first, first + "\n" + second + "\n" + second]:
            with self.assertRaisesRegex(RuntimeError, "every configured declaration"):
                comparator.validate_axiom_reports(output, "openai", build_log=True)


@unittest.skipUnless(TOOLS, "set KLS_COMPARATOR_TOOLS to the built pinned checkout")
class ComparatorBoundaryTests(unittest.TestCase):
    def compare(self, solution):
        tools = Path(TOOLS).resolve()
        stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        out = ROOT / "build/comparator-tests" / (stamp + "-" + self._testMethodName)
        out.mkdir(parents=True)
        (out / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
        (out / "lakefile.toml").write_text(
            'name = "comparator-boundary"\n[[lean_lib]]\nname = "Challenge"\n'
            '[[lean_lib]]\nname = "Solution"\n')
        (out / "Challenge.lean").write_text("theorem boundary : True := by sorry\n")
        (out / "Solution.lean").write_text(solution + "\n")
        config = {"challenge_module": "Challenge", "solution_module": "Solution",
                  "theorem_names": ["boundary"], "enable_nanoda": False,
                  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}
        (out / "config.json").write_text(json.dumps(config))
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("LEAN", "LAKE", "ELAN_TOOLCHAIN", "COMPARATOR_"))}
        env.update(COMPARATOR_LANDRUN=str(tools / "scripts/fake-landrun.sh"),
                   COMPARATOR_LEAN4EXPORT=str(tools / ".lake/packages/lean4export/.lake/build/bin/lean4export"),
                   LEAN_NUM_THREADS="2")
        with (out / "comparator.log").open("w") as stream:
            process = subprocess.run(["lake", "env", str(tools / ".lake/build/bin/comparator"),
                                      "config.json"], cwd=out, env=env,
                                     stdout=stream, stderr=subprocess.STDOUT, timeout=180)
        return process.returncode, (out / "comparator.log").read_text()

    def test_correct_proof_is_accepted(self):
        code, log = self.compare("theorem boundary : True := True.intro")
        self.assertEqual(code, 0, log)
        self.assertIn("Your solution is okay!", log)

    def test_changed_statement_is_rejected(self):
        code, log = self.compare("theorem boundary : True ∧ True := ⟨True.intro, True.intro⟩")
        self.assertNotEqual(code, 0, log)
        self.assertIn("theorem statement do not match", log)

    def test_proof_hole_is_rejected(self):
        code, log = self.compare("theorem boundary : True := by sorry")
        self.assertNotEqual(code, 0, log)
        self.assertIn("Illegal axiom", log)
        self.assertIn("sorryAx", log)


if __name__ == "__main__":
    unittest.main()
