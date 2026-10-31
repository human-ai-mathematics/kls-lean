"""Configuration, provenance and real-tool probes for research/comparator.py.

The real-tool probes (opt in with KLS_COMPARATOR_BUNDLED=1) use only Lean's prelude and the
toolchain-bundled `lake comparator`. They exercise the actual statement/axiom boundary rather
than mocking a successful process.
"""
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research"))
import comparator

BUNDLED = os.environ.get("KLS_COMPARATOR_BUNDLED")


class ComparatorConfigurationTests(unittest.TestCase):
    def config(self, target="kls"):
        config = json.loads((ROOT / "research/audits/KLS/Comparator/config.json").read_text())
        if target == "openai":
            config["theorem_names"] = ["KLSOpenAI.kls", "KLSOpenAI.of_conjecture"]
        if target == "palomar":
            config = {"challenge_module": "Challenge", "solution_module": "Solution",
                      "theorem_names": ["KLSOpenAI.kls"], "definition_names": [],
                      "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
                      "enable_nanoda": True}
        return config

    def test_complete_target_lists_are_accepted(self):
        for target in ["kls", "openai", "palomar"]:
            comparator.validate_config(self.config(target), target)

    def test_tracked_configurations_are_accepted(self):
        comparator.validate_config(json.loads(
            (ROOT / "research/audits/KLS/Comparator/config.json").read_text()), "kls")
        comparator.validate_config(json.loads(
            (ROOT / "integrations/openai/research/comparator/config.json").read_text()), "openai")
        comparator.validate_config(json.loads(
            (ROOT / "integrations/palomar/comparator.json").read_text()), "palomar")

    def test_palomar_requires_nanoda_exact_keys_and_one_target(self):
        for key, value in [("enable_nanoda", False), ("enable_nanoda", "true"),
                           ("external_kernels", {"nanoda": ["nanoda_bin"]}), ("extra", 1),
                           ("theorem_names", ["KLSOpenAI.kls", "KLSOpenAI.of_conjecture"]),
                           ("definition_names", ["OAI.LeanBlast.KLS.KLSStatement"]),
                           ("permitted_axioms", ["propext", "Quot.sound", "Classical.choice", "sorryAx"])]:
            with self.subTest(key=key, value=value):
                config = self.config("palomar")
                config[key] = value
                with self.assertRaises(RuntimeError):
                    comparator.validate_config(config, "palomar")
        config = self.config("palomar")
        del config["definition_names"]
        with self.assertRaises(RuntimeError):
            comparator.validate_config(config, "palomar")

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

    def test_comparator_log_requires_mode_and_kernel_messages(self):
        ok = "Your solution is okay!\nRunning Lean default kernel on solution\nLean default kernel accepts the solution\n"
        warning = comparator.SANDBOX_WARNING + "\n"
        comparator.validate_comparator_log(ok, "sandbox", nanoda=False)
        comparator.validate_comparator_log(warning + ok, "development", nanoda=False)
        comparator.validate_comparator_log(ok + "nanoda kernel accepts the solution\n", "sandbox", nanoda=True)
        for log, mode, nanoda in [(ok, "development", False), (warning + ok, "sandbox", False),
                                  (ok, "sandbox", True), ("Your solution is okay!\n", "sandbox", False),
                                  (ok.replace("Your solution is okay!\n", ""), "sandbox", False)]:
            with self.subTest(log=log, mode=mode, nanoda=nanoda), self.assertRaises(RuntimeError):
                comparator.validate_comparator_log(log, mode, nanoda=nanoda)

    def test_palomar_header_guards(self):
        challenge = "module\n\npublic import Mathlib\n\n@[expose] public section\n"
        solution = "module\n\npublic import OAI.Analysis.KLS.Model\npublic import KLSOpenAI.Target\n"
        self.assertEqual(comparator.header_guards(challenge, solution)["challenge_imports"],
                         ["public import Mathlib"])
        for bad_challenge, bad_solution in [
                ("public import Mathlib\n", solution), (challenge, "import KLSOpenAI.Target\n"),
                (challenge + "", "module\n\npublic import\n"),
                ("module\n\npublic import Mathlib\nimport FunctionalInequalities.KLS.Statement\n", solution),
                ("module\n\nimport all Mathlib.Order.Basic\n", solution),
                ("module\n\npublic meta import OAI.Analysis.KLS.Model\n", solution)]:
            with self.subTest(challenge=bad_challenge, solution=bad_solution), self.assertRaises(RuntimeError):
                comparator.header_guards(bad_challenge, bad_solution)

    def test_tracked_palomar_challenge_and_solution_pass_header_guards(self):
        project = ROOT / "integrations/palomar"
        comparator.header_guards((project / "Challenge.lean").read_text(),
                                 (project / "Solution.lean").read_text())

    def test_generated_solution_axiom_client_is_non_module(self):
        client = comparator.solution_axiom_client("palomar")
        self.assertEqual(client, "import Solution\n\n#print axioms KLSOpenAI.kls\n")
        self.assertFalse(comparator.lean_header.parse_header(client).is_module)

    def test_sandbox_reach_rejects_covered_dependency_paths(self):
        comparator.check_sandbox_reach([Path("/srv/kls/formalization"), Path("/opt/x")])
        for path in ["/home/runner/work/kls/formalization", "/tmp/x", "/root/kls", "/run/user/1000/x"]:
            with self.subTest(path=path), self.assertRaises(RuntimeError):
                comparator.check_sandbox_reach([Path(path)])

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


class CaptureBindingTests(unittest.TestCase):
    """Staged judge inputs are the captured bytes whose digests the receipt recorded."""

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.out = self.root / "out"
        self.out.mkdir()

    def test_mutation_after_capture_does_not_reach_the_staged_file(self):
        source = self.root / "Challenge.lean"
        source.write_bytes(b"module\n\npublic import Mathlib\n")
        captured = comparator.capture([source])
        recorded = comparator.sha(captured[source])
        source.write_bytes(b"module\n\npublic import Mathlib\ntheorem changed : True := trivial\n")
        comparator.stage(self.out, "Challenge.lean", captured[source], recorded)
        self.assertEqual((self.out / "Challenge.lean").read_bytes(), b"module\n\npublic import Mathlib\n")
        self.assertNotEqual(comparator.digest(self.out / "Challenge.lean"), comparator.digest(source))

    def test_staging_rejects_bytes_other_than_the_recorded_digest(self):
        with self.assertRaisesRegex(RuntimeError, "recorded input digest"):
            comparator.stage(self.out, "config.json", b"{}", comparator.sha(b"{ }"))

    def test_capture_drift_against_the_source_snapshot_is_detected(self):
        path = comparator.ROOT / "research/audits/KLS/Comparator/config.json"
        captured = {path: b"captured"}
        recorded = {str(path): comparator.sha(b"captured")}
        key = "research/audits/KLS/Comparator/config.json"
        self.assertEqual(comparator.captured_drift(captured, recorded, {key: recorded[str(path)]}), [])
        self.assertEqual(comparator.captured_drift(captured, recorded, {key: comparator.sha(b"later")}),
                         [str(path)])
        self.assertEqual(comparator.captured_drift(captured, recorded, {}), [str(path)])

    def test_fixture_inputs_are_rechecked_at_invocation(self):
        for name in comparator.FIXTURE_FILES:
            (self.out / name).write_text(name + "\n")
        recorded = comparator.fixture_digests(self.out)
        self.assertEqual(set(recorded), set(comparator.FIXTURE_FILES))
        comparator.check_fixture(self.out, recorded)
        for name in ("config.json", "lake-manifest.json", "lean-toolchain", "Solution.lean"):
            with self.subTest(name=name):
                original = (self.out / name).read_bytes()
                (self.out / name).write_bytes(original + b" ")
                with self.assertRaisesRegex(RuntimeError, name.replace(".", r"\.")):
                    comparator.check_fixture(self.out, recorded)
                (self.out / name).write_bytes(original)
        (self.out / "lakefile.toml").unlink()
        with self.assertRaises(RuntimeError):
            comparator.check_fixture(self.out, recorded)

    def test_generated_solution_client_digest_is_recorded_before_use(self):
        for name in comparator.FIXTURE_FILES:
            (self.out / name).write_text(name + "\n")
        recorded = comparator.fixture_digests(self.out)
        (self.out / "strict-solution.log").write_text("")  # the mocked runs write no log
        calls = []
        with patch.object(comparator, "run", side_effect=lambda cmd, *a, **k: calls.append(cmd)), \
                patch.object(comparator, "validate_axiom_reports", return_value={}):
            comparator.check_solution_client("compile", self.out, {}, "palomar", recorded)
        self.assertEqual(recorded["SolutionAxioms.lean"],
                         comparator.sha(comparator.solution_axiom_client("palomar").encode()))
        self.assertEqual(calls[-1][-1], "SolutionAxioms.lean")

    def test_tracked_palomar_project_parses_from_captured_bytes(self):
        project = ROOT / "integrations/palomar"
        captured = comparator.capture([project / "lakefile.toml", project / "lake-manifest.json"])
        requires, libraries, manifest = comparator.palomar_project(
            project, (ROOT / "integrations/openai").resolve(),
            captured[project / "lakefile.toml"], captured[project / "lake-manifest.json"])
        self.assertIn((ROOT / "integrations/openai").resolve(), {d for _, d in requires})
        self.assertEqual(sorted(lib["name"] for lib in libraries), ["Challenge", "Solution"])
        self.assertEqual(manifest, json.loads(captured[project / "lake-manifest.json"]))


class UpstreamModelTests(unittest.TestCase):
    UPSTREAM = b"/- c -/\nimport Mathlib\n\nnamespace OAI\n\ndef x : Nat := 1\n\nend OAI\n"

    def test_adaptation_round_trip_is_exact(self):
        local = comparator.adapt_upstream_model(self.UPSTREAM)
        self.assertEqual(local, b"module\n\n/- c -/\npublic import Mathlib\n\n@[expose] public section\n\n"
                                b"namespace OAI\n\ndef x : Nat := 1\n\nend OAI\n")
        self.assertEqual(comparator.restore_upstream_model(local), self.UPSTREAM)

    def test_other_local_changes_are_rejected(self):
        local = comparator.adapt_upstream_model(self.UPSTREAM)
        for bad in [local[len(b"module\n\n"):], b"module\n" + local[len(b"module\n\n"):],
                    local.replace(b"public import Mathlib\n", b"import Mathlib\n"),
                    local.replace(b"@[expose] public section\n\n", b""),
                    local.replace(b"@[expose] public section\n\n", b"public section\n\n"),
                    local.replace(b"namespace OAI\n", b"namespace OAI\n\npublic import Mathlib\n"),
                    local.replace(b"public import Mathlib\n", b"public import Mathlib\nimport Mathlib\n")]:
            with self.subTest(bad=bad), self.assertRaises(RuntimeError):
                comparator.restore_upstream_model(bad)

    def test_body_change_is_caught_by_the_upstream_hash(self):
        with tempfile.TemporaryDirectory() as directory:
            bridge = Path(directory)
            local = comparator.adapt_upstream_model(self.UPSTREAM)
            changed = local.replace(b"def x : Nat := 1", b"def x : Nat := 2")
            (bridge / "Model.lean").write_bytes(changed)
            record = {"revision": "r", "source": "s", "local": "Model.lean",
                      "sha256": hashlib.sha256(self.UPSTREAM).hexdigest(),
                      "local_sha256": hashlib.sha256(changed).hexdigest(),
                      "transformation": comparator.MODEL_TRANSFORMATION}
            (bridge / "UPSTREAM.json").write_text(json.dumps(record))
            with self.assertRaisesRegex(RuntimeError, "pinned source hash"):
                comparator.check_upstream_model(bridge)
            (bridge / "Model.lean").write_bytes(local)
            with self.assertRaisesRegex(RuntimeError, "recorded local hash"):
                comparator.check_upstream_model(bridge)
            record["local_sha256"] = hashlib.sha256(local).hexdigest()
            (bridge / "UPSTREAM.json").write_text(json.dumps(record))
            self.assertEqual(comparator.check_upstream_model(bridge)["upstream_sha256"], record["sha256"])
            for key, value in [("local_sha256", comparator.PLACEHOLDER), ("transformation", ["none"])]:
                with self.subTest(key=key):
                    (bridge / "UPSTREAM.json").write_text(json.dumps({**record, key: value}))
                    with self.assertRaises(RuntimeError):
                        comparator.check_upstream_model(bridge)

    def test_tracked_model_is_the_pinned_upstream_plus_the_adaptation(self):
        bridge = ROOT / "integrations/openai"
        record = json.loads((bridge / "UPSTREAM.json").read_text())
        original = comparator.restore_upstream_model((bridge / record["local"]).read_bytes())
        self.assertEqual(hashlib.sha256(original).hexdigest(), record["sha256"])
        # Fails until the integrator records local_sha256 for the ported file.
        comparator.check_upstream_model(bridge)


@unittest.skipUnless(BUNDLED, "set KLS_COMPARATOR_BUNDLED=1 to run the toolchain-bundled lake comparator")
class ComparatorBoundaryTests(unittest.TestCase):
    """Real-tool probes of the toolchain-bundled `lake comparator` (unsandboxed development mode)."""

    def compare(self, solution):
        stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        out = ROOT / "build/comparator-tests" / (stamp + "-" + self._testMethodName)
        out.mkdir(parents=True)
        pins = json.loads(comparator.JUDGE.read_text())
        (out / "lean-toolchain").write_text(pins["lean_toolchain"] + "\n")
        (out / "lakefile.toml").write_text(
            'name = "comparator-boundary"\n[[lean_lib]]\nname = "Challenge"\n'
            '[[lean_lib]]\nname = "Solution"\n')
        (out / "lake-manifest.json").write_text(json.dumps(
            {"version": "1.3.0", "packagesDir": ".lake/packages", "packages": [],
             "name": "«comparator-boundary»", "lakeDir": ".lake", "fixedToolchain": False}))
        (out / "Challenge.lean").write_text("theorem boundary : True := by sorry\n")
        (out / "Solution.lean").write_text(solution + "\n")
        config = {"challenge_module": "Challenge", "solution_module": "Solution",
                  "theorem_names": ["boundary"], "definition_names": [],
                  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}
        (out / "config.json").write_text(json.dumps(config))
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("LEAN", "LAKE", "ELAN_TOOLCHAIN", "COMPARATOR_"))}
        env.update(LEAN_NUM_THREADS="2")
        with (out / "comparator.log").open("w") as stream:
            process = subprocess.run(["lake", "comparator", "--config", "config.json",
                                      "--inadvisably-no-sandbox"], cwd=out, env=env,
                                     stdout=stream, stderr=subprocess.STDOUT, timeout=300)
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
