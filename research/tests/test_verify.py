"""Exercise the generated axiom audit against Lean, including its failure boundary."""
from contextlib import redirect_stderr, redirect_stdout
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import (axiom_audit_code, build_replay_inputs, check_research_audits,
                    library_axiom_audit_code, parse_axioms, prepare_replay, replay_sources,
                    reported_names, run_verification,
                    undiscovered_lean_sources, vendor_axiom_audit_code, verification_snapshot)

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

    def test_quoted_name_with_space_rejects_verification(self):
        with self.assertRaisesRegex(RuntimeError, "unexpected axioms"):
            self.check_sources({"research/audits/Quoted.lean":
                                "axiom «bad name» : False\n#print axioms «bad name»\n"})

    def test_quoted_name_with_line_break_fails_closed(self):
        with self.assertRaisesRegex(RuntimeError, "unparsed axiom report"):
            self.check_sources({"research/audits/Newline.lean":
                                "axiom «bad\nname» : False\n#print axioms «bad\nname»\n"})


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
        reports, errors = parse_axioms(result.stdout, names, structured=True)
        self.assertEqual(errors, [])
        self.assertEqual(reports, {name: [] for name in names})

    def test_transitive_nonstandard_axiom_is_rejected(self):
        names = {"auditDependency"}
        result = self.run_audit(
            "axiom auditForbidden : False\n"
            "theorem auditDependency : False := auditForbidden", names)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        reports, errors = parse_axioms(result.stdout, names, structured=True)
        self.assertEqual(reports["auditDependency"], ["auditForbidden"])
        self.assertTrue(any("unexpected axioms" in error for error in errors))

    def test_text_reports_keep_primes_generated_suffixes_and_spaces(self):
        output = ("'A.lemma'' depends on axioms: [propext]\n"
                  "'A.other'._simp_1_2' depends on axioms: [propext,\n Classical.choice]\n"
                  "'B.other'._simp_1_2' depends on axioms: [sorryAx]\n"
                  "'«bad name»' depends on axioms: [«bad name»]\n"
                  "'C.plain' does not depend on any axioms\n")
        names = {"A.lemma'", "A.other'._simp_1_2", "B.other'._simp_1_2", "«bad name»", "C.plain"}
        self.assertEqual(reported_names(output), names)
        reports, errors = parse_axioms(output, names)
        self.assertEqual(reports["A.other'._simp_1_2"], ["Classical.choice", "propext"])
        self.assertEqual(errors, ["B.other'._simp_1_2: unexpected axioms ['sorryAx']",
                                  "«bad name»: unexpected axioms ['«bad name»']"])

    def test_unparsed_text_report_fails_closed(self):
        # Actual Lean output for `axiom «bad\nname» : False` and `#print axioms «bad\nname»`.
        output = "'«bad\nname»' depends on axioms: [«bad\n   name»]\n"
        reports, errors = parse_axioms(output, reported_names(output))
        self.assertEqual(reports, {})
        self.assertEqual(errors, ["unparsed axiom report: 1 verdicts, 0 parsed"])

    def test_structured_reports_parse_any_name_and_reject_text(self):
        output = ('AXIOM_REPORT {"name":"«bad\\nname»","axioms":["propext"]}\n'
                  'AXIOM_REPORT {"name":"A.x\'._simp_1","axioms":["sorryAx"]}\n')
        reports, errors = parse_axioms(output, {"«bad\nname»", "A.x'._simp_1"}, structured=True)
        self.assertEqual(reports["«bad\nname»"], ["propext"])
        self.assertEqual(errors, ["A.x'._simp_1: unexpected axioms ['sorryAx']"])
        _, errors = parse_axioms(output + "'C' depends on axioms: [propext]\n",
                                 set(), structured=True)
        self.assertIn("unstructured axiom report in a structured audit", errors)
        _, errors = parse_axioms("AXIOM_REPORT {broken\n", set(), structured=True)
        self.assertTrue(errors[0].startswith("unparsed structured axiom report"))

    def test_missing_declaration_fails_before_collection(self):
        names = {"AuditMissing"}
        result = self.run_audit("", names)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Axiom audit declaration not found: AuditMissing", result.stdout)
        reports, errors = parse_axioms(result.stdout, names, structured=True)
        self.assertEqual(reports, {})
        self.assertIn("missing axiom report: AuditMissing", errors)


class KernelReplayFlagTests(unittest.TestCase):
    def setUp(self):
        (ROOT / "build").mkdir(exist_ok=True)

    def run_fixture(self, *, no_kernel_replay=False, replayed=None, axioms=("propext",)):
        # Exercise the real orchestration and receipt writer without building the repository.
        with tempfile.TemporaryDirectory(prefix="verify-flag-", dir=ROOT / "build") as directory:
            root = Path(directory)
            modules = ["FunctionalInequalities", "LevyStochCalc.Probe", "solutions.Probe"]
            snapshot = {"sha256": "fixture", "files": {
                "formalization/FunctionalInequalities.lean": "local",
                "formalization/vendor/LevyStochCalc/LevyStochCalc/Probe.lean": "vendor",
                "solutions/Probe.lean": "solution",
                "research/audits/Probe.lean": "audit"}}

            def run_command(command, *, cwd, logfile, **kwargs):
                output = ""
                if logfile.stem == "lake-search-path":
                    output = str(root / "formalization/.lake/build/lib/lean")
                elif logfile.stem == "lean-toolchain":
                    output = str(root / "toolchain")
                elif logfile.stem == "classical-kls":
                    out = Path(command[-1])
                    out.mkdir()
                    (out / "summary.json").write_text(json.dumps({"status": "passed"}))
                elif logfile.stem == "local-declaration-audit":
                    output = "AXIOM_REPORT " + json.dumps({
                        "name": "FunctionalInequalities.kls", "axioms": list(axioms)}) + "\n"
                elif logfile.stem == "research-audit-000":
                    output = "'Audit.checked' depends on axioms: [propext]\n"
                elif logfile.stem == "leanchecker":
                    output = "".join(f"replaying {m}\n" for m in (modules if replayed is None else replayed))
                logfile.write_text(output)
                return subprocess.CompletedProcess(command, 0)

            with (patch("verify.verification_snapshot", return_value=snapshot),
                  patch("verify.prepare_replay", return_value={"modules": modules, "compiled_sha256": {}}),
                  patch("verify.run_logged_command", side_effect=run_command),
                  redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO())):
                result = run_verification(root, lean_only=True, no_kernel_replay=no_kernel_replay)
            report = json.loads((root / "build/verification/latest-lean.json").read_text())
            return result, report

    def test_skip_replay_keeps_build_and_all_audits_and_records_scope(self):
        result, report = self.run_fixture(no_kernel_replay=True)
        self.assertEqual(result, 0, report["errors"])
        self.assertEqual(report["status"], "passed")
        self.assertEqual(report["kernel_replay"], "skipped")
        self.assertEqual(report["replayed_modules"], [])
        self.assertIn("local-module kernel replay was not run remotely", report["trust_scope"])
        self.assertIn("covered by the full local receipt", report["trust_scope"])
        gates = {gate["name"]: gate for gate in report["gates"]}
        self.assertNotIn("leanchecker", gates)
        for name in ["lake-build", "lake-build-replay-scope", "research-audit-000",
                     "local-declaration-audit", "vendor-axiom-audit", "classical-kls"]:
            self.assertIn(name, gates)
        self.assertIn("-DwarningAsError=true", gates["research-audit-000"]["command"])
        self.assertEqual(report["local_declarations_audited"], 1)
        self.assertEqual(report["excluded_open_targets"], [])

    def test_lean_only_without_flag_still_replays_and_checks_coverage(self):
        result, report = self.run_fixture()
        self.assertEqual(result, 0, report["errors"])
        self.assertIn("leanchecker", [gate["name"] for gate in report["gates"]])
        self.assertEqual(report["replayed_modules"],
                         ["FunctionalInequalities", "LevyStochCalc.Probe", "solutions.Probe"])
        self.assertIn("Local source build and local-module kernel replay", report["trust_scope"])
        result, report = self.run_fixture(replayed=["FunctionalInequalities"])
        self.assertEqual(result, 1)
        self.assertIn("checker coverage differs from current sources", report["errors"][0])

    def test_skip_replay_still_rejects_nonstandard_local_axioms(self):
        result, report = self.run_fixture(no_kernel_replay=True, axioms=["sorryAx"])
        self.assertEqual(result, 1)
        self.assertEqual(report["status"], "failed")
        self.assertIn("unexpected axioms ['sorryAx']", report["errors"][0])
        self.assertEqual(report["kernel_replay"], "skipped")
        self.assertEqual(report["replayed_modules"], [])

    def test_flag_without_lean_only_is_a_parser_error_before_verification(self):
        with tempfile.TemporaryDirectory(prefix="verify-args-", dir=ROOT / "build") as directory:
            result = subprocess.run([sys.executable, str(ROOT / "research/verify.py"),
                                     "--root", directory, "--no-kernel-replay"],
                                    text=True, capture_output=True, timeout=30)
            self.assertEqual(result.returncode, 2)
            self.assertIn("error: --no-kernel-replay requires --lean-only", result.stderr)
            self.assertFalse((Path(directory) / "build").exists())
            with self.assertRaisesRegex(ValueError, "--no-kernel-replay requires --lean-only"):
                run_verification(Path(directory), no_kernel_replay=True)


class LeanOnlyBoundaryTests(unittest.TestCase):
    def test_prose_does_not_change_lean_receipt_but_proof_inputs_do(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            subprocess.run(["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.org",
                            "commit", "--allow-empty", "-qm", "fixture"], cwd=root, check=True)
            proof = root / "Example.lean"
            prose = root / "README.md"
            proof.write_text("example : True := trivial\n")
            prose.write_text("draft\n")
            before = verification_snapshot(root, lean_only=True)["sha256"]
            prose.write_text("updated\n")
            self.assertEqual(verification_snapshot(root, lean_only=True)["sha256"], before)
            proof.write_text("example : False := by sorry\n")
            self.assertNotEqual(verification_snapshot(root, lean_only=True)["sha256"], before)

    def run_library_audit(self, source):
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        return subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT / "formalization",
                              input="import Lean\n" + source + library_axiom_audit_code([]).removeprefix("import Lean"),
                              text=True, capture_output=True, timeout=60, env=env)

    def test_hole_named_kls_is_rejected(self):
        result = self.run_library_audit("theorem FunctionalInequalities.KLS.kls : False := by sorry\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FunctionalInequalities.KLS.kls: unexpected axioms [sorryAx]", result.stdout + result.stderr)

    def test_wrapper_of_a_kls_hole_is_rejected(self):
        result = self.run_library_audit("theorem FunctionalInequalities.KLS.kls : False := by sorry\n"
            "theorem FunctionalInequalities.wrapper : False := FunctionalInequalities.KLS.kls\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unexpected axioms [sorryAx]", result.stdout + result.stderr)

    def test_proved_kls_with_standard_axioms_is_accepted(self):
        result = self.run_library_audit("theorem FunctionalInequalities.KLS.kls : True := trivial\n"
            "theorem FunctionalInequalities.checked : True := FunctionalInequalities.KLS.kls\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('"name":"FunctionalInequalities.KLS.kls"', result.stdout + result.stderr)

    def test_unlisted_nonstandard_axiom_is_rejected(self):
        result = self.run_library_audit("axiom FunctionalInequalities.unlisted : False\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unexpected axioms", result.stdout + result.stderr)


class VendorTests(unittest.TestCase):
    def test_vendored_sources_replay_under_their_module_roots(self):
        snapshot = {"files": {
            "formalization/FunctionalInequalities.lean": "root",
            "formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/Picard.lean": "vendored",
            "formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/Removed.lean": None,
            "formalization/vendor/LevyStochCalc/Stray/Helper.lean": "outside the module root",
            "formalization/vendor/BrownianMotion/LICENSE": "license",
        }}
        self.assertEqual(replay_sources(snapshot), {
            "FunctionalInequalities": "formalization/FunctionalInequalities.lean",
            "LevyStochCalc.Ito.Picard": "formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/Picard.lean",
        })

    def run_vendor_audit(self, source, listed):
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        code = vendor_axiom_audit_code([], set(listed)).removeprefix("import Lean")
        return subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT / "formalization",
                              input="import Lean\n" + source + code,
                              text=True, capture_output=True, timeout=60, env=env)

    hole = "theorem BrownianMotion.hole : True := by sorry\n"

    def test_listed_upstream_sorry_is_isolated(self):
        result = self.run_vendor_audit(
            self.hole + "theorem LevyStochCalc.fine : True := trivial\n", ["BrownianMotion.hole"])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("Audited 2 vendored declarations", result.stdout)

    def test_vendored_user_of_listed_sorry_is_rejected(self):
        result = self.run_vendor_audit(
            self.hole + "theorem LevyStochCalc.user : True := BrownianMotion.hole\n",
            ["BrownianMotion.hole"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("LevyStochCalc.user: unexpected axioms [sorryAx]", result.stdout + result.stderr)

    def test_unlisted_vendored_sorry_is_rejected(self):
        result = self.run_vendor_audit(self.hole, [])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unexpected axioms [sorryAx]", result.stdout + result.stderr)

    def test_fixed_or_missing_listed_declaration_is_rejected(self):
        fixed = self.run_vendor_audit("theorem BrownianMotion.hole : True := trivial\n",
                                      ["BrownianMotion.hole"])
        self.assertNotEqual(fixed.returncode, 0)
        self.assertIn("listed upstream sorry declaration has axioms", fixed.stdout + fixed.stderr)
        missing = self.run_vendor_audit("", ["BrownianMotion.hole"])
        self.assertNotEqual(missing.returncode, 0)
        self.assertIn("Listed upstream sorry declaration not found", missing.stdout + missing.stderr)

    def test_listed_name_outside_the_vendored_roots_is_rejected(self):
        result = self.run_vendor_audit(
            "theorem External.hole : True := by sorry\ntheorem LevyStochCalc.fine : True := trivial\n",
            ["External.hole"])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("is not a vendored declaration: External.hole", result.stdout + result.stderr)

    def test_unregistered_local_wrapper_of_vendored_sorry_fails_local_audit(self):
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        source = (self.hole +
                  "theorem FunctionalInequalities.unregisteredWrapper : True := BrownianMotion.hole\n")
        result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT / "formalization",
                                input="import Lean\n" + source +
                                library_axiom_audit_code([]).removeprefix("import Lean"),
                                text=True, capture_output=True, timeout=60, env=env)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FunctionalInequalities.unregisteredWrapper: unexpected axioms [sorryAx]",
                      result.stdout + result.stderr)

    @unittest.skipUnless((ROOT / "formalization/.lake/build/lib/lean/BrownianMotion/StochasticIntegral/"
                          "Quasimartingale/CadlagModification.olean").is_file(),
                         "vendored BrownianMotion is not built")
    def test_wrapper_of_actual_fixed_vendored_theorem_passes_local_audit(self):
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        source = ("import BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification\n"
                  "import Lean\n"
                  "set_option linter.defProp false in\n"
                  "def FunctionalInequalities.unregisteredWrapper :=\n"
                  "  @MeasureTheory.Martingale.isRealQuasimartingale\n")
        result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT / "formalization",
                                input=source + library_axiom_audit_code([]).removeprefix("import Lean"),
                                text=True, capture_output=True, timeout=300, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("sorryAx", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
