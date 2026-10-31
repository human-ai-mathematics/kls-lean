"""Regression mutations for the local documentation contract."""
import copy
from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_documentation as doc
import module_inventory
import verify


class DocumentationTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.source = "formalization/FunctionalInequalities/Analysis/Probe.lean"
        self.write(self.source, "/-!\n# Probe\n\nA complete module summary.\n-/\n"
                   "namespace Test\nsection Context\n"
                   "theorem result : True := trivial\n"
                   "end Context\nend Test\n")
        self.config = {
            "version": 1, "compact_headings": [],
            "maintenance": {"linter_exceptions": [], "audit_reports": []},
            "declaration_links": [{"document": "README.md", "label": "result",
                                   "source": self.source, "declaration": "Test.result"}],
            "current_letwin_scope": {
                "document": "research/progress/review.md", "paper": "Paper",
                "items": [{"id": "L22", "relation": "same", "declarations": ["Test.result"]}]},
            "handoff": {"document": "HANDOFF.md", "review_map": "research/progress/map.json",
                        "scope_lines": ["The active scope is a documentation fixture."],
                        "preservation": "Existing mathematical interfaces are retained.",
                        "next_step": "Shared-proof cleanup is deferred to the next batch."},
            "route_scope_notes": [{"source": "research/progress/route.json",
                                   "pointer": "/stages/@old/note", "prefix": "Earlier route only."}],
            "reviewed_scope_passages": [{"source": "research/progress/review.md",
                                         "required": "This support alone has no full regularity.",
                                         "reason": "Keep the support restriction separate."}]}
        self.write_json("research/progress/literature.json", {"papers": [{
            "id": "Paper", "lemma_map": {"items": [{"id": "L22", "locator": "Lemma 2.2",
                "relation": "same", "declarations": [{"name": "Test.result", "source": self.source}]}]}}]})
        self.write_json("research/progress/map.json", {})
        for name in ["formalization/README.md", "formalization/API.md", "LEAN_DESIGN.md",
                     "research/naming.md"]:
            self.write(name, "# Fixture\n")
        self.write_json("research/progress/route.json", {"stages": [
            {"id": "other", "note": "Unrelated."}, {"id": "old", "note": "Earlier route only. Gap."}]})
        self.write("README.md", f"# Home\n\n[result]({self.source}#L8)\n")
        self.write("HANDOFF.md", "# Handoff\n\n" + doc.maintenance_scope(self.config["handoff"]) + "\n")
        self.write("research/progress/review.md", doc.current_scope(
            self.root, self.config["current_letwin_scope"]) +
            "\n\nThis support alone has no full regularity.\n")
        self.save_config()
        self.refresh_modules()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def write_json(self, name, value):
        self.write(name, json.dumps(value, ensure_ascii=False))

    def save_config(self):
        self.write_json(doc.CONFIG, self.config)

    def refresh_modules(self):
        self.write(module_inventory.OUTPUT, module_inventory.render(module_inventory.inventory(self.root)))

    def errors(self):
        return doc.check_documentation(self.root)[0]

    def test_valid_fixture_and_in_range_wrong_declaration_anchor(self):
        self.assertEqual(self.errors(), [])
        path = self.root / "README.md"
        path.write_text(path.read_text().replace("#L8", "#L7"))
        self.assertTrue(any("must point to" in error for error in self.errors()))

    def test_split_source_heading_and_stale_directory_fail_independently(self):
        path = self.root / self.source
        path.write_text(path.read_text().replace("# Probe\n\n", "# Probe `C² ∩\nC¹`\n\n"))
        errors = self.errors()
        self.assertTrue(any("heading must end" in error for error in errors))
        self.assertTrue(any("Stale module directory" in error for error in errors))
        self.refresh_modules()
        self.assertFalse(any("Stale module directory" in error for error in self.errors()))
        self.assertTrue(any("heading must end" in error for error in self.errors()))

    def test_compact_synopsis_requires_live_reviewed_exception(self):
        path = self.root / self.source
        original = path.read_text()
        path.write_text(original.replace("# Probe\n\n", "# Probe\n"))
        self.config["compact_headings"] = [{"source": self.source, "heading": "# Probe",
                                             "reason": "Reviewed complete heading and synopsis."}]
        self.save_config()
        self.assertFalse(any("heading" in error for error in self.errors()))
        path.write_text(original)
        self.assertTrue(any("stale compact-heading exception" in error for error in self.errors()))

    def test_retargeted_or_removed_current_producer_fails(self):
        path = self.root / "research/progress/literature.json"
        record = json.loads(path.read_text())
        record["papers"][0]["lemma_map"]["items"][0]["relation"] = "alternative"
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "changed relation"):
            self.errors()
        record["papers"][0]["lemma_map"]["items"][0]["relation"] = "same"
        path.write_text(json.dumps(record))
        source = self.root / self.source
        source.write_text(source.read_text().replace("theorem result", "theorem renamed"))
        with self.assertRaisesRegex(ValueError, "declaration missing"):
            self.errors()

    def test_scope_and_handoff_blocks_and_route_notes_cannot_drift(self):
        for name, old, new, message in [
            ("research/progress/review.md", "every admissible moment potential", "one witness", "stale current Letwin"),
            ("HANDOFF.md", "deferred to the next batch", "completed", "stale current maintenance"),
            ("research/progress/review.md", "This support alone has no full regularity.", "Full theorem open.", "source-scope passage")]:
            with self.subTest(name=name, mutation=old):
                path = self.root / name
                original = path.read_text()
                path.write_text(original.replace(old, new))
                self.assertTrue(any(message in error for error in self.errors()))
                path.write_text(original)
        self.write_json("research/progress/route.json", {"stages": [
            {"id": "old", "note": "Earlier route only. Gap."}, {"id": "other", "note": "Unrelated."}]})
        self.assertEqual(self.errors(), [])
        self.write_json("research/progress/route.json", {"stages": [{"id": "old", "note": "Full theorem open."}]})
        self.assertTrue(any("missing route-specific gap scope" in error for error in self.errors()))

    def test_missing_handoff_markers_and_review_map_fail(self):
        (self.root / self.config["handoff"]["review_map"]).unlink()
        self.assertIn("Current maintenance source review is missing", self.errors())
        self.write("HANDOFF.md", "Superseded handoff\n")
        with self.assertRaisesRegex(ValueError, "exactly one generated block"):
            self.errors()

    def test_ambiguous_duplicate_and_unregistered_line_links_fail(self):
        self.config["declaration_links"].append(copy.deepcopy(self.config["declaration_links"][0]))
        self.save_config()
        self.assertTrue(any("duplicate declaration-link binding" in error for error in self.errors()))
        self.config["declaration_links"] = []
        self.save_config()
        self.assertTrue(any("unbound Lean declaration link" in error for error in self.errors()))
        self.config["declaration_links"] = [{"document": "README.md", "label": "result",
                                               "source": self.source, "declaration": "Test.result"}]
        path = self.root / self.source
        path.write_text(path.read_text() + "namespace Test\ntheorem result : True := trivial\nend Test\n")
        self.assertTrue(any("expected one declaration" in error for error in
                            doc.navigation(self.root, ["README.md"], self.config["declaration_links"])[0]))

    def test_structure_field_is_bound_to_its_owner(self):
        self.write(self.source, "namespace Test\nstructure Owner where\n  value : True\n"
                   "structure Other where\n  value : False\nend Test\n")
        binding = {"document": "README.md", "source": self.source, "label": "value",
                   "declaration": "Test.Owner", "field": "value"}
        self.write("README.md", f"[value]({self.source}#L3)\n")
        self.assertEqual(doc.navigation(self.root, ["README.md"], [binding])[0], [])
        self.write("README.md", f"[value]({self.source}#L5)\n")
        self.assertTrue(doc.navigation(self.root, ["README.md"], [binding])[0])
        binding["field"] = "absent"
        self.assertTrue(any("expected one field" in error for error in
                            doc.navigation(self.root, ["README.md"], [binding])[0]))

    def test_writer_changes_only_marked_blocks_and_bound_anchors(self):
        source = (self.root / self.source).read_bytes()
        self.write("README.md", f"# Retain this prose\n\n[result]({self.source}#L7)\n")
        path = self.root / "HANDOFF.md"
        path.write_text(path.read_text().replace("deferred to the next batch", "stale"))
        with redirect_stdout(io.StringIO()):
            self.assertEqual(doc.main(["--root", str(self.root), "--write"]), 0)
        self.assertEqual((self.root / "README.md").read_text(),
                         f"# Retain this prose\n\n[result]({self.source}#L8)\n")
        self.assertEqual((self.root / self.source).read_bytes(), source)
        self.assertEqual(self.errors(), [])

    def test_local_paths_heading_fragments_and_line_ranges(self):
        self.write("guide (draft).md", "# Repeated\n\n# Repeated\n")
        self.write("extra.md", "[valid](<guide (draft).md#repeated-1>)\n"
                   "[missing](guide.md)\n[fragment](guide%20(draft).md#absent)\n"
                   f"[range]({self.source}#L10-L2)\n[external](https://example.org/missing)\n")
        errors = self.errors()
        self.assertTrue(any("missing destination: guide.md" in e for e in errors))
        self.assertTrue(any("missing heading" in e for e in errors))
        self.assertTrue(any("line anchor out of range" in e for e in errors))
        self.assertFalse(any("repeated-1" in e or "https://" in e for e in errors))

    def test_module_summary_and_process_label_regressions(self):
        path = self.root / self.source
        original = path.read_text()
        path.write_text(original.replace("/-!", "/-", 1))
        self.assertTrue(any("missing module summary" in e for e in self.errors()))
        path.write_text(original + "\n/-! ### Source support (2026-10-10 candidate) -/\n")
        self.assertTrue(any("obsolete dated candidate label" in e for e in self.errors()))

    def test_production_output_and_migrated_audit_coverage(self):
        path = self.root / self.source
        original = path.read_text()
        path.write_text(original + '\ndef quoted := "#print axioms Test.result"\n')
        self.assertFalse(any("production axiom report" in e for e in self.errors()))
        path.write_text(original + "\n#print axioms Test.result\n")
        self.assertTrue(any("production axiom report" in e for e in self.errors()))
        path.write_text(original)
        self.config["maintenance"]["audit_reports"] = [
            {"declaration": "Test.result", "audit": "research/audits/Probe.lean"}]
        self.write("research/audits/Probe.lean", "-- #print axioms Test.result\n")
        self.save_config()
        self.assertTrue(any("missing migrated axiom report" in e for e in self.errors()))
        self.write("research/audits/Probe.lean", "#print axioms\n  Test.result\n")
        self.assertFalse(any("axiom report" in e for e in self.errors()))

    def test_empty_module_summary_fails_the_full_gate(self):
        path = self.root / self.source
        original = path.read_text()
        for blank in ["", "   "]:
            for later_section in ["", "\n/-! # A later section\n\nSection details.\n-/\n"]:
                with self.subTest(blank=blank, later_section=later_section):
                    path.write_text(original.replace("# Probe", blank).replace(
                        "A complete module summary.", blank) + later_section)
                    errors = self.errors()
                    self.assertTrue(any("missing module summary" in e for e in errors))
                    self.assertFalse(any("must point to" in e for e in errors))

    def test_source_references_include_root_paths_and_brace_groups(self):
        path = self.root / self.source
        original = path.read_text()
        self.write("examples/One.lean", "-- First referenced client.\n")
        self.write("examples/Two.lean", "-- Second referenced client.\n")
        path.write_text(original + "\n/-! Clients: `examples/{One, Two}.lean` and `One.lean`. -/\n")
        self.assertFalse(any("source-file reference" in e for e in self.errors()))
        path.write_text(original + "\n/-! Old owner: `DeletedOwner.lean`. -/\n")
        self.assertTrue(any("missing source-file reference" in e for e in self.errors()))

    def test_source_reference_suffix_fallback_must_be_unique(self):
        path = self.root / self.source
        original = path.read_text()
        self.write("examples/Left/Shared.lean", "-- First owner.\n")
        self.write("examples/Right/Shared.lean", "-- Second owner.\n")
        path.write_text(original + "\n/-! Support: `Shared.lean`. -/\n")
        errors = self.errors()
        ambiguous = [e for e in errors if "ambiguous source-file reference" in e]
        self.assertEqual(len(ambiguous), 1)
        self.assertIn("examples/Left/Shared.lean", ambiguous[0])
        self.assertIn("examples/Right/Shared.lean", ambiguous[0])
        path.write_text(original + "\n/-! Support: `examples/Left/Shared.lean`. -/\n")
        self.assertEqual(self.errors(), [])
        (self.root / "examples/Right/Shared.lean").unlink()
        path.write_text(original + "\n/-! Support: `Shared.lean`. -/\n")
        self.assertEqual(self.errors(), [])

    def test_source_reference_exact_owner_precedes_global_suffixes(self):
        path = self.root / self.source
        self.write("formalization/FunctionalInequalities/Analysis/Shared.lean",
                   "/-! # Shared\n\nThe local owner.\n-/\n")
        self.write("examples/Shared.lean", "-- A different owner.\n")
        path.write_text(path.read_text() + "\n/-! Support: `Shared.lean`. -/\n")
        self.refresh_modules()
        self.assertEqual(self.errors(), [])

    def test_linter_exception_is_local_exact_and_justified(self):
        path = self.root / self.source
        original = path.read_text()
        local = ("\nnamespace Test\nset_option linter.unusedVariables false in\n"
                 "theorem retained (h : True) : True := trivial\nend Test\n")
        path.write_text(original + local)
        self.config["maintenance"]["linter_exceptions"] = [{
            "source": self.source, "option": "linter.unusedVariables", "declaration": "Test.retained",
            "reason": "Keep the original named public premise h."}]
        self.save_config()
        self.assertFalse(any("linter" in e for e in self.errors()))
        self.config["maintenance"]["linter_exceptions"][0]["reason"] = ""
        self.save_config()
        self.assertTrue(any("interface-preservation reason" in e for e in self.errors()))
        self.config["maintenance"]["linter_exceptions"][0]["reason"] = "Retain the named premise h."
        self.save_config()
        path.write_text(original + local.replace(" false in", " false"))
        self.assertTrue(any("must be declaration-local" in e for e in self.errors()))
        path.write_text(original + local.replace("retained", "renamed"))
        self.assertTrue(any("unreviewed linter exception" in e for e in self.errors()))
        path.write_text(original)
        self.assertTrue(any("stale linter exception" in e for e in self.errors()))

    def test_owned_whitespace_encoding_and_set_notation(self):
        path = self.root / self.source
        original = path.read_text()
        for suffix, message in [("\n-- trailing  \n", "trailing whitespace"),
                                ("\n-- tab\t\n", "tab or"),
                                ("\n-- {x ; condition}\n", "whitespace before semicolon"),
                                ("\n-- \ufffd\n", "replacement character")]:
            with self.subTest(message=message):
                path.write_text(original + suffix)
                self.assertTrue(any(message in e for e in self.errors()))
        path.write_bytes(original.encode().replace(b"\n", b"\r\n"))
        self.assertTrue(any("Unix line endings" in e for e in self.errors()))
        path.write_text(original + "\n-- The existing notation μ̄, ψ̃ and h″ is retained.\n")
        self.assertFalse(any("whitespace" in e or "character" in e for e in self.errors()))
        self.config["maintenance"]["forbidden_lookalikes"] = ["ᐟ"]
        self.save_config()
        path.write_text(original + "\n-- Accidental exponent separator: Cov⁻¹ᐟ².\n")
        self.assertTrue(any("unreviewed lookalike character" in e for e in self.errors()))


class ParsingTests(unittest.TestCase):
    def test_namespaces_sections_comments_strings_and_structure_fields(self):
        source = ('/-! # Summary\nnamespace Fake\ntheorem wrong : True := trivial\n-/\n'
                  'namespace A\nsection X\nnamespace B\n'
                  'def literal := "namespace Fake\\n theorem wrong"\n'
                  '/- nested /- theorem wrong -/ comment -/\n'
                  'protected theorem right : True := trivial\nend B\nend X\n'
                  'theorem _root_.Global : True := trivial\nend A\n')
        self.assertEqual(set(doc.declaration_lines(source)), {"A.B.literal", "A.B.right", "Global"})

    def test_module_sections_and_meta_declarations(self):
        source = ('module\n\npublic import Mathlib.Order.Basic\n\n/-! # Summary -/\n\n'
                  '@[expose] public section\n\nnamespace A\n'
                  'public noncomputable section\nmeta def tool := 1\nend\n'
                  'public theorem visible : True := trivial\nend A\n\n'
                  'end\n\ntheorem Outside.after : True := trivial\n')
        self.assertEqual(set(doc.declaration_lines(source)), {"A.tool", "A.visible", "Outside.after"})

    def test_links_ignore_math_code_and_fenced_examples(self):
        text = ("Values in [0, 1]: |D(H_t f)| and [A] : Prop.\n"
                "`[fake](missing.md)`\n```md\n[fake](missing.md)\n```\n"
                "[actual](<guide (draft).md#part>)\n[reference]: actual.md\n")
        self.assertEqual([link.target for link in doc.markdown_links(text)],
                         ["guide (draft).md#part", "actual.md"])


class ModuleInventoryHeaderTests(unittest.TestCase):
    def inventory(self, files):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, text in files.items():
                path = root / module_inventory.LIBRARY / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            return module_inventory.inventory(root)

    def test_every_import_form_is_a_local_edge(self):
        data = self.inventory({
            "A.lean": "/- Copyright -/\nmodule\n\npublic import Mathlib.Order.Basic\n",
            "B.lean": "module\n\nimport FunctionalInequalities.A\n",
            "C.lean": "module\n\npublic import FunctionalInequalities.A\nmeta import FunctionalInequalities.B\n",
            "D.lean": ("module\n\npublic meta import FunctionalInequalities.C\n"
                       "import all FunctionalInequalities.B\n\n/-!\n# D\nimport FunctionalInequalities.X\n-/\n"),
            "Legacy.lean": "import FunctionalInequalities.D\n"})
        self.assertEqual(data["errors"], [])
        rows = {row["path"]: row for row in data["modules"]}
        self.assertEqual(rows["D.lean"]["imports"], ["FunctionalInequalities.C", "FunctionalInequalities.B"])
        self.assertEqual(rows["D.lean"]["title"], "D")
        self.assertTrue(rows["C.lean"]["is_module"])
        self.assertFalse(rows["Legacy.lean"]["is_module"])
        self.assertEqual(data["local_import_edges"], 6)

    def test_meta_and_all_edges_keep_cycle_and_resolution_checks(self):
        data = self.inventory({"A.lean": "module\n\nmeta import FunctionalInequalities.B\n",
                               "B.lean": "module\n\nimport all FunctionalInequalities.A\n",
                               "C.lean": "module\n\npublic meta import FunctionalInequalities.Missing\n"})
        self.assertTrue(any(e.startswith("Import cycle") for e in data["errors"]))
        self.assertIn("C.lean: unresolved local import FunctionalInequalities.Missing", data["errors"])

    def test_unparsable_header_is_an_error_not_a_dropped_edge(self):
        data = self.inventory({"A.lean": "public import FunctionalInequalities.B\n",
                               "B.lean": "module\n\nimport FunctionalInequalities.A\nprivate import X\n"})
        self.assertEqual(sorted(e.split(":")[0] for e in data["errors"]), ["A.lean", "B.lean"])


class VerifierIntegrationTests(unittest.TestCase):
    def test_documentation_failure_stops_full_verifier_before_lean(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            seen = []

            def run_command(command, *, logfile, **kwargs):
                seen.append(logfile.stem)
                logfile.write_text("intentional documentation mutation\n")
                return subprocess.CompletedProcess(command, 1)

            snapshot = {"sha256": "fixture", "files": {}}
            with (patch("verify.verification_snapshot", return_value=snapshot),
                  patch("verify.run_logged_command", side_effect=run_command),
                  redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO())):
                result = verify.run_verification(root)
            self.assertEqual(result, 1)
            self.assertEqual(seen, ["documentation"])
            report = json.loads((root / "build/verification/latest.json").read_text())
            self.assertEqual(report["status"], "failed")
            self.assertIn("documentation failed", report["errors"][0])


if __name__ == "__main__":
    unittest.main()
