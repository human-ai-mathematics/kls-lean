"""Regress aggregate-import and separate-package gaps that source-build Mathlib."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from cache_mathlib import check_cache, mathlib_roots, prepare_cache, required_modules


class MathlibCacheTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.mathlib = self.root / "formalization/.lake/packages/mathlib"
        self.write("formalization/FunctionalInequalities.lean", "import Mathlib\n")
        self.write("formalization/.lake/packages/mathlib/Mathlib.lean", "import Mathlib.A\n")
        self.write("formalization/.lake/packages/mathlib/Mathlib/A.lean", "import Mathlib.B\n")
        self.write("formalization/.lake/packages/mathlib/Mathlib/B.lean", "import Lean\n")

    def write(self, name, contents):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)

    def compile_modules(self, *names, mathlib=None, suffixes=(".olean",)):
        mathlib = self.mathlib if mathlib is None else mathlib
        for name in names:
            for suffix in suffixes:
                path = mathlib / ".lake/build/lib/lean" / Path(*name.split("."))
                path = path.with_suffix(suffix)
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"fixture")

    def add_bridge(self):
        self.write("integrations/openai/OAI/Analysis/KLS/Model.lean", "import Mathlib\n")
        for name in ["Mathlib.lean", "Mathlib/A.lean", "Mathlib/B.lean"]:
            self.write("integrations/openai/.lake/packages/mathlib/" + name,
                       (self.mathlib / name).read_text())
        return self.root / "integrations/openai/.lake/packages/mathlib"

    def add_palomar(self):
        self.write("integrations/palomar/Challenge.lean", "module\n\npublic import Mathlib\n")
        self.write("integrations/palomar/Solution.lean",
                   "module\n\npublic import OAI.Analysis.KLS.Model\npublic import KLSOpenAI.Target\n")
        for name in ["Mathlib.lean", "Mathlib/A.lean", "Mathlib/B.lean"]:
            self.write("integrations/palomar/.lake/packages/mathlib/" + name,
                       (self.mathlib / name).read_text())
        return self.root / "integrations/palomar/.lake/packages/mathlib"

    def test_root_is_selected_and_cache_request_is_explicit(self):
        self.write("research/audits/Client.lean", "import Mathlib.B\n")
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B")
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root), 0)
        self.assertEqual(run.call_args.args[0], ["lake", "exe", "cache", "get", "Mathlib"])
        self.assertEqual(run.call_args.kwargs["cwd"], self.root / "formalization")

    def test_transitive_cache_gap_fails_even_if_root_exists(self):
        self.compile_modules("Mathlib", "Mathlib.A")
        with patch("cache_mathlib.subprocess.run"):
            with self.assertRaisesRegex(ValueError, "Mathlib.B"):
                prepare_cache(self.root)

    def test_check_only_never_fetches(self):
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B")
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root, check_only=True), 0)
        run.assert_not_called()

    def test_comments_do_not_request_aggregate_and_dotted_imports_stay_narrow(self):
        self.write("formalization/FunctionalInequalities.lean",
                   "/- import Mathlib -/\nimport Mathlib.A -- import Mathlib\n")
        self.assertEqual(list(mathlib_roots(self.root)), ["Mathlib.A"])
        self.assertEqual(required_modules(self.mathlib, ["Mathlib.A"]), {"Mathlib.A", "Mathlib.B"})

    def test_vendor_and_nested_audit_imports_are_included(self):
        self.write("formalization/vendor/Example/Lib.lean", "public import Mathlib.A\n")
        self.write("research/audits/nested/Client.lean", "import Mathlib.B\n")
        roots = mathlib_roots(self.root)
        self.assertIn("formalization/vendor/Example/Lib.lean", roots["Mathlib.A"])
        self.assertIn("research/audits/nested/Client.lean", roots["Mathlib.B"])

    def test_no_import_and_missing_pinned_source_fail_closed(self):
        self.write("formalization/FunctionalInequalities.lean", "import Lean\n")
        with self.assertRaisesRegex(ValueError, "No Mathlib imports"):
            mathlib_roots(self.root)
        with self.assertRaisesRegex(ValueError, "Pinned Mathlib source is missing"):
            required_modules(self.mathlib, ["Mathlib.Missing"])
        self.assertEqual(check_cache(self.mathlib, {"Mathlib.A"}), [("Mathlib.A", ".olean")])

    def test_module_sources_require_every_companion_artifact(self):
        # Module-system Mathlib sources: `.olean` alone is not a complete cache entry.
        self.write("formalization/.lake/packages/mathlib/Mathlib/A.lean",
                   "module\n\npublic import Mathlib.B\n")
        self.write("formalization/.lake/packages/mathlib/Mathlib/B.lean",
                   "/- Copyright -/\nmodule\n\nmeta import Lean\n")
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B")
        self.assertEqual(check_cache(self.mathlib, {"Mathlib", "Mathlib.A", "Mathlib.B"}), [
            ("Mathlib.A", ".olean.server"), ("Mathlib.A", ".olean.private"),
            ("Mathlib.A", ".ir.sig"), ("Mathlib.A", ".ir"),
            ("Mathlib.B", ".olean.server"), ("Mathlib.B", ".olean.private"),
            ("Mathlib.B", ".ir.sig"), ("Mathlib.B", ".ir")])
        with patch("cache_mathlib.subprocess.run"):
            with self.assertRaisesRegex(ValueError, r"8 artifacts missing for 2 of 3 modules.*"
                                                    r"Mathlib\.A \(\.olean\.server\)"):
                prepare_cache(self.root, check_only=True)
        self.compile_modules("Mathlib.A", suffixes=(".olean.server", ".olean.private", ".ir.sig", ".ir"))
        self.assertEqual(check_cache(self.mathlib, {"Mathlib.A", "Mathlib.B"}),
                         [("Mathlib.B", s) for s in (".olean.server", ".olean.private", ".ir.sig", ".ir")])
        self.compile_modules("Mathlib.B", suffixes=(".olean.server", ".olean.private", ".ir.sig", ".ir"))
        # Mixed: the legacy aggregate still needs only `.olean`.
        self.assertEqual(check_cache(self.mathlib, {"Mathlib", "Mathlib.A", "Mathlib.B"}), [])
        with patch("cache_mathlib.subprocess.run"):
            self.assertEqual(prepare_cache(self.root, check_only=True), 0)

    def test_missing_private_companion_alone_is_reported(self):
        self.write("formalization/.lake/packages/mathlib/Mathlib/B.lean", "module\n\npublic import Lean\n")
        self.compile_modules("Mathlib.B", suffixes=(".olean", ".olean.server", ".ir.sig", ".ir"))
        self.assertEqual(check_cache(self.mathlib, {"Mathlib.B"}), [("Mathlib.B", ".olean.private")])

    def test_unparsable_pinned_source_fails_closed(self):
        self.write("formalization/.lake/packages/mathlib/Mathlib/B.lean", "module\n\nimport\tLean\n")
        self.compile_modules("Mathlib.B")
        with self.assertRaisesRegex(ValueError, "Cannot classify pinned Mathlib source Mathlib.B"):
            check_cache(self.mathlib, {"Mathlib.B"})

    def test_complete_library_cache_does_not_hide_missing_bridge_cache(self):
        bridge_mathlib = self.add_bridge()
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B")
        self.compile_modules("Mathlib", "Mathlib.A", mathlib=bridge_mathlib)
        with patch("cache_mathlib.subprocess.run") as run:
            with self.assertRaisesRegex(ValueError, r"\[openai\].*Mathlib.B"):
                prepare_cache(self.root, project="all", check_only=True)
        run.assert_not_called()

    def test_bridge_fetch_and_check_use_its_own_package(self):
        bridge_mathlib = self.add_bridge()
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B", mathlib=bridge_mathlib)
        # The primary package has no compiled cache; the selected bridge does.
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root, project="openai"), 0)
        run.assert_called_once_with(["lake", "exe", "cache", "get", "Mathlib"],
                                    cwd=self.root / "integrations/openai", check=True)

    def test_bridge_roots_include_library_and_bridge_sources_only(self):
        self.add_bridge()
        self.write("formalization/FunctionalInequalities.lean", "import Mathlib.A\n")
        self.write("integrations/openai/OAI/Analysis/KLS/Model.lean", "import Mathlib.B\n")
        self.write("integrations/openai/Check.lean", "import Mathlib.C\n")
        self.write("integrations/openai/research/audits/Client.lean", "import Mathlib.D\n")
        self.write("integrations/openai/.lake/packages/Other/Client.lean", "import Mathlib.Decoy\n")
        self.write("integrations/openai/build/Client.lean", "import Mathlib.Decoy\n")
        roots = mathlib_roots(self.root, "openai")
        self.assertEqual(set(roots), {"Mathlib.A", "Mathlib.B", "Mathlib.C", "Mathlib.D"})
        self.assertEqual(set(mathlib_roots(self.root)), {"Mathlib.A"})

    def test_all_fetches_each_package_and_check_only_fetches_neither(self):
        bridge_mathlib = self.add_bridge()
        palomar_mathlib = self.add_palomar()
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B")
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B", mathlib=bridge_mathlib)
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B", mathlib=palomar_mathlib)
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root, project="all"), 0)
        self.assertEqual([call.kwargs["cwd"] for call in run.call_args_list],
                         [self.root / "formalization", self.root / "integrations/openai",
                          self.root / "integrations/palomar"])
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root, project="all", check_only=True), 0)
        run.assert_not_called()

    def test_palomar_roots_include_its_modules_bridge_and_library(self):
        self.add_bridge()
        self.add_palomar()
        self.write("formalization/FunctionalInequalities.lean", "module\n\npublic import Mathlib.A\n")
        self.write("integrations/openai/KLSOpenAI/Target.lean",
                   "module\n\npublic import Mathlib.B\nmeta import Mathlib.C\n")
        self.write("integrations/palomar/.lake/packages/Other/Client.lean", "import Mathlib.Decoy\n")
        roots = mathlib_roots(self.root, "palomar")
        self.assertEqual(set(roots), {"Mathlib", "Mathlib.A", "Mathlib.B", "Mathlib.C"})
        self.assertIn("integrations/palomar/Challenge.lean", roots["Mathlib"])
        self.assertIn("integrations/openai/KLSOpenAI/Target.lean", roots["Mathlib.C"])

    def test_palomar_fetch_and_check_use_its_own_package(self):
        self.add_bridge()
        palomar_mathlib = self.add_palomar()
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B", mathlib=palomar_mathlib)
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root, project="palomar"), 0)
        run.assert_called_once_with(["lake", "exe", "cache", "get", "Mathlib"],
                                    cwd=self.root / "integrations/palomar", check=True)

    def test_missing_or_unknown_project_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "project directory is missing"):
            prepare_cache(self.root, project="openai", check_only=True)
        with self.assertRaisesRegex(ValueError, "project directory is missing"):
            prepare_cache(self.root, project="palomar", check_only=True)
        with self.assertRaisesRegex(ValueError, "Unknown cache project"):
            prepare_cache(self.root, project="typo", check_only=True)


if __name__ == "__main__":
    unittest.main()
