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

    def compile_modules(self, *names, mathlib=None):
        mathlib = self.mathlib if mathlib is None else mathlib
        for name in names:
            path = mathlib / ".lake/build/lib/lean" / Path(*name.split("."))
            path = path.with_suffix(".olean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"fixture")

    def add_bridge(self):
        self.write("integrations/openai/OAI/Analysis/KLS/Model.lean", "import Mathlib\n")
        for name in ["Mathlib.lean", "Mathlib/A.lean", "Mathlib/B.lean"]:
            self.write("integrations/openai/.lake/packages/mathlib/" + name,
                       (self.mathlib / name).read_text())
        return self.root / "integrations/openai/.lake/packages/mathlib"

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
        self.assertEqual(check_cache(self.mathlib, {"Mathlib.A"}), ["Mathlib.A"])

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
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B")
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B", mathlib=bridge_mathlib)
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root, project="all"), 0)
        self.assertEqual([call.kwargs["cwd"] for call in run.call_args_list],
                         [self.root / "formalization", self.root / "integrations/openai"])
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root, project="all", check_only=True), 0)
        run.assert_not_called()

    def test_missing_or_unknown_project_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "project directory is missing"):
            prepare_cache(self.root, project="openai", check_only=True)
        with self.assertRaisesRegex(ValueError, "Unknown cache project"):
            prepare_cache(self.root, project="typo", check_only=True)


if __name__ == "__main__":
    unittest.main()
