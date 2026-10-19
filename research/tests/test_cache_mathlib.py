"""Regress the aggregate import omission that caused CI to source-build Mathlib."""
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

    def compile_modules(self, *names):
        for name in names:
            path = self.mathlib / ".lake/build/lib/lean" / Path(*name.split("."))
            path = path.with_suffix(".olean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"fixture")

    def test_root_is_selected_and_cache_request_is_explicit(self):
        self.write("research/audits/Client.lean", "import Mathlib.B\n")
        self.compile_modules("Mathlib", "Mathlib.A", "Mathlib.B")
        with patch("cache_mathlib.subprocess.run") as run:
            self.assertEqual(prepare_cache(self.root), 0)
        self.assertEqual(run.call_args.args[0], ["lake", "exe", "cache", "get", "Mathlib"])

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


if __name__ == "__main__":
    unittest.main()
