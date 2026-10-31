"""Regressions for the shared Lean module-header parser (research/lean_header.py); no Lean runs."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_header import HeaderError, LeanImport, nonmodule_client, parse_header  # noqa: E402


class HeaderGrammarTests(unittest.TestCase):
    def test_every_directive_form_is_an_edge_with_its_modifiers(self):
        source = ("/- Copyright (c) 2026. Released under Apache 2.0. -/\n"
                  "module\n\n"
                  "import A.Plain\n"
                  "public import A.Public\n"
                  "meta import A.Meta\n"
                  "public meta import A.PublicMeta\n"
                  "import all A.All\n"
                  "meta import all A.MetaAll -- trailing comment\n\n"
                  "/-! # Title\nimport Fake.InDoc\n-/\n\n"
                  "@[expose] public section\n\ndef x := \"import Fake.InString\"\n")
        header = parse_header(source)
        self.assertTrue(header.is_module)
        self.assertFalse(header.prelude)
        self.assertEqual(header.imports, (
            LeanImport("A.Plain"), LeanImport("A.Public", public=True), LeanImport("A.Meta", meta=True),
            LeanImport("A.PublicMeta", public=True, meta=True), LeanImport("A.All", all=True),
            LeanImport("A.MetaAll", meta=True, all=True)))
        self.assertEqual([i.directive() for i in header.imports[3:5]],
                         ["public meta import A.PublicMeta", "import all A.All"])
        self.assertTrue(source[header.end:].startswith(" -- trailing comment\n"))

    def test_newline_and_comment_trivia_before_the_first_module(self):
        # Lean's keywordCore consumes whitespace after each keyword (ParseImportsFast.lean:123).
        cases = {
            "module\nimport /-\n  header comment\n-/ Mathlib\n": LeanImport("Mathlib"),
            "module\nimport\n  A.B\n": LeanImport("A.B"),
            "module\nimport all\n  /- a /- nested -/ b -/\n  -- line\n  A.B\n": LeanImport("A.B", all=True),
            "module\nimport -- c\n  all\n  A.B\n": LeanImport("A.B", all=True),
            "module\npublic\n  meta /- c -/\n import\n A.B\n": LeanImport("A.B", public=True, meta=True),
            "import\n  Legacy.A\n": LeanImport("Legacy.A"),
        }
        for source, expected in cases.items():
            with self.subTest(source=source):
                self.assertEqual(parse_header(source).imports, (expected,))

    def test_legacy_multiple_modules_only_on_the_first_modules_line(self):
        self.assertEqual(parse_header("import\n  A B\nimport C\n").modules, ["A", "B", "C"])
        # A name on a later line is not part of the directive (Lean reads one module per import).
        self.assertEqual(parse_header("import A\n  B\n").modules, ["A"])

    def test_legacy_file_without_module(self):
        header = parse_header("import Mathlib\nimport A.B C.D\n\nnamespace X\nend X\n")
        self.assertFalse(header.is_module)
        self.assertEqual(header.modules, ["Mathlib", "A.B", "C.D"])
        self.assertEqual(parse_header("namespace Leaf\n").modules, [])
        self.assertEqual(parse_header("").modules, [])

    def test_module_without_imports_and_section_or_meta_bodies(self):
        for body in ("public section\n", "@[expose] public section\n", "meta def f := 1\n",
                     "public meta def f := 1\n", "private def f := 1\n", "noncomputable section\n"):
            with self.subTest(body=body):
                header = parse_header("module\n\npublic import A\n\n" + body)
                self.assertEqual(header.modules, ["A"])
                self.assertTrue(header.is_module)

    def test_prelude_and_module(self):
        header = parse_header("module\n\nprelude\npublic import Init.Prelude\n")
        self.assertTrue(header.is_module and header.prelude)
        self.assertEqual(header.modules, ["Init.Prelude"])

    def test_fail_closed_forms(self):
        for source in ("public import A\n",             # modifier without `module`
                       "meta import A\n", "import all A\n",
                       "module\npublic import all A\n",  # `all` with `public import`
                       "module\npublic\n", "module\nimport all\n",
                       "module\nimport\n/-! doc -/ A\n",  # doc comments are tokens, not trivia
                       "module\nimport\tA\n",              # tabs are rejected like Lean does
                       "module\nimport /- open\nA\n", "module\npublic\n\n",
                       "import A.\n", "import A, B\n", "import «A B»\n",
                       "/- never closed\nimport A\n",
                       "import A\nmodule\n",              # `module` after imports
                       "module\nimport A\nprivate import B\n",
                       "module\nimport A\nmeta public import B\n"):
            with self.subTest(source=source), self.assertRaises(HeaderError):
                parse_header(source)


class NonModuleClientTests(unittest.TestCase):
    def test_module_driver_becomes_a_plain_import_root(self):
        driver = "module\n\npublic import Lean\npublic meta import Lean\n\n/-! d -/\n\n@[expose] public section\n"
        client = nonmodule_client(driver, ["X.Y"], allowed={"Lean"})
        self.assertEqual(client, "import X.Y\nimport Lean\n\n/-! d -/\n\n@[expose] public section\n")
        self.assertFalse(parse_header(client).is_module)

    def test_driver_imports_are_restricted(self):
        with self.assertRaises(HeaderError):
            nonmodule_client("module\n\npublic import Lean\npublic import Other\n", [], allowed={"Lean"})
        with self.assertRaises(HeaderError):
            nonmodule_client("prelude\nimport Init\n", [], allowed={"Init"})


if __name__ == "__main__":
    unittest.main()
