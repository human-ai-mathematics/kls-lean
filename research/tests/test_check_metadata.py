"""Metadata mutations that must fail before a Lean build or submission attempt."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_metadata import (METADATA_FILES, SCHEMA_DIR, SCHEMA_FILE, check_document,
                            check_metadata, schema_validator)
import yaml

ROOT = Path(__file__).resolve().parents[2]


class MetadataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.validator = schema_validator(ROOT)
        cls.source = (ROOT / "formalization.yaml").read_text(encoding="utf-8")

    def errors(self, text):
        return "\n".join(check_document(text, self.validator))

    def test_all_repository_documents_pass(self):
        self.assertEqual(check_metadata(ROOT), [])

    def test_unquoted_msc_reproduces_the_yaml_parser_disagreement(self):
        text = self.source.replace('["60E15", "46E35"]', '[60E15, 46E35]')
        # YAML 1.1 accepts these as strings; the browser's YAML 1.2 parser uses numbers.
        self.assertEqual(yaml.safe_load(text)["classification"]["msc2020"], ["60E15", "46E35"])
        self.assertIn("quote MSC codes", self.errors(text))

    def test_contained_palomar_codes_are_checked_too(self):
        text = (ROOT / METADATA_FILES[2]).read_text().replace('"52A40"', '52A40')
        self.assertIn("quote MSC codes", self.errors(text))

    def test_single_quotes_block_lists_and_hyphenated_codes_are_portable(self):
        text = self.source.replace('["60E15", "46E35"]', "\n    - '60E15'\n    - '00-01'")
        self.assertEqual(check_document(text, self.validator), [])

    def test_schema_rejects_wrong_types_and_missing_fields(self):
        for old, new, expected in [("authors: [kls-lean contributors]", "authors: 42", "project.authors"),
                                   ("review:", "misspelled_review:", "required property")]:
            with self.subTest(expected=expected):
                self.assertIn(expected, self.errors(self.source.replace(old, new, 1)))

    def test_version_and_msc_format_fail_closed(self):
        self.assertIn("reviewed v0.4", self.errors(self.source.replace("version: v0.4", "version: v0.3")))
        self.assertIn("five-character MSC2020", self.errors(self.source.replace('"60E15"', '"60E1"')))

    def test_duplicate_and_non_string_keys_are_rejected(self):
        for text, expected in [(self.source + "\nversion: v0.4\n", "duplicate metadata key"),
                               (self.source + "\ntrue: invalid\n", "keys must be strings")]:
            with self.subTest(expected=expected):
                self.assertIn(expected, self.errors(text))

    def test_non_json_scalars_and_recursive_aliases_are_rejected(self):
        for value in ["2026-11-01", ".nan", "&cycle [*cycle]"]:
            with self.subTest(value=value):
                self.assertIn("invalid metadata YAML", self.errors(self.source + f"\nextra: {value}\n"))

    def test_empty_malformed_and_unsafe_yaml_are_rejected(self):
        for text in ["", "project: [", "!!python/object:builtins.object {}"]:
            with self.subTest(text=text):
                self.assertTrue(check_document(text, self.validator))

    def test_missing_document_and_changed_schema_fail_offline(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            shutil.copytree(ROOT / SCHEMA_DIR, root / SCHEMA_DIR)
            for name in METADATA_FILES:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / name, target)
            (root / METADATA_FILES[1]).unlink()
            self.assertIn(METADATA_FILES[1], "\n".join(check_metadata(root)))
            schema = root / SCHEMA_DIR / SCHEMA_FILE
            schema.write_text(json.dumps({"type": "object"}))
            self.assertIn("provenance hash differs", "\n".join(check_metadata(root)))


if __name__ == "__main__":
    unittest.main()
