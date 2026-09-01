"""Regression tests for the minimal Issue #2 ledger checker."""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "research_check_ledger", REPO / "research/check_ledger.py"
)
CHECKER = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(CHECKER)


class LedgerFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        (self.root / "research/a-series").mkdir(parents=True)
        (self.root / "formalization").mkdir()
        (self.root / "solutions").mkdir()
        self.ledger = self.root / "research/a-series/ledger.yaml"
        self.certificate = self.root / "solutions/LemLinearTestLower.lean"
        self.certificate.write_text(
            "/-! certificate for `lem:linear-test-lower` -/\n"
            "theorem certificate : True := by trivial\n",
            encoding="utf-8",
        )
        (self.root / "formalization/lakefile.toml").write_text(
            'name = "fixture"\n'
            'defaultTargets = ["Issue2Solutions"]\n\n'
            '[[lean_lib]]\n'
            'name = "Issue2Solutions"\n'
            'srcDir = ".."\n'
            'roots = ["solutions.LemLinearTestLower"]\n',
            encoding="utf-8",
        )
        self.document = {
            "meta": {"program": "a-series", "scope": "fixture"},
            "nodes": [
                {
                    "id": "lem:linear-test-lower",
                    "kind": "lemma",
                    "status": "proved",
                    "statement": "fixture statement",
                    "lean_solution": "solutions/LemLinearTestLower.lean",
                    "checked_by": "lean",
                }
            ],
        }
        self.write_ledger()

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def write_ledger(self) -> None:
        self.ledger.write_text(
            json.dumps(self.document, indent=2) + "\n", encoding="utf-8"
        )

    def errors(self) -> list[str]:
        errors, _document = CHECKER.check_ledger(root=self.root)
        return errors


class LedgerCheckerTests(LedgerFixture):
    def test_valid_fixture_passes(self) -> None:
        self.assertEqual(self.errors(), [])

    def test_invalid_json_compatible_yaml_fails_closed(self) -> None:
        self.ledger.write_text("nodes: [not-json]\n", encoding="utf-8")
        self.assertIn("cannot read JSON-compatible YAML ledger", "\n".join(self.errors()))

    def test_duplicate_node_id_is_rejected(self) -> None:
        self.document["nodes"].append(dict(self.document["nodes"][0]))
        self.write_ledger()
        self.assertIn("duplicate node id", "\n".join(self.errors()))

    def test_missing_issue2_node_is_rejected(self) -> None:
        self.document["nodes"] = []
        self.write_ledger()
        self.assertIn("required Issue #2 node is missing", "\n".join(self.errors()))

    def test_checked_by_lean_requires_proved_status(self) -> None:
        self.document["nodes"][0]["status"] = "conditional"
        self.write_ledger()
        self.assertIn("checked_by lean requires 'proved'", "\n".join(self.errors()))

    def test_certificate_must_exist(self) -> None:
        self.certificate.unlink()
        self.assertIn("artifact does not exist", "\n".join(self.errors()))

    def test_certificate_must_stay_under_solutions(self) -> None:
        self.document["nodes"][0]["lean_solution"] = "formalization/Certificate.lean"
        self.write_ledger()
        self.assertIn("must stay under solutions", "\n".join(self.errors()))

    def test_certificate_must_have_lean_suffix(self) -> None:
        text_certificate = self.root / "solutions/LemLinearTestLower.txt"
        text_certificate.write_text(
            self.certificate.read_text(encoding="utf-8"), encoding="utf-8"
        )
        self.document["nodes"][0]["lean_solution"] = "solutions/LemLinearTestLower.txt"
        self.write_ledger()
        self.assertIn("must have the .lean suffix", "\n".join(self.errors()))

    def test_certificate_header_must_name_node(self) -> None:
        self.certificate.write_text(
            "theorem certificate : True := by trivial\n", encoding="utf-8"
        )
        self.assertIn("certificate header does not name", "\n".join(self.errors()))

    def test_certificate_rejects_lean_escape_tokens(self) -> None:
        self.certificate.write_text(
            "/-! certificate for `lem:linear-test-lower` -/\n"
            "theorem certificate : True := by sorry\n",
            encoding="utf-8",
        )
        self.assertIn("forbidden Lean escape token", "\n".join(self.errors()))

    def test_certificate_must_be_in_default_lake_build(self) -> None:
        (self.root / "formalization/lakefile.toml").write_text(
            'name = "fixture"\n'
            'defaultTargets = ["FunctionalInequalities"]\n\n'
            '[[lean_lib]]\n'
            'name = "FunctionalInequalities"\n',
            encoding="utf-8",
        )
        self.assertIn("not a root of a default Lake target", "\n".join(self.errors()))

    def test_unknown_node_field_is_rejected(self) -> None:
        self.document["nodes"][0]["note"] = "unvalidated metadata"
        self.write_ledger()
        self.assertIn("unknown field: note", "\n".join(self.errors()))

    def test_production_cli_passes(self) -> None:
        result = subprocess.run(
            [sys.executable, str(REPO / "research/check_ledger.py")],
            cwd=REPO,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("0 error(s)", result.stdout)


if __name__ == "__main__":
    unittest.main()
