"""Regression tests for the offline KLS Lean Blueprint checker."""
from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "research_check_blueprint", REPO / "research/check_blueprint.py"
)
CHECKER = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = CHECKER
SPEC.loader.exec_module(CHECKER)


class BlueprintFixture(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.chapters = self.root / "formalization/blueprint/src/chapters"
        self.chapters.mkdir(parents=True)
        (self.root / "research/a-series").mkdir(parents=True)
        self.routes_path = self.root / "formalization/blueprint/route-composition.yaml"
        self.ledger_path = self.root / "research/a-series/ledger.yaml"

        route_labels = "\n".join(
            f"\\begin{{definition}}\\label{{route:{route}}}route\\end{{definition}}"
            for route in CHECKER.EXPECTED_ROUTES
        )
        node_labels = "\n".join(
            f"\\begin{{lemma}}\\label{{{node}}}node\\end{{lemma}}"
            for nodes in CHECKER.EXPECTED_ROUTES.values()
            for node in nodes
        )
        certificate_blocks = "\n".join(
            "\\begin{theorem}\n"
            f"\\label{{{label}}}\n"
            f"\\lean{{{declaration}}}\n"
            "\\leanok\n"
            "certified\n"
            "\\end{theorem}"
            for label, (_node_id, declaration) in CHECKER.CERTIFICATES.items()
        )
        self.chapter = self.chapters / "blueprint.tex"
        self.chapter.write_text(
            "\\begin{conjecture}\n"
            "\\label{conj:kls}\n"
            "KLS target\n"
            "\\end{conjecture}\n"
            + route_labels
            + "\n"
            + node_labels
            + "\n"
            + certificate_blocks
            + "\n",
            encoding="utf-8",
        )

        self.routes = {
            "version": 1,
            "targets": [
                {
                    "target": "conj:kls",
                    "operator": "any_of",
                    "alternatives": [
                        {
                            "route": route,
                            "operator": "all_of",
                            "nodes": list(nodes),
                        }
                        for route, nodes in CHECKER.EXPECTED_ROUTES.items()
                    ],
                }
            ],
        }
        self.ledger = {
            "meta": {"program": "a-series", "scope": "fixture"},
            "nodes": [
                {
                    "id": node_id,
                    "kind": "lemma",
                    "status": "proved",
                    "statement": "fixture",
                    "lean_solution": "solutions/Fixture.lean",
                    "checked_by": "lean",
                }
                for node_id, _declaration in CHECKER.CERTIFICATES.values()
            ],
        }
        self.write_routes()
        self.write_ledger()

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def write_routes(self) -> None:
        self.routes_path.write_text(
            json.dumps(self.routes, indent=2) + "\n", encoding="utf-8"
        )

    def write_ledger(self) -> None:
        self.ledger_path.write_text(
            json.dumps(self.ledger, indent=2) + "\n", encoding="utf-8"
        )

    def errors(self) -> list[str]:
        errors, _summary = CHECKER.check_blueprint(root=self.root)
        return errors


class BlueprintCheckerTests(BlueprintFixture):
    def test_valid_fixture_passes(self) -> None:
        self.assertEqual(self.errors(), [])

    def test_commented_commands_are_ignored(self) -> None:
        with self.chapter.open("a", encoding="utf-8") as stream:
            stream.write("% \\label{conj:kls}\n% \\uses{missing:commented}\n")
        self.assertEqual(self.errors(), [])

    def test_duplicate_labels_are_rejected(self) -> None:
        with self.chapter.open("a", encoding="utf-8") as stream:
            stream.write("\\label{conj:kls}\n")
        self.assertIn("duplicate Blueprint label conj:kls", "\n".join(self.errors()))

    def test_uses_must_reference_an_existing_label(self) -> None:
        with self.chapter.open("a", encoding="utf-8") as stream:
            stream.write("\\uses{missing:dependency}\n")
        self.assertIn("\\uses references unknown label", "\n".join(self.errors()))

    def test_route_file_must_be_json_compatible_yaml(self) -> None:
        self.routes_path.write_text("version: 1\n", encoding="utf-8")
        self.assertIn("cannot read Blueprint route composition", "\n".join(self.errors()))

    def test_route_schema_rejects_metadata_fields(self) -> None:
        self.routes["statement"] = "KLS prose does not belong here"
        self.routes["targets"][0]["status"] = "open"
        self.routes["targets"][0]["alternatives"][0]["lean"] = "Fake.theorem"
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("routes: unknown field: statement", errors)
        self.assertIn("routes.targets[0]: unknown field: status", errors)
        self.assertIn("unknown field: lean", errors)

    def test_route_target_is_one_any_of_kls_object(self) -> None:
        self.routes["targets"][0]["target"] = "conj:other"
        self.routes["targets"][0]["operator"] = "all_of"
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("target must be 'conj:kls'", errors)
        self.assertIn("operator must be 'any_of'", errors)

    def test_alternatives_are_all_of_with_exact_approved_nodes(self) -> None:
        alternative = self.routes["targets"][0]["alternatives"][0]
        alternative["operator"] = "any_of"
        alternative["nodes"] = ["prop:spectral-sufficiency"]
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("operator must be 'all_of'", errors)
        self.assertIn("nodes must be exactly", errors)

    def test_routes_and_nodes_must_be_unique(self) -> None:
        alternatives = self.routes["targets"][0]["alternatives"]
        alternatives[1]["route"] = alternatives[0]["route"]
        alternatives[2]["nodes"] = list(alternatives[1]["nodes"])
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("duplicate Blueprint route", errors)
        self.assertIn("route node appears in more than one alternative", errors)

    def test_route_and_node_labels_must_exist_in_tex(self) -> None:
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace("\\label{route:moment-map-cmh}", "\\label{route:missing}")
        text = text.replace(
            "\\label{cor:cmh-recovery-sequence-suffices}",
            "\\label{cor:missing}",
        )
        self.chapter.write_text(text, encoding="utf-8")
        errors = "\n".join(self.errors())
        self.assertIn("unknown label route:moment-map-cmh", errors)
        self.assertIn("unknown label cor:cmh-recovery-sequence-suffices", errors)

    def test_kls_target_must_not_turn_all_routes_into_uses(self) -> None:
        nodes = [node for route in CHECKER.EXPECTED_ROUTES.values() for node in route]
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace(
            "KLS target",
            "KLS target\n\\uses{" + ",".join(nodes) + "}",
        )
        self.chapter.write_text(text, encoding="utf-8")
        self.assertIn("must not encode every any_of route node", "\n".join(self.errors()))

    def test_each_certificate_has_its_exact_lean_mapping(self) -> None:
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace(
            "Solutions.LemLinearTestLower.certificate",
            "Solutions.NotTheCertificate.certificate",
        )
        self.chapter.write_text(text, encoding="utf-8")
        self.assertIn(
            "\\lean must name Solutions.LemLinearTestLower.certificate",
            "\n".join(self.errors()),
        )

    def test_certificate_claim_requires_leanok(self) -> None:
        text = self.chapter.read_text(encoding="utf-8")
        needle = (
            "\\label{cert:linear-test-lower}\n"
            "\\lean{Solutions.LemLinearTestLower.certificate}\n"
            "\\leanok\n"
        )
        self.chapter.write_text(text.replace(needle, needle.replace("\\leanok\n", "")), encoding="utf-8")
        self.assertIn("certified statement must contain \\leanok", "\n".join(self.errors()))

    def test_certificate_claim_requires_lean_certified_ledger_node(self) -> None:
        node = next(
            node for node in self.ledger["nodes"] if node["id"] == "lem:linear-test-lower"
        )
        node.update(status="frozen", checked_by=None)
        self.write_ledger()
        self.assertIn(
            "must have status 'proved' and checked_by 'lean'",
            "\n".join(self.errors()),
        )

    def test_all_four_certificate_labels_are_required(self) -> None:
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace(
            "\\label{cert:gaussian-one-dimensional}",
            "\\label{cert:gaussian-omitted}",
        )
        self.chapter.write_text(text, encoding="utf-8")
        self.assertIn(
            "missing certified result label: cert:gaussian-one-dimensional",
            "\n".join(self.errors()),
        )


if __name__ == "__main__":
    unittest.main()
