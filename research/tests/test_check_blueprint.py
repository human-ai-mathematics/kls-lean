"""Regression tests for the offline KLS Lean Blueprint checker."""
from __future__ import annotations

import copy
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
        self.chapter = self.chapters / "blueprint.tex"

        self.active_route_nodes = {
            "eldan-localization": [
                "ass:tight-prefix-carleson",
                "cor:tight-window-consumption",
            ],
            "moment-map-spectral": [
                "q:mm-spectral-occupation",
                "prop:spectral-sufficiency",
            ],
            "moment-map-cmh": [
                "ass:cmh-recovery-envelope",
                "cor:cmh-recovery-sequence-suffices",
            ],
            "conditional-fiber-frame": [
                "q:conditional-fiber-frame",
                "lem:conditional-fiber-form",
            ],
        }
        self.branch_ids = {
            "eldan-localization": "eldan-tight-prefix",
            "moment-map-spectral": "moment-map-spectral-full-damping",
            "moment-map-cmh": "moment-map-cmh-recovery",
            "conditional-fiber-frame": "conditional-fiber-frame",
        }
        shared = sorted(CHECKER.REQUIRED_SHARED_PREREQUISITES)
        claim_labels = [
            "conj:kls",
            *shared,
            *(node for nodes in self.active_route_nodes.values() for node in nodes),
            "ass:weighted-package",
            "prop:weighted-spectator-obstruction",
        ]
        route_labels = [
            *(f"route:{route}" for route in self.active_route_nodes),
            "route:eldan-weighted-package",
        ]

        blocks = [
            "\\begin{conjecture}\n\\label{conj:kls}\nKLS target\n\\end{conjecture}"
        ]
        blocks.extend(
            "\\begin{lemma}\n"
            f"\\label{{{label}}}\n"
            "claim\n"
            "\\end{lemma}"
            for label in claim_labels
            if label != "conj:kls"
        )
        blocks.extend(
            "\\begin{definition}\n"
            f"\\label{{{label}}}\n"
            "route\n"
            "\\end{definition}"
            for label in route_labels
        )
        blocks.extend(
            "\\begin{theorem}\n"
            f"\\label{{{label}}}\n"
            f"\\lean{{{declaration}}}\n"
            "\\leanok\n"
            "certified\n"
            "\\end{theorem}"
            for label, (_node_id, declaration) in CHECKER.CERTIFICATES.items()
        )
        self.chapter.write_text("\n".join(blocks) + "\n", encoding="utf-8")

        git_source = "kls-exploration"
        local_source = "kls-lean"
        local_path = "formalization/blueprint/src/chapters/blueprint.tex"

        def claim(
            node: str,
            state: str = "open",
            evidence: list[dict[str, object]] | None = None,
            *,
            local: bool = False,
            refuted_by: list[str] | None = None,
        ) -> dict[str, object]:
            value: dict[str, object] = {
                "node": node,
                "state": state,
                "provenance": (
                    {"source": local_source, "path": local_path}
                    if local
                    else {"source": git_source, "record": node}
                ),
                "evidence": evidence or [],
            }
            if refuted_by is not None:
                value["refuted_by"] = refuted_by
            return value

        review = [
            {
                "kind": "agent_review",
                "source": git_source,
                "artifact": "research/reviews/fixture.md",
            }
        ]
        claims = [
            claim("conj:kls"),
            *(claim(label, local=True) for label in shared),
            claim("ass:tight-prefix-carleson"),
            claim("cor:tight-window-consumption", "proved", review),
            claim("q:mm-spectral-occupation"),
            claim("prop:spectral-sufficiency", "conditional", review),
            claim("ass:cmh-recovery-envelope"),
            claim("cor:cmh-recovery-sequence-suffices", "conditional", review),
            claim("q:conditional-fiber-frame"),
            claim("lem:conditional-fiber-form", "proved", review),
            claim(
                "ass:weighted-package",
                "refuted",
                refuted_by=["prop:weighted-spectator-obstruction"],
            ),
            claim("prop:weighted-spectator-obstruction", "proved", review),
        ]
        branches: list[dict[str, object]] = []
        for route, nodes in self.active_route_nodes.items():
            branches.append(
                {
                    "id": self.branch_ids[route],
                    "route": route,
                    "disposition": "active",
                    "provenance": {
                        "source": git_source,
                        "path": f"research/kls/routes/{route}.md",
                    },
                    "requires": {
                        "operator": "all_of",
                        "items": [{"node": node} for node in nodes],
                    },
                }
            )
        branches.append(
            {
                "id": "eldan-weighted-package-v1",
                "route": "eldan-weighted-package",
                "disposition": "refuted",
                "provenance": {
                    "source": git_source,
                    "path": "modules/kls/20-eldan-statements.tex",
                },
                "requires": {"node": "ass:weighted-package"},
                "refuted_by": ["prop:weighted-spectator-obstruction"],
                "superseded_by": ["eldan-tight-prefix"],
            }
        )
        self.routes: dict[str, object] = {
            "version": 2,
            "sources": [
                {
                    "id": local_source,
                    "kind": "local",
                    "root": ".",
                    "ledger": "research/a-series/ledger.yaml",
                },
                {
                    "id": git_source,
                    "kind": "git",
                    "repository": CHECKER.PINNED_EXPLORATION_REPOSITORY,
                    "revision": CHECKER.PINNED_EXPLORATION_REVISION,
                    "ledger": "research/kls/ledger.yaml",
                },
            ],
            "claims": claims,
            "branches": branches,
            "targets": [
                {
                    "target": "conj:kls",
                    "prerequisites": {
                        "operator": "all_of",
                        "items": [{"node": label} for label in shared],
                    },
                    "composition": {
                        "operator": "any_of",
                        "items": [
                            {"branch": self.branch_ids[route]}
                            for route in self.active_route_nodes
                        ],
                    },
                }
            ],
        }
        self.ledger: dict[str, object] = {
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

    def summary(self) -> dict[str, int]:
        _errors, summary = CHECKER.check_blueprint(root=self.root)
        return summary

    def claim(self, node: str) -> dict[str, object]:
        return next(
            claim
            for claim in self.routes["claims"]  # type: ignore[index]
            if claim["node"] == node
        )

    def branch(self, branch_id: str) -> dict[str, object]:
        return next(
            branch
            for branch in self.routes["branches"]  # type: ignore[index]
            if branch["id"] == branch_id
        )

    def source(self, source_id: str) -> dict[str, object]:
        return next(
            source
            for source in self.routes["sources"]  # type: ignore[index]
            if source["id"] == source_id
        )

    def append_to_claim_block(self, node: str, text: str) -> None:
        document = self.chapter.read_text(encoding="utf-8")
        marker = f"\\label{{{node}}}\n"
        self.assertIn(marker, document)
        self.chapter.write_text(
            document.replace(marker, marker + text, 1), encoding="utf-8"
        )

    def use_v1_routes(self) -> None:
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
                        for route, nodes in CHECKER.V1_EXPECTED_ROUTES.items()
                    ],
                }
            ],
        }
        self.write_routes()


class BlueprintCheckerTests(BlueprintFixture):
    def test_valid_v2_fixture_passes(self) -> None:
        self.assertEqual(self.errors(), [])
        self.assertEqual(self.summary()["schema_version"], 2)
        self.assertEqual(self.summary()["routes"], 4)

    def test_v1_regression_fixture_passes(self) -> None:
        self.use_v1_routes()
        self.assertEqual(self.errors(), [])
        self.assertEqual(self.summary()["schema_version"], 1)

    def test_versions_are_exact_integers(self) -> None:
        for version in (True, 3, "2"):
            with self.subTest(version=version):
                self.routes["version"] = version
                self.write_routes()
                self.assertIn(
                    "routes.version must be the integer 1 or 2",
                    "\n".join(self.errors()),
                )

    def test_commented_commands_are_ignored(self) -> None:
        with self.chapter.open("a", encoding="utf-8") as stream:
            stream.write("% \\label{conj:kls}\n% \\uses{missing:commented}\n")
        self.assertEqual(self.errors(), [])

    def test_duplicate_labels_are_rejected(self) -> None:
        with self.chapter.open("a", encoding="utf-8") as stream:
            stream.write("\\label{conj:kls}\n")
        self.assertIn("duplicate Blueprint label conj:kls", "\n".join(self.errors()))

    def test_uses_must_reference_existing_labels(self) -> None:
        with self.chapter.open("a", encoding="utf-8") as stream:
            stream.write("\\uses{missing:dependency}\n")
        self.assertIn("\\uses references unknown label", "\n".join(self.errors()))

    def test_route_file_must_be_json_compatible_yaml(self) -> None:
        self.routes_path.write_text("version: 2\n", encoding="utf-8")
        self.assertIn("cannot read Blueprint route composition", "\n".join(self.errors()))

    def test_v2_schema_rejects_unknown_fields(self) -> None:
        self.routes["statement"] = "not registry data"
        self.claim("conj:kls")["lean"] = "Fake.claim"
        self.branch("eldan-tight-prefix")["status"] = "proved"
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("routes: unknown field: statement", errors)
        self.assertIn("routes.claims[0]: unknown field: lean", errors)
        self.assertIn("unknown field: status", errors)

    def test_sources_are_pinned_and_paths_are_safe(self) -> None:
        exploration = self.source("kls-exploration")
        exploration["revision"] = "8185e46"
        self.source("kls-lean")["ledger"] = "../outside.yaml"
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("full lowercase Git commit hash", errors)
        self.assertIn("must pin 8185e46", errors)
        self.assertIn("safe repository-relative path", errors)

    def test_sources_are_unique_and_references_must_exist(self) -> None:
        sources = self.routes["sources"]  # type: ignore[index]
        sources.append(copy.deepcopy(sources[0]))
        self.claim("conj:kls")["provenance"] = {
            "source": "missing-source",
            "record": "conj:kls",
        }
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("duplicate route source id: kls-lean", errors)
        self.assertIn("references unknown source missing-source", errors)

    def test_local_claim_path_must_contain_the_claim_label(self) -> None:
        self.claim("thm:affine-isotropic-reduction")["provenance"] = {
            "source": "kls-lean",
            "path": "research/a-series/ledger.yaml",
        }
        self.write_routes()
        self.assertIn(
            "path does not contain label thm:affine-isotropic-reduction",
            "\n".join(self.errors()),
        )

    def test_nested_recursive_expression_is_accepted(self) -> None:
        self.branch("eldan-tight-prefix")["requires"] = {
            "operator": "all_of",
            "items": [
                {"node": "ass:tight-prefix-carleson"},
                {
                    "operator": "any_of",
                    "items": [
                        {"node": "cor:tight-window-consumption"},
                        {"node": "prop:spectral-sufficiency"},
                    ],
                },
            ],
        }
        self.write_routes()
        self.assertEqual(self.errors(), [])

    def test_target_composition_accepts_nested_any_of_and_all_of(self) -> None:
        target = self.routes["targets"][0]  # type: ignore[index]
        target["composition"] = {
            "operator": "any_of",
            "items": [
                {
                    "operator": "all_of",
                    "items": [
                        {"branch": "eldan-tight-prefix"},
                        {"branch": "moment-map-spectral-full-damping"},
                    ],
                },
                {"branch": "moment-map-cmh-recovery"},
                {"branch": "conditional-fiber-frame"},
            ],
        }
        self.write_routes()
        self.assertEqual(self.errors(), [])

    def test_expressions_are_strict_tagged_unions(self) -> None:
        malformed = (
            {"operator": "all_of", "items": [{"node": "ass:tight-prefix-carleson"}]},
            {"node": "ass:tight-prefix-carleson", "branch": "eldan-tight-prefix"},
            {"operator": "some_of", "items": [{"node": "a"}, {"node": "b"}]},
        )
        baseline = copy.deepcopy(self.routes)
        for expression in malformed:
            with self.subTest(expression=expression):
                self.routes = copy.deepcopy(baseline)
                self.branch("eldan-tight-prefix")["requires"] = expression
                self.write_routes()
                self.assertTrue(self.errors())

    def test_expression_references_are_unique(self) -> None:
        self.branch("eldan-tight-prefix")["requires"] = {
            "operator": "all_of",
            "items": [
                {"node": "ass:tight-prefix-carleson"},
                {"node": "ass:tight-prefix-carleson"},
            ],
        }
        self.write_routes()
        self.assertIn("duplicate node reference", "\n".join(self.errors()))

    def test_claim_and_branch_ids_are_unique(self) -> None:
        claims = self.routes["claims"]  # type: ignore[index]
        branches = self.routes["branches"]  # type: ignore[index]
        claims.append(copy.deepcopy(claims[0]))
        branches.append(copy.deepcopy(branches[0]))
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("duplicate route claim node: conj:kls", errors)
        self.assertIn("duplicate route branch id: eldan-tight-prefix", errors)

    def test_claim_branch_and_route_labels_must_exist(self) -> None:
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace(
            "\\label{q:mm-spectral-occupation}", "\\label{q:missing}", 1
        )
        text = text.replace(
            "\\label{route:moment-map-cmh}", "\\label{route:missing}", 1
        )
        self.chapter.write_text(text, encoding="utf-8")
        errors = "\n".join(self.errors())
        self.assertIn("node references unknown label q:mm-spectral-occupation", errors)
        self.assertIn("unknown label route:moment-map-cmh", errors)

    def test_shared_prerequisites_are_registry_requirements_not_tex_uses(self) -> None:
        self.assertNotIn("\\uses", self.chapter.read_text(encoding="utf-8"))
        self.assertEqual(self.errors(), [])

    def test_kls_requires_both_shared_prerequisites(self) -> None:
        target = self.routes["targets"][0]  # type: ignore[index]
        target["prerequisites"] = {"node": "thm:affine-isotropic-reduction"}
        self.write_routes()
        self.assertIn("missing shared requirement", "\n".join(self.errors()))

    def test_non_active_branches_cannot_be_target_exits(self) -> None:
        target = self.routes["targets"][0]  # type: ignore[index]
        target["composition"]["items"][0] = {  # type: ignore[index]
            "branch": "eldan-weighted-package-v1"
        }
        self.write_routes()
        self.assertIn("references non-active branch", "\n".join(self.errors()))

    def test_every_active_branch_must_be_reachable(self) -> None:
        target = self.routes["targets"][0]  # type: ignore[index]
        target["composition"]["items"].pop()  # type: ignore[index]
        self.write_routes()
        self.assertIn("active branch is unreachable", "\n".join(self.errors()))

    def test_active_route_set_is_exactly_the_current_four(self) -> None:
        branch = copy.deepcopy(self.branch("eldan-tight-prefix"))
        branch["id"] = "unexpected-active"
        branch["route"] = "eldan-weighted-package"
        self.routes["branches"].append(branch)  # type: ignore[index]
        target = self.routes["targets"][0]  # type: ignore[index]
        target["composition"]["items"].append(  # type: ignore[index]
            {"branch": "unexpected-active"}
        )
        self.write_routes()
        self.assertIn("unexpected active route", "\n".join(self.errors()))

    def test_historical_and_refuted_branch_lifecycle_is_checked(self) -> None:
        branch = self.branch("eldan-weighted-package-v1")
        branch["disposition"] = "historical"
        branch.pop("superseded_by")
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("historical branches require superseded_by", errors)
        self.assertIn("historical branches cannot carry refuted_by", errors)

    def test_superseded_historical_branch_is_supported_but_unreachable(self) -> None:
        branch = self.branch("eldan-weighted-package-v1")
        branch["disposition"] = "historical"
        branch.pop("refuted_by")
        self.write_routes()
        self.assertEqual(self.errors(), [])

    def test_refuters_must_be_evidenced_proved_claims(self) -> None:
        refuter = self.claim("prop:weighted-spectator-obstruction")
        refuter["state"] = "open"
        refuter["evidence"] = []
        self.write_routes()
        self.assertIn("must be proved or imported with evidence", "\n".join(self.errors()))

    def test_active_branch_cannot_require_refuted_claim(self) -> None:
        self.branch("eldan-tight-prefix")["requires"] = {
            "operator": "all_of",
            "items": [
                {"node": "ass:weighted-package"},
                {"node": "cor:tight-window-consumption"},
            ],
        }
        self.write_routes()
        self.assertIn("active branch requires refuted claim", "\n".join(self.errors()))

    def test_kls_target_must_not_turn_all_or_exits_into_uses(self) -> None:
        nodes = [node for route in self.active_route_nodes.values() for node in route]
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace(
            "KLS target", "KLS target\n\\uses{" + ",".join(nodes) + "}", 1
        )
        self.chapter.write_text(text, encoding="utf-8")
        self.assertIn("must not encode every any_of route node", "\n".join(self.errors()))

    def test_kls_target_may_use_shared_prerequisites(self) -> None:
        shared = sorted(CHECKER.REQUIRED_SHARED_PREREQUISITES)
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace(
            "KLS target", "KLS target\n\\uses{" + ",".join(shared) + "}", 1
        )
        self.chapter.write_text(text, encoding="utf-8")
        self.assertEqual(self.errors(), [])

    def test_kls_target_must_not_use_refuted_claim(self) -> None:
        text = self.chapter.read_text(encoding="utf-8")
        text = text.replace(
            "KLS target", "KLS target\n\\uses{ass:weighted-package}", 1
        )
        self.chapter.write_text(text, encoding="utf-8")
        self.assertIn("must not use refuted claim", "\n".join(self.errors()))

    def test_agent_review_never_authorizes_leanok(self) -> None:
        self.append_to_claim_block("cor:tight-window-consumption", "\\leanok\n")
        self.assertIn(
            "\\leanok requires explicit local Lean evidence", "\n".join(self.errors())
        )

    def test_git_sources_cannot_supply_lean_evidence(self) -> None:
        target = self.claim("cor:tight-window-consumption")
        target["evidence"] = [
            {
                "kind": "lean",
                "source": "kls-exploration",
                "ledger_node": "route:fake",
                "declaration": "Fixture.fake",
            }
        ]
        self.append_to_claim_block(
            "cor:tight-window-consumption", "\\lean{Fixture.fake}\n\\leanok\n"
        )
        self.write_routes()
        self.assertIn("Lean evidence source must be local", "\n".join(self.errors()))

    def test_local_lean_evidence_requires_ledger_tex_and_leanok(self) -> None:
        target = self.claim("cor:tight-window-consumption")
        target["evidence"] = [
            {
                "kind": "lean",
                "source": "kls-lean",
                "ledger_node": "route:tight-window",
                "declaration": "Fixture.tightWindow",
            }
        ]
        self.ledger["nodes"].append(  # type: ignore[index]
            {
                "id": "route:tight-window",
                "status": "proved",
                "checked_by": "lean",
            }
        )
        self.append_to_claim_block(
            "cor:tight-window-consumption",
            "\\lean{Fixture.tightWindow}\n\\leanok\n",
        )
        self.write_routes()
        self.write_ledger()
        self.assertEqual(self.errors(), [])

        node = self.ledger["nodes"][-1]  # type: ignore[index]
        node["checked_by"] = "agent"
        self.write_ledger()
        self.assertIn("checked_by 'lean'", "\n".join(self.errors()))

    def test_claim_state_and_evidence_are_orthogonal_but_consistent(self) -> None:
        self.claim("ass:tight-prefix-carleson")["evidence"] = [
            {
                "kind": "agent_review",
                "source": "kls-exploration",
                "artifact": "research/reviews/fixture.md",
            }
        ]
        self.claim("cor:tight-window-consumption")["evidence"] = []
        self.write_routes()
        errors = "\n".join(self.errors())
        self.assertIn("open claims must not carry proof evidence", errors)
        self.assertIn("proved claims require explicit evidence", errors)

    def test_imported_claims_require_published_evidence(self) -> None:
        target = self.claim("cor:tight-window-consumption")
        target["state"] = "imported"
        self.write_routes()
        self.assertIn("imported claims require published evidence", "\n".join(self.errors()))

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
        self.chapter.write_text(
            text.replace(needle, needle.replace("\\leanok\n", "")), encoding="utf-8"
        )
        self.assertIn("certified statement must contain \\leanok", "\n".join(self.errors()))

    def test_certificate_requires_lean_certified_ledger_node(self) -> None:
        node = next(
            node
            for node in self.ledger["nodes"]  # type: ignore[index]
            if node["id"] == "lem:linear-test-lower"
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
