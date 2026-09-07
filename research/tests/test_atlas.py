"""Task-graph regressions: preserve conditionality, provenance and evidence freshness."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import atlas
from verify import parse_axioms, prepare_replay


def node(name, *, deps=(), recorded=False, declarations=(), mathematics="local_argument", assumptions=()):
    result = {"id": name, "kind": "theorem", "dependencies": list(deps),
            "statement_question": False,
            "lean": {"recorded": recorded, "declarations": list(declarations)},
            "task": {"mathematics": mathematics, "assumptions": list(assumptions),
                     "evidence": ["blueprint:" + name], "note": "fixture", "priority": 0}}
    if mathematics in {"local_argument", "published"}:
        result["task"]["infrastructure"] = {"status": "available",
            "mathlib_revision": atlas.mathlib_revision(atlas.ROOT),
            "evidence": [{"path": "examples/PoincareFoundation.lean", "sha256":
                atlas.hashlib.sha256((atlas.ROOT / "examples/PoincareFoundation.lean").read_bytes()).hexdigest()}],
            "gaps": []}
    return result


class SchedulingTests(unittest.TestCase):
    def test_agent_review_does_not_satisfy_a_lean_dependency(self):
        nodes = {"A": node("A"), "B": node("B", deps=["A"])}
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["B"]["dispatch"]["action"], "blocked")

    def test_open_premise_may_be_retained_but_not_discharged(self):
        nodes = {"A": node("A", mathematics="conjectural", declarations=["A"]),
                 "B": node("B", deps=["A"], assumptions=["A"])}
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["A"]["dispatch"]["action"], "research")
        self.assertEqual(nodes["B"]["dispatch"]["action"], "formalize_conditional")
        self.assertEqual(nodes["B"]["dispatch"]["retained_assumptions"], ["A"])

    def test_conditional_proof_still_needs_the_premise_type(self):
        nodes = {"A": node("A", mathematics="conjectural"),
                 "B": node("B", deps=["A"], assumptions=["A"])}
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["B"]["dispatch"]["action"], "blocked")
        self.assertIn("statement, not a proof", nodes["B"]["dispatch"]["blockers"][0]["reason"])

    def test_certified_implication_cannot_silently_close_its_unconditional_consumer(self):
        nodes = {"A": node("A", mathematics="conjectural", declarations=["A"]),
                 "B": node("B", deps=["A"], assumptions=["A"], recorded=True),
                 "C": node("C", deps=["B"])}
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["B"]["dispatch"]["action"], "complete")
        self.assertEqual(nodes["C"]["dispatch"]["action"], "blocked")
        self.assertEqual(nodes["C"]["dispatch"]["blockers"][0]["node"], "A")

    def test_refuted_and_unresolved_statements_do_not_enter_proof_search(self):
        nodes = {"A": node("A", mathematics="refuted"), "B": node("B")}
        nodes["B"]["statement_question"] = True
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["A"]["dispatch"]["action"], "excluded")
        self.assertEqual(nodes["B"]["dispatch"]["action"], "clarify_statement")

    def test_stale_evidence_cannot_complete_or_dispatch_annotated_nodes(self):
        nodes = {"A": node("A", recorded=True), "B": node("B", deps=["A"])}
        atlas.schedule(nodes, verified=False)
        self.assertEqual(nodes["A"]["dispatch"]["action"], "verify_recorded")
        self.assertEqual(nodes["B"]["dispatch"]["action"], "verify_prerequisites")

    def test_infrastructure_is_separate_from_proof_and_dependency_state(self):
        nodes = {"A": node("A"), "B": node("B", deps=["A"]),
                 "C": node("C", mathematics="conjectural"), "D": node("D", recorded=True)}
        for n in nodes.values():
            n["task"]["infrastructure"] = {"status": "missing", "gaps": ["adapter"]}
        atlas.schedule(nodes, verified=False)
        self.assertEqual(nodes["A"]["dispatch"]["action"], "develop_infrastructure")
        self.assertEqual(nodes["A"]["dispatch"]["verification"], "required")
        self.assertEqual(nodes["B"]["dispatch"]["action"], "blocked")
        self.assertEqual(nodes["B"]["dispatch"]["infrastructure"]["gaps"], ["adapter"])
        self.assertEqual(nodes["C"]["dispatch"]["action"], "research")
        self.assertEqual(nodes["D"]["dispatch"]["action"], "verify_recorded")

    def test_unchecked_infrastructure_never_implies_ready(self):
        nodes = {"A": node("A")}
        nodes["A"]["task"]["infrastructure"]["status"] = "unchecked"
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["A"]["dispatch"]["action"], "inspect_infrastructure")

    def test_conditional_task_keeps_its_premise_during_infrastructure_work(self):
        nodes = {"A": node("A", mathematics="conjectural", declarations=["A"]),
                 "B": node("B", deps=["A"], assumptions=["A"])}
        nodes["B"]["task"]["infrastructure"]["status"] = "missing"
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["B"]["dispatch"]["action"], "develop_infrastructure")
        self.assertEqual(nodes["B"]["dispatch"]["retained_assumptions"], ["A"])


class GraphTests(unittest.TestCase):
    def test_definition_can_opt_into_infrastructure_without_changing_mathematics(self):
        nodes = {"A": node("A", mathematics="definition")}
        tasks = {"version": 2, "policy": {"max_attempts": 3, "on_exhaustion": "reclassify"},
                 "nodes": {"A": copy.deepcopy(nodes["A"]["task"])}}
        self.assertEqual(atlas.validate_tasks(tasks, nodes), [])
        meta = tasks["nodes"]["A"]
        meta["infrastructure"] = copy.deepcopy(node("infra")["task"]["infrastructure"])
        meta["infrastructure"].update(status="missing", gaps=["L2 representative independence"])
        self.assertEqual(atlas.validate_tasks(tasks, nodes), [])
        nodes["A"]["task"] = meta
        atlas.schedule(nodes, verified=True)
        self.assertEqual(nodes["A"]["dispatch"]["action"], "develop_infrastructure")
        self.assertEqual(meta["mathematics"], "definition")
        self.assertFalse(nodes["A"]["lean"]["recorded"])

    def test_definition_infrastructure_uses_the_same_evidence_validation(self):
        nodes = {"A": node("A", mathematics="definition")}
        meta = copy.deepcopy(nodes["A"]["task"])
        meta["infrastructure"] = copy.deepcopy(node("infra")["task"]["infrastructure"])
        tasks = {"version": 2, "policy": {"max_attempts": 3, "on_exhaustion": "reclassify"},
                 "nodes": {"A": meta}}
        meta["infrastructure"]["evidence"][0]["sha256"] = "stale"
        self.assertIn("stale infrastructure evidence", "\n".join(atlas.validate_tasks(tasks, nodes)))
        meta["unexpected"] = True
        self.assertIn("require exactly", "\n".join(atlas.validate_tasks(tasks, nodes)))

    def test_published_tasks_still_require_infrastructure(self):
        nodes = {"A": node("A", mathematics="published")}
        meta = copy.deepcopy(nodes["A"]["task"])
        del meta["infrastructure"]
        tasks = {"version": 2, "policy": {"max_attempts": 3, "on_exhaustion": "reclassify"},
                 "nodes": {"A": meta}}
        self.assertIn("require exactly", "\n".join(atlas.validate_tasks(tasks, nodes)))

    def test_cycle_reports_the_concrete_path(self):
        self.assertEqual(atlas.cycle_errors({"A": ["B"], "B": ["C"], "C": ["A"]}),
                         ["dependency cycle: A -> B -> C -> A"])

    def test_diamond_is_not_a_cycle(self):
        self.assertEqual(atlas.cycle_errors({"A": ["B", "C"], "B": ["D"], "C": ["D"], "D": []}), [])

    def test_proof_dependencies_belong_to_the_preceding_statement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            chapter = root / "formalization/blueprint/src/chapters/a.tex"
            chapter.parent.mkdir(parents=True)
            chapter.write_text(r"""\chapter{A}\label{chap:a}
\begin{theorem}\label{thm:a}\lean{A}\leanok Statement.\end{theorem}
\begin{proof}\leanok\uses{lem:b} Proof.\end{proof}
\begin{lemma}\label{lem:b} Other statement.\end{lemma}
""")
            nodes, errors = atlas.parse_nodes(root)
            self.assertEqual(errors, [])
            self.assertEqual(set(nodes), {"thm:a", "lem:b"})
            self.assertEqual(nodes["thm:a"]["dependencies"], ["lem:b"])
            self.assertTrue(nodes["thm:a"]["proof_leanok"])
            self.assertIsNone(nodes["lem:b"]["proof_text"])

    def test_unclassified_node_fails_closed(self):
        tasks = {"version": 2, "policy": {"max_attempts": 3, "on_exhaustion": "reclassify"}, "nodes": {}}
        errors = atlas.validate_tasks(tasks, {"A": node("A")})
        self.assertIn("explicit classification", "\n".join(errors))

    def test_proved_dependency_cannot_be_silently_relabelled_as_an_assumption(self):
        nodes = {"A": node("A", recorded=True), "B": node("B", deps=["A"], assumptions=["A"])}
        tasks = {"version": 2, "policy": {"max_attempts": 3, "on_exhaustion": "reclassify"},
                 "nodes": {"B": copy.deepcopy(nodes["B"]["task"])}}
        self.assertIn("not an explicit assumption", "\n".join(atlas.validate_tasks(tasks, nodes)))

    def test_existing_route_or_and_adapters_are_preserved_without_becoming_proof_edges(self):
        root = Path(__file__).resolve().parents[2]
        data, errors = atlas.build_atlas(root)
        self.assertEqual(errors, [])
        target = next(t for t in data["targets"] if t["target"] == "conj:kls")
        self.assertEqual(target["composition"]["operator"], "any_of")
        self.assertEqual(target["adapters"]["operator"], "all_of")
        self.assertNotIn("thm:selected-literature-constant-equivalence", data["nodes"]["conj:kls"]["dependencies"])
        self.assertEqual(data["nodes"]["ass:weighted-package"]["dispatch"]["action"], "excluded")


class EvidenceTests(unittest.TestCase):
    def test_infrastructure_evidence_requires_current_sources_and_pin(self):
        meta = node("A")["task"]["infrastructure"]
        self.assertEqual(atlas.validate_infrastructure(meta, atlas.ROOT), [])
        meta["mathlib_revision"] = "old"
        meta["evidence"][0]["sha256"] = "old"
        self.assertEqual(len(atlas.validate_infrastructure(meta, atlas.ROOT)), 2)

    def test_unchecked_does_not_claim_no_missing_prerequisites(self):
        meta = {"status": "unchecked", "mathlib_revision": None, "evidence": [], "gaps": []}
        self.assertEqual(atlas.validate_infrastructure(meta, atlas.ROOT), [])
        meta["status"] = "available"
        self.assertTrue(atlas.validate_infrastructure(meta, atlas.ROOT))

    def test_missing_infrastructure_requires_a_concrete_gap(self):
        meta = node("A")["task"]["infrastructure"]
        meta["status"] = "missing"
        self.assertTrue(atlas.validate_infrastructure(meta, atlas.ROOT))
        meta["gaps"] = ["specific derivative transport adapter"]
        self.assertEqual(atlas.validate_infrastructure(meta, atlas.ROOT), [])

    def test_missing_failed_and_invalid_receipts_require_verification(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "build/verification/latest.json"
            self.assertFalse(atlas.current_evidence(root, {"sha256": "same"})["current"])
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps({"status": "failed", "snapshot": {"sha256": "same"}, "artifact": "r"}))
            self.assertFalse(atlas.current_evidence(root, {"sha256": "same"})["current"])
            path.write_text("broken")
            self.assertFalse(atlas.current_evidence(root, {"sha256": "same"})["current"])

    def test_replay_view_excludes_orphaned_and_ignored_duplicate_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            compiled = root / "formalization/.lake/build/lib/lean/FunctionalInequalities"
            compiled.mkdir(parents=True)
            for name in ["Current.olean", "Current.olean.server", "Current.olean.private", "Current 2.olean", "Old.olean"]:
                (compiled / name).write_bytes(name.encode())
            snapshot = {"files": {"formalization/FunctionalInequalities/Current.lean": "source-hash",
                                  "formalization/FunctionalInequalities/Old.lean": None}}
            view = root / "view"
            result = prepare_replay(root, snapshot, view)
            self.assertEqual(result["modules"], ["FunctionalInequalities.Current"])
            self.assertEqual(len(result["compiled_sha256"]), 3)
            self.assertFalse((view / "FunctionalInequalities/Old.olean").exists())
            self.assertTrue((compiled / "Old.olean").exists())

    def test_replay_view_rejects_unbuilt_current_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with self.assertRaisesRegex(RuntimeError, "no built module"):
                prepare_replay(root, {"files": {"solutions/New.lean": "hash"}}, root / "view")

    def test_dirty_untracked_edits_and_deletions_change_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            (root / ".gitignore").write_text("build/\n")
            (root / "source.lean").write_text("def n := 1\n")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                            "commit", "-qm", "fixture"], cwd=root, check=True)
            initial = atlas.source_snapshot(root)
            (root / "source.lean").write_text("def n := 2\n")
            edited = atlas.source_snapshot(root)
            self.assertEqual(initial["head"], edited["head"])
            self.assertNotEqual(initial["sha256"], edited["sha256"])
            (root / "new.lean").write_text("def m := 3\n")
            self.assertNotEqual(edited["sha256"], atlas.source_snapshot(root)["sha256"])
            (root / "source.lean").unlink()
            self.assertIsNone(atlas.source_snapshot(root)["files"]["source.lean"])

    def test_old_success_becomes_stale_when_content_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "build/verification/latest.json"
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps({"status": "passed", "snapshot": {"sha256": "old"}, "artifact": "report.json"}))
            self.assertTrue(atlas.current_evidence(root, {"sha256": "old"})["current"])
            self.assertFalse(atlas.current_evidence(root, {"sha256": "new"})["current"])

    def test_missing_or_unexpected_axioms_fail_acceptance(self):
        _, errors = parse_axioms("'A' depends on axioms: [propext, sorryAx]\n", {"A", "B"})
        self.assertIn("missing axiom report: B", errors)
        self.assertTrue(any("sorryAx" in error for error in errors))

    def test_axiom_free_and_multiline_standard_reports_are_valid(self):
        reports, errors = parse_axioms("'A' does not depend on any axioms\n'B'\n depends on axioms: [propext,\n Classical.choice, Quot.sound]\n", {"A", "B"})
        self.assertEqual(errors, [])
        self.assertEqual(reports["A"], [])
        self.assertEqual(len(reports["B"]), 3)


if __name__ == "__main__":
    unittest.main()
