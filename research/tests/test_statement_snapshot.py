"""Regression checks for hidden definition changes and explicit snapshot updates."""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import statement_snapshot as snapshot


class ElaboratedSnapshotTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.outputs = []
        helper = (snapshot.ROOT / "research/StatementSnapshot.lean").read_text()
        env = dict(os.environ)
        env.pop("LEAN_PATH", None)
        for value in ("1", "2", "newDependency"):
            source = helper + f"""
namespace FunctionalInequalities.SnapshotFixture
def newDependency : Nat := 3
def hidden : Nat := {value}
structure Domain : Prop where
  condition : hidden = 0
def target : Prop := Domain
end FunctionalInequalities.SnapshotFixture
#statement_snapshot FunctionalInequalities.SnapshotFixture.target
"""
            result = subprocess.run(["lake", "env", "lean", "--stdin"], input=source,
                                    cwd=snapshot.ROOT / "formalization", env=env,
                                    text=True, capture_output=True, timeout=60)
            if result.returncode:
                raise AssertionError(result.stdout + result.stderr)
            cls.outputs.append(json.loads(result.stdout))

    def test_structure_fields_reveal_hidden_definition_drift(self):
        before, after = self.outputs[:2]
        name = "FunctionalInequalities.SnapshotFixture.target"
        self.assertEqual(next(d for d in before["declarations"] if d["name"] == name),
                         next(d for d in after["declarations"] if d["name"] == name))
        errors = snapshot.compare_snapshot(after, before)
        self.assertIn("statement dependency changed: FunctionalInequalities.SnapshotFixture.hidden", errors)
        self.assertTrue(any(d["name"].endswith("Domain.mk") for d in before["declarations"]))

    def test_new_transitive_dependency_changes_the_baseline(self):
        errors = snapshot.compare_snapshot(self.outputs[2], self.outputs[0])
        self.assertIn("statement dependency added: FunctionalInequalities.SnapshotFixture.newDependency", errors)

    def test_unreferenced_local_declaration_is_not_a_semantic_dependency(self):
        self.assertFalse(any(d["name"].endswith("newDependency") for d in self.outputs[0]["declarations"]))


class GoldenTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.decision = "research/a-series/statement-snapshot/first.md"
        path = self.root / self.decision
        path.parent.mkdir(parents=True)
        path.write_text("Initial scope review.\n")
        self.current = {"version": 1, "toolchain": "pinned", "lake_manifest_sha256": "pin",
                        "printing": {"pp.all": True}, "roots": ["A"], "external": ["Nat"],
                        "declarations": [{"name": "A", "type": "Nat", "value": "1"}]}

    def test_missing_and_malformed_golden_fail_closed(self):
        self.assertTrue(snapshot.check_snapshot(self.root, self.current))
        snapshot.update_snapshot(self.root, self.current, self.decision)
        (self.root / snapshot.DIRECTORY / "golden.json").write_text("malformed")
        self.assertTrue(snapshot.check_snapshot(self.root, self.current))

    def test_matching_golden_passes_and_changed_body_fails(self):
        snapshot.update_snapshot(self.root, self.current, self.decision)
        self.assertEqual(snapshot.check_snapshot(self.root, self.current), [])
        changed = copy.deepcopy(self.current)
        changed["declarations"][0]["value"] = "2"
        self.assertTrue(snapshot.check_snapshot(self.root, changed))
        self.assertEqual(snapshot.check_snapshot(self.root, self.current), [])

    def test_check_does_not_update_golden_automatically(self):
        snapshot.update_snapshot(self.root, self.current, self.decision)
        path = self.root / snapshot.DIRECTORY / "golden.json"
        before = path.read_bytes()
        changed = {**self.current, "toolchain": "different"}
        self.assertTrue(snapshot.check_snapshot(self.root, changed))
        self.assertEqual(before, path.read_bytes())

    def test_update_requires_new_decision_and_rejects_history_edits(self):
        snapshot.update_snapshot(self.root, self.current, self.decision)
        with self.assertRaisesRegex(ValueError, "new decision"):
            snapshot.update_snapshot(self.root, self.current, self.decision)
        (self.root / self.decision).write_text("Rewritten history")
        self.assertTrue(snapshot.check_snapshot(self.root, self.current))
        new = "research/a-series/statement-snapshot/second.md"
        (self.root / new).write_text("New review with the updated scope.")
        snapshot.update_snapshot(self.root, self.current, new)
        self.assertEqual(snapshot.check_snapshot(self.root, self.current), [])

    def test_toolchain_and_external_boundary_are_compared(self):
        changed = {**self.current, "lake_manifest_sha256": "new", "external": ["NewExternal"]}
        self.assertEqual(len(snapshot.compare_snapshot(changed, self.current)), 2)

    def test_external_decision_path_is_not_accepted(self):
        with self.assertRaises(ValueError):
            snapshot.update_snapshot(self.root, self.current, "../outside.md")

    def test_review_must_belong_to_a_current_snapshot_owner(self):
        for name in ("build/history/review.md", "research/decisions/review.md",
                     "research/a-series/statement-snapshot/../review.md"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                snapshot.decision_record(self.root, name)
        name = "research/audits/BKL/IndependentTargets/review.md"
        path = self.root / name
        path.parent.mkdir(parents=True)
        path.write_text("Current independent-target scope review.\n")
        self.assertEqual(snapshot.decision_record(self.root, name)["path"], name)

    def test_review_rejects_missing_empty_and_symlinked_inputs(self):
        path = self.root / self.decision
        path.unlink()
        with self.assertRaises(ValueError):
            snapshot.decision_record(self.root, self.decision)
        path.write_text("  \n")
        with self.assertRaises(ValueError):
            snapshot.decision_record(self.root, self.decision)
        outside = self.root / "outside.md"
        outside.write_text("A review outside the permitted owner.\n")
        path.unlink()
        path.symlink_to(outside)
        with self.assertRaises(ValueError):
            snapshot.decision_record(self.root, self.decision)


if __name__ == "__main__":
    unittest.main()
