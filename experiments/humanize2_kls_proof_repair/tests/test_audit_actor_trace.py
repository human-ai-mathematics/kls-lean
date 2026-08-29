from __future__ import annotations

import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "scripts" / "audit_actor_trace.py"
SPEC = importlib.util.spec_from_file_location("audit_actor_trace", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def _write_session(root: Path, records: list[dict[str, object]], name: str = "actor.jsonl") -> None:
    (root / name).write_text(
        "".join(json.dumps(record) + "\n" for record in records), encoding="utf-8"
    )


def _actor_records(actor_root: str, tool_name: str = "exec", tool_input: str = "CandidateProof.lean"):
    return [
        {
            "type": "session_meta",
            "payload": {"id": "actor-id", "cwd": actor_root, "source": "app-server"},
        },
        {
            "type": "turn_context",
            "payload": {
                "cwd": actor_root,
                "sandbox_policy": {"type": "danger-full-access"},
                "workspace_roots": [actor_root],
            },
        },
        {
            "type": "response_item",
            "payload": {"type": "custom_tool_call", "name": tool_name, "input": tool_input},
        },
        {
            "type": "response_item",
            "payload": {"type": "custom_tool_call_output", "output": "exit_code=0"},
        },
    ]


class AuditActorTraceTest(unittest.TestCase):
    @staticmethod
    def _seatbelt(root: Path, actor: str) -> Path:
        profile = root / "actor.sb"
        profile.write_text(
            f'(version 1)\n(deny default)\n; {os.path.realpath(actor)}\n', encoding="utf-8"
        )
        return profile

    def test_accepts_one_isolated_actor(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor = str(root / "actor")
            _write_session(root, _actor_records(actor))
            profile = self._seatbelt(root, actor)
            summary = MODULE.audit(root, actor, [str(root / "reviewer")], profile)
            self.assertTrue(summary["ok"], summary["errors"])

    def test_rejects_collaboration_tool(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor = str(root / "actor")
            _write_session(root, _actor_records(actor, tool_name="collaboration.spawn_agent"))
            profile = self._seatbelt(root, actor)
            summary = MODULE.audit(root, actor, [], profile)
            self.assertFalse(summary["ok"])
            self.assertIn("forbidden actor tool call", "\n".join(summary["errors"]))

    def test_rejects_unrelated_session_in_actor_home(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor = str(root / "actor")
            _write_session(root, _actor_records(actor))
            _write_session(
                root,
                [
                    {
                        "type": "session_meta",
                        "payload": {
                            "id": "unrelated-id",
                            "cwd": str(root / "elsewhere"),
                            "source": "app-server",
                        },
                    }
                ],
                name="unrelated.jsonl",
            )
            profile = self._seatbelt(root, actor)
            summary = MODULE.audit(root, actor, [], profile)
            self.assertFalse(summary["ok"])
            self.assertIn("exactly one session", "\n".join(summary["errors"]))

    def test_rejects_forbidden_path_and_descendant(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor = str(root / "actor")
            reviewer = str(root / "reviewer")
            _write_session(root, _actor_records(actor, tool_input=reviewer + "/oracle/x"))
            _write_session(
                root,
                [
                    {
                        "type": "session_meta",
                        "payload": {
                            "id": "child-id",
                            "cwd": str(root / "child"),
                            "source": {"subagent": {"parent": "actor-id"}},
                        },
                    }
                ],
                name="child.jsonl",
            )
            profile = self._seatbelt(root, actor)
            summary = MODULE.audit(root, actor, [reviewer], profile)
            self.assertFalse(summary["ok"])
            errors = "\n".join(summary["errors"])
            self.assertIn("descendant", errors)
            self.assertIn("forbidden root", errors)


if __name__ == "__main__":
    unittest.main()
