from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import stat
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).parents[1] / "scripts" / "stage_1b_audit_actor_trace.py"
SPEC = importlib.util.spec_from_file_location("stage1b_audit_actor_trace", SCRIPT)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def _write_session(root: Path, records: list[dict[str, object]], name: str = "actor.jsonl") -> None:
    (root / name).write_text(
        "".join(json.dumps(record) + "\n" for record in records), encoding="utf-8"
    )


def _actor_records(actor_root: str, tool_name: str = "exec", tool_input: object = None):
    if tool_input is None:
        tool_input = {"cmd": "lean CandidateStage1B.lean", "workdir": actor_root}
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
    def setUp(self) -> None:
        self._source_hash = MODULE.SOURCE_SHA256
        self._olean_hash = MODULE.OLEAN_SHA256

    def tearDown(self) -> None:
        MODULE.SOURCE_SHA256 = self._source_hash
        MODULE.OLEAN_SHA256 = self._olean_hash

    @staticmethod
    def _seatbelt(root: Path, actor: Path, codex_home: Path) -> Path:
        profile = root / "actor.sb"
        candidate = actor / "CandidateStage1B.lean"
        profile.write_text(
            "\n".join(
                [
                    "(version 1)",
                    "(deny default)",
                    '(allow network-outbound (process-path "/app/codex"))',
                    f'(allow file-read* (subpath "{os.path.realpath(actor)}"))',
                    f'(allow file-write* (literal "{os.path.realpath(candidate)}"))',
                    f'(allow file-read* (require-all (subpath "{os.path.realpath(codex_home)}") (process-path "/app/codex")))',
                ]
            ),
            encoding="utf-8",
        )
        return profile

    @staticmethod
    def _workspace(root: Path, mutate_candidate: bool = True) -> tuple[Path, Path]:
        actor = root / "actor"
        actor.mkdir()
        contents = {
            "AGENTS.md": b"actor contract\n",
            "TASK.md": b"frozen task\n",
            "AcceptedStage1A.lean": b"accepted source\n",
            "AcceptedStage1A.olean": b"accepted compiled dependency\n",
            "CandidateStage1B.lean": b"sentinel\n",
        }
        entries = {}
        for name, data in contents.items():
            path = actor / name
            path.write_bytes(data)
            path.chmod(0o644 if name == "CandidateStage1B.lean" else 0o444)
            entries[name] = {
                "sha256": hashlib.sha256(data).hexdigest(),
                "mode": stat.S_IMODE(path.stat().st_mode),
                "size": len(data),
            }
        manifest = root / "baseline.json"
        manifest.write_text(
            json.dumps(
                {
                    "actor_root": os.path.realpath(actor),
                    "directory_mode": 0o555,
                    "entries": entries,
                }
            ),
            encoding="utf-8",
        )
        MODULE.SOURCE_SHA256 = entries["AcceptedStage1A.lean"]["sha256"]
        MODULE.OLEAN_SHA256 = entries["AcceptedStage1A.olean"]["sha256"]
        if mutate_candidate:
            (actor / "CandidateStage1B.lean").write_bytes(b"implemented\n")
        actor.chmod(0o555)
        return actor, manifest

    def _audit(self, root: Path, actor: Path, manifest: Path, records=None, forbidden=None):
        codex_home = root / "codex-home"
        codex_home.mkdir()
        _write_session(codex_home, records or _actor_records(str(actor)))
        profile = self._seatbelt(root, actor, codex_home)
        return MODULE.audit(codex_home, str(actor), forbidden or [], profile, manifest)

    def test_accepts_one_turn_candidate_only_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor, manifest = self._workspace(root)
            summary = self._audit(root, actor, manifest)
            self.assertTrue(summary["ok"], summary["errors"])
            self.assertEqual(summary["workspace_mutations"], ["CandidateStage1B.lean"])

    def test_accepts_json_encoded_actor_paths(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor, manifest = self._workspace(root)
            encoded = json.dumps(
                {
                    "cmd": "lean CandidateStage1B.lean",
                    "cwd": str(actor),
                    "patch": f"*** Update File: {actor}/CandidateStage1B.lean\n@@\n",
                }
            )
            summary = self._audit(
                root, actor, manifest, records=_actor_records(str(actor), tool_input=encoded)
            )
            self.assertTrue(summary["ok"], summary["errors"])

    def test_accepts_lean_subtype_delimiter(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor, manifest = self._workspace(root)
            tool_input = {
                "cmd": "lean CandidateStage1B.lean",
                "workdir": str(actor),
                "patch": "def c := ⨅ C : {C : NNReal // HasPoincare μ (C : ℝ)}, C.1",
            }
            summary = self._audit(
                root, actor, manifest, records=_actor_records(str(actor), tool_input=tool_input)
            )
            self.assertTrue(summary["ok"], summary["errors"])
            self.assertNotIn("//", summary["trace_referenced_paths"])

    def test_rejects_immutable_mutation_and_extra_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor, manifest = self._workspace(root)
            actor.chmod(0o755)
            (actor / "AcceptedStage1A.lean").chmod(0o644)
            (actor / "AcceptedStage1A.lean").write_text("tampered\n", encoding="utf-8")
            (actor / "extra.txt").write_text("extra\n", encoding="utf-8")
            actor.chmod(0o555)
            summary = self._audit(root, actor, manifest)
            self.assertFalse(summary["ok"])
            errors = "\n".join(summary["errors"])
            self.assertIn("file set drifted", errors)
            self.assertIn("immutable actor artifact changed", errors)

    def test_rejects_unchanged_candidate(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor, manifest = self._workspace(root, mutate_candidate=False)
            summary = self._audit(root, actor, manifest)
            self.assertFalse(summary["ok"])
            self.assertIn("candidate-only", "\n".join(summary["errors"]))

    def test_rejects_compiled_dependency_inspection_network_and_mcp(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor, manifest = self._workspace(root)
            records = _actor_records(
                str(actor),
                tool_name="mcp.browser",
                tool_input={
                    "cmd": "python3 -c 'import urllib.request; urllib.request.urlopen(\"https://example.invalid\")'; strings AcceptedStage1A.olean"
                },
            )
            summary = self._audit(root, actor, manifest, records=records)
            self.assertFalse(summary["ok"])
            errors = "\n".join(summary["errors"])
            self.assertIn("tool call", errors)
            self.assertIn("compiled dependency", errors)
            self.assertIn("network access", errors)

    def test_rejects_descendant_extra_turn_environment_and_forbidden_path(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            actor, manifest = self._workspace(root)
            reviewer = root / "reviewer"
            records = _actor_records(
                str(actor),
                tool_input={"cmd": f"printenv; cat {reviewer}/oracle", "workdir": str(actor)},
            )
            records.append(
                {
                    "type": "response_item",
                    "payload": {
                        "type": "message",
                        "role": "assistant",
                        "content": [{"type": "output_text", "text": f"read {reviewer}/oracle"}],
                    },
                }
            )
            records.insert(2, records[1].copy())
            codex_home = root / "codex-home"
            codex_home.mkdir()
            _write_session(codex_home, records)
            _write_session(
                codex_home,
                [
                    {
                        "type": "session_meta",
                        "payload": {
                            "id": "child-id",
                            "cwd": str(reviewer),
                            "source": {"subagent": {"parent": "actor-id"}},
                        },
                    }
                ],
                name="child.jsonl",
            )
            profile = self._seatbelt(root, actor, codex_home)
            summary = MODULE.audit(
                codex_home, str(actor), [str(reviewer)], profile, manifest
            )
            self.assertFalse(summary["ok"])
            errors = "\n".join(summary["errors"])
            self.assertIn("descendant", errors)
            self.assertIn("exactly one actor turn", errors)
            self.assertIn("process environment", errors)
            self.assertIn("forbidden root", errors)
            self.assertIn("session record exposed", errors)


if __name__ == "__main__":
    unittest.main()
