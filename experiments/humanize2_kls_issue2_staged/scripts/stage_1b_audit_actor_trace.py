#!/usr/bin/env python3
"""Fail closed on the complete Stage 1B actor session, tools, paths, and mutations."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


EXPECTED_FILES = (
    "AGENTS.md",
    "TASK.md",
    "AcceptedStage1A.lean",
    "AcceptedStage1A.olean",
    "CandidateStage1B.lean",
)
IMMUTABLE_FILES = frozenset(EXPECTED_FILES) - {"CandidateStage1B.lean"}
SOURCE_SHA256 = "9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6"
OLEAN_SHA256 = "212cd1f5a0c20d2f3974c5948ea4c26550409a5b3b7b47a4b65e1e9cdf65a3a0"
DENIAL_MARKERS = (
    "operation not permitted",
    "permission denied",
    "sandbox denial",
    "sandbox denied",
)
FORBIDDEN_TOOLS = (
    "collab",
    "spawn_agent",
    "subagent",
    "send_message",
    "review",
    "mcp",
    "web_search",
    "browser",
    "computer_use",
)
ALLOWED_TOOLS = frozenset({"exec", "apply_patch"})
FORBIDDEN_COMMAND_MARKERS = (
    "auth.json",
    "curl ",
    "ftp ",
    "hmz ",
    "nc ",
    "scp ",
    "ssh ",
    "wget ",
)
CLIENT_STATE_MARKERS = (
    ".codex",
    ".humanize",
    "$home",
    "${home}",
    "actor-codex-home",
    "auth.json",
    "codex_home",
    "humanize_home",
    "openai_api_key",
    "refresh_token",
)
ENVIRONMENT_COMMAND = re.compile(
    r"(?:^|[\s;&|\"'])(?:/usr/bin/)?(?:env|printenv)(?:[\s;&|\"']|$)|"
    r"(?:^|[\s;&|\"'])(?:set|export\s+-p)(?:[\s;&|\"']|$)",
    flags=re.IGNORECASE,
)
CODEX_COMMAND = re.compile(
    r"(?:^|[\s;&|/\"'])(?:codex|hmz|humanize2?)(?:[\s\"']|$)", flags=re.IGNORECASE
)
NETWORK_COMMAND = re.compile(
    r"(?:^|[\s;&|/\"'])(?:curl|dig|ftp|git|nc|netcat|nslookup|ping|scp|sftp|ssh|telnet|wget)"
    r"(?:[\s;&|\"']|$)",
    flags=re.IGNORECASE,
)
NETWORK_CODE_MARKERS = (
    "/dev/tcp",
    "http.client",
    "http://",
    "https://",
    "requests.",
    "socket.",
    "urllib.",
)
PATH_PATTERN = re.compile(
    r"(?:/(?![-*/])[^\s\\\"'`;,(){}\[\]]+|"
    r"(?:AGENTS|TASK)\.md|AcceptedStage1A\.(?:lean|olean)|CandidateStage1B\.lean)"
)


@dataclass
class Session:
    path: Path
    ident: str
    cwd: str
    source: Any
    records: list[dict[str, Any]]


def _real(path: str | os.PathLike[str]) -> str:
    return os.path.realpath(os.fspath(path))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"{path}:{line_number}: invalid JSON: {error}") from error
        if not isinstance(value, dict):
            raise ValueError(f"{path}:{line_number}: record is not an object")
        records.append(value)
    return records


def _session(path: Path) -> Session | None:
    records = _load_jsonl(path)
    metas = [record.get("payload", {}) for record in records if record.get("type") == "session_meta"]
    if not metas:
        return None
    if len(metas) != 1:
        raise ValueError(f"{path}: expected exactly one session_meta record")
    meta = metas[0]
    ident = str(meta.get("id") or meta.get("session_id") or "")
    cwd = _real(str(meta.get("cwd") or "/"))
    return Session(path=path, ident=ident, cwd=cwd, source=meta.get("source"), records=records)


def _serialized(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def _tool_name(payload: dict[str, Any]) -> str:
    kind = str(payload.get("type") or "")
    if kind in {"custom_tool_call", "function_call", "mcp_tool_call", "dynamic_tool_call"}:
        return str(payload.get("name") or payload.get("tool") or "")
    if kind in {"collabAgentToolCall", "subAgentActivity"}:
        return kind
    return ""


def _tool_input(payload: dict[str, Any]) -> Any:
    for key in ("input", "arguments", "command", "changes"):
        if key in payload:
            return payload[key]
    return None


def _is_within(path: str, root: str) -> bool:
    path = _real(path)
    root = _real(root)
    return path == root or path.startswith(root + os.sep)


def _workspace_mutations(
    actor_root: str, baseline_manifest: Path, errors: list[str]
) -> list[str]:
    try:
        baseline = json.loads(baseline_manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        errors.append(f"cannot read workspace baseline: {error}")
        return []
    if _real(str(baseline.get("actor_root") or "/")) != actor_root:
        errors.append("workspace baseline actor root does not match the audited actor root")
    expected_entries = baseline.get("entries")
    if not isinstance(expected_entries, dict):
        errors.append("workspace baseline has no entry map")
        return []

    root = Path(actor_root)
    actual_names = sorted(path.name for path in root.iterdir()) if root.is_dir() else []
    if actual_names != sorted(EXPECTED_FILES):
        errors.append(f"post-run actor-visible file set drifted: {actual_names!r}")
    if root.is_dir() and stat.S_IMODE(root.stat().st_mode) & 0o222:
        errors.append("post-run actor workspace directory became writable")

    mutations: list[str] = []
    for name in EXPECTED_FILES:
        path = root / name
        if not path.is_file() or path.is_symlink():
            continue
        current = {
            "sha256": _sha256(path),
            "mode": stat.S_IMODE(path.stat().st_mode),
            "size": path.stat().st_size,
        }
        if current != expected_entries.get(name):
            mutations.append(name)
        if name in IMMUTABLE_FILES and current != expected_entries.get(name):
            errors.append(f"immutable actor artifact changed: {name}")

    if mutations != ["CandidateStage1B.lean"]:
        errors.append(f"actor mutation set was not candidate-only: {mutations!r}")
    accepted_source = root / "AcceptedStage1A.lean"
    accepted_olean = root / "AcceptedStage1A.olean"
    if accepted_source.is_file() and _sha256(accepted_source) != SOURCE_SHA256:
        errors.append("post-run accepted source hash does not match its pin")
    if accepted_olean.is_file() and _sha256(accepted_olean) != OLEAN_SHA256:
        errors.append("post-run accepted compiled dependency hash does not match its pin")
    return mutations


def audit(
    codex_home: Path,
    actor_root: str,
    forbidden_roots: list[str],
    seatbelt_profile: Path,
    baseline_manifest: Path,
) -> dict[str, Any]:
    codex_home_real = _real(codex_home)
    actor_root = _real(actor_root)
    forbidden_aliases: set[str] = set()
    for root in forbidden_roots:
        for candidate in (os.fspath(root), _real(root)):
            forbidden_aliases.add(candidate)
            if candidate.startswith("/private/"):
                forbidden_aliases.add(candidate.removeprefix("/private"))
    forbidden_roots = sorted(forbidden_aliases)
    errors: list[str] = []

    try:
        seatbelt_text = seatbelt_profile.read_text(encoding="utf-8")
    except OSError as error:
        seatbelt_text = ""
        errors.append(f"cannot read Seatbelt profile: {error}")
    if "(deny default)" not in seatbelt_text:
        errors.append("Seatbelt profile is not deny-default")
    if actor_root not in seatbelt_text:
        errors.append("Seatbelt profile does not allowlist the actor root")
    candidate_path = os.path.join(actor_root, "CandidateStage1B.lean")
    if f'(literal "{candidate_path}")' not in seatbelt_text:
        errors.append("Seatbelt profile does not name the candidate-only write path")
    if codex_home_real not in seatbelt_text or "(process-path " not in seatbelt_text:
        errors.append("Codex client state is not guarded by a process-path filter")
    if not re.search(
        r'\(allow\s+network-outbound\s+\(process-path\s+"[^"]+"\)\s*\)',
        seatbelt_text,
    ):
        errors.append("outbound network access is not restricted to the Codex process path")
    if re.search(
        rf'\(allow\s+file-write\*\s+\(subpath\s+"{re.escape(actor_root)}"\)',
        seatbelt_text,
    ):
        errors.append("Seatbelt write rules grant the full actor root")
    if f'(subpath "{os.path.dirname(actor_root)}")' in seatbelt_text:
        errors.append("Seatbelt profile grants file data access to the broad state root")
    for root in forbidden_roots:
        if root and root in seatbelt_text:
            errors.append(f"Seatbelt profile unexpectedly names forbidden root: {root}")

    sessions: list[Session] = []
    for path in sorted(codex_home.rglob("*.jsonl")):
        try:
            one = _session(path)
        except (OSError, ValueError) as error:
            errors.append(str(error))
            continue
        if one is not None:
            sessions.append(one)

    actor_sessions = [session for session in sessions if session.cwd == actor_root]
    if len(actor_sessions) != 1:
        errors.append(f"expected exactly one actor-root session, found {len(actor_sessions)}")
    if len(sessions) != 1:
        errors.append(f"expected actor Codex home to contain exactly one session, found {len(sessions)}")

    actor_ids = {session.ident for session in actor_sessions if session.ident}
    descendants: list[Session] = []
    changed = True
    while changed:
        changed = False
        lineage_ids = actor_ids | {session.ident for session in descendants if session.ident}
        for session in sessions:
            if session in actor_sessions or session in descendants:
                continue
            source = _serialized(session.source)
            if any(ident and ident in source for ident in lineage_ids):
                descendants.append(session)
                changed = True
    if descendants:
        errors.append(f"actor session has {len(descendants)} descendant session(s)")

    tool_names: list[str] = []
    tool_inputs: list[str] = []
    trace_paths: set[str] = set()
    turn_count = 0
    for session in actor_sessions + descendants:
        source_text = _serialized(session.source).lower()
        if any(marker in source_text for marker in ("subagent", "collab", "spawn", "reviewer")):
            errors.append(f"actor lineage contains delegated/reviewer source in {session.path.name}")
        for record in session.records:
            payload = record.get("payload")
            if not isinstance(payload, dict):
                continue
            payload_text = _serialized(payload)
            for root in forbidden_roots:
                if root and root in payload_text:
                    errors.append(
                        f"complete session record exposed forbidden root in {session.path.name}: {root}"
                    )
            if (
                record.get("type") == "response_item"
                and payload.get("type") == "message"
                and payload.get("role") == "assistant"
            ):
                lowered_message = payload_text.lower()
                if re.search(r"(?:^|[\s/'\"])(?:\.\./|\.\.)(?:[\s/'\"]|$)", payload_text):
                    errors.append("actor message used parent-directory traversal")
                if any(
                    marker in lowered_message
                    for marker in (
                        "/oracle/",
                        "/solutions/",
                        "/research/reviews/",
                        "/modules/",
                        "ledger.yaml",
                        "stage_1b_human_checklist",
                    )
                ):
                    errors.append("actor message named forbidden oracle/proof/review/ledger/manuscript material")
            if record.get("type") == "turn_context":
                turn_count += 1
                if _real(str(payload.get("cwd") or session.cwd)) != actor_root:
                    errors.append(f"turn cwd escaped actor root in {session.path.name}")
                sandbox = _serialized(payload.get("sandbox_policy")).lower().replace("_", "-")
                if "danger-full-access" not in sandbox and "dangerfullaccess" not in sandbox:
                    errors.append(f"turn was not marked as externally sandboxed in {session.path.name}")
                roots = [_real(str(root)) for root in payload.get("workspace_roots", [])]
                if roots != [actor_root]:
                    errors.append(
                        f"turn workspace roots were not exactly the actor root in {session.path.name}: {roots!r}"
                    )

            name = _tool_name(payload)
            if name:
                tool_names.append(name)
                lowered = name.lower()
                if lowered not in ALLOWED_TOOLS or any(marker in lowered for marker in FORBIDDEN_TOOLS):
                    errors.append(f"forbidden or unexpected actor tool call: {name}")
                value = _tool_input(payload)
                if value is not None:
                    text = _serialized(value)
                    lowered_text = text.lower()
                    tool_inputs.append(text)
                    if "AcceptedStage1A.olean" in text:
                        errors.append("actor tool input attempted to inspect the compiled dependency")
                    for matched in PATH_PATTERN.findall(text):
                        cleaned = matched.rstrip(":.")
                        trace_paths.add(cleaned)
                        if cleaned.startswith("/") and not _is_within(cleaned, actor_root):
                            errors.append(f"actor tool input named a path outside its workspace: {cleaned}")
                    for root in forbidden_roots:
                        if root and root in text:
                            errors.append(f"actor tool input referenced forbidden root: {root}")
                    if any(marker in lowered_text for marker in FORBIDDEN_COMMAND_MARKERS):
                        errors.append("actor tool input referenced client/reviewer state or a network command")
                    if any(marker in lowered_text for marker in CLIENT_STATE_MARKERS):
                        errors.append("actor tool input referenced client state or credentials")
                    if ENVIRONMENT_COMMAND.search(text):
                        errors.append("actor tool input attempted to inspect its process environment")
                    if CODEX_COMMAND.search(text):
                        errors.append("actor tool input attempted to launch a model/client process")
                    if NETWORK_COMMAND.search(text) or any(
                        marker in lowered_text for marker in NETWORK_CODE_MARKERS
                    ):
                        errors.append("actor tool input attempted shell or scripted network access")
                    if re.search(r"(?:^|[\s/'\"])(?:\.\./|\.\.)(?:[\s/'\"]|$)", text):
                        errors.append("actor tool input used parent-directory traversal")
                    if any(
                        marker in lowered_text
                        for marker in (
                            "/oracle/",
                            "/solutions/",
                            "/research/reviews/",
                            "/modules/",
                            "ledger.yaml",
                            "stage_1b_human_checklist",
                        )
                    ):
                        errors.append("actor tool input referenced forbidden oracle/proof/review/ledger/manuscript material")

            if record.get("type") == "response_item" and payload.get("type") in {
                "custom_tool_call_output",
                "function_call_output",
            }:
                output = str(payload.get("output") or "")
                lowered_output = output.lower()
                if any(marker in lowered_output for marker in DENIAL_MARKERS):
                    errors.append("actor encountered a filesystem sandbox denial")
                if any(marker in lowered_output for marker in CLIENT_STATE_MARKERS):
                    errors.append("actor tool output exposed client state or credential material")
                for root in forbidden_roots:
                    if root and root in output:
                        errors.append(f"actor tool output exposed forbidden root: {root}")

    if actor_sessions and turn_count != 1:
        errors.append(f"expected exactly one actor turn, found {turn_count}")
    if not tool_names and actor_sessions:
        errors.append("actor session contains no auditable tool calls")

    mutations = _workspace_mutations(actor_root, baseline_manifest, errors)
    digest = hashlib.sha256("\n".join(tool_inputs).encode()).hexdigest()
    seatbelt_digest = hashlib.sha256(seatbelt_text.encode()).hexdigest()
    return {
        "ok": not errors,
        "actor_root": actor_root,
        "actor_visible_files": list(EXPECTED_FILES),
        "workspace_mutations": mutations,
        "session_files_scanned": len(sessions),
        "actor_root_sessions": len(actor_sessions),
        "actor_descendants": len(descendants),
        "actor_turns": turn_count,
        "tool_calls": tool_names,
        "tool_input_sha256": digest,
        "trace_referenced_paths": sorted(trace_paths),
        "outer_sandbox": "macos-seatbelt-deny-default-candidate-write-only",
        "client_state_guard": "codex-process-path-only",
        "seatbelt_profile_sha256": seatbelt_digest,
        "accepted_source_sha256": SOURCE_SHA256,
        "accepted_olean_sha256": OLEAN_SHA256,
        "errors": errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--codex-home", required=True, type=Path)
    parser.add_argument("--actor-root", required=True)
    parser.add_argument("--forbidden-root", action="append", default=[])
    parser.add_argument("--seatbelt-profile", required=True, type=Path)
    parser.add_argument("--baseline-manifest", required=True, type=Path)
    args = parser.parse_args(argv)

    summary = audit(
        args.codex_home,
        _real(args.actor_root),
        [_real(path) for path in args.forbidden_root],
        args.seatbelt_profile,
        args.baseline_manifest,
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
