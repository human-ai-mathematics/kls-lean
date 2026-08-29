"""Physically separated Humanize2 proof actor and oracle-backed reviewer."""

from __future__ import annotations

import os
from typing import Literal, NamedTuple

from hmz.flows import Agent, flow
from pydantic import BaseModel, Field


Finding = Literal[
    "candidate_unchanged",
    "statement_drift",
    "placeholder",
    "compile_failure",
    "workspace_drift",
    "trace_invalid",
    "oracle_drift",
]


class Agents(NamedTuple):
    actor: Agent
    reviewer: Agent


class Config(BaseModel):
    model_config = {"extra": "forbid"}

    max_rounds: int = Field(default=3, ge=1, le=10)


class Review(BaseModel):
    """Structured result kept in the reviewer lane."""

    model_config = {"extra": "forbid"}

    done: bool
    findings: list[Finding]
    evidence: str = Field(
        description="Concise reviewer evidence. This field is never forwarded to the actor."
    )


FEEDBACK: dict[str, str] = {
    "candidate_unchanged": "The candidate is still the deliberately broken reset fixture.",
    "statement_drift": "Restore the theorem name, binders, and conclusion; edit only its proof body.",
    "placeholder": "Remove every forbidden proof escape hatch and provide a checked Lean proof.",
    "compile_failure": "The candidate does not compile. Run `lean CandidateProof.lean` and repair the exact diagnostic.",
    "workspace_drift": "Restore every file except `CandidateProof.lean`; that is the only writable result.",
    "trace_invalid": "The actor trace violated the session, tool, external-sandbox, or path-access boundary.",
    "oracle_drift": "The reviewer oracle pins do not match; stop rather than reasoning from a moving oracle.",
}


def _required(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise RuntimeError(f"{name} must be set")
    return os.path.realpath(value)


def _feedback(findings: list[Finding]) -> str:
    ordered = list(dict.fromkeys(findings))
    return "\n".join(
        [
            "The independent reviewer rejected the last round. Address only these bounded findings:",
            *(f"- {finding}: {FEEDBACK[finding]}" for finding in ordered),
            "Do not seek reviewer or oracle material. Compile the repair locally before finishing.",
        ]
    )


@flow()
def run(agents: Agents, task: str, config: Config | None = None) -> None:
    held = config or Config()
    actor_root = _required("H2_PROOF_ACTOR_ROOT")
    reviewer_root = _required("H2_PROOF_REVIEWER_ROOT")
    experiment = _required("H2_PROOF_EXPERIMENT_ROOT")
    scripts = os.path.join(experiment, "scripts")
    rubric = os.path.join(experiment, "oracle", "semantic_rubric.md")
    candidate = os.path.join(actor_root, "CandidateProof.lean")
    trace_root = _required("H2_PROOF_ACTOR_CODEX_HOME")
    seatbelt = _required("H2_PROOF_ACTOR_SEATBELT")

    reviewer_prompt = f"""You are the independent read-only reviewer for a disposable Lean proof-repair calibration.
Read the repository contract and `{rubric}`. The actor candidate is `{candidate}` and its external
workspace is `{actor_root}`. Run:

1. `{scripts}/verify_oracle_pins.sh`
2. `{scripts}/verify_actor_workspace.sh {actor_root}`
3. `{scripts}/verify_candidate.sh {actor_root}`
4. `python3 {scripts}/audit_actor_trace.py --codex-home {trace_root} --actor-root {actor_root} --forbidden-root {reviewer_root} --seatbelt-profile {seatbelt}`

Inspect the candidate and all ten rubric items yourself. Remain read-only. Return `done: true` only
when every command and rubric item passes. Otherwise return only applicable finding codes. Keep
specific evidence in `evidence`; never put an oracle proof or repair hint in a finding.
"""

    working = agents.actor.new(cwd=actor_root)
    prompt = task
    for round_number in range(1, held.max_rounds + 1):
        worked = working(prompt, suppress=True)
        if not worked:
            continue
        review_session = agents.reviewer.new(cwd=reviewer_root)
        review = review_session(reviewer_prompt, suppress=True, schema=Review)
        if review is None:
            continue
        if review.done and not review.findings:
            print(f"reviewer accepted disposable proof repair after round {round_number}")
            return
        if review.done or not review.findings:
            raise RuntimeError("reviewer returned an inconsistent structured result")
        prompt = _feedback(review.findings)

    raise RuntimeError(f"reviewer did not accept within {held.max_rounds} rounds")
