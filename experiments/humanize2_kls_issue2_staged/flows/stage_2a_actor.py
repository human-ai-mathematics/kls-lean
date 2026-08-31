"""One oracle-free Codex actor session for Issue 2 Stage 2A."""

from __future__ import annotations

import os
from typing import NamedTuple

from hmz.flows import Agent, flow


class Agents(NamedTuple):
    actor: Agent


def _required(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise RuntimeError(f"{name} must be set")
    return os.path.realpath(value)


@flow()
def run(agents: Agents, task: str) -> None:
    actor_root = _required("H2_ISSUE2_STAGE2A_ACTOR_ROOT")
    session = agents.actor.new(cwd=actor_root)
    result = session(task, suppress=False)
    if not result:
        raise RuntimeError("Stage 2A actor returned no final result")
    print("Stage 2A actor session stopped; human review is required")
