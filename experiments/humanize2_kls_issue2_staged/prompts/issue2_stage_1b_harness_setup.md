# Next repository task: build the Issue 2 Stage 1B isolated harness

Work in `/private/tmp/numina-humanize2-kls-autoformalization` on branch
`humanize2-kls-autoformalization-experiment`.

Begin with:

```bash
git status --short --branch
git rev-parse --short HEAD
```

If the branch or worktree differs from the handoff, investigate without resetting, checking out,
or overwriting user changes.

Read completely before editing:

1. `AGENTS.md`;
2. `solutions/README.md`;
3. `docs/HUMANIZE2_KLS_EXPERIMENT_HANDOFF.md`;
4. `experiments/humanize2_kls_issue2_staged/README.md`;
5. `experiments/humanize2_kls_issue2_staged/inputs/issue2_stage_1b_foundational_lemmas.md`;
6. `experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_1b_actor.md`;
7. `research/decisions/2026-08-29-humanize2-kls-issue2-stage1a-acceptance-stage1b-prompt.md`;
8. the complete Stage 1A fixture, reset, verifier, isolation, runner, trace auditor, tests, and pin
   files that the Stage 1B harness will adapt.

Stage 1A is human-accepted only as an experimental dependency. Its pinned source is
`experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage1A.lean`, SHA-256
`9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6`. Preserve its explicit
`HasPoincare` function binder. Do not reset or overwrite the stopped external Stage 1A candidate.

Build, but do not run, a dedicated Stage 1B Humanize2/Codex/Lean harness. It must provide:

- a deterministic external reset below `/private/tmp`, separate from Stage 1A;
- actor-visible entries exactly `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`,
  `AcceptedStage1A.olean`, and `CandidateStage1B.lean`;
- a byte-identical accepted source and a deterministic `.olean` compiled from it with the pinned
  Lean toolchain and upstream Mathlib only;
- physical write protection plus post-run hash verification for both accepted artifacts;
- a compiler-failing Stage 1B sentinel candidate;
- a candidate verifier for the exact imports, namespace, thirteen requested declarations,
  theorem surface, forbidden escape hatches, accepted-artifact hashes, and upstream-only Lean
  compilation;
- an independent hidden-oracle pin for only the relevant existing `Basic.lean` surface;
- a human-only Stage 1B semantic/proof checklist outside the actor lane;
- a single-session actor flow and compiler-feedback runner that refuse without an explicit live-run
  acknowledgement and dedicated ChatGPT-subscription login;
- complete-session trace auditing for one root session, one turn, zero descendants, no
  collaboration/reviewer/browser/web/MCP/network/client-state access, no forbidden paths, and
  mutation limited to `CandidateStage1B.lean`; and
- unit and adversarial model-free tests for reset, read/write isolation, compiled-dependency
  provenance, sentinel rejection, known-good verifier behavior, trace policy, and deterministic
  reruns.

Reuse the Stage 1A architecture where sound, but use Stage 1B-specific directories, environment
variables, fixtures, pins, prompts, audit outputs, and acknowledgements. The actor must never see
the existing Issue 2 implementation, proof, solution certificate, semantic reviews, ledgers,
manuscript, human checklist, oracle, or later-stage files. Prompt restrictions do not substitute
for physical isolation and complete trace audit.

Record harness rationale and validation in a new append-only
`research/decisions/2026-08-29-*.md`. Do not create an exploration unless an actual Stage 1B model
proof attempt occurs. Do not modify production KLS Lean, solutions, reviews, ledgers, or manuscript.
Do not commit raw transcripts, credentials, tokens, Codex/Humanize state, or machine-private
configuration. Do not push.

Before committing, run the Stage 1A verifier, Stage 1B model-free test suite, `lake build`,
`uv run --with pyyaml python research/check_ledger.py`, pin verification, and `git diff --check`.
Update the main handoff with exact actor-visible files, reset/verifier/compiler-loop/trace/oracle
design, commands and exit codes, commit, worktree state, authorization boundary, and the explicit
statement that no Stage 1B model run or mathematical status change occurred. Stop with a clean
worktree and report the exact live-run command, but do not execute it.
