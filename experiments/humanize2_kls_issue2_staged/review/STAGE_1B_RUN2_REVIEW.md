# Stage 1B Run 2 human review

## Decision boundary

The checked-in candidate is a stopped, mechanically verified actor output. It is deliberately
stored under `review/pending/`, not `accepted/`. Only a human may decide whether it becomes the
Stage 2A dependency. Do not send checklist findings or hidden reference proof text back to the
stopped actor session.

## Files

- Candidate: `pending/CandidateStage1BRun2.lean`
- Candidate pin: `pending/stage_1b_run2.sha256`
- Frozen actor specification: `../inputs/issue2_stage_1b_foundational_lemmas.md`
- Frozen checklist: `issue2_stage_1b_human_checklist.md`
- Existing human oracle: `../../../formalization/FunctionalInequalities/Basic.lean`
- Mechanical run record:
  `../../../research/explorations/2026-08-30-humanize2-kls-issue2-stage1b-run2.md`

All paths in commands below are relative to the repository root.

## Cursor setup

Open `Stage1BRun2Review.code-workspace` in Cursor, rather than opening the pending Lean file as a
loose file or using the repository root. The workspace selects this `review/` directory, which is
a small reviewer-only Lake project pinned to Lean/Mathlib 4.33.0. Its two targets point to the
immutable accepted Stage 1A source and the pending Run 2 candidate without copying or editing
either file.

Cursor is configured here to build imported dependencies automatically. On the first checkout it
may download the pinned Mathlib packages; afterward the InfoView should elaborate
`pending/CandidateStage1BRun2.lean` normally. The project adds no actor-visible file and does not
change the candidate's pending status.

## 1. Recheck provenance

From the repository root:

```bash
shasum -a 256 -c \
  experiments/humanize2_kls_issue2_staged/review/pending/stage_1b_run2.sha256
shasum -a 256 -c \
  experiments/humanize2_kls_issue2_staged/pins/stage_1b.sha256
```

Read the mechanical run record and confirm that checklist items 1–4 are supported: the complete
trace audit passed, the actor saw only the five permitted workspace entries, only the candidate
changed, and the exact-surface verifier passed. Raw authentication and session transcripts are not
committed; the append-only run record and compact audit hash are the persisted provenance.

## 2. Reproduce the independent Lean check

Use a new disposable review root. Do not point this command at either historical actor root.

```bash
export H2_ISSUE2_STAGE1B_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage1b-review
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_reset_actor_workspace.sh
cp \
  experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage1BRun2.lean \
  "$H2_ISSUE2_STAGE1B_STATE_ROOT/actor-workspace/CandidateStage1B.lean"
experiments/humanize2_kls_issue2_staged/scripts/stage_1b_verify_candidate.sh \
  "$H2_ISSUE2_STAGE1B_STATE_ROOT/actor-workspace"
```

The last command must exit zero and report that the exact thirteen-declaration surface compiles
against immutable Stage 1A plus upstream Mathlib only.

## 3. Perform the semantic/proof review

Read the frozen specification, the candidate, and the relevant existing `Basic.lean` declarations
side by side. Record PASS or FAIL, with a short reason, for every item in
`issue2_stage_1b_human_checklist.md`. In particular, inspect rather than infer from compilation:

1. the energy proof uses pointwise nonnegativity and adds no integrability hypothesis;
2. the derivative/gradient norm equality uses the real-Hilbert Riesz isometry and has no
   measurable-space assumption;
3. the integral equality is pointwise and does not assume admissibility;
4. the four `HasPoincare` accessors/monotonicity lemmas preserve the accepted Stage 1A semantics;
5. the optimal constant is definitionally the `ENNReal` infimum over valid `NNReal` constants;
6. the five optimal-constant theorems have the frozen implicit binders and correctly handle the
   empty subtype/`⊤` case; and
7. no escape hatch, later-stage claim, stronger hypothesis, or production-status claim appears.

Any failed item rejects this candidate. A repair must use a fresh isolated actor run; do not edit
the actor output in place and then call it accepted.

## 4. Record the human decision

There are three valid outcomes:

- **Accept:** record the reviewer, date, candidate hash, and all thirteen PASS results in a new
  append-only decision. Copy the candidate byte-for-byte to `accepted/AcceptedStage1B.lean`, add
  its pin, and only then prepare Stage 2A.
- **Reject:** append a decision naming the failed checklist items. Preserve this pending candidate
  and run record unchanged.
- **Fresh repair run:** first freeze the permitted non-oracular feedback and authorize a new
  isolated state root. Do not reuse Run 2 authentication state, workspace, or transcript.

Acceptance is only an experimental dependency transition. It does not promote the declarations to
production Lean or change a theorem, dossier, ledger, manuscript, or proof-certification status.
