# Autoformalization experiments

This directory is published only on the `autoformalization-experiments` branch. The repository
root `README.md` remains the minimal project README inherited from `main`.

## Experiment map

- `humanize2_baseline/`: verified Python editing, Lean compiler repair, and actor-reviewer
  infrastructure baseline.
- `humanize2_kls_statement_fidelity/`: completed linear-test statement-fidelity calibration.
- `humanize2_kls_proof_repair/`: oracle-free proof-repair isolation scaffold; model-free checks
  passed and no authenticated run has started.
- `humanize2_kls_issue2_staged/`: staged blind reconstruction of Issue 2.

## Current Issue 2 gate

Stage 1A and zero-warning Stage 1B Run 3 are human-accepted experimental dependencies. Stage 1B
Run 2 remains a mechanically successful but human-rejected historical output because it emitted
one `unnecessarySimpa` linter diagnostic. The Stage 2A linear-test-geometry specification, exact
five-declaration surface, actor prompt, seven-entry fixture, human checklist, isolated live runner,
and complete-trace policy are frozen. Authorized Run 1 produced a zero-diagnostic exact-surface
candidate in one actor turn with zero descendants, and every mechanical and trace gate passed. It
is stopped for human semantic/proof review; Stage 2B has not started.

The Stage 2A candidate and review guide are
`humanize2_kls_issue2_staged/review/pending/CandidateStage2ARun1.lean` and
`humanize2_kls_issue2_staged/review/STAGE_2A_RUN1_REVIEW.md`. The actor prompt is
`humanize2_kls_issue2_staged/prompts/issue2_stage_2a_actor.md`; its complete mathematical input is
`humanize2_kls_issue2_staged/inputs/issue2_stage_2a_linear_test_geometry.md`. Run 2 and the stopped
Run 3 output remain immutable historical records; the accepted Run 3 copy is pinned separately.
