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

Stages 1A, 1B Run 3, 2A Run 1, and 2B Run 1 are human-accepted experimental dependencies. The
Stage 2B candidate is accepted byte-for-byte after an independent Claude 5 Fable walkthrough
returned all sixteen review items `PASS`. Stage 3 is frozen to the five-declaration extended
Rayleigh surface with an eleven-entry actor fixture, exact verifier, hidden production pin,
deny-default isolation, complete-trace policy, and a model-free preflight suite that passes in
full. One fresh subscription-authenticated `gpt-5.6-sol` Run 1 at high effort is authorized; it
must stop at `mechanical-pass` for a new human decision.

The Stage 3 mathematical input and actor prompt are
`humanize2_kls_issue2_staged/inputs/issue2_stage_3_rayleigh_quotient.md` and
`humanize2_kls_issue2_staged/prompts/issue2_stage_3_actor.md`. The accepted Stage 2B source is
`humanize2_kls_issue2_staged/accepted/AcceptedStage2B.lean`. Earlier stopped and rejected outputs
remain immutable historical records.
