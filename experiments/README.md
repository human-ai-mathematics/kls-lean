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

Stages 1A, 1B Run 3, 2A Run 1, 2B Run 1, and Stage 3 Run 1 are human-accepted experimental
dependencies. A Claude 5 Fable interactive review independently reproduced the Stage 3 hash,
silent build, both verification scripts, hidden oracle, and compact trace, then returned all
sixteen items `PASS`. The byte-identical accepted source is `accepted/AcceptedStage3.lean`.

The sixteen-declaration production covariance section is split at its dependency-ordered midpoint.
Stage 4A Run 1 is now a zero-diagnostic `mechanical-pass`; Stage 4B remains planned and
unauthorized. The single actor turn produced the exact ordered two-import/eight-declaration
surface on its eighth compiler call after seven post-failure repairs. One session, zero
descendants, thirteen visible files, candidate-only mutation, the hidden production pin, exact
import/declaration/Borel controls, and complete-trace gates passed. The candidate remains stopped
for a separate sixteen-item human decision.
