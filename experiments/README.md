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

Stages 1A, 1B Run 3, 2A Run 1, 2B Run 1, Stage 3 Run 1, and Stage 4A Run 1 are human-accepted
experimental dependencies. The accepted Stage 4A source is byte-identical to its stopped
candidate after a Claude 5 Fable review reproduced all mechanical evidence, checked the two long
proofs line by line, and returned all sixteen items `PASS`.

Stage 4B Run 1 is now a human-accepted experimental dependency under the standing statement-level
alignment ruling. The accepted source is byte-identical to the stopped candidate, and all sixteen
review items pass.

Stage 5 Run 1 is now the final human-accepted experimental layer. An overall statement-level
audit found the three frozen theorem signatures exactly aligned with the production reference,
including the deliberate finite-dimensional/probability redundancy, strict-implicit certificate
binder, and `D = 0` Euclidean boundary. All sixteen review items pass, and the accepted source is
byte-identical to the stopped candidate.

The staged Issue 2 reconstruction is complete. The separate experiment wrap-up or synthesis has
not started, and no production, dossier, ledger, manuscript, or mathematical status changed.
