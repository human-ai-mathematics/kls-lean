# Weighted smooth approximation: semantic review and completion of four proofs

Date: 2026-09-06. This follows the [statement handoff](2026-09-06-weighted-approximation-statements.md).
The task is to review the semantics of the four Lean statements for
`lem:covariance-test-core-density` and complete their proofs if the semantics are correct.
This record changes no ledger status, Blueprint label, route status, or `tasks.json`
classification. The node remains `drafted / checked_by: null`; promotion belongs to later acceptance.

## Semantic review

All four signatures are byte-identical to the handoff batch (automatic comparison passed).
No conclusion is weakened and no input assumption added. Checks against Blueprint Appendix A:

- `gradient` is Mathlib's Hilbert gradient, zero where not differentiable. `ν ≪ m` and Rademacher ensure ν-a.e. differentiability of locally Lipschitz functions, so `MemLp (fun x ↦ B (gradient g x)) 2 ν` faithfully expresses `B∇g ∈ L²(ν;V)`.
- The main statement only requires square-integrable `B∇g`, allowing zero and singular B; its proof indeed does not use `∇g ∈ L²`.
- Dimension zero is quantified over; the proof has no special `finrank = 0` branch.
- Steps 2 and 4 conclude `MemLp` for the original function and gradient from global Lipschitz continuity, boundedness, and probability, as in the handoff.
- Step 4 retains any closed interval `[a, b]` and the same Lipschitz constant `K`; `a = 0, b = 1` recovers the Blueprint's range-preserving version.

## Proof structure

`formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation.lean` now has
no `sorry`. Helpers share the same namespace; reusable ones include:

- `lipschitzOnWith_of_locallyLipschitz_of_isCompact`: a locally Lipschitz real function is globally Lipschitz on a compact set (finite subcover and Lebesgue number lemma).
- `ae_differentiableAt_of_locallyLipschitz`: Haar-a.e. differentiability of locally Lipschitz functions (closed-ball exhaustion and McShane extension, reducing to Mathlib's `LipschitzWith.ae_differentiableAt`).
- `tendsto_eLpNorm_zero_of_dominated`: dominated convergence for `eLpNorm` when `0 < p < ∞`.
- `gradient_scaled_mul`: gradient formula for a cutoff times a function at a differentiable point.

Analysis: scale a fixed `bump` (one at radius 1, zero outside radius 2) to obtain `scaled R`
and normalized `kernel m R`. `mollify m R g = g ⋆ kernel m R` is smooth, preserves the Lipschitz
constant, lower/upper bounds, and compact support, and satisfies `‖mollify − g‖ ≤ 2 K R`.
Pointwise gradient convergence uses neither weak derivatives nor Lebesgue differentiation:
compare with the affine model `g x + L (· − x)` at differentiable points. The affine-convolution
derivative identity `integral_affine_smul_fderiv_kernel` follows from Mathlib's convolution
derivative formula and uniqueness. Control the remainder with `C₀ m`, the scale-independent
kernel-derivative mass constant. Cutoffs use dominators `‖g‖` and `‖B∇g‖ + ‖B‖ M ‖g‖`;
the main theorem selects a diagonal from steps 1 and 2.

## Local checks

Git HEAD: `70ca1c19c4d207a31716c2e589c0b096521a5490`; earlier uncommitted changes remain.

| Check | Actual result |
| --- | --- |
| `lake build` (under formalization) | Passed, 3253 jobs; no warnings in this module or solution entry |
| `#guard_msgs` for four `#print axioms` in `solutions/LemCovarianceTestCoreDensity.lean` | Passed; transitive axioms exactly `propext`, `Classical.choice`, `Quot.sound` |
| `grep -w sorry\|admit` in the module and entry file | No matches |
| `python3 research/check_ledger.py` | Passed, 7 nodes |
| `python3 research/check_blueprint.py` | Passed, 86 labels, 4 active routes |
| `python3 research/atlas.py check` | Passed, 73 nodes, 6 certificates, no cycles |
| `python3 -m unittest discover -s research/tests` | 97 passed |
| `python3 research/statement_snapshot.py check` | Passed, 26 declarations match golden |

No `verify.py`, leanchecker replay, isolated rebuild, remote CI, commit, or push was run.

## Next steps (not performed in this record)

1. Build a `certificate` matching the ledger contract and promote `lem:covariance-test-core-density` from `drafted` to `proved / checked_by: lean`, subject to human acceptance.
2. Update the node's `note` and `infrastructure.status` in `tasks.json` (still missing and "proof placeholders"), and add Blueprint `\lean{}` / `\leanok` anchors.
3. Run `verify.py` to generate a receipt bound to the current source snapshot.
