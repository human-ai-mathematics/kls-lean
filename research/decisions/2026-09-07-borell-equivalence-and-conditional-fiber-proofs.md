# Borell equivalence proof completion and proofs of the six conditional-fiber contracts

Date: 2026-09-07 (Asia/Shanghai). Baseline: uncommitted working tree atop `0451f2e`, starting at
[proof handover decision](2026-09-07-borell-equivalence-claude-handoff.md). Lean/Mathlib remains at v4.33.0,
Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. This handover was completed by Claude, completing seven `sorry`,
with no changes to the mathematical content, routing configurations, or historical decision documents of any already proven statements. This decision does not involve commit/push, remote CI
or Pages deployment.

## Overview of Results

| goal | before | now |
| --- | --- | --- |
| `KLS.LogConcave.borel_iff` | `sorry` | proved; wrapped by `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate` |
| ConditionalFiber six contract | six `sorry` | all proved; node definition obtains `\leanok` |
| ledger | ten proved + one drafted | eleven proved, `checked_by: lean` |
| `check_blueprint.CERTIFICATES` | ten mappings | eleven mappings |
| `atlas.py check` | passed | passed: 74 mathematical nodes, 11 certificates, acyclic |
| Python test | 100 passed | 100 passed |
| default `lake build` | passed (including `sorryAx`) | passed, all new axioms guards are standard three axioms |

## Borell Equivalence: Actual Proof Path

[LogConcaveBorel.lean](../../formalization/FunctionalInequalities/KLS/LogConcaveBorel.lean)
Add five named auxiliary lemmas, then prove the main theorem:

- `innerMeasure_mono`, `innerMeasure_le`, `le_innerMeasure_of_isCompact`: Inner measure is monotonic,
  does not exceed the original measure, and each compact subset provides a lower bound. These do not require finite-dimensional or Borel structure.
- `innerMeasure_eq_of_measurableSet`: On measurable sets of the `InnerRegular` measure, the inner measure equals the measure,
  directly given by `MeasurableSet.measure_eq_iSup_isCompact`, with the supremum shape matching exactly.
- `isCompact_combination`, `combination_mono`: The Minkowski sum of two compact sets is a compact set as the continuous image under `(x,y) ↦ t•x + (1-t)•y`, hence compact; the sum is monotonic for both sets.
- `LogConcave.borel_iff`: The Borel direction to the compact set direction is obtained via compact measurability and `innerMeasure_le`.
  The reverse direction first expresses the two Borel masses via inner regularity as supremums over compact subsets, then uses `ENNReal.orderIsoRpow`'s `map_iSup` and `ENNReal.iSup_mul`/`mul_iSup` to move powers and products inside the supremum, and finally applies the compact set inequality to each pair of compact subsets, using the compact sum as a lower bound for the inner measure.
  The empty compact set handles zero mass; finite-dimensional is used only for inner regularity instances, and zero-dimensional spaces are included.

The certificate file provides a unique `certificate`, along with `Fin n`, `Fin 0`, and type checking with unilateral inference, and includes standard axiom guards for `certificate`, `borel_iff`, `innerMeasure_eq_of_measurableSet`, and `isCompact_combination`.

## Conditional-fiber: Proofs of six contracts

[ConditionalFiber.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber.lean)
The definition remains unchanged. New auxiliary objects: `reconstruct_coordinates` (reconstruction and coordinate inverse), `baseMap` and
`baseLaw_eq_map` (the base law is the pushforward of `ρ ⊗ μ` by the base projection), `compProd_baseLaw_kernel`
(the local name of `Measure.disintegrate`), `memLp_id_two_iff`/`memLp_id_two_iff'`
(the second-moment finite lintegral expression), `instIsProbabilityMeasureBaseLaw`, and
`fiberEnergy_congr_kernel`, `fiberEnergy_congr_ae`, `ae_fiber_congr`.

| Contract | Proof points |
| --- | --- |
| `lintegral_baseLaw` | `lintegral_map` to `ρ ⊗ μ`, Tonelli (`lintegral_prod`), then reverse `lintegral_map` in each direction |
| `ae_memLp_id` | Integrating conditional second moments over the base law gives, via `Measure.lintegral_compProd` and the disintegration identity, the joint-law integral of `‖⟨x,θ⟩‖²`; `‖θ‖=1` bounds this by `∫‖x‖²dμ < ∞`, and `ae_lt_top` gives a.e. finiteness |
| `measurable_fiberEnergy` | conditional mean using `StronglyMeasurable.integral_kernel_prod_right'`, conditional variance and conditional second moment using `Measurable.lintegral_kernel_prod_right'`; `GoodFiber` set written as intersection of three measurable sets; `Measurable.ite` and ENNReal division |
| `energyWith_eq` | `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd` gives a.e. kernel equality, `fiberEnergy` depends only on `κ b` through the kernel |
| `energy_congr_ae` | The joint-law mass of the reconstruction preimage of `f ≠ g` equals `μ{f ≠ g} = 0` (`ae_map_iff`, `Measure.snd_prod`); the disintegration identity and `ae_ae_of_ae_compProd` then give a.e. equality on a.e. fibers, completed by `evariance_congr` |
| `form_toLp` | `Lp.stronglyMeasurable`, `Lp.memLp`, `MemLp.coeFn_toLp` substituted into `energy_congr_ae` |

The two `MemLp` assumptions in `energy_congr_ae` were not used in the proof; the signature is retained unchanged and is named with an underscore.
(`_hf₂`, `_hg₂`) shows this; the conclusion holds for all measurable representatives, and the L² context is used by `form_toLp`.
Six contracts obtain standard axiom guards at the end of `solutions/StatementChecks.lean`.

## Metadata Synchronization

- Blueprint: Add certificate declaration to `thm:compact-borell-logconcavity-equivalence`'s `\lean`, with both declaration and proof marked `\leanok`, and revise the proof text to actual argument; `def:conditional-fiber-form` marked `\leanok` and replace the "draft placeholder" text with the actual content of six contracts.
- ledger: Update Borell node to `proved / lean`, remove the sentence "contains sorry" from statement and record the certificate. No new ledger node is added for conditional-fiber: the definition is not a proved theorem.
- tasks.json: Add evidence of Borell node including `LogConcaveBorel.lean` and certificate file, refresh the `StatementChecks.lean` hash; update the infrastructure of conditional-fiber from `missing` to `available`, clear gaps, and refresh the `ConditionalFiber.lean` hash.
- Update certificate count in current guide (HANDOFF, solutions/README, verification.md, two READMEs) to eleven.

## Evidence Boundary

The density-representation node `thm:borell-logconcave-density`, `lem:conditional-fiber-form`, and their downstream nodes obtained no new proofs; this decision only removes the two root causes of Borell equivalence and conditional-fiber definition `sorry`.
The reading restrictions of Borell's (1974) original text remain unchanged. The final verification receipt is generated by `python3 research/verify.py` after this decision and all guideline edits, with its source code SHA recorded within the receipt itself, not written back to this file.
