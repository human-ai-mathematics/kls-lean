# 2026-09-11 — `thm:smooth-gradient-relaxation-two-cheeger`: filling proofs (WIP module)

This follows the list of 26 sorry obligations in `2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md`.

## Decision

- Completed 21 obligations (#1–#12, #14–#21, #25, #26) in `formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean`.
  No theorem/def statements (types) or imports changed, and no declarations were added other than new private helper lemmas.
- Retained 5 `sorry` proofs for the open comparisons under singular measures (of the AGS 2013 Density type) and their consequences:
  `LocalSlope.relaxation_eq_asymptoticLipschitz` (#13), `Cheeger.energy_eq_ofAsymptoticLipschitz` (#15),
  `SmoothGradient.relaxation_eq_localSlope` (#22), `SmoothGradient.relaxation_eq_two_mul_cheeger` (#23),
  and `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger` (#24).
  Note: #23 and #24 are purely algebraic/transport rewrites. Their sorry proofs remain only because they reduce to #22 through
  `Functional.ext`/`two_mul_energy`; once #22 is proved, each takes three lines.
- Cleaned up `unusedSectionVars` consistently: added `omit ... in` to 14 top-level declarations (20 occurrences in the file).
  These must precede the docstring, or Lean reports `unexpected token 'omit'; expected 'lemma'`.
  This linter reports in rounds: fixing one batch reveals the next. It took 4 compilation rounds to converge.
- The module docstring's original sentence "Every proof body is `sorry`" was no longer accurate; it now lists the 5 remaining open obligations.
- No registration, commit, or push; no shared files changed.

## Individual results

| # | Name (omitting `FunctionalInequalities.Energy`) | Status | Key API |
|---|---|---|---|
| 1 | `AsymptoticLipschitz.apply_const` | Completed | `iInf_le_of_le`, `le_antisymm _ bot_le` |
| 2 | `AsymptoticLipschitz.apply_eq_zero_of_subsingleton` | Completed | `Subsingleton.elim` + #1 |
| 3 | `AsymptoticLipschitz.apply_le_of_lipschitzWith` | Completed | `ENNReal.ofReal_coe_nnreal`, `div_le_iff₀`, `LipschitzWith.dist_le_mul` |
| 4 | `LocalSlope.apply_le_asymptoticLipschitz` | Completed | `iInf_mono`, `iSup_mono`, `le_iSup₂_of_le x` (take `z = x`) |
| 5 | `LocalSlope.energy_le_asymptoticLipschitz` | Completed | `lintegral_mono`, `ENNReal.pow_le_pow_left` |
| 6 | `LocalSlope.Admissible.of_asymptoticLipschitz` | Completed | `ne_top_of_le_ne_top` + #5 |
| 7 | `LocalSlope.coe_preEnergy_energy` | Completed | `ENNReal.coe_toNNReal` |
| 8 | `LocalSlope.lowerSemicontinuous_relaxation` | Completed | `PreEnergy.lowerSemicontinuous_sequentialRelaxation` |
| 9 | `LocalSlope.relaxation_toLp_le` | Completed | `PreEnergy.sequentialRelaxation_toAmbient_le` + #7 |
| 10 | `LocalSlope.le_relaxation_of_lowerSemicontinuous` | Completed | `PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous` + #7 |
| 11 | `LocalSlope.relaxation_eq_zero_of_subsingleton` | Completed | `nonempty_of_isProbabilityMeasure`, `memLp_const`, `Lp.ext`, `MemLp.coeFn_toLp` + #9 |
| 12 | `LocalSlope.relaxation_le_asymptoticLipschitz` | Completed | `PreEnergy.sequentialRelaxation_comp_le` + #6 + `ENNReal.toNNReal_mono` + #5 |
| 13 | `LocalSlope.relaxation_eq_asymptoticLipschitz` | **Intentionally retained (open comparison)** | — |
| 14 | `Cheeger.two_mul_energy` | Completed | `ENNReal.mul_div_cancel'` |
| 15 | `Cheeger.energy_eq_ofAsymptoticLipschitz` | **Intentionally retained (open comparison)** | — |
| 16 | `Cheeger.energy_eq_zero_of_subsingleton` | Completed | #11 + `ENNReal.zero_div` |
| 17 | `SmoothGradient.Test.localSlope_admissible` | Completed | `ContDiff.locallyLipschitz`, `Test.memLp_two` + #18 |
| 18 | `SmoothGradient.Test.localSlope_energy` | Completed | `LocalSlope.apply_eq_norm_gradient` (pointwise, with no measure assumptions), `ENNReal.ofReal_pow`, `ofReal_integral_eq_lintegral_ofReal`, `Test.coe_energy` |
| 19 | `SmoothGradient.localSlope_relaxation_le` | Completed | `PreEnergy.sequentialRelaxation_comp_le` + #17 + #18 + `ENNReal.toNNReal_coe` |
| 20 | `SmoothGradient.relaxation_le_localSlope_of_absolutelyContinuous` | Completed | `sequentialRelaxation_le_of_recovery_sequences`, `LocalSlope.admissible_iff_memLp_gradient`, `LipschitzApproximation.exists_smooth_weighted_L2` (`B = ContinuousLinearMap.id`), `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`, `L2.norm_toLp_sq`, `LocalSlope.energy_eq_integral_gradient`, `Tendsto.liminf_eq` |
| 21 | `SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous` | Completed | `Functional.ext` + `le_antisymm` #20 #19 |
| 22 | `SmoothGradient.relaxation_eq_localSlope` | **Intentionally retained (open comparison)** | — |
| 23 | `SmoothGradient.relaxation_eq_two_mul_cheeger` | **Intentionally retained** (reduces to #22) | — |
| 24 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger` | **Intentionally retained** (reduces to #23) | — |
| 25 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous` | Completed | `Intrinsic.energy_apply` (both sides)+ #21 + #14 |
| 26 | `KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | Completed | #25 + `LogConcave.intrinsic_absolutelyContinuous Measure.addHaar` |

## Verification

- `lake env lean FunctionalInequalities/Energy/WIP/Cheeger.lean`: no errors; exactly 5
  `declaration uses 'sorry'` warnings (lines 322, 366, 521, 527, 541), with no `unusedSectionVars` or other warnings.
- `lake env lean -DwarningAsError=true FunctionalInequalities/Energy/WIP/Cheeger.lean`: exactly the same 5 lines
  (sorry warnings promoted to errors), with no other diagnostics.
- Individual `#print axioms` checks for 25 completed top-level declarations: all report `[propext, Classical.choice, Quot.sound]`,
  with no `sorryAx`. The audit block was removed after compilation.

## Missing infrastructure (unchanged)

The inequality `Lip_a` relaxation ≤ slope relaxation under singular laws (the core of AGS 2013 Density) still has no repository input.
Mathlib `db584cd6` also has no Hopf–Lax semigroup / weak upper gradient / metric Sobolev space infrastructure.
The possible Euclidean detour (mollification yielding
`SmoothGradient.relaxation ≤ AsymptoticLipschitz.relaxation`, combined with #19 to obtain
`LocalSlope ≤ Smooth ≤ Lip_a`) still lacks its final step, so #13 and #22 remain open.
