# 2026-09-11 — `cor:conditional-fiber-twelve-bound`: The sole `sorry` obligation is proved

Following the [statement record](2026-09-11-conditional-fiber-twelve-bound-statement.md). The three infrastructure gaps listed there
(The one-dimensional Brunn–Minkowski/Prékopa–Leindler, explicit decomposition along lines, a.e. non-degenerate) has been fully completed,
`ae_conditionalFiber_logConcave` in `FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean`
Is no longer `sorry`. The other five theorems in the file have not changed types or proofs.

## Sub-obligation completion status

| Sub-obligation | Status | Description |
|---|---|---|
| A: one-dimensional log-concave density ⇒ log-concavity on compact sets | Completed | A1 Compact sets Brunn–Minkowski, A2 **Fully general** Prékopa–Leindler (without boundedness assumptions), A3 `LineDensity.logConcave` fully proven |
| Explicit decomposition kernel of B along a line | Completed | B1 `compProd_baseLaw_sliceKernel`, B2 `ae_sliceKernel_eq` proved |
| B3 compact sets almost everywhere | **Not carried out as planned, and not needed** | See below "route deviation" |
| C assembly | completed | `ae_conditionalFiber_logConcave` none `sorry` |

## New file and public statement

1. `formalization/FunctionalInequalities/Probability/Line/BrunnMinkowski.lean`
   (namespace `FunctionalInequalities.Probability.Line`, 384 line)
   - `volume_add_le_volume_add`: `K L : Set ℝ` non-empty compact ⇒ `volume K + volume L ≤ volume (K + L)`.
   - `le_volume_combination`: `S T` non-empty measurable, `0 < t < 1` ⇒
     `ofReal t * volume S + ofReal (1-t) * volume T ≤ volume {z | ∃ x ∈ S, ∃ y ∈ T, z = t•x+(1-t)•y}`.
     A combinatorial set need not be measurable (right endpoint using outer measure), which is precisely the form required by the layered argument.
   - `prekopaLeindler`: `f g h : ℝ → ℝ` measurable, `f, g ≥ 0`, `0 < t < 1`,
     `∀ x y, f x ^ t * g y ^ (1-t) ≤ h (t*x + (1-t)*y)` ⇒
     `(∫⁻ ofReal f)^t * (∫⁻ ofReal g)^(1-t) ≤ ∫⁻ ofReal h`. **No boundedness assumption**.
   - private: `geom_le_arith` (ENNReal two-weighted AM–GM, Mathlib only has `NNReal`/`Real` versions),
     `lintegral_add_le_of_sup_one` (supremum-normalized arithmetic form), `prekopaLeindler_bddAbove`, `rpow_iSup`.

2. `formalization/FunctionalInequalities/Probability/HaarLine.lean`
   (Namespace `FunctionalInequalities.Probability`, line 101)
   - `lineMap`, `lineEquiv` ( `(ℝ ∙ θ)ᗮ × ℝ ≃ₗ[ℝ] E`, `(z, s) ↦ z + s • θ` ) and two `@[simp]` evaluation lemmas.
   - `exists_lintegral_line`: `m` is Haar, `‖θ‖ = 1` ⇒ there exists `c ≠ 0, ≠ ⊤` such that for every measurable `G`,
     `c * ∫⁻ G dm = ∫⁻ z : (ℝ∙θ)ᗮ, ∫⁻ s : ℝ, G (z + s•θ)` (outer `Measure.addHaar`, inner `volume`).

3. `formalization/FunctionalInequalities/KLS/LogConcave/Line/OfDensity.lean`
   (namespace `FunctionalInequalities.KLS.LineDensity`, line 65)
   - `LineDensity.logConcave (d : LineDensity μ) : LogConcave μ`.
     Opposite to the existing `LogConcave.exists_lineDensity` in direction, called by the `d.` point notation (`research/naming.md`).

4. `formalization/FunctionalInequalities/KLS/ConditionalFiber/SliceKernel.lean`
   (Namespace `FunctionalInequalities.KLS.ConditionalFiber`, line 253)
   - `sliceMass p b`, `SliceGood p`, `sliceDensity p b t`, `sliceKernel p hp` (`Kernel (Direction E × E) ℝ`).
     `hp : Measurable p` is an explicit parameter (`Kernel.piecewise` requires a measurable set proof); `Measurable` is `Prop`, so there is no choice ambiguity.
   - `measurable_sliceMass`, `measurableSet_sliceGood`, `measurable_sliceDensity`,
     `sliceKernel_apply_of_good`, `sliceKernel_eq_withDensity_of_good`, `sliceKernel_apply_of_not_good`,
     `instIsMarkovKernelSliceKernel`.
   - `inner_add_smul_orthogonal`, `coordinates_add_smul_orthogonal`, `baseMap_add_smul_orthogonal`:
     orthogonal decomposition under `coordinates (θ, z + tθ) = ((θ, z), t)`.
   - `sliceKernel_mul_sliceMass`: `Z ≠ ⊤` ⇒ `sliceKernel b A * Z = ∫⁻ t in A, ofReal (p (reconstruct b t))`
     (also covers `Z = 0`).
   - `exists_lintegral_line_density`: Haar density `μ` along a fixed direction via Fubini decomposition.
   - `compProd_baseLaw_sliceKernel`: `baseLaw μ ρ ⊗ₘ sliceKernel p hp = jointLaw μ ρ`.
   - `ae_sliceKernel_eq`: `∀ᵐ b ∂baseLaw μ ρ, sliceKernel p hp b = kernel μ ρ b`.

## Modified Existing Files

- `FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean`:
  `affineSupport_eq_top_of_absolutelyContinuous` Remove `private` (types and proofs unchanged, docstring already present).
- `FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean`:
  Add four import statements; add private lemma `isBorellDensity_sliceKernel`; complete `ae_conditionalFiber_logConcave`;
  Update module docstring (no longer claims to have `sorry` or gaps). Five synthesis theorems unchanged.

## Route deviation (compared to hints)

1. **B3 is not needed.** The hint requires proving "good sets almost everywhere." In fact, at bad points `sliceKernel b = Measure.dirac 0`,
   and `KLS.logConcave_dirac` has already established the logarithm-concavity of the Dirac law, so `LogConcave (sliceKernel p hp b)` holds for **each** `b`,
   without needing to distinguish between good and bad sets. The decomposition identity only requires "`Z < ⊤` almost everywhere," which is directly obtained from `exists_lintegral_line_density`
   by taking `F ≡ 1` (see `∫⁻ z, Z(θ,z) = c < ⊤`), and is written internally in `lintegral_section_eq`.
2. **A2 is made into a completely general statement.** The hint allows first leaving `sorry`; in practice, "supremum normalization + truncation taking limit"
   removes the boundedness assumption, so `prekopaLeindler` holds for any measurable non-negative `f g`.
3. **`c_θ` is not made into a measurable object.** Following the alternative route suggested in the hint: for each fixed `θ`, rewrite pointwise using `lintegral_congr`,
   with both sides sharing the same `c`; thus, no measurability of `θ ↦ c_θ` is required, and `c` is never computed.
4. **A2 uses real-valued rather than ENNReal-valued functions.** The slice formula `lintegral_eq_lintegral_meas_lt` only has a real-valued version;
   the real-valued form is exactly how A3 is used (in `IsBorellDensity`'s `ρ : V → ℝ`).

## Key Mathlib API used

- `MeasureTheory.lintegral_eq_lintegral_meas_lt` (layer cake), `MeasurableSet.measure_eq_iSup_isCompact` (inner regularity),
  `measure_union_add_inter`, `measure_preimage_add`, `Measure.addHaar_smul`,
  `IsCompact.sSup_mem` / `sInf_mem`, `ENNReal.iSup_add_iSup_le`, `ENNReal.mul_iSup`,
  `NNReal.geom_mean_le_arith_mean2_weighted`, `ENNReal.orderIsoRpow`, `lintegral_iSup`.
- `ContinuousLinearEquiv.isAddHaarMeasure_map`, `Measure.prod.instIsAddHaarMeasure`,
  `Measure.isAddLeftInvariant_eq_smul`, `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure`,
  `LinearEquiv.toContinuousLinearEquiv`, `Submodule.mem_orthogonal_singleton_iff_inner_right`,
  `LinearMap.coprod` / `toSpanSingleton`.
- `ProbabilityTheory.Kernel.withDensity(')`, `Kernel.piecewise`, `Kernel.measurable_kernel_prodMk_left`,
  `Measure.compProd_apply`, `Measure.prod_apply`, `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`.
- `UpperSemicontinuous.comp`, `Continuous.comp_upperSemicontinuous` (slice density's upper semicontinuity).

## Skepticism at the Statement Level

No existing statements were found to be incorrect: `ae_conditionalFiber_logConcave` can be proven as is, no missing premises or opposite directions were found.
Two points recorded for owner's judgment:

- `hρ : Admissible μ ρ` and `[CompleteSpace E]` are not used in the proof of this lemma (the conclusion holds for any direction law).
  To maintain consistency with the parameter list of the five theorems in the same block and without changing types, we locally close two linter checks using `set_option linter.unusedSectionVars false in` and `set_option linter.unusedVariables false in`, rather than removing parameters. Whether to tighten the signature is left to the owner.
- `hac : μ ≪ m` is only used to derive the affine support as ⊤ (thus implying the interior of the support is non-empty and a Borell density exists); the reference measure `m` itself does not appear in the conclusion.

## Where should these new lemmas be placed in the shared file?

- `volume_add_le_volume_add`, `le_volume_combination`, `prekopaLeindler`: remain in `Probability/Line/BrunnMinkowski.lean`. They are unrelated to log-concavity and are purely one-dimensional measure-theoretic tools, on the same level as `Probability/Line/{Cdf,AffineProfile,ExpIntegral}.lean`. If future high-dimensional Prékopa–Leindler is to be developed, this file naturally serves as the one-dimensional base case.
- `lineEquiv`, `exists_lintegral_line`: remain in `Probability/HaarLine.lean`. Independent of probability, relying only on inner product spaces and Haar measure; if directional Fubini is to be performed on the `Energy/` side in the future, it should be taken from here.
- `LineDensity.logConcave`: it is also plausible to merge into `KLS/LogConcave/Line/Density.lean` (being inverses of `LogConcave.exists_lineDensity`), but that would make `Density.lean` depend on `BrunnMinkowski.lean`. For now, it is kept independently in `Line/OfDensity.lean`, with a cleaner dependence on direction; if the owner values "concentration of density conclusions" more, merging into `Density.lean` would be a low-risk modification.
- `sliceMass` / `sliceKernel` family: remain in `KLS/ConditionalFiber/SliceKernel.lean`, on the same level as `ConditionalFiber/{Closed,EnergyComparison}.lean`. It provides an explicit construction of fiber bundles, and does not belong to `KLS/LogConcave/` (no log-concavity assumption, only requiring a Haar density).

## Compilation and Axioms

```
lake env lean -DwarningAsError=true <each new file with KLS/LogConcave/ConditionalFiber.lean>   # no output at all
lake build                                                                                # 3383 jobs passed successfully
```

`#print axioms`: `ae_conditionalFiber_logConcave`, `conditionalFiber_literatureConstant_le_four_mul`,
`conditionalFiber_literatureConstant_le_twelve_mul_of_four`, `compProd_baseLaw_sliceKernel`,
`Probability.Line.prekopaLeindler`, `LineDensity.logConcave`
all depend only on `propext, Classical.choice, Quot.sound`.

## Not done

Under current round constraints: not registered (`FunctionalInequalities.lean` aggregation import, lakefile `Solutions` root,
`research/a-series/ledger.yaml`, `research/check_blueprint.py`'s `CERTIFICATES`, `research/tasks.json`
None of them have been modified), the Blueprint's `\lean{}`/`\leanok` have not been added, have not been `git commit`, nor `git push`.
`tasks.json` still marks this node as `missing`, and the owner must mark it proved and write the certificate during the registration round.
`solutions/CorConditionalFiberTwelveBound.lean`.
