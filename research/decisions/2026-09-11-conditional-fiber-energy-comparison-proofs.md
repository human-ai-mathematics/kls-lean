# 2026-09-11 — `lem:conditional-fiber-energy-comparison`: Proofs of the two sorry obligations

## Decision

- Fill in the two `sorry` in `formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean`
  (`energy_le_of_fiberBound`, `literatureConstant_le_of_fiberBound`). Types of two `theorem` and `FiberBound`
  One character unchanged; sentence-by-sentence alignment between statement and Blueprint remains
  [Statement records of the same day](2026-09-11-conditional-fiber-energy-comparison-statement.md) take precedence.
- Work only within this file: add `private` auxiliary lemma / one `private def`, two `import`
   (`Mathlib.MeasureTheory.Function.SpecialFunctions.Inner`, `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`).
  No changes made to any shared files, not registered (`FunctionalInequalities.lean` aggregate import, `lakefile.toml` of `Solutions` root,
  `research/a-series/ledger.yaml`, `research/check_blueprint.py`'s `CERTIFICATES`, `research/tasks.json`),
  No changes to Blueprint's `\lean{}`/`\leanok`. No `git commit`, no `git push`.

## Compilation

Under `formalization/`:

```
lake env lean FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean
```

Both have no diagnosis (no error, no warning, no `declaration uses 'sorry'`). `#print axioms` applies to both top-level theorems as
`[propext, Classical.choice, Quot.sound]`. (The x86_64 lake / arm64 xcrun incompatibility issue with CommandLineTools is handled by the git wrapper script + `GIT_EXEC_PATH`/`GIT_TEMPLATE_DIR` workarounds; lake re-cloned `.lake/packages/checkdecls` upon its first run due to manifest URL changes, affecting only `.lake/`, without altering the repository content.)

## Proof structure (private lemma divided into three groups)

### 1. Isometric transportation (`section IsometryTransport`, general finite-dimensional Hilbert space `X Y`)

- `localSlope_apply_comp_isometryEquiv (e : X ≃ᵢ Y) h x : apply (h ∘ e) x = apply h (e x)`:
  Change variables directly in the `iInf`/`iSup` definition of `apply` using `e.surjective.iSup_comp`, then finish with `e.dist_eq`.
- `localSlope_energy_comp_isometryEquiv`: `MeasurePreserving.lintegral_comp_emb` (use
  `e.toHomeomorph.toMeasurableEquiv.measurableEmbedding`, no need for `apply` measurability).
- `evariance_comp_measurePreserving`: `evariance` expanded using `MeasurePreserving.integral_comp` and
  `lintegral_comp_emb`.
- `holds_of_isometryEquiv`: `Holds ν' C → Holds ν C` (`e : X ≃ᵢ Y` preserves measure `ν ↦ ν'`). Test `g` against `g ∘ e.symm`,
  Local Lipschitz by `LocallyLipschitz.comp`, `L²` by `MemLp.comp_measurePreserving`, energy and variance by the first two.

### 2. Full affine support (`section FullAffineSupport`)

- `surjective_intrinsicReconstruct`, `intrinsicIsometryEquiv`: `affineSupport ν = ⊤` when
  `Probability.reconstruct ν : direction ≃ᵢ E` ( `Equiv.ofBijective` + `AffineIsometry.isometry` ),
  `Probability.measurePreserving_reconstruct` is preserved.
- `holds_iff_intrinsicMeasure`: `Holds ν C ↔ Holds (intrinsicMeasure ν) C` (each direction used once
  `holds_of_isometryEquiv`).
- `intrinsic_constant_eq_iInf`: `Intrinsic.constant ν = ⨅ C : {C // Holds ν C}, C`.
- `evariance_le_mul_energy_of_iInf_le`: `⨅ C : {C // Holds ν C}, C ≤ B`, `B ≠ ⊤`, `Admissible ν g` ⇒
  `evariance g ν ≤ B * energy ν g`. Using `le_iInf` + `ENNReal.iInf_mul` ( `Nonempty` excluded by `B ≠ ⊤` for empty infimum),
  no `ε` remaining terms; `B = 0` and `energy = 0` require no branching. This is the step mentioned in the task prompt as "most delicate", unchanged `Poincare/LocalSlope/Basic.lean`.
- `affineSupport_eq_top_of_absolutelyContinuous`: `μ ≪ m` (Haar) ⇒ `affineSupport μ = ⊤`
  ( `Measure.addHaar_affineSubspace` + `measure_compl_affineSupport` ).
- `affineSupport_eq_top_of_evariance_ne_zero`: `ν : ProbabilityMeasure ℝ`, `evariance id ν ≠ 0` ⇒
  `affineSupport ν = ⊤` (the direction of a true affine subspace is a proper submodule of `ℝ` ⇒ `⊥` ( `Submodule.finrank_lt`, `finrank_self`,
  `Submodule.finrank_eq_zero` ) ⇒ all points in the support equal `supportPoint` ⇒ `id =ᵐ const` ⇒ variance is 0).

### 3. Analytic core (main namespace)

- `lipschitzWith_reconstruct b : LipschitzWith 1 (reconstruct b)`.
- `hasDerivAt_comp_reconstruct`/`localSlope_apply_comp_reconstruct`: `f` is differentiable at `reconstruct b t` ⇒
  The slice `s ↦ f (reconstruct b s)` has a derivative `fderiv ℝ f x θ` (`HasFDerivAt.comp_hasDerivAt`) at `t`.
  Local slope `= ofReal |fderiv ℝ f x θ|` (one-dimensional instance of `Energy.LocalSlope.apply_eq_norm_gradient` +
  `HasDerivAt.hasGradientAt.gradient`).
- `fderiv_apply_eq_inner_gradient : fderiv ℝ f x θ = ⟪θ, ∇f x⟫` (`InnerProductSpace.toDual_symm_apply`).
- `directionalIntegrand f q := ofReal (⟪θ, ∇f(reconstruct b t)⟫²)` (`q = (b, t)`), `measurable_directionalIntegrand`
  Use `LipschitzApproximation.measurable_gradient` + `Measurable.inner`.
- `ae_ae_reconstruct`: `μ`-a.e. has measurable properties along a.e. fibers (analogous to `ae_restrict_congr`: `ae_map_iff`,
  `Measure.snd_prod`, `compProd_baseLaw_kernel`, `Measure.ae_ae_of_ae_compProd`).
- `ae_memLp_comp_reconstruct`: `MemLp f 2 μ` ⇒ a.e. section over the fiber `MemLp 2` (analogous to `ae_memLp_id`:
  `Measure.lintegral_compProd`, `lintegral_map`, `lintegral_prod_symm`, `ae_lt_top`).
- Main proof of `energy_le_of_fiberBound`:
  1. `hI`: `∫⁻ b ∫⁻ t directionalIntegrand = ∫⁻ x ∫⁻ θ ofReal ⟪θ,∇f x⟫² dρ dμ` (compProd → jointLaw →
     `lintegral_map` + `reconstruct_coordinates` → `lintegral_prod_symm`).
  2. `hframe`: `d * ∫⁻ θ ofReal ⟪θ,u⟫² dρ = ofReal ‖u‖²` (`Integrable.of_bound`,
     `ofReal_integral_eq_lintegral_ofReal`, `hρ.frame_identity u u`, `real_inner_self_eq_norm_sq`).
  3. `hItot`: total directional integral `≠ ⊤` (`1 ≤ d` from `positive_dimension`, with `energy_eq_lintegral_gradient`,
     (`hf.finite_energy`); thus a.e. the directional integral over the fiber is finite.
  4. `hfiberwise`: a.e. `b`, non-degenerate case `energyAt ≤ κ * ∫⁻ t directionalIntegrand`: slice `Admissible`
     (Group 3 + `ae_memLp_comp_reconstruct` + finiteness), `intrinsic_constant_eq_iInf` +
     `affineSupport_eq_top_of_evariance_ne_zero` convert `hfiber` to `⨅ ≤ κ·Var`,
     `evariance_le_mul_energy_of_iInf_le` For specific test inequality, `ENNReal.div_le_iff` divided by variance. Degenerate fibers are 0.
  5. Assembly: `lintegral_mono_ae`, `lintegral_const_mul'`, `hI`, `hframe`, `energy_eq_lintegral_gradient`;
     `≠ ⊤` by `ENNReal.mul_ne_top` and `ne_top_of_le_ne_top`.
- `literatureConstant_le_of_fiberBound`: `Holds μ (κ*C)` direct expansion proof (`form_toLp` puts `toLp f` into
  `domain μ ρ`, `L2.variance_toLp` + `ofReal_variance` replace `L2.variance` with `evariance` (connected to obligation 1),
  Again via `holds_iff_intrinsicMeasure` (`affineSupport_eq_top_of_absolutelyContinuous`) and `iInf_le_of_le`.
  No `Poincare.L2Comparison` or `SmoothTest.constant_eq_intrinsicMeasure_and_localSlope` is needed.

## Correspondence with Blueprint proof segments

| Blueprint | Lean |
|---|---|
| "A finite upper bound for the literature infimum is itself valid: choose admissible constants below that bound plus 1/j and pass to the limit" | `evariance_le_mul_energy_of_iInf_le` (using `ENNReal.iInf_mul` in one step, without `1/j` sequence) |
| "Disintegration gives square integrability of the restricted test and integrability of its directional derivative on almost every fiber" | `ae_memLp_comp_reconstruct`, `hItot` + `ae_lt_top` |
| "Rademacher's theorem, absolute continuity, and Fubini identify that derivative with ⟨∇f,θ⟩" | `hdiff` (`ae_differentiableAt_of_locallyLipschitz` + `hac.ae_le`), `ae_ae_reconstruct`, `localSlope_apply_comp_reconstruct`, `fderiv_apply_eq_inner_gradient` |
| "Dividing the assumed fiber inequality by its positive variance and using Tonelli" | `hfiberwise` (`ENNReal.div_le_iff`), `hI` (`lintegral_prod_symm`) |
| "The last equality is the frame identity" | `hframe` |
| "Conditional Dirac laws have zero numerator; exceptional ... fibers are null" | `energyAt`'s `if_neg` branch; a.e. filter |
| "puts the test in the maximal form domain before the form-gap inequality is applied" | `hmem : toLp f ∈ domain μ ρ` |
| "The final multiplication by C is the abstract implication in lem:finite-energy-factor-poincare" | Expand directly on `Holds` (naked function version), without invoking `Poincare.L2Energy` |

## To be moved to shared file auxiliary lemma (to be left for registration phase)

- `holds_of_isometryEquiv`, `holds_iff_intrinsicMeasure`, `intrinsic_constant_eq_iInf`, `evariance_le_mul_energy_of_iInf_le` belong to `Poincare.LocalSlope` (`Poincare/LocalSlope/Basic.lean`).
- `localSlope_apply_comp_isometryEquiv`, `localSlope_energy_comp_isometryEquiv` belong to `Energy.LocalSlope`.
- `affineSupport_eq_top_of_absolutelyContinuous`, `affineSupport_eq_top_of_evariance_ne_zero`, `surjective_intrinsicReconstruct`, `intrinsicIsometryEquiv` belong to `Probability` (`AffineSupport.lean`).
- `evariance_comp_measurePreserving` is a gap in the general Mathlib.
- `ae_ae_reconstruct`, `ae_memLp_comp_reconstruct`, `lipschitzWith_reconstruct` belong to the base module `KLS.ConditionalFiber`.

## Not done / Future work

- Unregistered, unsubmitted, unpushed; no modifications to Blueprint, `FunctionalInequalities.lean`, `lakefile.toml`, `solutions/README.md`, `research/tasks.json`, `research/a-series/ledger.yaml`.
- If registered: `cor:conditional-fiber-twelve-bound` is available `κ = 4` (`KLS.LogConcave.localSlope_constant_le_four_evariance`), instantiated `literatureConstant_le_of_fiberBound`.
