import FunctionalInequalities.KLS.Geometry.CheegerInfimum
import FunctionalInequalities.KLS.Geometry.DistanceCutoff
import FunctionalInequalities.KLS.Isoperimetry
import FunctionalInequalities.KLS.Geometry.RegularSuperlevel
import FunctionalInequalities.KLS.Geometry.LipschitzCoarea
import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

/-!
# The two Cheeger infima agree

Hole-free module for Blueprint `lem:relative-perimeter-cheeger-infimum` (Appendix A), together
with the `h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν` clauses of
`thm:klartag-density-frontend-identification`.  It is a **drop-in replacement** of the
work-in-progress module `KLS/WIP/CheegerInfimum.lean`: it carries the same seven public
declarations with byte-identical `pp.all` signatures, the same two private helpers, and it proves
the two obligations that were left open there,
`smoothConstant_mul_lintegral_min_superlevel_le` and `smoothConstant_le_minkowskiConstant`.

## The two infima

For a probability law `ν` on a finite-dimensional real inner-product space `V`, with
`m(t) = min {t, 1 - t}`:

* `h_M = minkowskiConstant ν = inf_{0 < ν(B) < 1} ν⁺(B) / m(ν(B))` over Borel sets, where
  `minkowskiContent ν B = ν⁺(B) = liminf_{r ↓ 0} (ν(B^r) - ν(B)) / r` is the outer Minkowski
  content with open `r`-thickenings (`KLS/Geometry/MinkowskiContent.lean`,
  `KLS/Geometry/MinkowskiConstant.lean`);
* `h_S = smoothConstant ρ Ω ν = inf_{0 < ν(U) < 1} P_ρ(U) / m(ν(U))` over smooth domains, with the
  relative perimeter `relativePerimeter ρ Ω U` of `KLS/Geometry/RelativePerimeter.lean`
  (normalized `ℋ^{n-1}`, `ρ` the Borell density of `ν` with respect to Lebesgue measure `volume`,
  `Ω = interior ν.support`); `smoothConstant` lives in `KLS/Geometry/CheegerInfimum.lean`.

Both infima are `⊤` when no admissible set exists, in particular in dimension zero, where the
equality reads `⊤ = ⊤`.

## The two new proofs

`smoothConstant_mul_lintegral_min_superlevel_le` (the smooth coarea bound
`h_S · ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν`).  For almost every level `t` the strict superlevel set
`{u > t}` is a smooth domain (`SmoothDomain.ae_exists_superlevel`, the smooth Sard theorem) whose
frontier lies in `{u = t}` (`SmoothDomain.frontier_superlevel_subset`), so its relative perimeter
is at most the level integral `∫_{u = t} ρ dσ` of the density
(`relativePerimeter_le_lintegral_levelSet`); the multiplied form of the defining infimum,
`h_S · m(ν U) ≤ P_ρ(U)`, holds for **every** smooth domain, the degenerate masses `0` and `1`
through the `ENNReal` identity `⊤ * 0 = 0` (`smoothConstant_mul_min_le`); integrating over
`t ∈ (0, 1)` and applying the weighted coarea formula for the density
(`lintegral_enorm_gradient_eq_lintegral_levelSet_density`, the proved Lipschitz coarea formula
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` with weight `ofReal ∘ ρ`) gives
`∫ ‖∇u‖ dν`.  Nothing requires measurability of `t ↦ ∫_{u = t} ρ dσ`: `lintegral_mono_ae` does
not ask for it.

`smoothConstant_le_minkowskiConstant` (`h_S ≤ h_M`).  Fix a Borel `B` with `0 < ν B < 1`.  An
infinite Minkowski content makes the quotient `⊤`, so assume `ν⁺(B) ≠ ⊤`; then
`ν(closure B) = ν B` (`measure_closure_eq_of_minkowskiContent_ne_top`).  Write
`e r = ν(B^r) - ν B`.  The distance cutoff `w_r` has gradient integral at most
`(ν(B^r) - ν(closure B)) / r = e r / r` (`lintegral_enorm_gradient_distanceCutoff_le`) and `L¹`
distance at most `e r` to `𝟙_B` (`lintegral_enorm_distanceCutoff_sub_indicator_le`); mollifying it
by `exists_smooth_approximation_lipschitz` gives smooth Lipschitz `[0,1]`-valued `u_j` with
`‖u_j - w_r‖₁ → 0` and `∫ ‖∇u_j‖ dν → ∫ ‖∇w_r‖ dν`.  Since the balance is `1`-Lipschitz in the
set (`min_measure_le_lintegral_min_superlevel_add`),
`m(ν B) ≤ ∫₀¹ m(ν{u_j > t}) dt + ‖u_j - w_r‖₁ + e r`, so the smooth coarea bound gives
`h_S · (m(ν B) - (‖u_j - w_r‖₁ + e r)) ≤ ∫ ‖∇u_j‖ dν`.  The error is **subtracted from the
balance** rather than multiplied into `h_S`, so no finiteness of `h_S` is needed; letting
`j → ∞` yields `h_S · (m(ν B) - e r) ≤ e r / r` for every `r > 0` (the branch `m(ν B) ≤ e r` is
trivial and also supplies the side condition of `ENNReal.Tendsto.const_mul` in the other branch).
Finally `e r → 0` as `r ↓ 0` because `ν(closure B) = ν B`, so the left side converges to
`h_S · m(ν B)` while the right side has `liminf` equal to `ν⁺(B)`.

## Claimed, not claimed, restricted scope, dimension zero

Claimed (`minkowskiConstant_eq_smoothConstant`): for every probability law `ν` with a Borell
density `ρ` relative to `volume`, `h_M = h_S`.  This is stronger than the Blueprint's
"full-dimensional log-concave probability", which supplies such a density for the intrinsic law of
a log-concave `μ` through `KLS.LogConcave.exists_isBorellDensity`.  Consequently
(`constant_eq_smoothConstant_intrinsic`), for a log-concave `μ` the affine-support isoperimetric
constant `h_μ` of `def:isoperimetric-cheeger-scale` equals `h_ν^{sm,rel}`, and the inverse scales
agree (`inverseScale_eq_inv_smoothConstant_intrinsic`).

Not claimed: any relation between `ν⁺(B)` and `P_ρ(B)` for an individual set ("The statement
compares infima, not the two perimeters of each test set"), the BV-perimeter identification of
`thm:logconcave-cheeger-poincare-comparison`, the Poincaré-constant clause of
`thm:klartag-density-frontend-identification`, or Cheeger–Buser.

Restricted scope: none of the statements assumes `dim V ≥ 1`.  The intermediate
`smoothConstant_mul_lintegral_min_superlevel_le` carries the Borell-density hypothesis because it
uses the density in the coarea formula.  `lintegral_enorm_distanceCutoff_sub_indicator_le` needs
`B` nonempty: Mathlib's convention `Metric.infDist x ∅ = 0` makes `distanceCutoff ∅ r` the
constant `1` while `Metric.thickening r ∅ = ∅`, so the bound fails for the empty set.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff symmDiff

namespace FunctionalInequalities.KLS

universe u

namespace Isoperimetry

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### Smooth replacements of Lipschitz `[0,1]`-valued functions -/

omit [SecondCountableTopology V] in
/-- Mollification of a globally Lipschitz `[0,1]`-valued function: smooth, Lipschitz,
`[0,1]`-valued replacements converging in `L¹(ν)` with convergent gradient integrals.  This is the
"bounded `L¹` convolution assertion" of `lem:covariance-test-core-density` used by the Blueprint;
it needs only absolute continuity of `ν` with respect to a Haar measure.

Proved from `Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`, which mollifies `w`
against a smooth kernel: the approximants keep the interval `[0, 1]` and the Lipschitz constant `K`
of `w`, and both `u j - w` and `∇u j - ∇w` tend to zero in `L¹(ν)`.  The gradient clause here is
the `L¹` norm itself, so it follows from convergence in `L¹(ν; V)` and continuity of the norm. -/
theorem exists_smooth_approximation_lipschitz (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) {w : V → ℝ} {K : ℝ≥0}
    (hw : LipschitzWith K w) (hw01 : ∀ x, w x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ u : ℕ → V → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K' : ℝ≥0, LipschitzWith K' (u j)) ∧
        ∀ x, u j x ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖u j x - w x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V)) atTop
        (𝓝 (∫⁻ x, ‖gradient w x‖ₑ ∂(ν : Measure V))) := by
  obtain ⟨-, hwgrad, g, hg, hgL1, hggrad⟩ :=
    Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1 ν m hac w K hw 0 1
      fun x ↦ ⟨(hw01 x).1, (hw01 x).2⟩
  refine ⟨g, fun j ↦ ⟨(hg j).1, ⟨K, (hg j).2.1⟩, fun x ↦ ⟨((hg j).2.2.1 x).1, ((hg j).2.2.1 x).2⟩⟩,
    ?_, ?_⟩
  · simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hgL1
  · -- `L¹` convergence of the gradients is convergence in `L¹(ν; V)`, and the norm of that space
    -- is `f ↦ ∫⁻ ‖f‖ₑ`, which is continuous.
    have hLp : Tendsto (fun j ↦ ((hg j).2.2.2.2).toLp (gradient (g j))) atTop
        (𝓝 (hwgrad.toLp (gradient w))) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun j ↦ gradient (g j)) (fun j ↦ (hg j).2.2.2.2)
        (gradient w) hwgrad).2 hggrad
    simpa only [Lp.enorm_toLp, eLpNorm_one_eq_lintegral_enorm] using hLp.enorm

/-! ### The defining infimum in multiplied form -/

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The defining infimum of `h_S` in multiplied form: `h_S · m(ν U) ≤ P_ρ(U)` for every smooth
domain `U`, including the degenerate masses `0` and `1`.  There the balance vanishes and the bound
is the `ENNReal` identity `⊤ * 0 = 0`, so no finiteness of `h_S` is needed and the infimum, which
only ranges over domains of intermediate mass, is not applied to an inadmissible domain. -/
theorem smoothConstant_mul_min_le (ρ : V → ℝ) (Ω : Set V) (ν : ProbabilityMeasure V)
    (U : SmoothDomain V) :
    smoothConstant ρ Ω ν * min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) ≤
      relativePerimeter ρ Ω U := by
  rcases eq_or_ne (min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier)) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact zero_le
  have hmtop : min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_left _ _).trans prob_le_one)
  have hUpos : 0 < (ν : Measure V) U.carrier := by
    refine pos_iff_ne_zero.mpr fun h ↦ h0 ?_
    simp [h]
  have hUlt : (ν : Measure V) U.carrier < 1 := by
    refine lt_of_le_of_ne prob_le_one fun h ↦ h0 ?_
    simp [h]
  have hiInf : smoothConstant ρ Ω ν ≤ relativePerimeter ρ Ω U /
      min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) := by
    simp only [smoothConstant]
    refine le_trans (iInf_le _ U) ?_
    rw [iInf_pos hUpos, iInf_pos hUlt]
  exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hmtop)).mp hiInf

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The relative perimeter of a superlevel domain is bounded by the level integral of the weight:
the frontier of `{x | t < u x}` lies in `{x | u x = t}` for a continuous `u`, and the relative
perimeter only integrates over a subset of that frontier. -/
theorem relativePerimeter_le_lintegral_levelSet (ρ : V → ℝ) (Ω : Set V) {u : V → ℝ}
    (hu : Continuous u) {t : ℝ} (U : SmoothDomain V) (hU : U.carrier = {x | t < u x}) :
    relativePerimeter ρ Ω U ≤
      ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V) := by
  unfold relativePerimeter
  refine lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl
  rw [hU]
  exact Set.inter_subset_left.trans (SmoothDomain.frontier_superlevel_subset hu t)

omit [SecondCountableTopology V] in
/-- The weighted coarea formula for the Borell density: with `ν = volume.withDensity (ofReal ∘ ρ)`
the proved Lipschitz coarea formula with weight `ofReal ∘ ρ` reads
`∫ ‖∇u‖ dν = ∫ (∫_{u = t} ρ dσ) dt`. -/
theorem lintegral_enorm_gradient_eq_lintegral_levelSet_density {ν : ProbabilityMeasure V}
    {ρ : V → ℝ} (hρ : IsBorellDensity (ν : Measure V) volume ρ) {u : V → ℝ} {K : ℝ≥0}
    (hK : LipschitzWith K u) :
    ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V)
        ∂(volume : Measure ℝ) := by
  have hgrad : Measurable fun x : V ↦ ‖gradient u x‖ₑ :=
    (Energy.Euclidean.LipschitzApproximation.measurable_gradient u).enorm
  rw [← hρ.withDensity_eq,
    lintegral_withDensity_eq_lintegral_mul _ hρ.measurable.ennreal_ofReal hgrad,
    ← Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet hK hρ.measurable.ennreal_ofReal]
  exact lintegral_congr fun x ↦ by simp [Pi.mul_apply, mul_comm]

/-! ### The two coarea inequalities -/

-- `hu01` is part of the published interface and fixes the mathematical scope of the statement;
-- the Sard route below needs no bound on the range of `u`, so the linter is silenced instead of
-- the hypothesis being renamed.
set_option linter.unusedVariables false in
/-- Weighted coarea and Sard: for a smooth Lipschitz `[0,1]`-valued `u`,
`h_S ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν`. -/
theorem smoothConstant_mul_lintegral_min_superlevel_le {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    {K : ℝ≥0} (hK : LipschitzWith K u) (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) :
    smoothConstant ρ (interior (ν : Measure V).support) ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  have hpt : ∀ᵐ t ∂(volume : Measure ℝ),
      smoothConstant ρ (interior (ν : Measure V).support) ν *
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
        ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V) := by
    filter_upwards [SmoothDomain.ae_exists_superlevel hu] with t ht
    obtain ⟨U, hU⟩ := ht
    calc smoothConstant ρ (interior (ν : Measure V).support) ν *
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x})
        = smoothConstant ρ (interior (ν : Measure V).support) ν *
            min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) := by rw [hU]
      _ ≤ relativePerimeter ρ (interior (ν : Measure V).support) U :=
          smoothConstant_mul_min_le _ _ _ _
      _ ≤ ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V) :=
          relativePerimeter_le_lintegral_levelSet _ _ hu.continuous U hU
  calc smoothConstant ρ (interior (ν : Measure V).support) ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x})
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1, smoothConstant ρ (interior (ν : Measure V).support) ν *
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) :=
        (lintegral_const_mul _ (measurable_min_measure_superlevel ν u)).symm
    _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V) :=
        lintegral_mono_ae (ae_restrict_of_ae hpt)
    _ ≤ ∫⁻ t, ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V)
          ∂(volume : Measure ℝ) :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) :=
        (lintegral_enorm_gradient_eq_lintegral_levelSet_density hρ hK).symm

/-! ### The distance cutoff and the balance -/

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The `L¹(ν)` distance of a distance cutoff to the indicator: `w_r = 1` on `B`, `0 ≤ w_r ≤ 1`,
and `w_r = 0` off the open `r`-thickening, so `‖w_r - 𝟙_B‖₁ ≤ ν(B^r) - ν B`.  Nonemptiness of `B`
is needed, since `Metric.infDist x ∅ = 0` makes `distanceCutoff ∅ r` the constant `1`. -/
theorem lintegral_enorm_distanceCutoff_sub_indicator_le (ν : ProbabilityMeasure V) {B : Set V}
    (hB : B.Nonempty) (hBm : MeasurableSet B) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
  have hsub : B ⊆ Metric.thickening r B := Metric.self_subset_thickening hr B
  have hdiff : (ν : Measure V) (Metric.thickening r B \ B) =
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B :=
    measure_sdiff hsub hBm.nullMeasurableSet (measure_ne_top _ _)
  rw [← hdiff, ← lintegral_indicator_one (Metric.isOpen_thickening.measurableSet.diff hBm)]
  refine lintegral_mono fun x ↦ ?_
  by_cases hxB : x ∈ B
  · rw [distanceCutoff_eq_one_of_mem_closure hB hr (subset_closure hxB),
      Set.indicator_of_mem hxB]
    simp
  · by_cases hxt : x ∈ Metric.thickening r B
    · rw [Set.indicator_of_notMem hxB, Set.indicator_of_mem (Set.mem_sdiff_of_mem hxt hxB)]
      obtain ⟨h0, h1⟩ := distanceCutoff_mem_Icc B hr x
      rw [sub_zero, Real.enorm_eq_ofReal_abs, abs_of_nonneg h0]
      simpa using ENNReal.ofReal_le_one.2 h1
    · rw [distanceCutoff_eq_zero_of_notMem_thickening hB hr hxt,
        Set.indicator_of_notMem hxB]
      simp

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- The balance is `1`-Lipschitz in the set, in integrated form:
`m(ν B) ≤ ∫₀¹ m(ν{u > t}) dt + ‖u - 𝟙_B‖₁` for a measurable `[0,1]`-valued `u`.  The layer-cake
identity `lintegral_measure_symmDiff_superlevel` turns the `L¹` distance into
`∫₀¹ ν({u > t} ∆ B) dt`, and `min_measure_le_add_measure_symmDiff` compares the balances. -/
theorem min_measure_le_lintegral_min_superlevel_add (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : Measurable u) (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) {B : Set V}
    (hB : MeasurableSet B) :
    min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≤
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x})) +
        ∫⁻ x, ‖u x - B.indicator 1 x‖ₑ ∂(ν : Measure V) := by
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≤
        min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) +
          (ν : Measure V) ({x | t < u x} ∆ B) := by
    intro t _
    have h := min_measure_le_add_measure_symmDiff (A := B) (B := {x | t < u x}) ν hB
      (measurableSet_lt measurable_const hu)
    rwa [symmDiff_comm] at h
  have hstep : (∫⁻ _ in Set.Ioo (0 : ℝ) 1, min ((ν : Measure V) B) (1 - (ν : Measure V) B)) ≤
      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        (min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) +
          (ν : Measure V) ({x | t < u x} ∆ B)) :=
    setLIntegral_mono' measurableSet_Ioo hpt
  rwa [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one,
    lintegral_add_left (measurable_min_measure_superlevel ν u),
    lintegral_measure_symmDiff_superlevel ν hu hu01 hB] at hstep

/-! ### The two infima agree -/

/-- `h_S ≤ h_M`: distance cutoffs of a Borel set of finite content, smooth replacements, and the
weighted coarea bound. -/
theorem smoothConstant_le_minkowskiConstant {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    smoothConstant ρ (interior (ν : Measure V).support) ν ≤ minkowskiConstant ν := by
  classical
  have hac : (ν : Measure V) ≪ volume := by
    rw [← hρ.withDensity_eq]
    exact withDensity_absolutelyContinuous _ _
  simp only [minkowskiConstant]
  refine le_iInf fun B ↦ le_iInf fun hBm ↦ le_iInf fun hpos ↦ le_iInf fun hlt ↦ ?_
  have hm0 : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≠ 0 :=
    ne_of_gt (lt_min hpos (tsub_pos_of_lt hlt))
  have hmtop : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_left _ _).trans prob_le_one)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)]
  -- An infinite Minkowski content needs no argument.
  rcases eq_or_ne (minkowskiContent ν B) ⊤ with hc | hc
  · rw [hc]
    exact le_top
  have hcl : (ν : Measure V) (closure B) = (ν : Measure V) B :=
    measure_closure_eq_of_minkowskiContent_ne_top ν hc
  have hBne : B.Nonempty := nonempty_of_measure_ne_zero (ne_of_gt hpos)
  set e : ℝ → ℝ≥0∞ :=
    fun r ↦ (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B with hedef
  -- The single-radius estimate, with the error subtracted from the balance.
  have hmain : ∀ r : ℝ, 0 < r →
      smoothConstant ρ (interior (ν : Measure V).support) ν *
          (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r) ≤
        e r / ENNReal.ofReal r := by
    intro r hr
    rcases le_or_gt (min ((ν : Measure V) B) (1 - (ν : Measure V) B)) (e r) with hle | hgt
    · rw [tsub_eq_zero_of_le hle, mul_zero]
      exact zero_le
    have hne : min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r ≠ 0 :=
      ne_of_gt (tsub_pos_of_lt hgt)
    set w : V → ℝ := distanceCutoff B r with hwdef
    have hwL : LipschitzWith (Real.toNNReal r⁻¹) w := lipschitzWith_distanceCutoff B hr
    have hw01 : ∀ x, w x ∈ Set.Icc (0 : ℝ) 1 := distanceCutoff_mem_Icc B hr
    obtain ⟨g, hgreg, hgL1, hggrad⟩ :=
      exists_smooth_approximation_lipschitz ν volume hac hwL hw01
    set δ : ℕ → ℝ≥0∞ := fun j ↦ ∫⁻ x, ‖g j x - w x‖ₑ ∂(ν : Measure V) with hδdef
    have hwmeas : Measurable w := hwL.continuous.measurable
    -- for each mollification index, the error-corrected balance is controlled
    have hstep : ∀ j, smoothConstant ρ (interior (ν : Measure V).support) ν *
        (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - (δ j + e r)) ≤
          ∫⁻ x, ‖gradient (g j) x‖ₑ ∂(ν : Measure V) := by
      intro j
      obtain ⟨K', hK'⟩ := (hgreg j).2.1
      have hgmeas : Measurable (g j) := (hgreg j).1.continuous.measurable
      have hmeas1 : Measurable fun x : V ↦ ‖g j x - w x‖ₑ := (hgmeas.sub hwmeas).enorm
      have htri : ∫⁻ x, ‖g j x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤ δ j + e r := by
        calc ∫⁻ x, ‖g j x - B.indicator 1 x‖ₑ ∂(ν : Measure V)
            ≤ ∫⁻ x, (‖g j x - w x‖ₑ + ‖w x - B.indicator 1 x‖ₑ) ∂(ν : Measure V) := by
              refine lintegral_mono fun x ↦ ?_
              calc ‖g j x - B.indicator 1 x‖ₑ
                  = ‖(g j x - w x) + (w x - B.indicator 1 x)‖ₑ := by ring_nf
                _ ≤ ‖g j x - w x‖ₑ + ‖w x - B.indicator 1 x‖ₑ := enorm_add_le _ _
          _ = δ j + ∫⁻ x, ‖w x - B.indicator 1 x‖ₑ ∂(ν : Measure V) :=
              lintegral_add_left hmeas1 _
          _ ≤ δ j + e r :=
              add_le_add le_rfl (lintegral_enorm_distanceCutoff_sub_indicator_le ν hBne hBm hr)
      have hbal := min_measure_le_lintegral_min_superlevel_add ν hgmeas (hgreg j).2.2 hBm
      have hbal' : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≤
          (∫⁻ t in Set.Ioo (0 : ℝ) 1,
            min ((ν : Measure V) {x | t < g j x}) (1 - (ν : Measure V) {x | t < g j x})) +
              (δ j + e r) := hbal.trans (add_le_add le_rfl htri)
      calc smoothConstant ρ (interior (ν : Measure V).support) ν *
            (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - (δ j + e r))
          ≤ smoothConstant ρ (interior (ν : Measure V).support) ν *
              ∫⁻ t in Set.Ioo (0 : ℝ) 1,
                min ((ν : Measure V) {x | t < g j x})
                  (1 - (ν : Measure V) {x | t < g j x}) :=
            mul_le_mul' le_rfl (tsub_le_iff_right.mpr hbal')
        _ ≤ ∫⁻ x, ‖gradient (g j) x‖ₑ ∂(ν : Measure V) :=
            smoothConstant_mul_lintegral_min_superlevel_le hρ (hgreg j).1 hK' (hgreg j).2.2
    -- pass to the limit in the mollification index
    have hδe : Tendsto (fun j ↦ δ j + e r) atTop (𝓝 (e r)) := by
      simpa using hgL1.add (tendsto_const_nhds (x := e r))
    have hleft : Tendsto (fun j ↦ smoothConstant ρ (interior (ν : Measure V).support) ν *
        (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - (δ j + e r))) atTop
        (𝓝 (smoothConstant ρ (interior (ν : Measure V).support) ν *
          (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r))) :=
      ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.sub tendsto_const_nhds hδe (Or.inl hmtop)) (Or.inl hne)
    have hlim := le_of_tendsto_of_tendsto' hleft hggrad hstep
    refine hlim.trans ?_
    have hgradw := lintegral_enorm_gradient_distanceCutoff_le ν volume hac B hr
    rwa [hcl] at hgradw
  -- let the radius tend to zero
  have he0 : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ ↦ (ν : Measure V) (Metric.thickening r B)) (𝓝[>] 0)
        (𝓝 ((ν : Measure V) (closure B))) :=
      tendsto_measure_thickening ⟨1, one_pos, measure_ne_top _ _⟩
    rw [hcl] at h1
    have h2 := ENNReal.Tendsto.sub h1 (tendsto_const_nhds (x := (ν : Measure V) B))
      (Or.inl (measure_ne_top _ _))
    rwa [tsub_self] at h2
  have hLtend : Tendsto (fun r : ℝ ↦ smoothConstant ρ (interior (ν : Measure V).support) ν *
      (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r)) (𝓝[>] 0)
      (𝓝 (smoothConstant ρ (interior (ν : Measure V).support) ν *
        min ((ν : Measure V) B) (1 - (ν : Measure V) B))) := by
    have h2 : Tendsto (fun r : ℝ ↦ min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r)
        (𝓝[>] 0) (𝓝 (min ((ν : Measure V) B) (1 - (ν : Measure V) B))) := by
      have h3 := ENNReal.Tendsto.sub
        (tendsto_const_nhds (x := min ((ν : Measure V) B) (1 - (ν : Measure V) B))) he0
        (Or.inl hmtop)
      rwa [tsub_zero] at h3
    exact ENNReal.Tendsto.const_mul h2 (Or.inl hm0)
  calc smoothConstant ρ (interior (ν : Measure V).support) ν *
        min ((ν : Measure V) B) (1 - (ν : Measure V) B)
      = liminf (fun r : ℝ ↦ smoothConstant ρ (interior (ν : Measure V).support) ν *
          (min ((ν : Measure V) B) (1 - (ν : Measure V) B) - e r)) (𝓝[>] 0) :=
        hLtend.liminf_eq.symm
    _ ≤ liminf (fun r : ℝ ↦ e r / ENNReal.ofReal r) (𝓝[>] 0) := by
        refine liminf_le_liminf ?_
        filter_upwards [self_mem_nhdsWithin] with r hr using hmain r hr
    _ = minkowskiContent ν B := rfl

/-- Blueprint `lem:relative-perimeter-cheeger-infimum`: for a probability law with a Borell density
relative to Lebesgue measure, the Minkowski Cheeger infimum over Borel sets equals the
relative-perimeter Cheeger infimum over smooth domains. -/
theorem minkowskiConstant_eq_smoothConstant {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    minkowskiConstant ν = smoothConstant ρ (interior (ν : Measure V).support) ν :=
  le_antisymm (minkowskiConstant_le_smoothConstant hρ) (smoothConstant_le_minkowskiConstant hρ)

end Isoperimetry

/-! ### Transport to the affine support -/

namespace Isoperimetry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- A surjective isometry pulls thickenings back to thickenings. -/
private theorem thickening_preimage_of_isometry {α β : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] {f : α → β} (hf : Isometry f) (hsurj : Function.Surjective f)
    (r : ℝ) (B : Set β) :
    Metric.thickening r (f ⁻¹' B) = f ⁻¹' Metric.thickening r B := by
  ext x
  have himg : f '' (f ⁻¹' B) = B := Set.image_preimage_eq _ hsurj
  have hdist : Metric.infEDist x (f ⁻¹' B) = Metric.infEDist (f x) B := by
    have hkey := Metric.infEDist_image (Φ := f) (x := x) (t := f ⁻¹' B) hf
    rw [himg] at hkey
    exact hkey.symm
  simp only [Set.mem_preimage, Metric.mem_thickening_iff_infEDist_lt, hdist]

omit [CompleteSpace E] in
/-- Intrinsic coordinates and the affine carrier are identified, as measure spaces, by the
translation `coordinateEquiv`. -/
private theorem measurePreserving_coordinateEquiv (μ : ProbabilityMeasure E) :
    MeasurePreserving (Probability.coordinateEquiv μ)
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
      (carrierMeasure μ : Measure (Probability.affineSupport μ)) := by
  refine ⟨(Probability.coordinateEquiv μ).continuous.measurable, ?_⟩
  rw [Probability.intrinsicMeasure, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (Probability.coordinateEquiv μ).continuous.measurable
      (Probability.measurable_intrinsicMap μ),
    carrierMeasure, ProbabilityMeasure.toMeasure_map]
  congr 1
  funext x
  simp [Function.comp, Probability.intrinsicMap]

-- The type is the one fixed by the statement round; `CompleteSpace E` became unused only because
-- the body is now a proof rather than a hole, so the linter is silenced instead of the signature
-- changed.
set_option linter.unusedSectionVars false in
/-- The affine-support isoperimetric constant of `def:isoperimetric-cheeger-scale` is the
coordinate-space Minkowski constant of the intrinsic law: the map `x ↦ x - a` from the affine
carrier to its direction space is an isometry carrying `carrierMeasure μ` to
`Probability.intrinsicMeasure μ`; the zero-dimensional convention `⊤` agrees on both sides. -/
theorem constant_eq_minkowskiConstant_intrinsic (μ : ProbabilityMeasure E) :
    constant μ = minkowskiConstant (Probability.intrinsicMeasure μ) := by
  classical
  have hmp := measurePreserving_coordinateEquiv μ
  have hiso : Isometry (Probability.coordinateEquiv μ) := (Probability.coordinateEquiv μ).isometry
  have hsurj : Function.Surjective (Probability.coordinateEquiv μ) :=
    (Probability.coordinateEquiv μ).surjective
  have hsymm : Measurable (Probability.coordinateEquiv μ).symm :=
    (Probability.coordinateEquiv μ).symm.continuous.measurable
  have hmass : ∀ B : Set (Probability.affineSupport μ), MeasurableSet B →
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction)
          ((Probability.coordinateEquiv μ) ⁻¹' B) =
        (carrierMeasure μ : Measure (Probability.affineSupport μ)) B :=
    fun B hB ↦ hmp.measure_preimage hB.nullMeasurableSet
  have hcontent : ∀ B : Set (Probability.affineSupport μ), MeasurableSet B →
      minkowskiContent (Probability.intrinsicMeasure μ) ((Probability.coordinateEquiv μ) ⁻¹' B) =
        boundaryContent μ B := by
    intro B hB
    unfold minkowskiContent boundaryContent
    congr 1
    funext r
    rw [thickening_preimage_of_isometry hiso hsurj, hmass _ hB,
      hmass _ Metric.isOpen_thickening.measurableSet]
  by_cases hdim : Module.finrank ℝ (Probability.affineSupport μ).direction = 0
  · have hsub : Subsingleton (Probability.affineSupport μ).direction :=
      Module.finrank_zero_iff.mp hdim
    unfold constant
    rw [if_pos hdim]
    exact (minkowskiConstant_eq_top_of_subsingleton _).symm
  · unfold constant
    rw [if_neg hdim]
    refine le_antisymm ?_ ?_
    · -- every admissible coordinate set comes from an admissible carrier set
      refine le_iInf fun B' ↦ le_iInf fun hB' ↦ le_iInf fun hpos ↦ le_iInf fun hlt ↦ ?_
      have hBeq : (Probability.coordinateEquiv μ) ⁻¹'
          ((Probability.coordinateEquiv μ).symm ⁻¹' B') = B' := by
        ext x
        simp
      have hBmeas : MeasurableSet ((Probability.coordinateEquiv μ).symm ⁻¹' B') := hsymm hB'
      have hmass' : (carrierMeasure μ : Measure (Probability.affineSupport μ))
          ((Probability.coordinateEquiv μ).symm ⁻¹' B') =
          (Probability.intrinsicMeasure μ :
            Measure (Probability.affineSupport μ).direction) B' := by
        rw [← hmass _ hBmeas, hBeq]
      have hcont' : boundaryContent μ ((Probability.coordinateEquiv μ).symm ⁻¹' B') =
          minkowskiContent (Probability.intrinsicMeasure μ) B' := by
        rw [← hcontent _ hBmeas, hBeq]
      refine iInf_le_of_le ((Probability.coordinateEquiv μ).symm ⁻¹' B') ?_
      refine iInf_le_of_le hBmeas ?_
      refine iInf_le_of_le (by rwa [hmass']) ?_
      refine iInf_le_of_le (by rwa [hmass']) ?_
      rw [hmass', hcont']
    · -- and conversely
      refine le_iInf fun B ↦ le_iInf fun hB ↦ le_iInf fun hpos ↦ le_iInf fun hlt ↦ ?_
      have hBmeas : MeasurableSet ((Probability.coordinateEquiv μ) ⁻¹' B) := hiso.continuous.measurable hB
      refine iInf_le_of_le ((Probability.coordinateEquiv μ) ⁻¹' B) ?_
      refine iInf_le_of_le hBmeas ?_
      refine iInf_le_of_le (by rwa [hmass _ hB]) ?_
      refine iInf_le_of_le (by rwa [hmass _ hB]) ?_
      rw [hmass _ hB, hcontent _ hB]

/-- The `h_μ = h_ν^{sm,rel}` clause of `thm:klartag-density-frontend-identification`: for a
log-concave law with a Borell density `ρ` of its intrinsic law relative to Lebesgue measure on
the direction space, the affine-support isoperimetric constant is the smooth relative-perimeter
Cheeger infimum.  Dirac laws are included with both sides `⊤`. -/
theorem constant_eq_smoothConstant_intrinsic {μ : ProbabilityMeasure E} (_hμ : LogConcave μ)
    {ρ : (Probability.affineSupport μ).direction → ℝ}
    (hρ : IsBorellDensity (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) volume ρ) :
    constant μ =
      smoothConstant ρ
        (interior (Probability.intrinsicMeasure μ :
          Measure (Probability.affineSupport μ).direction).support)
        (Probability.intrinsicMeasure μ) := by
  rw [constant_eq_minkowskiConstant_intrinsic, minkowskiConstant_eq_smoothConstant hρ]

/-- The `Ψ_KLS(μ) = ψ_ν` clause: inverse scales agree. -/
theorem inverseScale_eq_inv_smoothConstant_intrinsic {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) {ρ : (Probability.affineSupport μ).direction → ℝ}
    (hρ : IsBorellDensity (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) volume ρ) :
    inverseScale μ =
      (smoothConstant ρ
        (interior (Probability.intrinsicMeasure μ :
          Measure (Probability.affineSupport μ).direction).support)
        (Probability.intrinsicMeasure μ))⁻¹ := by
  unfold inverseScale
  rw [constant_eq_smoothConstant_intrinsic hμ hρ]

end Isoperimetry

end FunctionalInequalities.KLS
