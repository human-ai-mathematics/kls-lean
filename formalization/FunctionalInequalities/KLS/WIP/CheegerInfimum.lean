import FunctionalInequalities.KLS.Geometry.CheegerInfimum
import FunctionalInequalities.KLS.Geometry.DistanceCutoff
import FunctionalInequalities.KLS.Isoperimetry
import FunctionalInequalities.KLS.Geometry.RegularSuperlevel
import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

/-!
# The two Cheeger infima agree

Partially proved work-in-progress module for Blueprint `lem:relative-perimeter-cheeger-infimum`
(Appendix A), together with the `h_μ = h_ν^{sm,rel}` clause of
`thm:klartag-density-frontend-identification`. Two explicit `sorry` bodies remain; filled
consequences may still depend on `sorryAx`. The module is not
imported by the library root, not registered in the ledger, and not anchored from the Blueprint.
Only the direction `minkowskiConstant_le_smoothConstant` is proved, and it has moved down to the
hole-free `KLS/Geometry/CheegerInfimum.lean`; `minkowskiConstant_eq_smoothConstant` has a
`le_antisymm` body but inherits `sorryAx` through the unproved reverse direction. Read the
remaining integrated superlevel bound and reverse comparison, then `minkowskiConstant_eq_smoothConstant` and
`constant_eq_smoothConstant_intrinsic`.

## The two infima

For a probability law `ν` on a finite-dimensional real inner-product space `V`, with
`m(t) = min {t, 1 - t}`:

* `h_M = minkowskiConstant ν = inf_{0 < ν(B) < 1} ν⁺(B) / m(ν(B))` over Borel sets, where
  `minkowskiContent ν B = ν⁺(B) = liminf_{r ↓ 0} (ν(B^r) - ν(B)) / r` is the outer Minkowski
  content with open `r`-thickenings.  Both live in the hole-free modules
  `KLS/Geometry/MinkowskiContent.lean` and `KLS/Geometry/MinkowskiConstant.lean`.  This is
  `def:isoperimetric-cheeger-scale` written on the
  coordinate space `V` itself; `constant_eq_minkowskiConstant_intrinsic` identifies it with the
  affine-support definition `KLS.Isoperimetry.constant μ` for `ν` the intrinsic law of `μ`.
* `h_S = smoothConstant ρ Ω ν = inf_{0 < ν(U) < 1} P_ρ(U) / m(ν(U))` over smooth domains, with the
  relative perimeter `relativePerimeter ρ Ω U` of `KLS/Geometry/RelativePerimeter.lean`
  (normalized `ℋ^{n-1}`,
  `ρ` the Borell density of `ν` with respect to Lebesgue measure `volume`, `Ω = interior ν.support`).
  `smoothConstant` itself lives in the hole-free `KLS/Geometry/CheegerInfimum.lean`.

Both infima are `⊤` when no admissible set exists, in particular in dimension zero.

## Claimed, not claimed, restricted scope, dimension zero

Claimed (`minkowskiConstant_eq_smoothConstant`): for every probability law `ν` with a Borell
density `ρ` relative to `volume`, `h_M = h_S`.  **Only `h_M ≤ h_S` is proved** (in
`KLS/Geometry/CheegerInfimum.lean`); the equality and everything downstream of it still depend on
the unproved `smoothConstant_le_minkowskiConstant`, hence transitively on `sorryAx`.  Lean is stronger than the Blueprint's
"full-dimensional log-concave probability" in taking any law with a Borell density
(`KLS.LogConcave.exists_isBorellDensity` supplies one for the intrinsic law of a log-concave `μ`).
Consequently (`constant_eq_smoothConstant_intrinsic`), for a log-concave `μ` the affine-support
isoperimetric constant `h_μ` of `def:isoperimetric-cheeger-scale` equals `h_ν^{sm,rel}`, and the
inverse scales agree.

Not claimed: any relation between `ν⁺(B)` and `P_ρ(B)` for an individual set ("The statement
compares infima, not the two perimeters of each test set"), the BV-perimeter identification of
`thm:logconcave-cheeger-poincare-comparison`, the Poincaré-constant clause of
`thm:klartag-density-frontend-identification`, or Cheeger–Buser.

Restricted scope: none of the statements assumes `dim V ≥ 1`.  The reverse-direction intermediate
`smoothConstant_mul_lintegral_min_superlevel_le` is stated under the Borell-density hypothesis
because it uses the density in the coarea formula.

Dimension zero: no set has `0 < ν(B) < 1`, both infima are `⊤`, and the equality is `⊤ = ⊤`.

## Intermediate obligations named here

`exists_smooth_approximation_lipschitz` (smooth `[0,1]`-valued replacements preserving the
`L¹(ν)` limit and the gradient integrals, the "bounded `L¹` convolution assertion");
and the one-sided bound `smoothConstant_mul_lintegral_min_superlevel_le`.
The `C¹` weighted coarea formula
`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is **no longer** an obligation
here: it moved to the hole-free `KLS/Geometry/IsoperimetryCoarea.lean` with a byte-identical
`pp.all` signature, where it is proved from `KLS.coarea_of_contDiff`.

`minkowskiContent`, `measure_closure_eq_of_minkowskiContent_ne_top` and the Minkowski coarea
inequality `lintegral_minkowskiContent_superlevel_le` (Ambrosio–Di Marino–Gigli 2017, Lemma 3.2)
are **proved** and live in `KLS/Geometry/MinkowskiContent.lean`, which imports no
work-in-progress layer.  `minkowskiConstant`, `minkowskiConstant_eq_top_of_subsingleton`, the
almost-everywhere agreement `ae_measure_superlevel_lt_eq_le` of the strict and closed superlevel
masses, the measurability `measurable_min_measure_superlevel` of the superlevel balance used by
`tendsto_lintegral_min_superlevel`, the multiplied infimum bound `minkowskiConstant_mul_min_le`
and the **proved** `minkowskiConstant_mul_lintegral_min_superlevel_le` live one layer up, in the
likewise hole-free `KLS/Geometry/MinkowskiConstant.lean`; this module imports both and states no
obligation of its own for them.

The Sard obligation is **discharged**: `SmoothDomain.ae_exists_superlevel` and
`SmoothDomain.frontier_superlevel_subset` have moved out of this module to the hole-free
`KLS/Geometry/RegularSuperlevel.lean`, where the former is proved from the proved smooth Sard
theorem `Analysis.sard_smooth` via `Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top`.  Their
statements are unchanged and neither depends on `sorryAx` any more, so this module no longer
imports `KLS/WIP/AnalyticPrerequisites.lean` at all.  The **sharp** `C^(finrank)` statement
`Analysis.sard` remains a direct hole there, and `Analysis.ae_forall_fderiv_ne_zero` inherits it.
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (weighted coarea for Lipschitz `u`,
with no `C¹` hypothesis) is proved in `KLS/Geometry/LipschitzCoarea.lean`. Nothing in this module
imports that coarea module or the sharp Sard obligation. Its
`C¹` specialization `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is **proved**
and lives in `KLS/Geometry/IsoperimetryCoarea.lean`.
`smoothConstant`, `smoothConstant_eq_top_of_subsingleton`, the layer-cake identity
`lintegral_measure_symmDiff_superlevel`, the balance estimate
`min_measure_le_add_measure_symmDiff`, the convergence `tendsto_lintegral_min_superlevel` and the
**proved** `minkowskiConstant_le_smoothConstant` live in the hole-free
`KLS/Geometry/CheegerInfimum.lean`, over the likewise hole-free
`KLS/Geometry/PerimeterRecovery.lean` (which proves
`RelativePerimeter.exists_smooth_recovery_sequence`); this module imports that layer and states no
obligation of its own for any of them.
`distanceCutoff` with its range, Lipschitz and boundary-value lemmas, the `L¹(ν)` convergence
`tendsto_distanceCutoff_indicator` and the **proved** gradient estimate
`lintegral_enorm_gradient_distanceCutoff_le` live in the hole-free
`KLS/Geometry/DistanceCutoff.lean`, whose local import closure is empty (Mathlib only); this
module imports it and states no obligation of its own for them.
`exists_smooth_approximation_lipschitz` is now proved from
`Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`, which is certified and free of
`sorryAx`: its mollification keeps the range `[0,1]` and the Lipschitz constant of `w`, and
convergence of the gradients in `L¹(ν; V)` is convergence in the norm `f ↦ ∫⁻ ‖f‖ₑ`, so the
gradient-norm integrals converge. The measure hypotheses of the statement are unchanged. The
repaired distance-cutoff lemmas require nonemptiness and, for indicator convergence,
measurability of `B`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff symmDiff

namespace FunctionalInequalities.KLS

universe u

/-! ### Sard and coarea for smooth functions -/

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

/-! ### The two coarea inequalities -/

/-- Weighted coarea and Sard: for a smooth Lipschitz `[0,1]`-valued `u`,
`h_S ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν`. -/
theorem smoothConstant_mul_lintegral_min_superlevel_le {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    {K : ℝ≥0} (hK : LipschitzWith K u) (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) :
    smoothConstant ρ (interior (ν : Measure V).support) ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  sorry

/-! ### The two infima agree -/

/-- `h_S ≤ h_M`: distance cutoffs of a Borel set of finite content, smooth replacements, and the
weighted coarea bound. -/
theorem smoothConstant_le_minkowskiConstant {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    smoothConstant ρ (interior (ν : Measure V).support) ν ≤ minkowskiConstant ν := by
  sorry

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
-- the body is now a proof rather than `sorry`, so the linter is silenced instead of the signature
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
