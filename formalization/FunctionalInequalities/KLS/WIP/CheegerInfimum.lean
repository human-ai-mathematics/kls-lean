import FunctionalInequalities.KLS.WIP.RelativePerimeter
import FunctionalInequalities.KLS.Isoperimetry

/-!
# The two Cheeger infima agree

Partially proved work-in-progress module for Blueprint `lem:relative-perimeter-cheeger-infimum`
(Appendix A), together with the `h_μ = h_ν^{sm,rel}` clause of
`thm:klartag-density-frontend-identification`. Nine explicit `sorry` bodies remain; filled
consequences may still depend on `sorryAx`. The module is not
imported by the library root, not registered in the ledger, and not anchored from the Blueprint.
Read `minkowskiContent`, `minkowskiConstant`, `smoothConstant`, the coarea obligations, then
`minkowskiConstant_eq_smoothConstant` and `constant_eq_smoothConstant_intrinsic`.

## The two infima

For a probability law `ν` on a finite-dimensional real inner-product space `V`, with
`m(t) = min {t, 1 - t}`:

* `h_M = minkowskiConstant ν = inf_{0 < ν(B) < 1} ν⁺(B) / m(ν(B))` over Borel sets, where
  `minkowskiContent ν B = ν⁺(B) = liminf_{r ↓ 0} (ν(B^r) - ν(B)) / r` is the outer Minkowski
  content with open `r`-thickenings.  This is `def:isoperimetric-cheeger-scale` written on the
  coordinate space `V` itself; `constant_eq_minkowskiConstant_intrinsic` identifies it with the
  affine-support definition `KLS.Isoperimetry.constant μ` for `ν` the intrinsic law of `μ`.
* `h_S = smoothConstant ρ Ω ν = inf_{0 < ν(U) < 1} P_ρ(U) / m(ν(U))` over smooth domains, with the
  relative perimeter `relativePerimeter ρ Ω U` of the companion module (normalized `ℋ^{n-1}`,
  `ρ` the Borell density of `ν` with respect to Lebesgue measure `volume`, `Ω = interior ν.support`).

Both infima are `⊤` when no admissible set exists, in particular in dimension zero.

## Claimed, not claimed, restricted scope, dimension zero

Claimed (`minkowskiConstant_eq_smoothConstant`): for every probability law `ν` with a Borell
density `ρ` relative to `volume`, `h_M = h_S`.  Lean is stronger than the Blueprint's
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

`measure_closure_eq_of_minkowskiContent_ne_top` (finite content forces `ν(closure B) = ν(B)`);
`distanceCutoff` with its Lipschitz, range, and gradient bounds
(`lintegral_enorm_gradient_distanceCutoff_le`, the estimate `∫ ‖∇w_r‖ dν ≤ (ν(B^r) - ν(B̄)) / r`);
`exists_smooth_approximation_lipschitz` (smooth `[0,1]`-valued replacements preserving the
`L¹(ν)` limit and the gradient integrals, the "bounded `L¹` convolution assertion");
`lintegral_measure_symmDiff_superlevel` (`∫₀¹ ν({u > t} ∆ B) dt = ‖u - 𝟙_B‖_{L¹(ν)}`);
`tendsto_lintegral_min_superlevel` (`L¹` convergence moves the denominators);
`SmoothDomain.ae_exists_superlevel` (Sard: almost every superlevel set of a `C^∞` function is a
smooth domain); `lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (weighted coarea formula
with the normalized surface measure); `lintegral_minkowskiContent_superlevel_le` (the Minkowski
coarea inequality, Ambrosio–Di Marino–Gigli 2017, Lemma 3.2); and the two one-sided bounds
`smoothConstant_mul_lintegral_min_superlevel_le`, `minkowskiConstant_mul_lintegral_min_superlevel_le`.

The general forms of the two infrastructure obligations are stated, KLS-independently and
still unproved, in `KLS/WIP/AnalyticPrerequisites.lean`: `Analysis.sard` and
`Analysis.ae_forall_fderiv_ne_zero` (Sard with the sharp `C^n` exponent; together with
`SmoothDomain.frontier_superlevel_subset` they give `SmoothDomain.ae_exists_superlevel`), and
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (weighted coarea for Lipschitz `u`, of
which `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is the `C¹` specialization).
`exists_smooth_approximation_lipschitz` already has sufficient certified input in
`Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`: gradient convergence in L¹
implies convergence of its norm integrals. An independent audit client checked this implication;
the placeholder here is deliberately retained together with all other WIP holes. The repaired
distance-cutoff lemmas require nonemptiness and, for indicator convergence, measurability of `B`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff symmDiff

namespace FunctionalInequalities.KLS

universe u

/-! ### Sard and coarea for smooth functions -/

section Coarea

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

namespace SmoothDomain

/-- Sard: for a `C^∞` real function, almost every strict superlevel set is a smooth domain, with
defining function `u - t` at its regular value `t`. -/
theorem ae_exists_superlevel {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x} := by
  sorry

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The frontier of a strict superlevel set of a continuous function lies in the level set. -/
theorem frontier_superlevel_subset {u : V → ℝ} (hu : Continuous u) (t : ℝ) :
    frontier {x | t < u x} ⊆ {x | u x = t} := by
  intro x hx
  have h1 : x ∈ closure {x | t < u x} := frontier_subset_closure hx
  have h2 : t ≤ u x := closure_lt_subset_le continuous_const hu h1
  have hopen : IsOpen {x | t < u x} := isOpen_lt continuous_const hu
  have h3 : x ∉ {x | t < u x} := by
    have hx2 := hx.2
    rwa [hopen.interior_eq] at hx2
  simp only [Set.mem_ofPred_eq, not_lt] at h3
  exact le_antisymm h3 h2

end SmoothDomain

namespace Isoperimetry

/-- Weighted coarea formula for a `C¹` Lipschitz function on `V`, with Lebesgue measure on `V`
and the normalized surface measure `ℋ^{n-1}` on the level sets. -/
theorem lintegral_enorm_gradient_mul_eq_lintegral_levelSet {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    {K : ℝ≥0} (hK : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  sorry

end Isoperimetry

end Coarea

namespace Isoperimetry

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### Outer Minkowski content on the coordinate space -/

/-- Outer Minkowski content `ν⁺(B) = liminf_{r ↓ 0} (ν(B^r) - ν(B)) / r` on the coordinate space,
with open thickenings; the coordinate-space form of `boundaryContent`. -/
def minkowskiContent (ν : ProbabilityMeasure V) (B : Set V) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦
    ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r) (𝓝[>] 0)

/-- The Minkowski Cheeger infimum `h_M` over Borel sets of intermediate mass; `⊤` if none. -/
def minkowskiConstant (ν : ProbabilityMeasure V) : ℝ≥0∞ :=
  ⨅ (B : Set V) (_ : MeasurableSet B) (_ : 0 < (ν : Measure V) B) (_ : (ν : Measure V) B < 1),
    minkowskiContent ν B / min ((ν : Measure V) B) (1 - (ν : Measure V) B)

/-- The smooth relative-perimeter Cheeger infimum `h_S` over smooth domains of intermediate
mass; `⊤` if none. -/
def smoothConstant (ρ : V → ℝ) (Ω : Set V) (ν : ProbabilityMeasure V) : ℝ≥0∞ :=
  ⨅ (U : SmoothDomain V) (_ : 0 < (ν : Measure V) U.carrier)
    (_ : (ν : Measure V) U.carrier < 1),
    relativePerimeter ρ Ω U / min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Dimension zero: no Borel set has intermediate mass. -/
theorem minkowskiConstant_eq_top_of_subsingleton [Subsingleton V] (ν : ProbabilityMeasure V) :
    minkowskiConstant ν = ⊤ := by
  unfold minkowskiConstant
  refine iInf_eq_top.mpr fun B => ?_
  by_cases hB : MeasurableSet B
  · rw [iInf_pos hB]
    rcases Set.eq_empty_or_nonempty B with hBe | ⟨x, hx⟩
    · subst hBe
      simp only [measure_empty]
      exact iInf_neg (lt_irrefl 0)
    · have hBu : B = Set.univ := Set.eq_univ_of_forall fun y ↦ by rwa [Subsingleton.elim y x]
      subst hBu
      rw [measure_univ, iInf_pos (by norm_num : (0 : ℝ≥0∞) < 1)]
      exact iInf_neg (lt_irrefl 1)
  · exact iInf_neg hB

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Dimension zero: no smooth domain has intermediate mass. -/
theorem smoothConstant_eq_top_of_subsingleton [Subsingleton V] (ρ : V → ℝ) (Ω : Set V)
    (ν : ProbabilityMeasure V) :
    smoothConstant ρ Ω ν = ⊤ := by
  unfold smoothConstant
  refine iInf_eq_top.mpr fun U => ?_
  rcases Set.eq_empty_or_nonempty U.carrier with hUe | ⟨x, hx⟩
  · rw [hUe, measure_empty]
    exact iInf_neg (lt_irrefl 0)
  · have hUu : U.carrier = Set.univ := Set.eq_univ_of_forall fun y ↦ by rwa [Subsingleton.elim y x]
    rw [hUu, measure_univ, iInf_pos (by norm_num : (0 : ℝ≥0∞) < 1)]
    exact iInf_neg (lt_irrefl 1)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Finite Minkowski content forces the closure to carry no extra mass. -/
theorem measure_closure_eq_of_minkowskiContent_ne_top (ν : ProbabilityMeasure V) {B : Set V}
    (h : minkowskiContent ν B ≠ ⊤) :
    (ν : Measure V) (closure B) = (ν : Measure V) B := by
  by_contra hne
  have hle : (ν : Measure V) B ≤ (ν : Measure V) (closure B) := measure_mono subset_closure
  have hlt : (ν : Measure V) B < (ν : Measure V) (closure B) := lt_of_le_of_ne hle (Ne.symm hne)
  set δ : ℝ≥0∞ := (ν : Measure V) (closure B) - (ν : Measure V) B with hδ
  have hδpos : 0 < δ := tsub_pos_of_lt hlt
  have hle2 : ∀ r : ℝ, 0 < r →
      δ / ENNReal.ofReal r ≤
        ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r := by
    intro r hr
    apply ENNReal.div_le_div_right
    have hsub : closure B ⊆ Metric.thickening r B := Metric.closure_subset_thickening hr B
    have hmono : (ν : Measure V) (closure B) ≤ (ν : Measure V) (Metric.thickening r B) :=
      measure_mono hsub
    exact tsub_le_tsub_right hmono _
  have htendsto : Tendsto (fun r : ℝ ↦ δ / ENNReal.ofReal r) (𝓝[>] 0) (𝓝 ⊤) := by
    have hinv : Tendsto (fun r : ℝ ↦ r⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have h1 : Tendsto (fun r : ℝ ↦ ENNReal.ofReal r⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_nhds_top.mpr hinv
    have h2 : Tendsto (fun r : ℝ ↦ δ * ENNReal.ofReal r⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (δ * ⊤)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inl ENNReal.top_ne_zero)
    rw [ENNReal.mul_top hδpos.ne'] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [ENNReal.ofReal_inv_of_pos hr, div_eq_mul_inv]
  have hliminf_top : liminf (fun r : ℝ ↦ δ / ENNReal.ofReal r) (𝓝[>] 0) = ⊤ := htendsto.liminf_eq
  have hmono2 : liminf (fun r : ℝ ↦ δ / ENNReal.ofReal r) (𝓝[>] 0) ≤
      liminf (fun r : ℝ ↦
        ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r)
        (𝓝[>] 0) :=
    liminf_le_liminf (by filter_upwards [self_mem_nhdsWithin] with r hr; exact hle2 r hr)
  rw [hliminf_top] at hmono2
  exact h (top_le_iff.mp hmono2)

/-! ### Layer-cake identities for `[0,1]`-valued functions -/

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- `∫₀¹ ν({u > t} ∆ B) dt = ‖u - 𝟙_B‖_{L¹(ν)}` for a measurable `[0,1]`-valued `u`. -/
theorem lintegral_measure_symmDiff_superlevel (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : Measurable u) (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) {B : Set V}
    (hB : MeasurableSet B) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ν : Measure V) ({x | t < u x} ∆ B) =
      ∫⁻ x, ‖u x - B.indicator 1 x‖ₑ ∂(ν : Measure V) := by
  have hSmeas : ∀ t : ℝ, MeasurableSet ({x : V | t < u x} ∆ B) := fun t ↦
    (measurableSet_lt measurable_const hu).symmDiff hB
  set F : ℝ × V → ℝ≥0∞ := fun p ↦ ({y : V | p.1 < u y} ∆ B).indicator (1 : V → ℝ≥0∞) p.2
    with hFdef
  have hFmeas : Measurable F := by
    have hfst : Measurable (Prod.fst : ℝ × V → ℝ) := measurable_fst
    have hsnd : Measurable (Prod.snd : ℝ × V → V) := measurable_snd
    have hS : MeasurableSet {p : ℝ × V | p.1 < u p.2} :=
      measurableSet_lt hfst (hu.comp hsnd)
    have hBp : MeasurableSet (Prod.snd ⁻¹' B) := hB.preimage hsnd
    have hFeq : F
        = ({q : ℝ × V | q.1 < u q.2} ∆ (Prod.snd ⁻¹' B)).indicator (1 : ℝ × V → ℝ≥0∞) := by
      have hmem : ∀ p : ℝ × V, (p.2 ∈ {y : V | p.1 < u y} ∆ B) ↔
          (p ∈ {q : ℝ × V | q.1 < u q.2} ∆ (Prod.snd ⁻¹' B)) := by
        intro p; simp [Set.mem_symmDiff]
      funext p
      simp only [hFdef]
      by_cases h : p.2 ∈ {y : V | p.1 < u y} ∆ B
      · simp [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem p).mp h)]
      · simp [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc ↦ h ((hmem p).mpr hc))]
    rw [hFeq]
    exact measurable_one.indicator (hS.symmDiff hBp)
  have hstep1 : ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ν : Measure V) ({x | t < u x} ∆ B)
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ∫⁻ x, F (t, x) ∂(ν : Measure V) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun t _ ↦ ?_
    exact (lintegral_indicator_one (hSmeas t)).symm
  rw [hstep1,
    lintegral_lintegral_swap (μ := (volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) 1))
      (ν := (ν : Measure V)) (f := fun t x ↦ F (t, x)) hFmeas.aemeasurable]
  refine lintegral_congr fun x ↦ ?_
  have hux0 : 0 ≤ u x := (hu01 x).1
  have hux1 : u x ≤ 1 := (hu01 x).2
  set Tx : Set ℝ := {t : ℝ | x ∈ {y : V | t < u y} ∆ B} with hTxdef
  have hFTx : ∀ t : ℝ, F (t, x) = Tx.indicator (1 : ℝ → ℝ≥0∞) t := by
    intro t
    simp only [hFdef]
    by_cases ht : x ∈ {y : V | t < u y} ∆ B
    · simp [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ Tx from ht)]
    · simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ Tx from ht)]
  have hlint : ∀ S : Set ℝ, MeasurableSet S →
      ∫⁻ t in Set.Ioo (0 : ℝ) 1, S.indicator (1 : ℝ → ℝ≥0∞) t ∂volume = volume (S ∩ Set.Ioo (0 : ℝ) 1) := by
    intro S hSm
    rw [lintegral_indicator_one hSm, MeasureTheory.Measure.restrict_apply' measurableSet_Ioo]
  by_cases hxB : x ∈ B
  · have hTxeq : Tx = Set.Ici (u x) := by
      ext t
      simp [hTxdef, Set.mem_symmDiff, hxB]
    have hIntersect : Set.Ici (u x) ∩ Set.Ioo (0 : ℝ) 1 =
        Set.Ioo (0 : ℝ) 1 \ Set.Ioo (0 : ℝ) (u x) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioo, Set.mem_sdiff, not_and, not_lt]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h2, h3⟩, fun _ ↦ h1⟩
      · rintro ⟨⟨h2, h3⟩, h4⟩
        exact ⟨h4 h2, h2, h3⟩
    rw [setLIntegral_congr_fun measurableSet_Ioo (fun t _ ↦ hFTx t),
      hTxeq, hlint _ measurableSet_Ici, hIntersect,
      measure_sdiff (Set.Ioo_subset_Ioo le_rfl hux1) measurableSet_Ioo.nullMeasurableSet
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top),
      Real.volume_Ioo, Real.volume_Ioo, sub_zero, sub_zero, ← ENNReal.ofReal_sub 1 hux0]
    rw [Real.enorm_eq_ofReal_abs, Set.indicator_of_mem hxB, Pi.one_apply,
      abs_of_nonpos (by linarith : u x - 1 ≤ 0)]
    congr 1
    ring
  · have hTxeq : Tx = Set.Iio (u x) := by
      ext t
      simp [hTxdef, Set.mem_symmDiff, hxB]
    have hIoo1 : Set.Ioo (0 : ℝ) 1 ∩ Set.Iio (u x) = Set.Ioo (0 : ℝ) (u x) := by
      rw [Set.Ioo_inter_Iio, min_eq_right hux1]
    rw [setLIntegral_congr_fun measurableSet_Ioo (fun t _ ↦ hFTx t),
      hTxeq, hlint _ measurableSet_Iio,
      show Set.Iio (u x) ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 ∩ Set.Iio (u x) from
        Set.inter_comm _ _,
      hIoo1, Real.volume_Ioo, sub_zero]
    rw [Real.enorm_eq_ofReal_abs, Set.indicator_of_notMem hxB, sub_zero,
      abs_of_nonneg hux0]

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The balance `min {t, 1 - t}` is `1`-Lipschitz in the set: `m(ν A) ≤ m(ν B) + ν(A ∆ B)`. -/
theorem min_measure_le_add_measure_symmDiff (ν : ProbabilityMeasure V) {A B : Set V}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    min ((ν : Measure V) A) (1 - (ν : Measure V) A) ≤
      min ((ν : Measure V) B) (1 - (ν : Measure V) B) + (ν : Measure V) (A ∆ B) := by
  have hbasic : ∀ C D : Set V, (ν : Measure V) C ≤ (ν : Measure V) D + (ν : Measure V) (C ∆ D) := by
    intro C D
    have hsub : C ⊆ D ∪ (C ∆ D) := by
      intro a ha
      by_cases h : a ∈ D
      · exact Set.mem_union_left _ h
      · exact Set.mem_union_right _ (Set.mem_symmDiff.mpr (Or.inl ⟨ha, h⟩))
    calc (ν : Measure V) C ≤ (ν : Measure V) (D ∪ (C ∆ D)) := measure_mono hsub
      _ ≤ (ν : Measure V) D + (ν : Measure V) (C ∆ D) := measure_union_le _ _
  have hA_le : (ν : Measure V) A ≤ (ν : Measure V) B + (ν : Measure V) (A ∆ B) := hbasic A B
  have h1mA_le : 1 - (ν : Measure V) A ≤ (1 - (ν : Measure V) B) + (ν : Measure V) (A ∆ B) := by
    have hcompl : (ν : Measure V) Aᶜ ≤ (ν : Measure V) Bᶜ + (ν : Measure V) (Aᶜ ∆ Bᶜ) := hbasic Aᶜ Bᶜ
    rwa [compl_symmDiff_compl, measure_compl hA (measure_ne_top _ _),
      measure_compl hB (measure_ne_top _ _), measure_univ] at hcompl
  rcases le_total ((ν : Measure V) B) (1 - (ν : Measure V) B) with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans hA_le
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans h1mA_le

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
/-- `L¹(ν)` convergence of `[0,1]`-valued functions to an indicator moves the integrated balance of
the superlevel sets to the balance of the limit set. -/
theorem tendsto_lintegral_min_superlevel (ν : ProbabilityMeasure V) {u : ℕ → V → ℝ}
    (hu : ∀ j, Measurable (u j)) (hu01 : ∀ j x, u j x ∈ Set.Icc (0 : ℝ) 1) {B : Set V}
    (hB : MeasurableSet B)
    (hconv : Tendsto (fun j ↦ ∫⁻ x, ‖u j x - B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        min ((ν : Measure V) {x | t < u j x}) (1 - (ν : Measure V) {x | t < u j x}))
      atTop (𝓝 (min ((ν : Measure V) B) (1 - (ν : Measure V) B))) := by
  set mB : ℝ≥0∞ := min ((ν : Measure V) B) (1 - (ν : Measure V) B) with hmBdef
  set ε : ℕ → ℝ≥0∞ := fun j ↦ ∫⁻ x, ‖u j x - B.indicator 1 x‖ₑ ∂(ν : Measure V) with hεdef
  set F : ℕ → ℝ → ℝ≥0∞ := fun j t ↦
      min ((ν : Measure V) {x | t < u j x}) (1 - (ν : Measure V) {x | t < u j x}) with hFdef
  have hmB_ne_top : mB ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_left _ _).trans prob_le_one)
  have hanti : ∀ j, Antitone (fun t : ℝ ↦ (ν : Measure V) {x | t < u j x}) := by
    intro j t1 t2 ht12
    exact measure_mono fun x hx ↦ lt_of_le_of_lt ht12 hx
  have hFmeas : ∀ j, Measurable (F j) := by
    intro j
    have hmono : Monotone (fun t : ℝ ↦ 1 - (ν : Measure V) {x | t < u j x}) := fun t1 t2 ht12 ↦
      tsub_le_tsub_left ((hanti j) ht12) 1
    exact (hanti j).measurable.min hmono.measurable
  have hj_ub : ∀ j, ∫⁻ t in Set.Ioo (0 : ℝ) 1, F j t ∂volume ≤ mB + ε j := by
    intro j
    have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F j t ≤ mB + (ν : Measure V) ({x | t < u j x} ∆ B) :=
      fun t _ ↦
        min_measure_le_add_measure_symmDiff (A := {x | t < u j x}) (B := B) ν
          (measurableSet_lt measurable_const (hu j)) hB
    calc ∫⁻ t in Set.Ioo (0 : ℝ) 1, F j t ∂volume
        ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, (mB + (ν : Measure V) ({x | t < u j x} ∆ B)) ∂volume :=
          setLIntegral_mono' measurableSet_Ioo hpt
      _ = (∫⁻ _ in Set.Ioo (0 : ℝ) 1, mB ∂volume) +
          ∫⁻ t in Set.Ioo (0 : ℝ) 1, (ν : Measure V) ({x | t < u j x} ∆ B) ∂volume :=
          lintegral_add_left measurable_const _
      _ = mB + ε j := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one,
            lintegral_measure_symmDiff_superlevel ν (hu j) (hu01 j) hB]
  have hj_lb : ∀ j, mB ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, F j t ∂volume) + ε j := by
    intro j
    have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        mB ≤ F j t + (ν : Measure V) ({x | t < u j x} ∆ B) := by
      intro t _
      have h := min_measure_le_add_measure_symmDiff (A := B) (B := {x | t < u j x}) ν hB
        (measurableSet_lt measurable_const (hu j))
      rwa [symmDiff_comm] at h
    have hstep : (∫⁻ _ in Set.Ioo (0 : ℝ) 1, mB ∂volume) ≤
        ∫⁻ t in Set.Ioo (0 : ℝ) 1, (F j t + (ν : Measure V) ({x | t < u j x} ∆ B)) ∂volume :=
      setLIntegral_mono' measurableSet_Ioo hpt
    rwa [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one,
      lintegral_add_left (hFmeas j),
      lintegral_measure_symmDiff_superlevel ν (hu j) (hu01 j) hB] at hstep
  have hlb : Tendsto (fun j ↦ mB - ε j) atTop (𝓝 mB) := by
    have h := ENNReal.Tendsto.sub (a := mB) (b := 0) tendsto_const_nhds hconv (Or.inl hmB_ne_top)
    simpa using h
  have hub : Tendsto (fun j ↦ mB + ε j) atTop (𝓝 mB) := by
    have h : Tendsto (fun j ↦ mB + ε j) atTop (𝓝 (mB + 0)) := Tendsto.const_add mB hconv
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlb hub ?_ ?_
  · filter_upwards with j using tsub_le_iff_right.mpr (hj_lb j)
  · filter_upwards with j using hj_ub j

/-! ### Distance cutoffs -/

/-- The distance cutoff `w_r = (1 - d(·, B) / r)₊`: equal to `1` on the closure of `B`, to `0`
outside the open `r`-thickening, and `1/r`-Lipschitz. -/
def distanceCutoff (B : Set V) (r : ℝ) (x : V) : ℝ :=
  max 0 (1 - Metric.infDist x B / r)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff takes values in `[0, 1]`. -/
theorem distanceCutoff_mem_Icc (B : Set V) {r : ℝ} (hr : 0 < r) (x : V) :
    distanceCutoff B r x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold distanceCutoff
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have h0 : 0 ≤ Metric.infDist x B / r := div_nonneg Metric.infDist_nonneg hr.le
  linarith

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff is `1/r`-Lipschitz. -/
theorem lipschitzWith_distanceCutoff (B : Set V) {r : ℝ} (hr : 0 < r) :
    LipschitzWith (Real.toNNReal r⁻¹) (distanceCutoff B r) := by
  apply LipschitzWith.of_dist_le' (K := r⁻¹)
  intro x y
  unfold distanceCutoff
  have hinf : dist (Metric.infDist x B) (Metric.infDist y B) ≤ dist x y := by
    simpa using (Metric.lipschitz_infDist_pt (s := B)).dist_le_mul x y
  rw [Real.dist_eq] at hinf
  have hstep : |max 0 (1 - Metric.infDist x B / r) - max 0 (1 - Metric.infDist y B / r)|
      ≤ |(1 - Metric.infDist x B / r) - (1 - Metric.infDist y B / r)| := by
    rw [max_comm 0 (1 - Metric.infDist x B / r), max_comm 0 (1 - Metric.infDist y B / r)]
    exact abs_max_sub_max_le_abs _ _ 0
  have heq : (1 - Metric.infDist x B / r) - (1 - Metric.infDist y B / r)
      = -(Metric.infDist x B - Metric.infDist y B) / r := by ring
  rw [Real.dist_eq]
  refine hstep.trans ?_
  rw [heq, abs_div, abs_neg, abs_of_pos hr, div_le_iff₀ hr]
  calc |Metric.infDist x B - Metric.infDist y B| ≤ dist x y := hinf
    _ = r⁻¹ * dist x y * r := by field_simp

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff equals `1` on the closure of a nonempty `B`. -/
theorem distanceCutoff_eq_one_of_mem_closure {B : Set V} (hB : B.Nonempty) {r : ℝ} (_hr : 0 < r)
    {x : V} (hx : x ∈ closure B) :
    distanceCutoff B r x = 1 := by
  unfold distanceCutoff
  have h0 : Metric.infDist x B = 0 := (Metric.mem_closure_iff_infDist_zero hB).mp hx
  rw [h0]
  simp

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff vanishes outside the open `r`-thickening of a nonempty `B`.  Nonemptiness is
needed: `Metric.thickening r ∅ = ∅` makes the hypothesis vacuous for every `x`, while Mathlib's
convention `Metric.infDist x ∅ = 0` gives `distanceCutoff ∅ r x = 1`. -/
theorem distanceCutoff_eq_zero_of_notMem_thickening {B : Set V} (hB : B.Nonempty)
    {r : ℝ} (hr : 0 < r) {x : V} (hx : x ∉ Metric.thickening r B) :
    distanceCutoff B r x = 0 := by
  unfold distanceCutoff
  rw [Metric.mem_thickening_iff_infDist_lt hB, not_lt] at hx
  refine max_eq_left ?_
  rw [sub_nonpos, le_div_iff₀ hr, one_mul]
  exact hx

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- When `B` is measurable and its closure carries no extra mass, the cutoffs converge to the
indicator in `L¹(ν)` as `r ↓ 0`.  Measurability is needed to identify the mass of the annulus
`B^r \ B` with `ν(B^r) − ν(B)`. -/
theorem tendsto_distanceCutoff_indicator (ν : ProbabilityMeasure V) {B : Set V}
    (hB : B.Nonempty) (hBm : MeasurableSet B)
    (hcl : (ν : Measure V) (closure B) = (ν : Measure V) B) :
    Tendsto (fun r : ℝ ↦ ∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
      (𝓝[>] 0) (𝓝 0) := by
  -- pointwise bound by the indicator of the annulus
  have hbound : ∀ r : ℝ, 0 < r →
      ∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
    intro r hr
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
  -- the annulus mass tends to zero
  have hthin : Tendsto
      (fun r : ℝ ↦ (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) (𝓝[>] 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    -- continuity from above along the radii `1 / (n + 1)`
    have hmono : Antitone fun n : ℕ ↦ Metric.thickening (1 / ((n : ℝ) + 1)) B := by
      intro a b hab
      refine Metric.thickening_mono ?_ B
      have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ hb ha]
      have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.2 hab
      linarith
    have hiInter : ⋂ n : ℕ, Metric.thickening (1 / ((n : ℝ) + 1)) B = closure B := by
      refine Set.Subset.antisymm ?_ ?_
      · rw [Metric.closure_eq_iInter_thickening B]
        refine Set.subset_iInter fun δ ↦ Set.subset_iInter fun hδ ↦ ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        exact (Set.iInter_subset _ n).trans (Metric.thickening_mono hn.le B)
      · refine Set.subset_iInter fun n ↦ ?_
        refine Metric.closure_subset_thickening ?_ B
        positivity
    have htend := tendsto_measure_iInter_atTop (μ := (ν : Measure V))
      (s := fun n : ℕ ↦ Metric.thickening (1 / ((n : ℝ) + 1)) B)
      (fun n ↦ Metric.isOpen_thickening.measurableSet.nullMeasurableSet) hmono
      ⟨0, measure_ne_top _ _⟩
    rw [hiInter, hcl] at htend
    have hεpos : (0 : ENNReal) < ε := hε
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop (measure_ne_top (ν : Measure V) B)).1 htend ε hεpos
    have hr0 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hr0] with r hr
    have hrt : Metric.thickening r B ⊆ Metric.thickening (1 / ((N : ℝ) + 1)) B :=
      Metric.thickening_mono hr.2.le B
    have hle : (ν : Measure V) (Metric.thickening r B) ≤ ε + (ν : Measure V) B := by
      refine (measure_mono hrt).trans ?_
      have hNN := (hN N le_rfl).2
      simpa [Function.comp, add_comm] using hNN
    exact tsub_le_iff_right.2 hle
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hthin ?_ ?_
  · filter_upwards with r using zero_le
  · filter_upwards [self_mem_nhdsWithin] with r hr using hbound r hr

/-- The gradient of the cutoff vanishes almost everywhere on its two constant-value sets and is
bounded by `1/r` on the open annulus `B^r ∖ closure B`, so
`∫ ‖∇w_r‖ dν ≤ (ν(B^r) - ν(closure B)) / r` for `ν` absolutely continuous with respect to a Haar
measure.  This sharpens the Blueprint's `(ν(B^r) - ν(B)) / r`. -/
theorem lintegral_enorm_gradient_distanceCutoff_le (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) (B : Set V) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r := by
  sorry

/-! ### Smooth replacements of Lipschitz `[0,1]`-valued functions -/

/-- Mollification of a globally Lipschitz `[0,1]`-valued function: smooth, Lipschitz,
`[0,1]`-valued replacements converging in `L¹(ν)` with convergent gradient integrals.  This is the
"bounded `L¹` convolution assertion" of `lem:covariance-test-core-density` used by the Blueprint;
it needs only absolute continuity of `ν` with respect to a Haar measure. -/
theorem exists_smooth_approximation_lipschitz (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) {w : V → ℝ} {K : ℝ≥0}
    (hw : LipschitzWith K w) (hw01 : ∀ x, w x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ u : ℕ → V → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K' : ℝ≥0, LipschitzWith K' (u j)) ∧
        ∀ x, u j x ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖u j x - w x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V)) atTop
        (𝓝 (∫⁻ x, ‖gradient w x‖ₑ ∂(ν : Measure V))) := by
  sorry

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

/-- Minkowski coarea inequality (Ambrosio–Di Marino–Gigli 2017, Lemma 3.2) for a `C¹` Lipschitz
function, with closed superlevel sets and the Euclidean gradient: `∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`.
No density is assumed. -/
theorem lintegral_minkowskiContent_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  sorry

/-- Consequence for `h_M`: `h_M ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν` for a `C¹` Lipschitz
`[0,1]`-valued `u` (open and closed superlevel sets have the same mass for almost every `t`). -/
theorem minkowskiConstant_mul_lintegral_min_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) :
    minkowskiConstant ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  sorry

/-! ### The two infima agree -/

/-- `h_M ≤ h_S`: apply the smoothing lemma to a smooth domain and pass the Minkowski coarea bound
to the limit. -/
theorem minkowskiConstant_le_smoothConstant {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    minkowskiConstant ν ≤ smoothConstant ρ (interior (ν : Measure V).support) ν := by
  sorry

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
