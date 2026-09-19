import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiConstant
import FunctionalInequalities.KLS.Geometry.Perimeter.Recovery

/-!
# The smooth Cheeger infimum and the bound `h_M ≤ h_S`

Hole-free application layer over the proved recovery sequence
(`KLS/Geometry/Perimeter/Recovery.lean`) and the proved integrated Minkowski coarea bound
(`KLS/Geometry/Cheeger/MinkowskiConstant.lean`).  It owns

* `Isoperimetry.smoothConstant ρ Ω ν = ⨅_{0 < ν U < 1} P_ρ(U) / min {ν U, 1 - ν U}`, the infimum
  over smooth domains, `⊤` when no admissible domain exists (in particular in dimension zero, by
  `smoothConstant_eq_top_of_subsingleton`);
* the layer-cake identity `lintegral_measure_symmDiff_superlevel`, the balance estimate
  `min_measure_le_add_measure_symmDiff` and the convergence `tendsto_lintegral_min_superlevel`,
  all migrated unchanged from `KLS/WIP/CheegerInfimum.lean`;
* the proved one-sided comparison `minkowskiConstant_le_smoothConstant`.

Only one direction is proved here.  `smoothConstant_le_minkowskiConstant` still needs Sard, the
weighted coarea formula and the distance-cutoff gradient estimate, so it and the equality
`minkowskiConstant_eq_smoothConstant` stay in `KLS/WIP/CheegerInfimum.lean`; nothing in this module
claims that the two Cheeger infima agree.

No mathematical scope was added: an arbitrary finite-dimensional real inner-product space, zero
dimension included; an arbitrary Borell density relative to Lebesgue `volume`; no bounded support,
no bounded domain, no finite total boundary measure, no finiteness or positivity of the constants,
and no assumption that an admissible smooth domain exists or that relative perimeters are finite.
A domain of infinite relative perimeter is handled by `le_top` alone, so the finiteness hypothesis
of `RelativePerimeter.exists_smooth_recovery_sequence` never becomes a hypothesis of the theorem.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff symmDiff

namespace FunctionalInequalities.KLS

universe u

namespace Isoperimetry

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### The two Cheeger infima -/

/-- The smooth relative-perimeter Cheeger infimum `h_S` over smooth domains of intermediate
mass; `⊤` if none. -/
def smoothConstant (ρ : V → ℝ) (Ω : Set V) (ν : ProbabilityMeasure V) : ℝ≥0∞ :=
  ⨅ (U : SmoothDomain V) (_ : 0 < (ν : Measure V) U.carrier)
    (_ : (ν : Measure V) U.carrier < 1),
    relativePerimeter ρ Ω U / min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier)

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
  have hFmeas : ∀ j, Measurable (F j) := fun j ↦ measurable_min_measure_superlevel ν (u j)
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

/-! ### The Minkowski infimum is at most the smooth infimum -/

/-- `h_M ≤ h_S`: apply the smoothing lemma to a smooth domain and pass the Minkowski coarea bound
to the limit. -/
theorem minkowskiConstant_le_smoothConstant {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    minkowskiConstant ν ≤ smoothConstant ρ (interior (ν : Measure V).support) ν := by
  classical
  simp only [smoothConstant]
  refine le_iInf fun U ↦ le_iInf fun hUpos ↦ le_iInf fun hUlt ↦ ?_
  have hm0 : min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) ≠ 0 :=
    ne_of_gt (lt_min hUpos (tsub_pos_of_lt hUlt))
  have hmtop : min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_left _ _).trans prob_le_one)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)]
  -- An infinite relative perimeter needs no recovery sequence.
  rcases eq_or_ne (relativePerimeter ρ (interior (ν : Measure V).support) U) ⊤ with hP | hP
  · rw [hP]
    exact le_top
  obtain ⟨u, hureg, hconv, hlimsup⟩ := RelativePerimeter.exists_smooth_recovery_sequence hρ U hP
  have hstep : ∀ j, minkowskiConstant ν *
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        min ((ν : Measure V) {x | t < u j x}) (1 - (ν : Measure V) {x | t < u j x})) ≤
      ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V) := by
    intro j
    obtain ⟨K, hK⟩ := (hureg j).2.1
    exact minkowskiConstant_mul_lintegral_min_superlevel_le ν
      ((hureg j).1.of_le (by simp)) hK (hureg j).2.2
  have hItend : Tendsto (fun j ↦ ∫⁻ t in Set.Ioo (0 : ℝ) 1,
      min ((ν : Measure V) {x | t < u j x}) (1 - (ν : Measure V) {x | t < u j x})) atTop
      (𝓝 (min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier))) :=
    tendsto_lintegral_min_superlevel ν (fun j ↦ (hureg j).1.continuous.measurable)
      (fun j ↦ (hureg j).2.2) U.isOpen.measurableSet hconv
  have hmul : Tendsto (fun j ↦ minkowskiConstant ν *
      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        min ((ν : Measure V) {x | t < u j x}) (1 - (ν : Measure V) {x | t < u j x})) atTop
      (𝓝 (minkowskiConstant ν *
        min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier))) :=
    ENNReal.Tendsto.const_mul hItend (Or.inl hm0)
  calc minkowskiConstant ν * min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier)
      = limsup (fun j ↦ minkowskiConstant ν *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            min ((ν : Measure V) {x | t < u j x}) (1 - (ν : Measure V) {x | t < u j x}))
          atTop := hmul.limsup_eq.symm
    _ ≤ limsup (fun j ↦ ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V)) atTop :=
        limsup_le_limsup (Eventually.of_forall hstep)
    _ ≤ relativePerimeter ρ (interior (ν : Measure V).support) U := hlimsup

end Isoperimetry

end FunctionalInequalities.KLS
