import FunctionalInequalities.Probability.MomentMeasure.Compactness
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Audit clients for Cordero-Erausquin–Klartag (arXiv:1304.0630v1), Lemma 17 (56)
(`Probability/MomentMeasure/Compactness.lean`). Client blocks are verbatim from the accepted `Lemma17Clients.lean`
(67758a78…): a mass-two measure at the endpoints of `[-1, 1]` (not a probability measure, all mass outside the open
support hull) and the zero-dimensional case with mass three. Both use the single joint producer, so one subsequence and
one limit satisfy (56a) and (56b). -/

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis FunctionalInequalities.Probability.MomentMeasure
open scoped ENNReal

namespace CEKLemma17Clients

/-- A mass-two measure at the endpoints; it is not a probability measure, and
all its mass lies outside the open hull used for pointwise compactness. -/
theorem boundary_norm_sequence_both :
    let μ : Measure ℝ := Measure.dirac (-1) + Measure.dirac 1
    μ Set.univ = 2 ∧
      ∃ (s : ℕ → ℕ) (ψ : ℝ → EReal), StrictMono s ∧
        (∀ x ∈ interior (convexHull ℝ μ.support), ψ x = (‖x‖ : EReal)) ∧
        PotentialIntegrable ψ μ ∧
        (∫⁻ x, (ψ x).toENNReal ∂μ ≤ 2) ∧
        mass volume (legendre (fun x : ℝ => (‖x‖ : EReal))) ≤ mass volume (legendre ψ) := by
  dsimp only
  let μ : Measure ℝ := Measure.dirac (-1) + Measure.dirac 1
  have hdirac (a : ℝ) : a ∈ (Measure.dirac a).support := by
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
    norm_num
  have hends : {(-1 : ℝ), 1} ⊆ μ.support := by
    intro x hx
    rw [Measure.support_add]
    rcases hx with rfl | hx
    · exact Set.mem_union_left _ (hdirac (-1))
    · have hx1 : x = 1 := hx
      subst x
      exact Set.mem_union_right _ (hdirac 1)
  have h0 : (0 : ℝ) ∈ interior (convexHull ℝ μ.support) := by
    have hsubset := convexHull_mono (𝕜 := ℝ) hends
    rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)] at hsubset
    have hsmall : Set.Ioo (-1 : ℝ) 1 ⊆ convexHull ℝ μ.support :=
      (Set.Ioo_subset_Icc_self).trans hsubset
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1)) hsmall)
  have hconv : Convex ℝ {p : ℝ × ℝ | (‖p.1‖ : EReal) ≤ (p.2 : EReal)} := by
    simpa only [Set.mem_univ, true_and, EReal.coe_le_coe_iff] using
      (convexOn_norm (E := ℝ) convex_univ).convex_epigraph
  have hm : Measurable (fun x : ℝ => ((‖x‖ : EReal)).toENNReal) :=
    (continuous_coe_real_ereal.comp continuous_norm).measurable.ereal_toENNReal
  have hi : ∫⁻ x, ((‖x‖ : EReal)).toENNReal ∂μ = 2 := by
    norm_num [μ, lintegral_add_measure]
  have hb : (⨆ _ : ℕ, ∫⁻ x, ((‖x‖ : EReal)).toENNReal ∂μ) ≠ ⊤ := by
    simp only [hi, iSup_const]
    norm_num
  obtain ⟨s, ψ, hs, _, _, _, _, hlim, _, _, hpot, _, hbound, hdual⟩ :=
    exists_subseq_integral_bounds_of_convex_epigraph volume μ h0
      (fun _ x => (‖x‖ : EReal))
      (fun _ x => EReal.coe_nonneg.mpr (norm_nonneg x))
      (fun _ => by simp) (fun _ => hconv) (fun _ => hm.aemeasurable) hb
  refine ⟨?_, s, ψ, hs, ?_, hpot, ?_, ?_⟩
  · norm_num
  · intro x hx
    exact tendsto_nhds_unique (hlim x hx).2 tendsto_const_nhds
  · simpa only [hi, Filter.liminf_const] using hbound
  · simpa only [Filter.limsup_const] using hdual

/-- The zero-dimensional case with arbitrary non-probability mass remains in
the original source signature; there is no nontriviality or positive-dimension premise. -/
theorem zeroDim_mass_three_both :
    let E := EuclideanSpace ℝ (Fin 0)
    let μ : Measure E := (3 : ℝ≥0∞) • Measure.dirac 0
    ∃ (s : ℕ → ℕ) (ψ : E → EReal), StrictMono s ∧ ψ 0 = 0 ∧
      (∫⁻ x, (ψ x).toENNReal ∂μ = 0) ∧
      mass volume (legendre ψ) ≠ ⊤ ∧
      mass volume (legendre (fun _ : E => (0 : EReal))) ≤ mass volume (legendre ψ) := by
  dsimp only
  let E := EuclideanSpace ℝ (Fin 0)
  let μ : Measure E := (3 : ℝ≥0∞) • Measure.dirac 0
  let : IsFiniteMeasure μ := (Measure.dirac (0 : E)).smul_finite (by norm_num)
  have hsupp : μ.support = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hzero : x = (0 : E) := Subsingleton.elim _ _
    have hx : (0 : E) ∈ U := hzero ▸ mem_of_mem_nhds hU
    simp [μ, Measure.dirac_apply_of_mem hx]
  have h0 : (0 : E) ∈ interior (convexHull ℝ μ.support) := by simp [hsupp]
  have hc : Convex ℝ {p : E × ℝ | (0 : EReal) ≤ (p.2 : EReal)} := by
    intro p hp q hq a b ha hb hab
    change (0 : EReal) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
    exact EReal.coe_nonneg.mpr
      (add_nonneg (mul_nonneg ha (EReal.coe_nonneg.mp hp))
        (mul_nonneg hb (EReal.coe_nonneg.mp hq)))
  obtain ⟨s, ψ, hs, _, hψ0, _, _, _, _, _, _, hf, hbound, hd⟩ :=
    exists_subseq_integral_bounds_of_convex_epigraph volume μ h0
      (fun _ _ => (0 : EReal)) (fun _ _ => le_rfl)
      (fun _ => rfl) (fun _ => hc) (fun _ => aemeasurable_const) (by simp)
  refine ⟨s, ψ, hs, hψ0, ?_, hf, ?_⟩
  ·
    have hi : ∫⁻ x, (ψ x).toENNReal ∂μ ≤ 0 := by
      simpa only [EReal.toENNReal_zero, lintegral_zero, Filter.liminf_const] using hbound
    exact le_antisymm hi zero_le
  · simpa only [Filter.limsup_const] using hd

end CEKLemma17Clients

#print axioms CEKLemma17Clients.boundary_norm_sequence_both
#print axioms CEKLemma17Clients.zeroDim_mass_three_both
#print axioms FunctionalInequalities.Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph
#print axioms FunctionalInequalities.Analysis.exists_subseq_tendsto_of_convexOn_of_bddAbove
#print axioms FunctionalInequalities.Analysis.exists_radial_extension_of_convexOn
