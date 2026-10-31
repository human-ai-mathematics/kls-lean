module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
public import FunctionalInequalities.Analysis.Convex.Section.Covering

@[expose] public section

noncomputable section
namespace LetwinSectionCoveringAudit
open Set MeasureTheory FunctionalInequalities.Analysis
open scoped ContDiff RealInnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Actual literal-source selection. The equation and the engulfing estimate
are produced from the source; neither is an assumption of this client. -/
theorem source_section_cover (hn : 0 < n)
    {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      (∀ Q : Set E, IsCompact Q → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
        ∀ x ∈ Q, ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
      ∀ Q : Set E, IsCompact Q → ∃ A h₀ : ℝ, 1 < A ∧ 0 < h₀ ∧
        ∀ {ι : Type*} (I : Set ι) (x : ι → E) (h : ι → ℝ),
          (∀ i ∈ I, x i ∈ Q) → (∀ i ∈ I, 0 < h i ∧ h i ≤ h₀) →
          ∃ J ⊆ I, J.Countable ∧
            J.PairwiseDisjoint (fun i => {z | SoftEngulfing.defect u (x i) z < h i}) ∧
            ∀ i ∈ I, {z | SoftEngulfing.defect u (x i) z < h i} ⊆
              ⋃ j ∈ J, {z | SoftEngulfing.defect u (x j) z < A * h j} := by
  obtain ⟨u, L, hs, hl, hnorm, hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hnorm, hm, hC1, he, hholder, ?_⟩
  intro Q hQ
  exact exists_disjoint_section_cover_of_alexandrov_density hn hs hC1 hf
    (fun x => Real.exp_pos _) hMA hQ
end LetwinSectionCoveringAudit
#print axioms LetwinSectionCoveringAudit.source_section_cover
#print axioms FunctionalInequalities.Analysis.SoftEngulfing.exists_bregman_comparison
#print axioms FunctionalInequalities.Analysis.SoftEngulfing.exists_section_engulfing
#print axioms FunctionalInequalities.Analysis.exists_section_engulfing_of_alexandrov_density
#print axioms FunctionalInequalities.Analysis.SoftEngulfing.section_subset_of_intersection
#print axioms FunctionalInequalities.Analysis.SoftEngulfing.exists_disjoint_section_cover
#print axioms FunctionalInequalities.Analysis.exists_disjoint_section_cover_of_alexandrov_density

namespace LetwinSectionCoveringAudit
open Set MeasureTheory FunctionalInequalities.Analysis
open scoped ContDiff RealInnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The weak-type bound is derived from the actual literal-source equation,
with common constants before the set, density threshold and section family. -/
theorem source_weak_type_section_cover (hn : 0 < n)
    {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      (∀ Q : Set E, IsCompact Q → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
        ∀ x ∈ Q, ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
      ∀ Q : Set E, IsCompact Q → ∃ M h₀ : ℝ, 0 < M ∧ 0 < h₀ ∧
        ∀ {ι : Type*} (δ : ℝ), 0 < δ → ∀ s : Set E, MeasurableSet s →
        ∀ (I : Set ι) (x : ι → E) (h : ι → ℝ),
          (∀ i ∈ I, x i ∈ Q) → (∀ i ∈ I, 0 < h i ∧ h i ≤ h₀) →
          (∀ i ∈ I, ENNReal.ofReal δ * volume {z | SoftEngulfing.defect u (x i) z < h i} ≤
            volume (s ∩ {z | SoftEngulfing.defect u (x i) z < h i})) →
          ENNReal.ofReal δ * volume (⋃ i ∈ I, {z | SoftEngulfing.defect u (x i) z < h i}) ≤
            ENNReal.ofReal M * volume s := by
  obtain ⟨u, L, hs, hl, hnorm, hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hnorm, hm, hC1, he, hholder, ?_⟩
  intro Q hQ
  exact exists_quantitative_weak_type_section_cover hn hs hC1 hf (fun x => Real.exp_pos _) hMA hQ
end LetwinSectionCoveringAudit
#print axioms LetwinSectionCoveringAudit.source_weak_type_section_cover
#print axioms FunctionalInequalities.Analysis.section_volume_mul_le
#print axioms FunctionalInequalities.Analysis.exists_quantitative_weak_type_section_cover
