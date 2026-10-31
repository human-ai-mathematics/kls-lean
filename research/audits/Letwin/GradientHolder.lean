module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder

@[expose] public section

noncomputable section
namespace LetwinGradientHolderAudit
open Set MeasureTheory FunctionalInequalities.Analysis
open scoped ContDiff RealInnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A literal-source invocation, with no MA equation or regularity estimate supplied.
One normalized transporting potential has both the compact Hölder gradient and the
power-radius inclusion at every centre and every height in (0,1]. -/
theorem source_holder_gradient_and_sections (hn : 0 < n)
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
      ∀ Q : Set E, IsCompact Q → ∃ α c : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < c ∧
        ∀ x ∈ Q, ∀ h : ℝ, 0 < h → h ≤ 1 →
          Metric.closedBall x (c * h ^ (1 + α)⁻¹) ⊆
            {z | u z ≤ u x + ⟪gradient u x, z - x⟫ + h} := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, _hf, _hMA, _hae, _hu, _hd, hholder, hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  exact ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, hpower⟩
end LetwinGradientHolderAudit
#print axioms LetwinGradientHolderAudit.source_holder_gradient_and_sections
#print axioms
  FunctionalInequalities.Analysis.exists_moment_potential_holder_gradient_of_bounded_open_convex
#print axioms FunctionalInequalities.Analysis.exists_holder_gradient_of_alexandrov_density
#print axioms FunctionalInequalities.Analysis.exists_section_power_inclusion_of_alexandrov_density
