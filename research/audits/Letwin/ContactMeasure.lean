module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped RealInnerProductSpace Topology
namespace LetwinContactMeasureAudit
open FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- Actual source client at the same normalized transporting Holder witness.
The only local extra condition is the displayed density ceiling, not a derivative,
N property, contact measurability or requested image estimate. -/
theorem source_contact_image_bound (hn : 0 < n)
    {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = volume.withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      (∀ Q : Set E, IsCompact Q → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
        ∀ x ∈ Q, ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
      ∀ Ω : Set E, IsOpen Ω → ∀ ε δ : ℝ, 0 ≤ ε → 0 < δ → δ < 1 →
        (∀ x ∈ Ω, Real.exp (-u x + W (gradient u x)) ≤ (1 + ε) ^ n) →
        let Γ := {x | x ∈ Ω ∧ ∀ y ∈ Ω,
          u x - ((1 - δ) / 2) * ‖x‖ ^ 2 +
            ⟪gradient u x - (1 - δ) • x, y - x⟫ ≤
              u y - ((1 - δ) / 2) * ‖y‖ ^ 2}
        volume ((fun x => gradient u x - (1 - δ) • x) '' Γ) ≤
          ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  intro Ω hΩ ε δ hε hδ hδ1 hfupper
  exact full_quadratic_contact_image_bound hn hs.convexOn hC1 hΩ hf.continuousOn
    (fun x _ => Real.exp_pos _) (fun G hG _ => hMA G hG) hε hδ hδ1 hfupper

end LetwinContactMeasureAudit
#print axioms LetwinContactMeasureAudit.source_contact_image_bound

#print axioms FunctionalInequalities.Analysis.measurableSet_quadratic_contacts
#print axioms FunctionalInequalities.Analysis.volume_image_residual_le_of_quadratic_contacts
#print axioms FunctionalInequalities.Analysis.full_quadratic_contact_image_bound
#check FunctionalInequalities.Analysis.measurableSet_quadratic_contacts
  (E := EuclideanSpace ℝ (Fin 0))
#check FunctionalInequalities.Analysis.full_quadratic_contact_image_bound (n := 1)
