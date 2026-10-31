module

public import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.Maximizer
public import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.Finite
public import FunctionalInequalities.KLS.CEK.Uniqueness

/-! Client of the uniqueness of moment potentials without a support bound
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2, uniqueness; Letwin arXiv:2607.24164v1,
Lemma 2.1): finite convex potentials of an arbitrary moment measure, the maximality inequality
(CEK Theorem 8) against integrable perturbations and the integrability of the conjugate (CEK
Proposition 7) for finite potentials, the equality case of the midpoint Prékopa–Leindler
inequality for finite and for extended-real potentials, and the uniqueness of the maximizers of
the CEK functional up to translation. -/

@[expose] public section
noncomputable section
namespace LetwinUnboundedUniquenessAudit
open MeasureTheory Set FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure

/-- On `ℝⁿ`: two finite convex potentials with the same moment measure, an arbitrary finite
nonzero measure, are translates of each other in both directions. -/
theorem translate_client {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {ψ₀ ψ₁ : EuclideanSpace ℝ (Fin n) → EReal}
    (hψ₀ : ConvexPotential ψ₀) (hψ₁ : ConvexPotential ψ₁)
    (hfin₀ : ∀ x, ψ₀ x ≠ ⊤) (hfin₁ : ∀ x, ψ₁ x ≠ ⊤)
    (hm₀ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => EReal.exp (-ψ₀ x))).map (gradient fun x => (ψ₀ x).toReal) = μ)
    (hm₁ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => EReal.exp (-ψ₁ x))).map (gradient fun x => (ψ₁ x).toReal) = μ) :
    ∃ y₀ : EuclideanSpace ℝ (Fin n), (∀ y, ψ₁ y = ψ₀ (y - y₀)) ∧ ∀ y, ψ₀ y = ψ₁ (y + y₀) := by
  obtain ⟨y₀, hy₀⟩ :=
    FunctionalInequalities.KLS.CEK.exists_eq_translate_of_ofPotential_eq_of_ne_top hμ hψ₀ hψ₁
      hfin₀ hfin₁ hm₀ hm₁
  exact ⟨y₀, hy₀, fun y => by rw [hy₀, add_sub_cancel_right]⟩

/-- On `ℝⁿ`: normalized maximizers of the CEK functional have translated conjugates. -/
theorem maximizer_client {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    [IsProbabilityMeasure μ] {φ₀ φ₁ : EuclideanSpace ℝ (Fin n) → EReal}
    (hφ₀ : PotentialIntegrable φ₀ μ) (hφ₁ : PotentialIntegrable φ₁ μ)
    (hm₀ : ∫⁻ x, EReal.exp (-legendre φ₀ x) = 1) (hm₁ : ∫⁻ x, EReal.exp (-legendre φ₁ x) = 1)
    (hmax₀ : ∀ f, PotentialIntegrable f μ →
      variationalFunctional volume μ f ≤ variationalFunctional volume μ φ₀)
    (hmax₁ : ∀ f, PotentialIntegrable f μ →
      variationalFunctional volume μ f ≤ variationalFunctional volume μ φ₁) :
    ∃ y₀ : EuclideanSpace ℝ (Fin n), ∀ y, legendre φ₁ y = legendre φ₀ (y - y₀) :=
  exists_eq_translate_legendre_of_maximizer hφ₀ hφ₁ hm₀ hm₁ hmax₀ hmax₁

end LetwinUnboundedUniquenessAudit
#print axioms FunctionalInequalities.Probability.MomentMeasure.midpointDensity
#print axioms FunctionalInequalities.Probability.MomentMeasure.measurable_midpointDensity
#print axioms FunctionalInequalities.Probability.MomentMeasure.le_midpointDensity
#print axioms FunctionalInequalities.Probability.MomentMeasure.midpointDensity_le_of_legendre
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_eq_translate_of_lintegral_midpointDensity_le_one
#print axioms FunctionalInequalities.Probability.MomentMeasure.integrable_of_map_gradient_of_le
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.lintegral_le_exp_integral_of_map_gradient_of_integrable
#print axioms FunctionalInequalities.Probability.MomentMeasure.integrable_legendre_toReal
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_eq_translate_of_map_gradient_eq_unbounded
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.map_gradient_eq_iff_exists_eq_translate_unbounded
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_eq_translate_of_midpoint_le_of_lintegral_le_one
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_eq_translate_legendre_of_maximizer
#print axioms FunctionalInequalities.KLS.CEK.exists_eq_translate_of_ofPotential_eq_of_ne_top
#print axioms LetwinUnboundedUniquenessAudit.translate_client
#print axioms LetwinUnboundedUniquenessAudit.maximizer_client
