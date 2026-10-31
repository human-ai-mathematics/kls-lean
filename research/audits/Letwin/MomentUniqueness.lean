module

public import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.Finite

/-! Client of the uniqueness of finite moment potentials with bounded-support moment measure
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2; Letwin arXiv:2607.24164v1, Lemma 2.1),
with its Prékopa–Leindler, maximality and translation supports. -/

@[expose] public section
noncomputable section
namespace LetwinMomentUniquenessAudit
open MeasureTheory Set FunctionalInequalities.Probability.MomentMeasure

/-- On `ℝⁿ`: two normalized convex potentials with the same moment measure carried by a ball
are translates of each other in both directions. -/
theorem translate_client {n : ℕ} {ψ₀ ψ₁ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ₀ : ConvexOn ℝ univ ψ₀) (hψ₁ : ConvexOn ℝ univ ψ₁)
    (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hn₁ : ∫ x, Real.exp (-ψ₁ x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hm₀ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-ψ₀)).map (gradient ψ₀) = μ)
    (hm₁ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-ψ₁)).map (gradient ψ₁) = μ)
    {R : ℝ} (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) :
    ∃ y₀ : EuclideanSpace ℝ (Fin n), (∀ y, ψ₁ y = ψ₀ (y - y₀)) ∧ ∀ y, ψ₀ y = ψ₁ (y + y₀) := by
  obtain ⟨y₀, hy₀⟩ := exists_eq_translate_of_map_gradient_eq hψ₀ hψ₁ hn₀ hn₁ hm₀ hm₁ hR
  exact ⟨y₀, hy₀, fun y => by rw [hy₀, add_sub_cancel_right]⟩

/-- Every translate of a normalized convex moment potential of a bounded-support measure is
again one, and these are all of them. -/
theorem iff_client {n : ℕ} {ψ₀ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ₀ : ConvexOn ℝ univ ψ₀)
    (hn₀ : ∫ x, Real.exp (-ψ₀ x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hm₀ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-ψ₀)).map (gradient ψ₀) = μ)
    {R : ℝ} (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) (a : EuclideanSpace ℝ (Fin n)) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (fun x => -ψ₀ (x - a))).map
      (gradient fun x => ψ₀ (x - a)) = μ := by
  have hψ₁ : ConvexOn ℝ univ fun x => ψ₀ (x - a) := by
    refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
    have h := hψ₀.2 (mem_univ (x - a)) (mem_univ (y - a)) hs ht hst
    have he : s • (x - a) + t • (y - a) = s • x + t • y - a := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    simpa only [he, smul_eq_mul] using h
  have hn₁ : ∫ x, Real.exp (-ψ₀ (x - a)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1 := by
    rw [integral_sub_right_eq_self (fun x => Real.exp (-ψ₀ x)) a, hn₀]
  exact (map_gradient_eq_iff_exists_eq_translate hψ₀ hψ₁ hn₀ hn₁ hm₀ hR).2 ⟨a, fun _ => rfl⟩

end LetwinMomentUniquenessAudit
#print axioms FunctionalInequalities.Analysis.lintegral_prekopaLeindler
#print axioms FunctionalInequalities.Analysis.lintegral_slice_prekopaLeindler
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.translate_moment_potential_of_normalized
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_linear_lower_bound_of_integrable_exp_neg
#print axioms FunctionalInequalities.Probability.MomentMeasure.ae_norm_gradient_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_gradient
#print axioms FunctionalInequalities.Probability.MomentMeasure.inner_sub_le_legendre_toReal
#print axioms FunctionalInequalities.Probability.MomentMeasure.measurable_legendre_toReal
#print axioms FunctionalInequalities.Probability.MomentMeasure.ae_legendre_ne_top
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.lintegral_le_exp_integral_of_map_gradient
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exp_mul_abs_legendre
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_eq_translate_of_map_gradient_eq
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.map_gradient_eq_iff_exists_eq_translate
#print axioms LetwinMomentUniquenessAudit.translate_client
#print axioms LetwinMomentUniquenessAudit.iff_client
