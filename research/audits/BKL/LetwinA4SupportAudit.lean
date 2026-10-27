import FunctionalInequalities.Analysis.Convex.Coercivity
import FunctionalInequalities.Analysis.BakryEmery.Hessian.Diffusion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Audit: Letwin Lemma A.4 support results

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17). Clients of the coercivity theorem
`exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`, every premise derived here:

* the real Gaussian potential `φ x = x²` on `ℝ` with Lebesgue measure: convexity from `Even.convexOn_pow`, integrability
  of `e^{-x²}` from Mathlib's `integrable_exp_neg_mul_sq` (not assumed); consumers: every global minimiser is `0`
  (independent arithmetic) and the sublevel `{x² ≤ 1}` is bounded;
* dimension zero: an arbitrary `φ` on `EuclideanSpace ℝ (Fin 0)` with its volume (an additive Haar measure); convexity
  and integrability of `e^{-φ}` are derived from the space being a single point (finite Haar measure on a compact space).

Axiom reports for the four Lemma A.4 support declarations and the clients follow. Client bodies: Claude.
-/

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery

namespace A4GaussianCoercivity

/-- The Gaussian potential `x ↦ x²` is convex on `ℝ`. -/
theorem convexOn_sq : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := even_two.convexOn_pow

/-- `e^{-x²}` is Lebesgue integrable (Mathlib's Gaussian integrability with `b = 1`). -/
theorem integrable_exp_neg_sq : Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) volume := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

/-- The coercivity theorem for the Gaussian: a global minimiser and compact sublevels. -/
theorem minimum_and_compact_sublevels :
    (∃ y₀ : ℝ, ∀ y, y₀ ^ 2 ≤ y ^ 2) ∧ ∀ c : ℝ, IsCompact {y : ℝ | y ^ 2 ≤ c} :=
  exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg volume convexOn_sq integrable_exp_neg_sq

/-- Consumer: the minimiser provided by the theorem is `0` (independent arithmetic check). -/
theorem minimiser_eq_zero : ∃ y₀ : ℝ, (∀ y, y₀ ^ 2 ≤ y ^ 2) ∧ y₀ = 0 := by
  obtain ⟨y₀, h⟩ := minimum_and_compact_sublevels.1
  exact ⟨y₀, h, pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm (by simpa using h 0) (sq_nonneg y₀))⟩

/-- Consumer: a compact sublevel is bounded. -/
theorem isBounded_sublevel_one : Bornology.IsBounded {y : ℝ | y ^ 2 ≤ 1} :=
  (minimum_and_compact_sublevels.2 1).isBounded

end A4GaussianCoercivity

namespace A4DimensionZeroCoercivity

/-- The zero-dimensional Euclidean space is a single point. -/
theorem subsingleton : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
  Module.finrank_zero_iff.mp (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 0))

attribute [local instance] subsingleton

/-- Every potential on a point is convex. -/
theorem convexOn (φ : EuclideanSpace ℝ (Fin 0) → ℝ) : ConvexOn ℝ Set.univ φ := by
  refine ⟨convex_univ, fun x _ y _ a b _ _ hab => ?_⟩
  rw [Subsingleton.elim y x, Subsingleton.elim (a • x + b • x) x, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]

/-- `e^{-φ}` is integrable for the volume of the point: a constant on a finite (compact, Haar) measure space. -/
theorem integrable (φ : EuclideanSpace ℝ (Fin 0) → ℝ) :
    Integrable (fun x => Real.exp (-φ x)) (volume : Measure (EuclideanSpace ℝ (Fin 0))) := by
  have h : (fun x => Real.exp (-φ x)) = fun _ => Real.exp (-φ 0) := funext fun x => by rw [Subsingleton.elim x 0]
  rw [h]
  exact integrable_const _

/-- The coercivity theorem in dimension zero, every premise derived. -/
theorem minimum_and_compact_sublevels (φ : EuclideanSpace ℝ (Fin 0) → ℝ) :
    (∃ y₀, ∀ y, φ y₀ ≤ φ y) ∧ ∀ c : ℝ, IsCompact {y | φ y ≤ c} :=
  exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg volume (convexOn φ) (integrable φ)

end A4DimensionZeroCoercivity

#print axioms exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
#print axioms hessianInverseOperator_self
#print axioms bounded_hessianInverseOperator_self
#print axioms hessianInverseOperator_comp
#print axioms A4GaussianCoercivity.convexOn_sq
#print axioms A4GaussianCoercivity.integrable_exp_neg_sq
#print axioms A4GaussianCoercivity.minimum_and_compact_sublevels
#print axioms A4GaussianCoercivity.minimiser_eq_zero
#print axioms A4GaussianCoercivity.isBounded_sublevel_one
#print axioms A4DimensionZeroCoercivity.subsingleton
#print axioms A4DimensionZeroCoercivity.convexOn
#print axioms A4DimensionZeroCoercivity.integrable
#print axioms A4DimensionZeroCoercivity.minimum_and_compact_sublevels
