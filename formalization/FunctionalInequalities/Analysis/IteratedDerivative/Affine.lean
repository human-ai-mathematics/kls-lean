module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Affine changes of variables for actual derivatives

Supporting the unit-ball reduction in Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60. For `z ↦ f (c + a • z)`:

* `iteratedFDeriv_comp_smul`, `iteratedFDeriv_affine`: every total iterated Fréchet derivative
  scales
  by `a ^ k`, with no global smoothness assumption (unlike Mathlib's smooth version);
* `norm_iteratedFDeriv_affine`, `norm_iteratedFDeriv_inverse_scale`: the exact operator-norm scale;
* `laplacian_affine`: the actual Laplacian scales by `a ^ 2`;
* `inverse_affine_mem_ball`, `derivative_cap_transfer`: a unit-scale derivative cap transfers to the
  physical ball with the factor `R⁻¹ ^ k` (the cap is a premise, not produced here);
* `fderiv_affine`, `hessian_affine`, `norm_hessian_difference_affine`: the first derivative, the
  nested-operator Hessian and its differences, in operator norm.

These are identities and cap transport only; no harmonic reproducing formula or Schauder estimate
is proved here.
-/

@[expose] public section
noncomputable section
open scoped Topology
open Function
namespace FunctionalInequalities.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Total iterated derivatives respect scalar dilation, including at nonsmooth points.
Unlike Mathlib's smooth version, no global `ContDiff` hypothesis is needed. -/
theorem iteratedFDeriv_comp_smul (a : ℝ) (f : E → F) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z ↦ f (a • z)) =
      fun x ↦ a ^ k • iteratedFDeriv ℝ k f (a • x) := by
  induction k with
  | zero => ext; simp
  | succ k ih =>
    ext x v
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left]
    simp only [Nat.succ_eq_add_one, ih, comp_apply,
      continuousMultilinearCurryLeftEquiv_symm_apply, smul_apply]
    rw [show (fun x ↦ a ^ k • iteratedFDeriv ℝ k f (a • x)) =
      (a ^ k) • (fun x ↦ iteratedFDeriv ℝ k f (a • x)) from rfl]
    rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ)
      (f := fun y : E ↦ iteratedFDeriv ℝ k f (a • y)) (a ^ k)) x]
    simp only [Pi.smul_apply, smul_apply]
    rw [fderiv_comp_smul]
    simp [smul_smul, pow_succ, mul_comm]

/-- All derivative orders under translation and scalar dilation. -/
theorem iteratedFDeriv_affine (f : E → F) (c : E) (a : ℝ) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (fun z ↦ f (c + a • z)) x =
      a ^ k • iteratedFDeriv ℝ k f (c + a • x) := by
  simpa only [iteratedFDeriv_comp_add_left] using
    congrFun (iteratedFDeriv_comp_smul a (fun z ↦ f (c + z)) k) x

/-- Exact operator-norm scaling. -/
theorem norm_iteratedFDeriv_affine (f : E → F) (c : E) (a : ℝ) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun z ↦ f (c + a • z)) x‖ =
      |a| ^ k * ‖iteratedFDeriv ℝ k f (c + a • x)‖ := by
  rw [iteratedFDeriv_affine, norm_smul, Real.norm_eq_abs, abs_pow]

/-- Recover the physical derivative norm from its unit-scale counterpart. -/
theorem norm_iteratedFDeriv_inverse_scale (f : E → F) (c : E) {R : ℝ}
    (hR : 0 < R) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k f (c + R • x)‖ =
      R⁻¹ ^ k * ‖iteratedFDeriv ℝ k (fun z ↦ f (c + R • z)) x‖ := by
  rw [norm_iteratedFDeriv_affine, abs_of_pos hR]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hR.ne']
  simp

section Laplacian
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]
open InnerProductSpace Laplacian
/-- The actual Laplacian rescales by `R²`; no PDE identity is assumed. -/
theorem laplacian_affine (f : H → F) (c : H) (a : ℝ) (x : H) :
    Δ (fun z ↦ f (c + a • z)) x = a ^ 2 • Δ f (c + a • x) := by
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_affine, smul_apply]
  rw [Finset.smul_sum]
end Laplacian
/-- The actual inverse affine coordinate of a point in a physical ball lies in the
unit-coordinate ball, for every positive scale and every inner-radius multiplier. -/
theorem inverse_affine_mem_ball (c y : E) {R ρ : ℝ} (hR : 0 < R)
    (hy : y ∈ Metric.ball c (R * ρ)) :
    R⁻¹ • (y - c) ∈ Metric.ball (0 : E) ρ := by
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hy ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  calc
    R⁻¹ * ‖y - c‖ < R⁻¹ * (R * ρ) := mul_lt_mul_of_pos_left hy (inv_pos.mpr hR)
    _ = ρ := by rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

/-- Every derivative order transfers with exactly R^{-k}. The cap B is arbitrary;
no harmonic estimate is assumed to have been proved by this transfer lemma. -/
theorem derivative_cap_transfer (f : E → F) (c : E) {R ρ B : ℝ}
    (hR : 0 < R) (k : ℕ)
    (hcap : ∀ x ∈ Metric.ball (0 : E) ρ,
      ‖iteratedFDeriv ℝ k (fun z ↦ f (c + R • z)) x‖ ≤ B) :
    ∀ y ∈ Metric.ball c (R * ρ),
      ‖iteratedFDeriv ℝ k f y‖ ≤ R⁻¹ ^ k * B := by
  intro y hy
  let x := R⁻¹ • (y - c)
  have hx : x ∈ Metric.ball (0 : E) ρ := inverse_affine_mem_ball c y hR hy
  have hcoord : c + R • x = y := by
    dsimp [x]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, add_sub_cancel]
  rw [← hcoord, norm_iteratedFDeriv_inverse_scale f c hR]
  exact mul_le_mul_of_nonneg_left (hcap x hx) (pow_nonneg (inv_nonneg.mpr hR.le) k)

/-- The first total Fréchet derivative under an affine dilation. -/
theorem fderiv_affine (f : E → F) (c : E) (a : ℝ) (x : E) :
    fderiv ℝ (fun z ↦ f (c + a • z)) x = a • fderiv ℝ f (c + a • x) := by
  simpa only [fderiv_comp_add_left] using
    (fderiv_comp_smul a (f := fun z ↦ f (c + z)) (x := x))

/-- The nested-operator Hessian
rescales by a², without any additional differentiability assumption. -/
theorem hessian_affine (f : E → F) (c : E) (a : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z ↦ f (c + a • z))) x =
      a ^ 2 • fderiv ℝ (fderiv ℝ f) (c + a • x) := by
  have heq : fderiv ℝ (fun z ↦ f (c + a • z)) =
      fun z ↦ a • fderiv ℝ f (c + a • z) := funext (fderiv_affine f c a)
  rw [heq]
  change (fderiv ℝ (a • (fun z ↦ fderiv ℝ f (c + a • z)))) x = _
  rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun z ↦ fderiv ℝ f (c + a • z)) a) x]
  simp only [Pi.smul_apply]
  rw [fderiv_affine]
  simp [smul_smul, pow_two]

/-- Exact Hessian-difference norm scaling, suitable for Hölder seminorms in
operator norms. This statement is about the Hessian used in the Poisson API. -/
theorem norm_hessian_difference_affine (f : E → F) (c : E) (a : ℝ) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ f (c + a • z))) x -
      fderiv ℝ (fderiv ℝ (fun z ↦ f (c + a • z))) y‖ =
    |a| ^ 2 * ‖fderiv ℝ (fderiv ℝ f) (c + a • x) -
      fderiv ℝ (fderiv ℝ f) (c + a • y)‖ := by
  rw [hessian_affine, hessian_affine]
  rw [← smul_sub (a ^ 2) (fderiv ℝ (fderiv ℝ f) (c + a • x))
    (fderiv ℝ (fderiv ℝ f) (c + a • y))]
  have hn := @norm_smul ℝ (E →L[ℝ] E →L[ℝ] F) _ _ _
    (NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] F)) (a ^ 2)
    (fderiv ℝ (fderiv ℝ f) (c + a • x) - fderiv ℝ (fderiv ℝ f) (c + a • y))
  simpa only [norm_pow, Real.norm_eq_abs] using hn

end FunctionalInequalities.Analysis
