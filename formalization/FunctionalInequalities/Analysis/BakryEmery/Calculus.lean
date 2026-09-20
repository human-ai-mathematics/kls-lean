import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Local differential calculus

Hessians, directional derivatives, gradients and standard-basis trace identities.
These are pointwise tools; there is no measure, semigroup or curvature estimate here.
-/

noncomputable section

open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

section Hessian

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bilinear second Fréchet derivative of a `C²` real-valued function is symmetric. -/
theorem bilinearIteratedFDerivTwo_symm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w =
      bilinearIteratedFDerivTwo ℝ f x w v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons

end Hessian

section PointwiseTools

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

section Pointwise

omit [CompleteSpace E] in
/-- The Laplacian of a function on a finite-dimensional inner product space is the trace of its
second Fréchet derivative in the standard orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv (f : E → ℝ) (x : E) :
    Laplacian.laplacian f x =
      ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) := by
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  rfl

/-- The inner product of two gradients is the sum of the products of the directional
derivatives in the standard orthonormal basis. -/
theorem inner_gradient_eq_sum_fderiv_mul_fderiv (f g : E → ℝ) (x : E) :
    ⟪gradient f x, gradient g x⟫ =
      ∑ i, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ g x (stdOrthonormalBasis ℝ E i) := by
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_gradient_left, real_inner_comm, inner_gradient_left]

omit [CompleteSpace E] in
/-- The Laplacian of a `C²` function is continuous. -/
theorem continuous_laplacian {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ f)) := h1.continuous_fderiv one_ne_zero
  have : Laplacian.laplacian f = fun x =>
      ∑ i, fderiv ℝ (fderiv ℝ f) x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) :=
    funext fun x => laplacian_eq_sum_fderiv_fderiv f x
  rw [this]
  exact continuous_finsetSum _ fun i _ =>
    (h2.clm_apply continuous_const).clm_apply continuous_const

omit [CompleteSpace E] in
/-- The Laplacian of a compactly supported function has compact support. -/
theorem hasCompactSupport_laplacian {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (Laplacian.laplacian f) := by
  have : Laplacian.laplacian f = (fun A : E →L[ℝ] E →L[ℝ] ℝ =>
      ∑ i, A (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)) ∘ fderiv ℝ (fderiv ℝ f) :=
    funext fun x => laplacian_eq_sum_fderiv_fderiv f x
  rw [this]
  exact ((hfc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left (by simp)

omit [FiniteDimensional ℝ E] in
/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

omit [FiniteDimensional ℝ E] in
/-- The gradient of a compactly supported function has compact support. -/
theorem hasCompactSupport_gradient {f : E → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (gradient f) := by
  change HasCompactSupport ((toDual ℝ E).symm ∘ fderiv ℝ f)
  exact (hfc.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

end Pointwise

end PointwiseTools

section DifferentialTools

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Directional derivatives -/

section Directional

/-- The directional derivative `y ↦ D f (y) v` of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem contDiff_fderiv_apply {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hmn : m + 1 ≤ n) (v : E) : ContDiff ℝ m (fun y => fderiv ℝ f y v) :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

/-- The directional derivative of a `C²` function is differentiable. -/
theorem differentiable_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (v : E) :
    Differentiable ℝ (fun y => fderiv ℝ f y v) :=
  (contDiff_fderiv_apply hf (m := 1) (by norm_num) v).differentiable one_ne_zero

/-- The second derivative applied to `v, w` is the derivative in direction `v` of the directional
derivative in direction `w`. -/
theorem fderiv_fderiv_apply {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [(hf.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
  simp

/-- The bilinear Hessian of a `C²` function as an iterated directional derivative:
`D²f(x)(v, w) = D (y ↦ D f (y) w) x v`. -/
theorem bilinearIteratedFDerivTwo_eq_fderiv_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  rw [fderiv_fderiv_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)]
  rfl

/-- Mixed directional derivatives of a `C²` function commute (route `B2` in directional form). -/
theorem fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fun y => fderiv ℝ f y v) x w := by
  rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hf, ← bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
  exact bilinearIteratedFDerivTwo_symm hf x v w

/-- Third-order commutation for a `C³` function: `∂_w ∂_v ∂_v f = ∂_v ∂_v ∂_w f`. The first
step commutes the two outer derivatives of the `C²` function `∂_v f`; the second commutes the two
inner derivatives of `f` at every point. -/
theorem fderiv_fderiv_fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v) x v := by
  have hg : ContDiff ℝ 2 (fun z => fderiv ℝ f z v) := contDiff_fderiv_apply hf (by norm_num) v
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have h1 : fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) x v :=
    fderiv_apply_comm hg x w v
  have h2 : (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) =
      fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v :=
    funext fun y => fderiv_apply_comm hf2 y w v
  rw [h1, h2]

/-- Product rule for directional derivatives. -/
theorem fderiv_mul_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y * g y) x v = f x * fderiv ℝ g x v + g x * fderiv ℝ f x v := by
  rw [fderiv_fun_mul hf hg]
  simp

/-- Directional derivative of a constant multiple. -/
theorem fderiv_const_mul_apply {g : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x) (c : ℝ) (v : E) :
    fderiv ℝ (fun y => c * g y) x v = c * fderiv ℝ g x v := by
  rw [fderiv_const_mul hg c]
  simp

/-- Sum rule for directional derivatives. -/
theorem fderiv_sum_apply {ι : Type*} (s : Finset ι) {g : ι → E → ℝ} {x : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) (v : E) :
    fderiv ℝ (fun y => ∑ i ∈ s, g i y) x v = ∑ i ∈ s, fderiv ℝ (g i) x v := by
  rw [fderiv_fun_sum hg]
  simp

/-- Difference rule for directional derivatives. -/
theorem fderiv_sub_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y - g y) x v = fderiv ℝ f x v - fderiv ℝ g x v := by
  rw [fderiv_fun_sub hf hg]
  simp

/-- Sum rule for directional derivatives. -/
theorem fderiv_add_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y + g y) x v = fderiv ℝ f x v + fderiv ℝ g x v := by
  rw [fderiv_fun_add hf hg]
  simp

end Directional

/-! ### Gradient calculus -/

section Gradient

variable [CompleteSpace E]

/-- The gradient of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem contDiff_gradient {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradient f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)

/-- Product rule for the gradient. -/
theorem gradient_mul {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  unfold gradient
  rw [fderiv_fun_mul hf hg, map_add, map_smulₛₗ, map_smulₛₗ]
  simp

/-- Difference rule for the gradient. -/
theorem gradient_sub {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y - g y) x = gradient f x - gradient g x := by
  unfold gradient
  rw [fderiv_fun_sub hf hg, map_sub]

end Gradient

/-! ### Expansions in the standard orthonormal basis -/

section StdBasis

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A bilinear form on two expansions `∑ aᵢ vᵢ`. -/
theorem bilinear_sum_smul_sum_smul {ι : Type*} [Fintype ι] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (a : ι → ℝ) (v : ι → E) :
    B (∑ i, a i • v i) (∑ j, a j • v j) = ∑ i, ∑ j, a i * a j * B (v i) (v j) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [CompleteSpace E]

/-- The gradient expanded in the standard orthonormal basis. -/
theorem gradient_eq_sum_fderiv_smul (f : E → ℝ) (x : E) :
    gradient f x =
      ∑ i, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) • stdOrthonormalBasis ℝ E i := by
  conv_lhs => rw [← (stdOrthonormalBasis ℝ E).sum_repr' (gradient f x)]
  simp only [real_inner_comm, inner_gradient_left]

/-- `‖∇f‖²` is the sum of the squared directional derivatives in the standard orthonormal basis. -/
theorem norm_gradient_sq_eq_sum (f : E → ℝ) (y : E) :
    ‖gradient f y‖ ^ 2 = ∑ i, fderiv ℝ f y (stdOrthonormalBasis ℝ E i) ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  simp only [inner_gradient_left]

/-- A bilinear Hessian evaluated twice on a gradient, expanded in the standard basis. -/
theorem bilinearIteratedFDerivTwo_gradient_gradient (U f : E → ℝ) (x : E) :
    bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) =
      ∑ i, ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        bilinearIteratedFDerivTwo ℝ U x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) := by
  rw [gradient_eq_sum_fderiv_smul]
  exact bilinear_sum_smul_sum_smul _ _ _

omit [CompleteSpace E] in
/-- The Laplacian as the trace of the iterated directional derivatives, at a point where the
derivative is differentiable. -/
theorem laplacian_eq_sum_fderiv_apply_fderiv_apply {g : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) :
    Laplacian.laplacian g x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  exact Finset.sum_congr rfl fun i _ => (fderiv_fderiv_apply hg _ _).symm

omit [CompleteSpace E] in
/-- The Laplacian of a `C²` function as a function: the trace of the iterated directional
derivatives in the standard orthonormal basis. -/
theorem laplacian_eq_fun_sum {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    Laplacian.laplacian g = fun x =>
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) :=
  funext fun x => laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)

omit [CompleteSpace E] in
/-- The Laplacian of a `C^n` function is `C^m` when `m + 2 ≤ n`. -/
theorem contDiff_laplacian {g : E → ℝ} {n m : WithTop ℕ∞} (hg : ContDiff ℝ n g) (hmn : m + 2 ≤ n) :
    ContDiff ℝ m (Laplacian.laplacian g) := by
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by simp) hmn
  rw [laplacian_eq_fun_sum (hg.of_le h2)]
  refine ContDiff.sum fun i _ => ?_
  refine contDiff_fderiv_apply (contDiff_fderiv_apply hg ?_ _) le_rfl _
  calc m + 1 + 1 = m + 2 := by rw [add_assoc]; norm_num
    _ ≤ n := hmn

/-- Product rule for the Laplacian: `Δ(fg) = f Δg + g Δf + 2 ⟪∇f, ∇g⟫`. -/
theorem laplacian_mul {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    Laplacian.laplacian (fun y => f y * g y) x =
      f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x +
        2 * ⟪gradient f x, gradient g x⟫ := by
  have hfg : ContDiff ℝ 2 (fun y => f y * g y) := hf.mul hg
  have hfd : ∀ y, DifferentiableAt ℝ f y := fun y => hf.differentiable (by norm_num) y
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by norm_num) y
  rw [laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hfg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    inner_gradient_eq_sum_fderiv_mul_fderiv]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => fderiv ℝ (fun z => f z * g z) y (stdOrthonormalBasis ℝ E i)) =
      fun y => f y * fderiv ℝ g y (stdOrthonormalBasis ℝ E i) +
        g y * fderiv ℝ f y (stdOrthonormalBasis ℝ E i) :=
    funext fun y => fderiv_mul_apply (hfd y) (hgd y) _
  have hA : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x :=
    (hfd x).mul (differentiable_fderiv_apply hg _ x)
  have hB : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y (stdOrthonormalBasis ℝ E i)) x :=
    (hgd x).mul (differentiable_fderiv_apply hf _ x)
  rw [h1, fderiv_add_apply hA hB, fderiv_mul_apply (hfd x) (differentiable_fderiv_apply hg _ x),
    fderiv_mul_apply (hgd x) (differentiable_fderiv_apply hf _ x)]
  ring

end StdBasis

end DifferentialTools

end FunctionalInequalities.Analysis.BakryEmery
