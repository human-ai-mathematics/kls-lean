import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Scope audit for the local `Γ`/`Γ₂` calculus: `B0`–`B4`

This client imports the two new modules of the round (`Analysis/BakryEmery/Gamma.lean`,
`Analysis/BakryEmery/Bochner/Basic.lean`) and discharges the five route obligations `B0`–`B4` of
`research/audits/BakryEmeryRouteStatements.lean`. The propositions are restated **verbatim** from
that file as `route_B0`–`route_B4`; each proof is one `exact` (after weakening `ContDiff ℝ 2 U`
or `ContDiff ℝ 3 U` to what the library theorem needs: `B0` uses no regularity of `U`, `B3` and
`B4` use `C²`).

Conventions. The diffusion generator is `ℒ f = Δ f - ⟪∇U, ∇f⟫` (`weightedLaplacian U f`); the
nonnegative operator of the semigroup is `A = -ℒ` on the identified smooth tests (`G1`).
`Γ(f, g) = ⟪∇f, ∇g⟫` (`gamma`), `Γ₂(f) = ℒ(Γ(f, f))/2 - Γ(f, ℒf)` (`gammaTwo`). `B3` is stated in
the **fixed** standard orthonormal basis; the double sum `hessianSqStdBasis` is not claimed to be
basis independent.

Boundary section: with `U = 0` the identity is the Euclidean Bochner formula
`Δ‖∇f‖²/2 - ⟪∇f, ∇Δf⟫ = ∑ᵢ∑ⱼ (D²f(eᵢ,eⱼ))²`; for affine `f` the Hessian square vanishes and
`Γ₂(f) = D²U(∇f, ∇f)`; in a zero-dimensional space `Γ₂ = 0` with no regularity hypothesis; and a
one-dimensional sanity value computed **without** `B3`, from Mathlib's `laplacian_eq_iteratedDeriv_real`
and `gradient_eq_deriv'`, gives `Γ₂(t²) = 4 = 4 · 1` for the zero potential on `ℝ`, which
pins the factor `1/2` and the sign (a reversed sign would give `-4`, a missing factor `8`).

Nothing about the heat semigroup (`S0`: regular representatives of `P_t f`, `Γ(P_t f) ≤ P_t Γ(f)`,
the `L¹` gradient bound), about general log-concave laws, or about Buser is claimed here.

The axiom reports at the end cover every public declaration of the two new modules and every
theorem of this client; each must list only `propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace BakryEmeryBochnerAudit

/-! ### `B0` — the carré-du-champ product identity for the diffusion sign convention -/

theorem route_B0 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U f g : E → ℝ),
    ContDiff ℝ 2 U → ContDiff ℝ 2 f → ContDiff ℝ 2 g → ∀ x,
      ((Laplacian.laplacian (fun y => f y * g y) x -
          inner ℝ (gradient U x) (gradient (fun y => f y * g y) x)) -
        f x * (Laplacian.laplacian g x - inner ℝ (gradient U x) (gradient g x)) -
        g x * (Laplacian.laplacian f x - inner ℝ (gradient U x) (gradient f x))) / 2 =
      inner ℝ (gradient f x) (gradient g x) := by
  intro E _ _ _ _ U f g _ hf hg x
  exact gamma_eq_weightedLaplacian U hf hg x

/-! ### `B1` — convexity gives a positive-semidefinite Hessian -/

theorem route_B1 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U : E → ℝ),
    ContDiff ℝ 2 U → ConvexOn ℝ Set.univ U → ∀ x v,
      0 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  intro E _ _ _ _ U hU hconv x v
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hU hconv x v

/-! ### `B2` — symmetry of the Hessian / mixed derivatives -/

theorem route_B2 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (f : E → ℝ),
    ContDiff ℝ 2 f → ∀ x v w,
      bilinearIteratedFDerivTwo ℝ f x v w =
        bilinearIteratedFDerivTwo ℝ f x w v := by
  intro E _ _ _ _ f hf x v w
  exact bilinearIteratedFDerivTwo_symm hf x v w

/-! ### `B3` — coordinate form of the Bochner identity -/

theorem route_B3 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U f : E → ℝ),
    ContDiff ℝ 3 U → ContDiff ℝ 3 f → ∀ x,
      (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
          inner ℝ (gradient U x) (gradient (fun y => ‖gradient f y‖ ^ 2) x)) / 2 -
        inner ℝ (gradient f x)
          (gradient (fun y => Laplacian.laplacian f y -
            inner ℝ (gradient U y) (gradient f y)) x) =
      (∑ i, ∑ j,
          (bilinearIteratedFDerivTwo ℝ f x
            (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2) +
        bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) := by
  intro E _ _ _ _ U f hU hf x
  exact bochner_stdBasis hU hf x

/-! ### `B4` — the local `Γ₂ ≥ 0` consequence -/

theorem route_B4 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U f : E → ℝ),
    ContDiff ℝ 3 U → ConvexOn ℝ Set.univ U → ContDiff ℝ 3 f → ∀ x,
      0 ≤
        (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
            inner ℝ (gradient U x) (gradient (fun y => ‖gradient f y‖ ^ 2) x)) / 2 -
          inner ℝ (gradient f x)
            (gradient (fun y => Laplacian.laplacian f y -
              inner ℝ (gradient U y) (gradient f y)) x) := by
  intro E _ _ _ _ U f hU hconv hf x
  exact bochner_nonneg_stdBasis hU hconv hf x

/-! ### `Γ₂` form of `B3`/`B4` -/

theorem route_B3_gammaTwo : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (U f : E → ℝ),
    ContDiff ℝ 3 U → ContDiff ℝ 3 f → ∀ x,
      gammaTwo U f x =
        hessianSqStdBasis f x + bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) := by
  intro E _ _ _ _ U f hU hf x
  exact gammaTwo_eq_hessianSqStdBasis_add (hU.of_le (by norm_num)) hf x

theorem route_B4_gammaTwo : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (U f : E → ℝ),
    ContDiff ℝ 3 U → ConvexOn ℝ Set.univ U → ContDiff ℝ 3 f → ∀ x, 0 ≤ gammaTwo U f x := by
  intro E _ _ _ _ U f hU hconv hf x
  exact gammaTwo_nonneg (hU.of_le (by norm_num)) hconv hf x

/-! ### Boundary checks -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- `U = 0`: the Euclidean Bochner identity `Δ‖∇f‖²/2 - ⟪∇f, ∇Δf⟫ = ∑ᵢ∑ⱼ (D²f(eᵢ, eⱼ))²`. -/
theorem boundary_euclidean {f : V → ℝ} (hf : ContDiff ℝ 3 f) (x : V) :
    Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x / 2 -
      ⟪gradient f x, gradient (Laplacian.laplacian f) x⟫ =
    ∑ i, ∑ j,
      (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j)) ^ 2 := by
  have h := gammaTwo_zero_potential hf x
  rw [gammaTwo_eq_expanded, hessianSqStdBasis_apply] at h
  simpa only [gradient_fun_const, inner_zero_left, sub_zero] using h

/-- Affine `f`: the Hessian square vanishes and `Γ₂(f) = D²U(∇f, ∇f)`. -/
theorem boundary_affine {U : V → ℝ} (hU : ContDiff ℝ 3 U) (L : V →L[ℝ] ℝ) (c : ℝ) (x : V) :
    hessianSqStdBasis (fun y => L y + c) x = 0 ∧
      gammaTwo U (fun y => L y + c) x =
        bilinearIteratedFDerivTwo ℝ U x (gradient (fun y => L y + c) x)
          (gradient (fun y => L y + c) x) :=
  ⟨hessianSqStdBasis_affine L c x, gammaTwo_affine (hU.of_le (by norm_num)) L c x⟩

/-- Zero-dimensional space: `Γ₂ = 0` for every `U`, `f`, with no regularity hypothesis. -/
theorem boundary_zero_dim [Subsingleton V] (U f : V → ℝ) (x : V) : gammaTwo U f x = 0 :=
  gammaTwo_of_subsingleton U f x

/-- Convex potential, affine test: `Γ₂` is the (nonnegative) second derivative of `U` along the
gradient, with no sign reversal. -/
theorem boundary_affine_nonneg {U : V → ℝ} (hU : ContDiff ℝ 3 U) (hconv : ConvexOn ℝ Set.univ U)
    (L : V →L[ℝ] ℝ) (c : ℝ) (x : V) : 0 ≤ gammaTwo U (fun y => L y + c) x :=
  gammaTwo_nonneg (hU.of_le (by norm_num)) hconv (L.contDiff.add contDiff_const) x

/-- One-dimensional sanity value computed **without** `B3`: on `ℝ` with the zero potential and
`f(t) = t²`, `Γ₂(f)(0) = Δ(‖∇f‖²)(0)/2 - ⟪∇f(0), ∇(Δf)(0)⟫ = 8/2 - 0 = 4`, evaluated through
Mathlib's `laplacian_eq_iteratedDeriv_real` and `gradient_eq_deriv'`. This agrees with the
right-hand side of `B3`, `(f'')² = 4`; a reversed sign would give `-4`, a missing `1/2` would give
`8`. -/
theorem boundary_one_dim_value : gammaTwo (fun _ : ℝ => (0 : ℝ)) (fun t : ℝ => t ^ 2) 0 = 4 := by
  have hgrad : ∀ y : ℝ, gradient (fun t : ℝ => t ^ 2) y = 2 * y := by
    intro y
    rw [gradient_eq_deriv']
    simp
  have hgamma : (fun y : ℝ => gamma (fun t : ℝ => t ^ 2) (fun t : ℝ => t ^ 2) y) =
      fun y => 4 * y ^ 2 := by
    funext y
    rw [gamma_self, hgrad, Real.norm_eq_abs, sq_abs]
    ring
  rw [gammaTwo_apply, hgamma]
  simp only [weightedLaplacian_apply, gradient_fun_const, inner_zero_left, sub_zero, gamma_apply,
    hgrad]
  rw [InnerProductSpace.laplacian_eq_iteratedDeriv_real]
  simp

/-- The same value through `B3`: the Hessian square of `t²` in the standard basis of `ℝ` is `4`. -/
theorem boundary_one_dim_hessianSq : hessianSqStdBasis (fun t : ℝ => t ^ 2) 0 = 4 := by
  have hf : ContDiff ℝ 3 (fun t : ℝ => t ^ 2) := contDiff_id.pow 2
  rw [← gammaTwo_zero_potential hf 0]
  exact boundary_one_dim_value

end BakryEmeryBochnerAudit

/-! ### Axiom reports -/

#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiff_fderiv_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_fderiv_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_apply_comm
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_fderiv_fderiv_apply_comm
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_mul_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_const_mul_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_sum_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_sub_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_add_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient
#print axioms FunctionalInequalities.Analysis.BakryEmery.gradient_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.gradient_sub
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinear_sum_smul_sum_smul
#print axioms FunctionalInequalities.Analysis.BakryEmery.gradient_eq_sum_fderiv_smul
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_gradient_sq_eq_sum
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_gradient_gradient
#print axioms FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_fun_sum
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiff_laplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.laplacian_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.gamma
#print axioms FunctionalInequalities.Analysis.BakryEmery.gamma_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.gamma_comm
#print axioms FunctionalInequalities.Analysis.BakryEmery.gamma_self
#print axioms FunctionalInequalities.Analysis.BakryEmery.gamma_self_fun
#print axioms FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.gamma_eq_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_expanded
#print axioms FunctionalInequalities.Analysis.BakryEmery.convexOn_line
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasDerivAt_line
#print axioms FunctionalInequalities.Analysis.BakryEmery.deriv_line
#print axioms FunctionalInequalities.Analysis.BakryEmery.deriv_deriv_line
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_nonneg
#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_two_mul_sum_add
#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_mul_sum_add_swap
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_gradient_sq_fun
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_norm_gradient_sq_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_norm_sq
#print axioms FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq
#print axioms FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add
#print axioms FunctionalInequalities.Analysis.BakryEmery.bochner_stdBasis
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo_nonneg
#print axioms FunctionalInequalities.Analysis.BakryEmery.bochner_nonneg_stdBasis
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo_zero_potential
#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_affine
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_affine
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo_affine
#print axioms FunctionalInequalities.Analysis.BakryEmery.gammaTwo_of_subsingleton
#print axioms BakryEmeryBochnerAudit.route_B0
#print axioms BakryEmeryBochnerAudit.route_B1
#print axioms BakryEmeryBochnerAudit.route_B2
#print axioms BakryEmeryBochnerAudit.route_B3
#print axioms BakryEmeryBochnerAudit.route_B4
#print axioms BakryEmeryBochnerAudit.route_B3_gammaTwo
#print axioms BakryEmeryBochnerAudit.route_B4_gammaTwo
#print axioms BakryEmeryBochnerAudit.boundary_euclidean
#print axioms BakryEmeryBochnerAudit.boundary_affine
#print axioms BakryEmeryBochnerAudit.boundary_zero_dim
#print axioms BakryEmeryBochnerAudit.boundary_affine_nonneg
#print axioms BakryEmeryBochnerAudit.boundary_one_dim_value
#print axioms BakryEmeryBochnerAudit.boundary_one_dim_hessianSq
