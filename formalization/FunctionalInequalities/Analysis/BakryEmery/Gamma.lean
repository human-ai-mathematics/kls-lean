import FunctionalInequalities.Analysis.BakryEmery.Laplacian

/-!
# The carre du champ and its iteration

Gamma, Gamma_2 and the product identity. Generic differential tools live in
Calculus.lean. These pointwise statements provide no semigroup gradient estimate.
-/

noncomputable section

open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The carré du champ and `B0` -/

section Gamma

variable [CompleteSpace E]

/-- The **carré du champ** `Γ(f, g)(x) = ⟪∇f(x), ∇g(x)⟫`, defined geometrically. -/
def gamma (f g : E → ℝ) (x : E) : ℝ := ⟪gradient f x, gradient g x⟫

theorem gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl

theorem gamma_comm (f g : E → ℝ) (x : E) : gamma f g x = gamma g f x := real_inner_comm _ _

/-- `Γ(f, f) = ‖∇f‖²`: the normalisation of `Γ` carries no extra factor. -/
theorem gamma_self (f : E → ℝ) (x : E) : gamma f f x = ‖gradient f x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

theorem gamma_self_fun (f : E → ℝ) : gamma f f = fun y => ‖gradient f y‖ ^ 2 :=
  funext (gamma_self f)

variable [FiniteDimensional ℝ E]

/-- Product rule for the weighted Laplacian: `ℒ(fg) = f ℒg + g ℒf + 2 Γ(f, g)`, for `C²` `f`, `g`
and an arbitrary potential `U`. -/
theorem weightedLaplacian_mul (U : E → ℝ) {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : E) :
    weightedLaplacian U (fun y => f y * g y) x =
      f x * weightedLaplacian U g x + g x * weightedLaplacian U f x + 2 * gamma f g x := by
  simp only [weightedLaplacian_apply, gamma_apply]
  rw [laplacian_mul hf hg x, gradient_mul (hf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x), inner_add_right, inner_smul_right, inner_smul_right]
  ring

/-- **Route `B0`, the carré-du-champ product identity**: for `C²` functions `f`, `g` and any
potential `U`, `(ℒ(fg) - f ℒg - g ℒf) / 2 = Γ(f, g) = ⟪∇f, ∇g⟫`. -/
theorem gamma_eq_weightedLaplacian (U : E → ℝ) {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : E) :
    (weightedLaplacian U (fun y => f y * g y) x - f x * weightedLaplacian U g x -
        g x * weightedLaplacian U f x) / 2 = gamma f g x := by
  rw [weightedLaplacian_mul U hf hg x]
  ring

/-- The **iterated carré du champ** in the diffusion convention,
`Γ₂(f) = ℒ(Γ(f, f)) / 2 - Γ(f, ℒf)`, with `Γ(f, ℒf) = ⟪∇f, ∇(ℒf)⟫` read geometrically. -/
def gammaTwo (U f : E → ℝ) (x : E) : ℝ :=
  weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x

theorem gammaTwo_apply (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x := rfl

/-- `Γ₂` written out in gradients and Laplacians, exactly the left-hand side of route `B3`. -/
theorem gammaTwo_eq_expanded (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
          ⟪gradient U x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫) / 2 -
        ⟪gradient f x,
          gradient (fun y => Laplacian.laplacian f y - ⟪gradient U y, gradient f y⟫) x⟫ := by
  simp only [gammaTwo_apply, gamma_self, weightedLaplacian_apply, gamma_apply]
  rfl

end Gamma

end FunctionalInequalities.Analysis.BakryEmery
