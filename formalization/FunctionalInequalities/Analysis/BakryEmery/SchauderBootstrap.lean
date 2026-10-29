import FunctionalInequalities.Analysis.IteratedDerivative.Bootstrap.Induction
import FunctionalInequalities.Analysis.BakryEmery.LinearizedEquation

/-!
# Smoothness of a strictly elliptic moment Monge–Ampère potential

Letwin arXiv:2607.24164v1 Lemma 2.2, strong-class smoothness support, following
Gilbarg–Trudinger, Classics 2001, Lemma 17.16 and Theorem 6.2. The potential is given and
locally C^{3,α}; the proof retains it while inducting through every finite order.
-/
local macro "nat_cast_le" : tactic => `(tactic| first | (norm_cast; done) | (norm_cast; omega))

noncomputable section
namespace FunctionalInequalities.Analysis
open Set Metric
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff BigOperators Matrix.Norms.Elementwise
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The inverse Hessian is locally uniformly elliptic once the Hessian is C¹ and positive definite. -/
theorem locallyUniformElliptic_inverse_hessian {u : E → ℝ}
    (hu : LocHolderDeriv 3 u) (hp : ∀ x, (hessianMatrix u x).PosDef) :
    LocallyUniformElliptic (fun i j x => (hessianMatrix u x)⁻¹ i j) := by
  have hreg : ∀ i j, LocHolderDeriv 1 (fun x => (hessianMatrix u x)⁻¹ i j) :=
    LocHolderDeriv.matrix_inv_entry (fun i j => hu.hessianEntry i j)
      (fun x => (hp x).det_pos.ne')
  have hc : Continuous (fun x => (hessianMatrix u x)⁻¹) :=
    continuous_pi fun i => continuous_pi fun j => (hreg i j).contDiff.continuous
  intro s hs
  let : CompactSpace (closedBall (0 : E) s) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) s)
  obtain ⟨a, b, ha, _hb, h⟩ := exists_uniform_quadratic_bounds
    (fun x : closedBall (0 : E) s => (hessianMatrix u x.val)⁻¹)
    (hc.comp continuous_subtype_val) (fun x => (hp x.val).inv)
  refine ⟨a, max a b, ha, le_max_left _ _, fun x hx ξ => ?_⟩
  refine ⟨(h ⟨x, hx⟩ ξ).1, (h ⟨x, hx⟩ ξ).2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg ‖ξ‖)

/-- All finite-order local Hölder regularity at the same given solution. -/
theorem locHolderDeriv_all_of_mongeAmpere (hn : 2 ≤ n) {u W : E → ℝ}
    (hu : LocHolderDeriv 3 u) (hW : ContDiff ℝ ∞ W)
    (hp : ∀ x, (hessianMatrix u x).PosDef)
    (heq : ∀ x, Real.log (hessianMatrix u x).det = -u x + W (gradient u x)) :
    ∀ m : ℕ, LocHolderDeriv m u := by
  let a : Fin n → Fin n → E → ℝ := fun i j x => (hessianMatrix u x)⁻¹ i j
  let b : Fin n → E → ℝ := fun i x => -gradient W (gradient u x) i
  have hsymm : ∀ x i j, a i j x = a j i x := by
    intro x i j
    exact ((Matrix.isHermitian_iff_isSymm.mp (hp x).inv.isHermitian).apply i j).symm
  have hell : LocallyUniformElliptic a := locallyUniformElliptic_inverse_hessian hu hp
  have hW1 : ContDiff ℝ 1 W := hW.of_le (natCast_le_infty 1)
  have hlinear (i : Fin n) : ∀ x,
      (∑ j, ∑ k, a j k x *
        fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i))) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k)) +
      (∑ j, b j x * fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
        (EuclideanSpace.basisFun (Fin n) ℝ j)) +
      fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) = 0 :=
    coordinate_linear_equation_of_mongeAmpere hu.contDiff hW1 hp heq i
  have hreg : ∀ k : ℕ, LocHolderDeriv (k + 3) u := by
    intro k
    induction k with
    | zero => exact hu
    | succ k ih =>
      have ha : ∀ i j, LocHolderDeriv (k + 1) (a i j) :=
        LocHolderDeriv.matrix_inv_entry (fun i j => ih.hessianEntry i j)
          (fun x => (hp x).det_pos.ne')
      have hb : ∀ i, LocHolderDeriv (k + 1) (b i) := by
        intro i
        have hWi : ContDiff ℝ ∞ (fun y => gradient W y i) :=
          (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (contDiff_gradient hW le_rfl)
        exact (LocHolderDeriv.comp_gradient (k + 1) hWi (ih.of_le (by omega))).neg
      have hd : ∀ i, LocHolderDeriv 2
          (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
        fun i => (hu.directional _)
      have hnext : ∀ i, LocHolderDeriv (k + 3)
          (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
        intro i
        exact locHolderDeriv_succ_succ_succ_of_linear_equation hn k (hd i) ha hb
          (LocHolderDeriv.const (k + 1) 0) hsymm hell (hlinear i)
      exact LocHolderDeriv.of_coordinate (hu.contDiff.of_le (by norm_num)) hnext
  intro m
  exact (hreg m).of_le (by omega)

/-- A locally C^{3,α} solution of the strictly elliptic moment Monge–Ampère equation is smooth. -/
theorem contDiff_infty_of_mongeAmpere (hn : 2 ≤ n) {u W : E → ℝ}
    (hu : LocHolderDeriv 3 u) (hW : ContDiff ℝ ∞ W)
    (hp : ∀ x, (hessianMatrix u x).PosDef)
    (heq : ∀ x, Real.log (hessianMatrix u x).det = -u x + W (gradient u x)) :
    ContDiff ℝ ∞ u :=
  contDiff_infty.mpr fun m => (locHolderDeriv_all_of_mongeAmpere hn hu hW hp heq m).contDiff

end FunctionalInequalities.Analysis
