module

public import FunctionalInequalities.Analysis.Newtonian.Kernel.Measurable

/-!
# Third derivatives of the Newtonian kernel

For `n ≥ 2` and `x ≠ 0`, the kernel `Γ` of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12):

* `fderiv_bilinear_newtonianKernel`: the explicit derivative in direction `w` of the Hessian entry
  `y ↦ D²Γ(y)(u, v)`, i.e. the third derivative of `Γ`;
* `contDiffAt_bilinear_newtonianKernel`: each Hessian entry is smooth of every order off the origin.

These supply the third-derivative bound used in the far-field step of Lemma 4.4.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

private theorem hasFDerivAt_inner_right {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x u : E) : HasFDerivAt (fun y => ⟪y, u⟫) (innerSL ℝ u) x := by
  convert (innerSL ℝ u).hasFDerivAt using 1
  funext y
  exact (real_inner_comm y u).symm

/-- Actual directional derivative of the Hessian of the source-normalized
Newtonian expression, including n=2. This supplies the third kernel derivative
in GT2001 (2.14) and the far step of Lemma 4.4. -/
theorem fderiv_bilinear_newtonianKernel {n : ℕ} (hn : 2 ≤ n)
    (x u v w : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) y u v) x w =
      (1 / ((n : ℝ) * euclideanUnitBallVolume n)) *
        ((-(n : ℝ)) * ‖x‖ ^ (-(n : ℝ) - 2) * ⟪x, w⟫ * ⟪u, v⟫ -
          (n : ℝ) *
            ((-(n : ℝ) - 2) * ‖x‖ ^ (-(n : ℝ) - 4) * ⟪x, w⟫ * ⟪x, u⟫ * ⟪x, v⟫ +
              ‖x‖ ^ (-(n : ℝ) - 2) * (⟪w, u⟫ * ⟪x, v⟫ + ⟪x, u⟫ * ⟪w, v⟫))) := by
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    (1 / ((n : ℝ) * euclideanUnitBallVolume n)) *
      (‖y‖ ^ (-(n : ℝ)) * ⟪u, v⟫ - (n : ℝ) * ‖y‖ ^ (-(n : ℝ) - 2) * ⟪y, u⟫ * ⟪y, v⟫)
  have he : (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) y u v) =ᶠ[𝓝 x] G := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact bilinear_newtonianKernel hn y u v hy
  have hu := hasFDerivAt_inner_right x u
  have hv := hasFDerivAt_inner_right x v
  have h1 := (hasFDerivAt_norm_rpow_of_ne_zero x (-(n : ℝ)) hx).mul_const ⟪u, v⟫
  have h2 :=
    (((hasFDerivAt_norm_rpow_of_ne_zero x (-(n : ℝ) - 2) hx).const_mul (n : ℝ)).mul hu).mul hv
  have hG := (h1.sub h2).const_mul (1 / ((n : ℝ) * euclideanUnitBallVolume n))
  change HasFDerivAt G _ x at hG
  rw [(hG.congr_of_eventuallyEq he).fderiv]
  simp only [add_apply, sub_apply, smul_apply, Pi.mul_apply, innerSL_apply_apply, smul_eq_mul]
  have hexp : -(n : ℝ) - 2 - 2 = -(n : ℝ) - 4 := by ring
  rw [hexp]
  rw [real_inner_comm w u, real_inner_comm w v]
  ring


/-- Smoothness of the actual Hessian kernel away from zero; this concerns
Gamma only and gives no smoothness bootstrap of a moment potential. -/
theorem contDiffAt_bilinear_newtonianKernel {n : ℕ} (hn : 2 ≤ n)
    (x u v : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) y u v) x := by
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    (1 / ((n : ℝ) * euclideanUnitBallVolume n)) *
      (‖y‖ ^ (-(n : ℝ)) * ⟪u, v⟫ - (n : ℝ) * ‖y‖ ^ (-(n : ℝ) - 2) * ⟪y, u⟫ * ⟪y, v⟫)
  have he : (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) y u v) =ᶠ[𝓝 x] G := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact bilinear_newtonianKernel hn y u v hy
  have hp (p : ℝ) : ContDiffAt ℝ k (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ p) x :=
    (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
  have hu : ContDiffAt ℝ k (fun y : EuclideanSpace ℝ (Fin n) => ⟪y, u⟫) x :=
    contDiffAt_id.inner ℝ contDiffAt_const
  have hv : ContDiffAt ℝ k (fun y : EuclideanSpace ℝ (Fin n) => ⟪y, v⟫) x :=
    contDiffAt_id.inner ℝ contDiffAt_const
  have hG : ContDiffAt ℝ k G x :=
    contDiffAt_const.mul
      (((hp (-(n : ℝ))).mul contDiffAt_const).sub
        ((((contDiffAt_const.mul (hp (-(n : ℝ) - 2))).mul hu).mul hv)))
  exact hG.congr_of_eventuallyEq he

end FunctionalInequalities.Analysis
