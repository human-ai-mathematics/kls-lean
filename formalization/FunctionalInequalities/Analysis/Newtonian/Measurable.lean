import FunctionalInequalities.Analysis.Newtonian.Kernel

/-!
# Measurability of the Newtonian kernel Hessian

`measurable_bilinear_newtonianKernel`: for `n ≥ 2` and fixed directions `u, v`, the actual Hessian entry
`x ↦ D²Γ(x)(u, v)` of the kernel of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12), is Borel measurable, whatever its value at
the singular point.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The actual Hessian entries of the source-normalized kernel are Borel
measurable, including their arbitrary finite values at the singular point. -/
theorem measurable_bilinear_newtonianKernel {n : ℕ} (hn : 2 ≤ n)
    (u v : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) x u v) := by
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    (1/((n:ℝ)*euclideanUnitBallVolume n))*(‖x‖^(-(n:ℝ))*⟪u,v⟫ -
      (n:ℝ)*‖x‖^(-(n:ℝ)-2)*⟪x,u⟫*⟪x,v⟫)
  have hc : ContinuousOn G ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    intro x hx
    have hx0 : x ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using hx
    have hp (p : ℝ) : ContinuousAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖^p) x :=
      continuousAt_id.norm.rpow_const (Or.inl (norm_ne_zero_iff.mpr hx0))
    have hu : Continuous (fun y : EuclideanSpace ℝ (Fin n) => ⟪y,u⟫) := by fun_prop
    have hv : Continuous (fun y : EuclideanSpace ℝ (Fin n) => ⟪y,v⟫) := by fun_prop
    exact (continuousAt_const.mul (((hp (-(n:ℝ))).mul continuousAt_const).sub
      ((((continuousAt_const.mul (hp (-(n:ℝ)-2))).mul hu.continuousAt).mul hv.continuousAt)))).continuousWithinAt
  apply measurable_of_continuousOn_compl_singleton (0:EuclideanSpace ℝ (Fin n))
  apply hc.congr
  intro x hx
  exact bilinear_newtonianKernel hn x u v (by simpa only [mem_compl_iff,mem_singleton_iff] using hx)

end FunctionalInequalities.Analysis
