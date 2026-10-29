import FunctionalInequalities.Analysis.Newtonian.Kernel.EntryBound
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The Newtonian kernel

This module opens the Newtonian-potential family `Analysis/Newtonian/`, which formalizes the
Newtonian half of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), Chapter 4, in every dimension `n ≥ 2` (the planar logarithmic
case included) and for Hölder exponents `0 < α < 1`. The chain is
`Kernel/` (this module: the source-normalized fundamental solution `Γ`, (2.12)/(4.1), with its
radial calculus) → `Truncation/` (smooth truncations) → `Potential/Basic` (the potential
`w = Γ ⋆ f` and its first derivative, Lemma 4.1) → `Potential/C2` (Lemma 4.2: `w ∈ C²`, `Δw = f`
and its Hessian representation) → `Schauder/Potential`, `Schauder/LocalHolder` (Lemma 4.4:
interior `C^{2,α}` estimates on balls) → `Potential/Representation` (`u = Γ ⋆ Δu` for compactly
supported `C²` functions, (4.15)) → `Schauder/CompactPoisson` (Theorem 4.5 for compactly supported
solutions). `HessianIntegral/` holds the annular, near-field and far-field integrals of the kernel
Hessian; `BallGrowth/` holds near- and far-field integrals of radial powers and cancelled kernels
for measures with power ball growth. The harmonic half of Theorem 4.6 is not part of this family.

This module defines:

* `euclideanUnitBallVolume n`, the Lebesgue volume of the open unit ball of
  `EuclideanSpace ℝ (Fin n)` (GT's `ω_n`), with `euclideanUnitBallVolume_pos` and
  `euclideanUnitBallVolume_two : euclideanUnitBallVolume 2 = π`. It is not identified here with
  the Gamma-function formula `Analysis.unitBallVolume` of `Analysis/Hausdorff/Measure.lean`;
* `newtonianKernel n x`, equal to `(2π)⁻¹ log ‖x‖` for `n = 2` and to
  `(n (2 - n) ω_n)⁻¹ ‖x‖^(2-n)` otherwise. Its value at `x = 0` is the Lean junk value of the formula
  and carries no meaning; no distributional identity is asserted;
* `bilinear_newtonianKernel` ((2.13)) and `abs_bilinear_newtonianKernel_basis_le` ((2.14)): the
  actual Hessian and the entrywise bound `|D_ij Γ(x)| ≤ ω_n⁻¹ ‖x‖^(-n)` at `x ≠ 0`, `n ≥ 2`.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Actual Euclidean unit-ball volume, the omega_n of GT2001. -/
def euclideanUnitBallVolume (n : ℕ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1)

theorem euclideanUnitBallVolume_pos (n : ℕ) : 0 < euclideanUnitBallVolume n := by
  exact ENNReal.toReal_pos (measure_ball_pos volume (0:EuclideanSpace ℝ (Fin n)) zero_lt_one).ne'
    measure_ball_lt_top.ne

theorem euclideanUnitBallVolume_two : euclideanUnitBallVolume 2 = Real.pi := by
  change ((volume : Measure (EuclideanSpace ℝ (Fin 2))) (ball 0 1)).toReal = Real.pi
  rw [EuclideanSpace.volume_ball_fin_two]
  simp [Real.pi_pos.le]

/-- The GT2001 (2.12)/(4.1) scalar expression with the source normalization.
Its arbitrary value at zero is not a distributional identity or a potential
representation theorem. Only dimensions n>=2 are used in the statements. -/
def newtonianKernel (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if n=2 then (1/(2*Real.pi))*Real.log ‖x‖ else powerKernel n (euclideanUnitBallVolume n) x

/-- Exact GT2001 (2.14) Hessian-entry bound, now in every source dimension n>=2
and with the actual Euclidean unit-ball volume. -/
theorem abs_bilinear_newtonianKernel_basis_le {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (i j : Fin n) :
    |bilinearIteratedFDerivTwo ℝ (newtonianKernel n) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      (1/euclideanUnitBallVolume n)*‖x‖^(-(n:ℝ)) := by
  by_cases hn2 : n=2
  · subst n
    have he : newtonianKernel 2 = logKernel := by funext y;simp [newtonianKernel,logKernel]
    rw [he,euclideanUnitBallVolume_two]
    exact abs_bilinear_logKernel_basis_le x hx i j
  · have hn3 : 3 ≤ n := by omega
    have he : newtonianKernel n = powerKernel n (euclideanUnitBallVolume n) := by
      funext y;simp only [newtonianKernel,if_neg hn2]
    rw [he]
    exact abs_bilinear_powerKernel_basis_le hn3 (euclideanUnitBallVolume_pos n) x hx i j


/-- Unified actual Hessian formula (2.13) at every nonzero point, with the
actual unit-ball volume and the logarithmic case included. -/
theorem bilinear_newtonianKernel {n : ℕ} (hn : 2 ≤ n)
    (x u v : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) x u v =
      (1/((n:ℝ)*euclideanUnitBallVolume n))*(‖x‖^(-(n:ℝ))*⟪u,v⟫ -
        (n:ℝ)*‖x‖^(-(n:ℝ)-2)*⟪x,u⟫*⟪x,v⟫) := by
  by_cases hn2 : n=2
  · subst n
    have he : newtonianKernel 2 = logKernel := by funext y;simp [newtonianKernel,logKernel]
    rw [he,euclideanUnitBallVolume_two]
    simpa only [Nat.cast_ofNat,show (-2:ℝ)-2 = -4 by norm_num] using bilinear_logKernel x u v hx
  · have hn3 : 3 ≤ n := by omega
    have he : newtonianKernel n = powerKernel n (euclideanUnitBallVolume n) := by
      funext y;simp only [newtonianKernel,if_neg hn2]
    rw [he]
    exact bilinear_powerKernel hn3 (euclideanUnitBallVolume_pos n) x u v hx

end FunctionalInequalities.Analysis
