import FunctionalInequalities.Analysis.Newtonian.Truncation.L1
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Scalar truncation error of the Newtonian kernel and vanishing majorants

Kernel-level inputs of the proof of Lemma 4.1 of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), p. 54, in every dimension `n ≥ 2`:

* `integrableOn_newtonianKernel_ball`: `Γ` is integrable on every ball `B_R(0)` with the explicit
  bound (planar and `n ≥ 3` cases combined);
* `newtonianScalarErrorBound`, `newtonianDerivErrorBound`: the explicit L¹ majorants of the scalar and
  first-derivative truncation errors, and `integrable_truncatedNewtonianKernel_sub`:
  `∫ |Γ_eps - Γ| ≤ newtonianScalarErrorBound n eps`;
* `tendsto_newtonian_error_bounds`: both majorants tend to `0` along `eps_k = 1/(k+1)`;
* `opNorm_le_sum_abs_basisFun`: the operator norm of a linear functional on `ℝⁿ` is at most the sum of
  the absolute values of its coordinate entries.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- The scalar L¹ error majorant of the radial truncation of the source-normalized kernel
(GT2001 Lemma 4.1): `R²/2 (|log R| + 1/2)` in the plane and `R²/(2(n−2))` for `n > 2`, at `R = 2ε`. -/
def newtonianScalarErrorBound (n : ℕ) (eps : ℝ) : ℝ :=
  if n = 2 then (2*eps)^2/2*(|Real.log (2*eps)|+1/2) else (2*eps)^2/(2*((n:ℝ)-2))

/-- The first-derivative L¹ error majorant of GT2001 Lemma 4.1, p. 54 (without the profile factor `1+B/2`):
`4ε(1+|log 2ε|)` in the plane and `2nε/(n−2)` for `n > 2`. -/
def newtonianDerivErrorBound (n : ℕ) (eps : ℝ) : ℝ :=
  if n = 2 then 4*eps*(1+|Real.log (2*eps)|) else 2*(n:ℝ)*eps/((n:ℝ)-2)

/-- The source-normalized kernel is locally L¹ on every ball about the origin, in every dimension `n ≥ 2`. -/
theorem integrableOn_newtonianKernel_ball {n : ℕ} (hn : 2 ≤ n) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (newtonianKernel n) (ball 0 R) volume ∧
    (∫ y in ball 0 R, |newtonianKernel n y|) ≤
      if n = 2 then R^2/2*(|Real.log R|+1/2) else R^2/(2*((n:ℝ)-2)) := by
  by_cases h2 : n = 2
  · subst n
    simpa only [if_true] using integrableOn_newtonianKernel_two_ball hR
  · simpa only [if_neg h2] using integrableOn_newtonianKernel_ball_of_two_lt (by omega : 3 ≤ n) hR

/-- Pointwise: the truncation error is supported in the open `2ε` ball and bounded there by `|Γ|`. -/
theorem abs_truncatedNewtonianKernel_sub_le {n : ℕ} {eps : ℝ} (heps : 0 < eps) (y : EuclideanSpace ℝ (Fin n)) :
    |truncatedNewtonianKernel n eps y - newtonianKernel n y| ≤
      (ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)).indicator (fun z => |newtonianKernel n z|) y := by
  by_cases hy : y ∈ ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)
  · rw [Set.indicator_of_mem hy]
    have h0 := Real.smoothTransition.nonneg (2-‖y‖/eps)
    have h1 := Real.smoothTransition.le_one (2-‖y‖/eps)
    have he : truncatedNewtonianKernel n eps y - newtonianKernel n y =
        -(newtonianKernel n y*Real.smoothTransition (2-‖y‖/eps)) := by
      simp only [truncatedNewtonianKernel]; ring
    rw [he, abs_neg, abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  · rw [Set.indicator_of_notMem hy]
    have hge : 2*eps ≤ ‖y‖ := not_lt.mp (by simpa only [mem_ball, dist_zero_right] using hy)
    rw [truncatedNewtonianKernel_eq_of_far heps y hge, sub_self, abs_zero]

/-- Global L¹ control of the scalar truncation error: integrable, with `∫|Γ_ε − Γ| ≤ newtonianScalarErrorBound n ε`. -/
theorem integrable_truncatedNewtonianKernel_sub {n : ℕ} (hn : 2 ≤ n) {eps : ℝ} (heps : 0 < eps) :
    Integrable (fun y => truncatedNewtonianKernel n eps y - newtonianKernel n y) volume ∧
    (∫ y, |truncatedNewtonianKernel n eps y - newtonianKernel n y|) ≤ newtonianScalarErrorBound n eps := by
  have hR : 0 < 2*eps := by positivity
  obtain ⟨hi, hb⟩ := integrableOn_newtonianKernel_ball hn hR
  have hI : Integrable ((ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)).indicator (fun z => |newtonianKernel n z|)) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hi.abs
  have hm : Measurable (fun y => truncatedNewtonianKernel n eps y - newtonianKernel n y) :=
    (contDiff_truncatedNewtonianKernel hn heps).continuous.measurable.sub (measurable_newtonianKernel hn)
  have hei : Integrable (fun y => truncatedNewtonianKernel n eps y - newtonianKernel n y) volume :=
    hI.mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using abs_truncatedNewtonianKernel_sub_le heps y)
  refine ⟨hei, ?_⟩
  calc
    _ ≤ ∫ y, (ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)).indicator (fun z => |newtonianKernel n z|) y :=
      integral_mono hei.abs hI fun y => abs_truncatedNewtonianKernel_sub_le heps y
    _ = ∫ y in ball (0:EuclideanSpace ℝ (Fin n)) (2*eps), |newtonianKernel n y| :=
      integral_indicator measurableSet_ball
    _ ≤ _ := by
      unfold newtonianScalarErrorBound
      by_cases h2 : n = 2
      · simpa only [h2, if_true] using hb
      · simpa only [h2, if_false] using hb

/-- A continuous model of `ε ↦ newtonianScalarErrorBound n ε` that agrees with it for `ε > 0` and vanishes at `0`. -/
private def scalarModel (n : ℕ) (eps : ℝ) : ℝ :=
  if n = 2 then eps*|(2*eps)*Real.log (2*eps)| + eps^2 else (2*eps)^2/(2*((n:ℝ)-2))

/-- A continuous model of `ε ↦ newtonianDerivErrorBound n ε`, agreeing for `ε > 0` and vanishing at `0`. -/
private def derivModel (n : ℕ) (eps : ℝ) : ℝ :=
  if n = 2 then 4*eps + 2*|(2*eps)*Real.log (2*eps)| else 2*(n:ℝ)*eps/((n:ℝ)-2)

private theorem scalarModel_eq {n : ℕ} {eps : ℝ} (heps : 0 < eps) :
    newtonianScalarErrorBound n eps = scalarModel n eps := by
  unfold newtonianScalarErrorBound scalarModel
  split_ifs
  · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*eps)]; ring
  · rfl

private theorem derivModel_eq {n : ℕ} {eps : ℝ} (heps : 0 < eps) :
    newtonianDerivErrorBound n eps = derivModel n eps := by
  unfold newtonianDerivErrorBound derivModel
  split_ifs
  · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*eps)]; ring
  · rfl

private theorem continuous_scalarModel (n : ℕ) : Continuous (scalarModel n) := by
  unfold scalarModel
  split_ifs
  · exact (continuous_id.mul (Real.continuous_mul_log.comp (continuous_const.mul continuous_id)).abs).add
      (continuous_id.pow 2)
  · fun_prop

private theorem continuous_derivModel (n : ℕ) : Continuous (derivModel n) := by
  unfold derivModel
  split_ifs
  · exact (continuous_const.mul continuous_id).add
      (continuous_const.mul (Real.continuous_mul_log.comp (continuous_const.mul continuous_id)).abs)
  · fun_prop

/-- Along `ε_k = 1/(k+1)`, both truncation error majorants tend to `0`, in every dimension (for `n = 2` through
`t log t → 0`). -/
theorem tendsto_newtonian_error_bounds (n : ℕ) :
    Tendsto (fun k : ℕ => newtonianScalarErrorBound n (1/((k:ℝ)+1))) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => newtonianDerivErrorBound n (1/((k:ℝ)+1))) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos (k : ℕ) : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
  have h0s : scalarModel n 0 = 0 := by unfold scalarModel; split_ifs <;> simp
  have h0d : derivModel n 0 = 0 := by unfold derivModel; split_ifs <;> simp
  constructor
  · have h := ((continuous_scalarModel n).tendsto 0).comp hk
    rw [h0s] at h
    exact h.congr fun k => (scalarModel_eq (hpos k)).symm
  · have h := ((continuous_derivModel n).tendsto 0).comp hk
    rw [h0d] at h
    exact h.congr fun k => (derivModel_eq (hpos k)).symm

/-- A linear functional on Euclidean space is bounded in operator norm by the sum of the absolute values of its
coordinate entries. -/
theorem opNorm_le_sum_abs_basisFun {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (EuclideanSpace.basisFun (Fin n) ℝ i)| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
  intro v
  have hv : v = ∑ i, v i • EuclideanSpace.basisFun (Fin n) ℝ i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    rfl
  have hc (i : Fin n) : |v i| ≤ ‖v‖ := by
    have h := abs_real_inner_le_norm v (EuclideanSpace.basisFun (Fin n) ℝ i)
    rwa [EuclideanSpace.inner_basisFun_real, (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one i,
      mul_one] at h
  have hLv : L v = ∑ i, v i * L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [Real.norm_eq_abs, hLv, Finset.sum_mul]
  calc
    _ ≤ ∑ i, |v i * L (EuclideanSpace.basisFun (Fin n) ℝ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hc i) (abs_nonneg _)

end FunctionalInequalities.Analysis
