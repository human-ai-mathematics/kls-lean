import FunctionalInequalities.Analysis.Newtonian.AbsLogNear
import FunctionalInequalities.Analysis.Newtonian.L1

/-!
# Local integrability of the planar Newtonian kernel

For `n = 2` and the kernel `Γ = (2π)⁻¹ log ‖·‖` of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12):

* `integrableOn_newtonianKernel_two_ball`: `Γ` is integrable on `B_R(0)` for every `R > 0`, with
  `∫_{B_R} |Γ| ≤ R²/2 (|log R| + 1/2)`;
* `newtonian_cutoff_majorant_two_integrable_integral_le`: the planar cutoff majorant
  `|∂ᵢΓ| + (2 / eps) |Γ|` of the proof of Lemma 4.1 (p. 54) is integrable on `B_{2 eps}(0)` with integral
  at most `4 eps (1 + |log (2 eps)|)`.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

/-- Planar Gamma is locally L1 with its source normalization, including
its finite chosen value at zero. The bound holds for every R>0. -/
theorem integrableOn_newtonianKernel_two_ball {R : ℝ} (hR : 0 < R) :
    IntegrableOn (newtonianKernel 2) (ball 0 R) volume ∧
    (∫ y in ball 0 R, |newtonianKernel 2 y|) ≤ R^2/2*(|Real.log R|+1/2) := by
  have hgrowth : ∀ r : ℝ, 0 < r → (volume : Measure (EuclideanSpace ℝ (Fin 2))) (ball 0 r) ≤
      ENNReal.ofReal (Real.pi*r^(2:ℝ)) := by
    intro r hr
    rw [EuclideanSpace.volume_ball_fin_two,Real.rpow_two,
      ENNReal.ofReal_mul Real.pi_pos.le,ENNReal.ofReal_pow hr.le,mul_comm]
  have h := integrableOn_log_norm_sub_ball_of_ball_growth volume
    (0:EuclideanSpace ℝ (Fin 2)) Real.pi_pos.le hR (by norm_num : 0 < (2:ℝ)) hgrowth
  simp only [sub_zero,Real.rpow_two] at h
  obtain ⟨hi,hb⟩ := h
  have hc : 0 ≤ 1/(2*Real.pi) := by positivity
  have hki : IntegrableOn (newtonianKernel 2) (ball 0 R) volume := by
    change Integrable (fun y => (1/(2*Real.pi))*Real.log ‖y‖) (volume.restrict (ball 0 R))
    exact hi.const_mul (1/(2*Real.pi))
  refine ⟨hki,?_⟩
  change (∫ y in ball (0:EuclideanSpace ℝ (Fin 2)) R, |(1/(2*Real.pi))*Real.log ‖y‖|) ≤ _
  simp_rw [abs_mul,abs_of_nonneg hc]
  rw [integral_const_mul]
  calc
    _ ≤ (1/(2*Real.pi))*(Real.pi*R^2*(|Real.log R|+1/2)) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = _ := by field_simp [Real.pi_ne_zero]

/-- Exact planar cutoff-majorant factor of GT2001 Lemma 4.1, p. 54.
This does not assert the actual cutoff derivative or potential regularity. -/
theorem newtonian_cutoff_majorant_two_integrable_integral_le
    {eps : ℝ} (heps : 0 < eps) (i : Fin 2) :
    IntegrableOn (fun y => |fderiv ℝ (newtonianKernel 2) y (EuclideanSpace.basisFun (Fin 2) ℝ i)| +
      (2/eps)*|newtonianKernel 2 y|) (ball 0 (2*eps)) volume ∧
    (∫ y in ball 0 (2*eps), |fderiv ℝ (newtonianKernel 2) y (EuclideanSpace.basisFun (Fin 2) ℝ i)| +
      (2/eps)*|newtonianKernel 2 y|) ≤ 4*eps*(1+|Real.log (2*eps)|) := by
  have hR : 0 < 2*eps := by positivity
  obtain ⟨hd,hdb⟩ := integrableOn_fderiv_newtonianKernel_ball (by norm_num : 2 ≤ 2) hR i
  obtain ⟨hk,hkb⟩ := integrableOn_newtonianKernel_two_ball hR
  have hc : 0 ≤ 2/eps := by positivity
  refine ⟨hd.abs.add (hk.abs.const_mul (2/eps)),?_⟩
  rw [integral_add hd.abs (hk.abs.const_mul (2/eps)),integral_const_mul]
  calc
    _ ≤ 2*eps+(2/eps)*((2*eps)^2/2*(|Real.log (2*eps)|+1/2)) :=
      add_le_add hdb (mul_le_mul_of_nonneg_left hkb hc)
    _ = _ := by
      field_simp [heps.ne']
      ring

end FunctionalInequalities.Analysis
