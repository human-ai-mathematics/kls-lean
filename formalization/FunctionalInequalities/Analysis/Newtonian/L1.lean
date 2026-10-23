import FunctionalInequalities.Analysis.Newtonian.First
import FunctionalInequalities.Analysis.Newtonian.NearKernel

/-!
# Local integrability of the Newtonian kernel and its gradient

For the kernel `Γ` of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), (2.12), on balls `B_R(0)`, with the explicit constants used in the
proof of Lemma 4.1:

* `integrableOn_fderiv_newtonianKernel_ball` (`n ≥ 2`): each `∂ᵢΓ` is integrable on `B_R(0)` with
  `∫_{B_R} |∂ᵢΓ| ≤ R`;
* `integrableOn_newtonianKernel_ball_of_two_lt` (`n ≥ 3`): `Γ` is integrable on `B_R(0)` with
  `∫_{B_R} |Γ| ≤ R² / (2 (n - 2))`. The planar logarithmic case is in
  `Analysis/Newtonian/LogL1.lean`.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

private theorem volume_ball_growth (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) ≤ ENNReal.ofReal (euclideanUnitBallVolume n*r^(n:ℝ)) := by
  rw [Measure.addHaar_ball_of_pos _ x hr,finrank_euclideanSpace_fin,Real.rpow_natCast]
  change ENNReal.ofReal (r^n)*(volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≤
    ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)).toReal*r^n)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal measure_ball_lt_top.ne,mul_comm]

/-- Actual first kernel derivative is locally L1, with the exact radius bound
used in the radial-cutoff proof of GT2001 Lemma 4.1. -/
theorem integrableOn_fderiv_newtonianKernel_ball {n : ℕ} (hn : 2 ≤ n) {R : ℝ} (hR : 0 < R) (i : Fin n) :
    IntegrableOn (fun y => fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)) (ball 0 R) volume ∧
    (∫ y in ball 0 R, |fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)|) ≤ R := by
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => fderiv ℝ (newtonianKernel n) y
    (EuclideanSpace.basisFun (Fin n) ℝ i)
  let c := 1/((n:ℝ)*euclideanUnitBallVolume n)
  have hw := euclideanUnitBallVolume_pos n
  have hN : 1 < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hc : 0 ≤ c := by dsimp [c];positivity
  have hp : Measurable (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (‖y‖^((1:ℝ)-n))) :=
    (continuous_id.norm.measurable.pow_const ((1:ℝ)-n)).ennreal_ofReal
  have hg : Measurable g := measurable_fderiv_newtonianKernel_apply hn _
  have hnear : (∫⁻ y in ball (0:EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal (‖y‖^((1:ℝ)-n))) ≤
      ENNReal.ofReal (euclideanUnitBallVolume n*(n:ℝ)*R) := by
    simpa only [sub_zero,div_one,Real.rpow_one] using
      near_rpow_integral_le_of_ball_growth volume (0:EuclideanSpace ℝ (Fin n)) hw.le hR zero_lt_one hN
        (volume_ball_growth n 0)
  have hbound : (∫⁻ y in ball (0:EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal |g y|) ≤ ENNReal.ofReal R := by
    calc
      _ ≤ ∫⁻ y in ball (0:EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal (c*‖y‖^((1:ℝ)-n)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae ((volume : Measure (EuclideanSpace ℝ (Fin n))).ae_ne 0)] with y hy
        exact ENNReal.ofReal_le_ofReal (abs_fderiv_newtonianKernel_basis_le hn y hy i)
      _ = ENNReal.ofReal c*(∫⁻ y in ball (0:EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal (‖y‖^((1:ℝ)-n))) := by
        simp_rw [ENNReal.ofReal_mul hc]
        exact lintegral_const_mul _ hp
      _ ≤ ENNReal.ofReal c*ENNReal.ofReal (euclideanUnitBallVolume n*(n:ℝ)*R) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul hc]
        congr 1
        dsimp [c]
        field_simp [hw.ne',(by linarith : (n:ℝ) ≠ 0)]
  have hfinite : HasFiniteIntegral g (volume.restrict (ball 0 R)) := by
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hi : Integrable g (volume.restrict (ball 0 R)) := ⟨hg.aestronglyMeasurable,hfinite⟩
  refine ⟨hi,?_⟩
  have he := integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable
  simp only [Real.norm_eq_abs,Real.enorm_eq_ofReal_abs] at he
  rw [he]
  simpa only [ENNReal.toReal_ofReal hR.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

/-- Exact scalar kernel L1 bound in dimensions n>2, used by GT2001 Lemma 4.1. -/
theorem integrableOn_newtonianKernel_ball_of_two_lt {n : ℕ} (hn : 3 ≤ n) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (newtonianKernel n) (ball 0 R) volume ∧
    (∫ y in ball 0 R, |newtonianKernel n y|) ≤ R^2/(2*((n:ℝ)-2)) := by
  let c := 1/((n:ℝ)*((n:ℝ)-2)*euclideanUnitBallVolume n)
  have hw := euclideanUnitBallVolume_pos n
  have hN : (2:ℝ) < n := by exact_mod_cast (by omega : 2 < n)
  have hc : 0 ≤ c := by dsimp [c];positivity
  have hp : Measurable (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (‖y‖^((2:ℝ)-n))) :=
    (continuous_id.norm.measurable.pow_const ((2:ℝ)-n)).ennreal_ofReal
  have hnear : (∫⁻ y in ball (0:EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal (‖y‖^((2:ℝ)-n))) ≤
      ENNReal.ofReal (euclideanUnitBallVolume n*(n:ℝ)/2*R^2) := by
    simpa only [sub_zero,Real.rpow_two] using near_rpow_integral_le_of_ball_growth volume
      (0:EuclideanSpace ℝ (Fin n)) hw.le hR (by norm_num : 0 < (2:ℝ)) hN (volume_ball_growth n 0)
  have hbound : (∫⁻ y in ball (0:EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal |newtonianKernel n y|) ≤
      ENNReal.ofReal (R^2/(2*((n:ℝ)-2))) := by
    simp_rw [abs_newtonianKernel_of_two_lt hn]
    change (∫⁻ y in ball (0:EuclideanSpace ℝ (Fin n)) R, ENNReal.ofReal (c*‖y‖^((2:ℝ)-n))) ≤ _
    simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul _ hp]
    calc
      _ ≤ ENNReal.ofReal c*ENNReal.ofReal (euclideanUnitBallVolume n*(n:ℝ)/2*R^2) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul hc]
        congr 1
        dsimp [c]
        field_simp [hw.ne',(by linarith : (n:ℝ) ≠ 0),(by linarith : (n:ℝ)-2 ≠ 0)]
  have hfinite : HasFiniteIntegral (newtonianKernel n) (volume.restrict (ball 0 R)) := by
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hi : Integrable (newtonianKernel n) (volume.restrict (ball 0 R)) :=
    ⟨(measurable_newtonianKernel (by omega : 2 ≤ n)).aestronglyMeasurable,hfinite⟩
  refine ⟨hi,?_⟩
  have he := integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable
  simp only [Real.norm_eq_abs,Real.enorm_eq_ofReal_abs] at he
  rw [he]
  have hC : 0 ≤ R^2/(2*((n:ℝ)-2)) := by positivity
  simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

end FunctionalInequalities.Analysis
