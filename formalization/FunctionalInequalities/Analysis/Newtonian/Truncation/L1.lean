import FunctionalInequalities.Analysis.Newtonian.Truncation.Derivative
import FunctionalInequalities.Analysis.Newtonian.Truncation.CutoffMajorant
import FunctionalInequalities.Analysis.Newtonian.Kernel.LogL1

/-!
# Global L¹ derivative error of the truncated Newtonian kernel

`exists_newtonian_truncation_derivative_l1_cap`: one constant `B > 0` such that, in every dimension
`n ≥ 2`, for every `eps > 0` and every coordinate `i`, `∂ᵢΓ_eps - ∂ᵢΓ` is integrable on `ℝⁿ` with
`∫ |∂ᵢΓ_eps - ∂ᵢΓ| ≤ (1 + B/2) · (4 eps (1 + |log 2 eps|)` if `n = 2`, `2 n eps / (n - 2)` otherwise`)`.
This is the kernel-level L¹ estimate of the proof of Lemma 4.1 of Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), p. 54; no
derivative is passed through a convolution here.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- Global L1 derivative approximation for the actual truncated normalized
kernel. A single derived smooth-profile cap works before all dimensions,
radii and entries. This does not yet pass derivatives through a convolution. -/
theorem exists_newtonian_truncation_derivative_l1_cap :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ), 2 ≤ n → ∀ eps : ℝ, 0 < eps → ∀ i : Fin n,
      Integrable (fun y => fderiv ℝ (truncatedNewtonianKernel n eps) y (EuclideanSpace.basisFun (Fin n) ℝ i)-
        fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)) volume ∧
      (∫ y, |fderiv ℝ (truncatedNewtonianKernel n eps) y (EuclideanSpace.basisFun (Fin n) ℝ i)-
        fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)|) ≤
        (1+B/2)*(if n=2 then 4*eps*(1+|Real.log (2*eps)|) else 2*(n:ℝ)*eps/((n:ℝ)-2)) := by
  obtain ⟨B,hB,hpoint⟩ := exists_newtonian_truncation_derivative_error_cap
  refine ⟨B,hB,?_⟩
  intro n hn eps heps i
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let e : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    fderiv ℝ (truncatedNewtonianKernel n eps) y (EuclideanSpace.basisFun (Fin n) ℝ i)-
      fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)
  let M : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    |fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)|+
      (2/eps)*|newtonianKernel n y|
  let Q := 1+B/2
  let C := if n=2 then 4*eps*(1+|Real.log (2*eps)|) else 2*(n:ℝ)*eps/((n:ℝ)-2)
  have hR : 0 < 2*eps := by positivity
  have hQ : 0 ≤ Q := by dsimp [Q];positivity
  have hQ1 : 1 ≤ Q := by dsimp [Q];linarith
  have hM : IntegrableOn M (ball 0 (2*eps)) volume ∧ (∫ y in ball 0 (2*eps),M y) ≤ C := by
    by_cases hn2 : n=2
    · subst n
      simpa only [M,C,if_pos rfl] using newtonian_cutoff_majorant_two_integrable_integral_le heps i
    · have hn3 : 3 ≤ n := by omega
      simpa only [M,C,if_neg hn2] using newtonian_cutoff_majorant_integrable_integral_le hn3 heps i
  have hcoef : B/eps ≤ Q*(2/eps) := by
    calc
      _ ≤ (B+2)/eps := div_le_div_of_nonneg_right (by linarith) heps.le
      _ = _ := by dsimp [Q];ring
  have hdom : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      |e y| ≤ Q*((ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)).indicator M y) := by
    have hs : (volume : Measure (EuclideanSpace ℝ (Fin n))) (sphere 0 (2*eps))=0 :=
      Measure.addHaar_sphere_of_ne_zero volume 0 hR.ne'
    filter_upwards [((volume : Measure (EuclideanSpace ℝ (Fin n))).ae_ne 0),
      measure_eq_zero_iff_ae_notMem.mp hs] with y hy0 hys
    by_cases hy : y ∈ ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)
    · rw [Set.indicator_of_mem hy]
      calc
        _ ≤ |fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)|+
            (B/eps)*|newtonianKernel n y| := hpoint n hn eps heps y hy0 i
        _ ≤ Q*|fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)|+
            (Q*(2/eps))*|newtonianKernel n y| :=
          add_le_add (le_mul_of_one_le_left (abs_nonneg _) hQ1)
            (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))
        _ = _ := by dsimp [M];ring
    · have hge : 2*eps ≤ ‖y‖ := not_lt.mp (by simpa only [mem_ball,dist_zero_right] using hy)
      have hne : ‖y‖ ≠ 2*eps := by simpa only [mem_sphere,dist_zero_right] using hys
      have hf := fderiv_truncatedNewtonianKernel_eq_of_far heps y (lt_of_le_of_ne hge (Ne.symm hne))
      simp only [e,hf,sub_self,abs_zero,Set.indicator_of_notMem hy,mul_zero,le_refl]
  have hcont := (contDiff_truncatedNewtonianKernel hn heps).continuous_fderiv (by simp)
  have hm : Measurable e := ((hcont.clm_apply continuous_const).measurable).sub
    (measurable_fderiv_newtonianKernel_apply hn _)
  have hiM : Integrable ((ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)).indicator M) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hM.1
  have himaj := hiM.const_mul Q
  have hei : Integrable e volume := himaj.mono' hm.aestronglyMeasurable (by
    simpa only [Real.norm_eq_abs] using hdom)
  refine ⟨hei,?_⟩
  change (∫ y, |e y|) ≤ Q*C
  calc
    _ ≤ ∫ y, Q*((ball (0:EuclideanSpace ℝ (Fin n)) (2*eps)).indicator M y) :=
      integral_mono_ae hei.abs himaj hdom
    _ = Q*(∫ y in ball (0:EuclideanSpace ℝ (Fin n)) (2*eps),M y) := by
      rw [integral_const_mul,integral_indicator measurableSet_ball]
    _ ≤ _ := mul_le_mul_of_nonneg_left hM.2 hQ

end FunctionalInequalities.Analysis
