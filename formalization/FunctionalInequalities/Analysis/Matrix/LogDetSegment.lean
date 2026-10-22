import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The log-determinant along a matrix segment

For real square matrices `A` and `B` with a nonsingular segment `A + t(B − A)`, `t ∈ [0, 1]`, the fundamental theorem of calculus
with Jacobi's formula gives `log det B − log det A = ∫₀¹ tr((A + t(B − A))⁻¹ (B − A)) dt`, and expanding the trace gives the averaged
inverse coefficients `∑ᵢ ∑ⱼ (∫₀¹ (A + t(B − A))⁻¹ᵢⱼ dt) (B − A)ⱼᵢ` of Gilbarg–Trudinger (2001), (17.56). For positive definite endpoints
the nonsingularity of the segment is derived. The integrability of every coefficient is derived from continuity of the inverse.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

section SegmentIntegral

open MeasureTheory Set
open scoped Topology Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Log-determinant along a segment.** If `det (A + t(B − A)) ≠ 0` for every `t ∈ [0, 1]`, then
`log det B − log det A = ∫₀¹ tr((A + t(B − A))⁻¹ (B − A)) dt` (fundamental theorem of calculus with Jacobi's formula; the
integrand is continuous, hence interval integrable). `Real.log` is `log |·|`, and the determinant keeps one sign along the
segment. -/
theorem log_det_sub_eq_integral_trace (A B : Matrix ι ι ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, (A + t • (B - A)).det ≠ 0) :
    Real.log B.det - Real.log A.det =
      ∫ t in (0 : ℝ)..1,
        Matrix.trace ((A + t • (B - A))⁻¹ * (B - A)) := by
  have hp (t : ℝ) : HasDerivAt (fun s : ℝ => A + s • (B - A)) (B - A) t := by
    exact HasDerivAt.const_add A (by
      simpa only [one_smul, id_eq] using (hasDerivAt_id t).smul_const (B - A))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => Real.log (A + s • (B - A)).det)
        (Matrix.trace ((A + t • (B - A))⁻¹ * (B - A))) t := by
    have hh := (FunctionalInequalities.Analysis.differentiableAt_logDet _
        (hdet t ht)).hasFDerivAt.comp_hasDerivAt t (hp t)
    convert hh using 1 <;> first
    | rfl
    | exact (FunctionalInequalities.Analysis.fderiv_logDet_apply
        (A + t • (B - A)) (B - A) (hdet t ht)).symm
  have hc : ContinuousOn
      (fun t : ℝ => Matrix.trace ((A + t • (B - A))⁻¹ * (B - A)))
      (Icc 0 1) := by
    intro t ht
    have hi : ContinuousAt (fun s : ℝ => (A + s • (B - A))⁻¹) t :=
      (continuousAt_matrix_inv (A + t • (B - A)) (by
        simpa only [Ring.inverse_eq_inv'] using
          (continuousAt_inv₀ (hdet t ht)))).comp (f := fun s : ℝ => A + s • (B - A))
        (hp t).continuousAt
    exact ((continuous_id.matrix_trace).continuousAt.comp
      (hi.mul continuousAt_const)).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le zero_le_one] using ht))
    (hc.intervalIntegrable_of_Icc (by norm_num))
  simpa using h.symm

end SegmentIntegral

section PositiveSegment

open MeasureTheory Set
open scoped Topology Matrix.Norms.Elementwise ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Every point `A + t(B − A)`, `t ∈ [0, 1]`, of the segment between positive definite matrices is positive definite. -/
private theorem posDef_segment {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : t ∈ Icc 0 1) :
    (A + t • (B - A)).PosDef := by
  by_cases h0 : t = 0
  · simpa only [h0, zero_smul, add_zero] using hA
  by_cases h1 : t = 1
  · have heq : A + (B - A) = B := by abel
    simpa only [h1, one_smul, heq] using hB
  have heq : A + t • (B - A) = (1 - t) • A + t • B := by module
  rw [heq]
  exact (hA.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))).add
    (hB.smul (lt_of_le_of_ne ht.1 (Ne.symm h0)))

/-- For positive definite `A` and `B`, `log det B − log det A = ∫₀¹ tr((A + t(B − A))⁻¹ (B − A)) dt`; nonsingularity along
the segment is derived, not assumed. -/
theorem log_det_sub_eq_integral_trace_of_posDef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det - Real.log A.det =
      ∫ t in (0 : ℝ)..1,
        Matrix.trace ((A + t • (B - A))⁻¹ * (B - A)) :=
  log_det_sub_eq_integral_trace A B
    (fun _ ht => (posDef_segment hA hB ht).det_pos.ne')

end PositiveSegment

section AveragedInverseCoefficients

open MeasureTheory Set
open scoped Topology Matrix.Norms.Elementwise ComplexOrder BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Averaged inverse coefficients** (Gilbarg–Trudinger (2001), (17.56)). If the segment is nonsingular,
`log det B − log det A = ∑ᵢ ∑ⱼ (∫₀¹ (A + t(B − A))⁻¹ᵢⱼ dt) (B − A)ⱼᵢ`. The interval integrability of every inverse entry is
derived from continuity of the inverse. -/
theorem log_det_sub_eq_sum_averaged_inverse (A B : Matrix ι ι ℝ)
    (hdet : ∀ t ∈ Icc (0 : ℝ) 1, (A + t • (B - A)).det ≠ 0) :
    Real.log B.det - Real.log A.det =
      ∑ i, ∑ j, (∫ t in (0 : ℝ)..1, (A + t • (B - A))⁻¹ i j) * (B - A) j i := by
  have hi (i j : ι) : IntervalIntegrable
      (fun t : ℝ => (A + t • (B - A))⁻¹ i j) volume 0 1 := by
    have hc : ContinuousOn (fun t : ℝ => (A + t • (B - A))⁻¹ i j) (Icc 0 1) := by
      intro t ht
      have hm : ContinuousAt (fun s : ℝ => (A + s • (B - A))⁻¹) t :=
        (continuousAt_matrix_inv (A + t • (B - A)) (by
          simpa only [Ring.inverse_eq_inv'] using
            (continuousAt_inv₀ (hdet t ht)))).comp (f := fun s : ℝ => A + s • (B - A))
          (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      exact (((continuous_apply j).comp (continuous_apply i)).continuousAt.comp
        (f := fun s : ℝ => (A + s • (B - A))⁻¹) hm).continuousWithinAt
    exact hc.intervalIntegrable_of_Icc (by norm_num)
  have hrow (i : ι) : IntervalIntegrable
      (fun t : ℝ => ∑ j, (A+t • (B-A))⁻¹ i j*(B-A) j i) volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ
      (fun j _ => (hi i j).mul_const ((B-A) j i)) using 1 <;> try rfl
    funext t
    simp only [Finset.sum_apply]
  calc
    _ = ∫ t in (0 : ℝ)..1, Matrix.trace ((A+t • (B-A))⁻¹*(B-A)) :=
      log_det_sub_eq_integral_trace A B hdet
    _ = ∫ t in (0 : ℝ)..1, ∑ i, ∑ j, (A+t • (B-A))⁻¹ i j*(B-A) j i := by
      rfl
    _ = ∑ i, ∫ t in (0 : ℝ)..1, ∑ j, (A+t • (B-A))⁻¹ i j*(B-A) j i :=
      intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun i t => ∑ j, (A+t • (B-A))⁻¹ i j*(B-A) j i) (fun i _ => hrow i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun j t => (A+t • (B-A))⁻¹ i j*(B-A) j i)
        (fun j _ => (hi i j).mul_const ((B-A) j i))]
      apply Finset.sum_congr rfl
      intro j _
      exact intervalIntegral.integral_mul_const ((B-A) j i) _

/-- The averaged-inverse identity `log det B − log det A = ∑ᵢ ∑ⱼ (∫₀¹ (A + t(B − A))⁻¹ᵢⱼ dt) (B − A)ⱼᵢ` for positive
definite `A` and `B`; nonsingularity along the segment is derived. -/
theorem log_det_sub_eq_sum_averaged_inverse_of_posDef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det - Real.log A.det =
      ∑ i, ∑ j, (∫ t in (0 : ℝ)..1, (A + t • (B - A))⁻¹ i j) * (B - A) j i := by
  apply log_det_sub_eq_sum_averaged_inverse A B
  intro t ht
  have hp : (A + t • (B-A)).PosDef := by
    by_cases h0 : t = 0
    · simpa only [h0,zero_smul,add_zero] using hA
    by_cases h1 : t = 1
    · have he : A+(B-A) = B := by abel
      simpa only [h1,one_smul,he] using hB
    have he : A+t • (B-A) = (1-t) • A+t • B := by module
    rw [he]
    exact (hA.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))).add
      (hB.smul (lt_of_le_of_ne ht.1 (Ne.symm h0)))
  exact hp.det_pos.ne'

end AveragedInverseCoefficients

end FunctionalInequalities.Analysis
