import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Evaluation, functional expansions and norm bounds in Euclidean coordinates

Ordinary finite coordinate producers used by derivative/flat-support and
elliptic-drift consumers. Empty finite indices are included. The target of
a continuous linear map can be any real normed space, without completeness.
-/
noncomputable section
namespace FunctionalInequalities.Analysis

/-- A continuous linear map is evaluated by its actual standard coordinates. -/
theorem clm_apply_eq_sum_single {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ ι →L[ℝ] F) (v : EuclideanSpace ℝ ι) :
    L v = ∑ i, v i • L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]

/-- Component bounds generate a Euclidean norm bound, also for an empty index. -/
theorem norm_le_card_mul_of_coord_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℝ ι) (M : ℝ) (h : ∀ i, |v i| ≤ M) :
    ‖v‖ ≤ (Fintype.card ι : ℝ) * M := by
  have hv := (EuclideanSpace.basisFun ι ℝ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hv
  calc
    ‖v‖ = ‖∑ i, v i • EuclideanSpace.single i (1 : ℝ)‖ := congrArg norm hv.symm
    _ ≤ ∑ i, ‖v i • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
    _ = ∑ i, |v i| := by simp only [norm_smul, PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one]
    _ ≤ ∑ _i : ι, M := Finset.sum_le_sum (fun i _ => h i)
    _ = (Fintype.card ι : ℝ) * M := by simp

/-- Every functional on `ℝⁿ` is `Σ_i L(e_i) e_i^*`. -/
theorem eq_sum_apply_basisFun_smul_proj {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    L = ∑ i : Fin n, L (EuclideanSpace.basisFun (Fin n) ℝ i) • EuclideanSpace.proj i := by
  ext v
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_repr, mul_comm]

/-- A real bilinear map on `ℝⁿ` is bounded by the sum of its basis entries. -/
theorem norm_le_sum_abs_apply_basisFun_apply {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖B‖ ≤ ∑ j : Fin n, ∑ i : Fin n,
      |B (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i)| := by
  simp only [EuclideanSpace.basisFun_apply]
  refine ContinuousLinearMap.opNorm_le_bound₂ B
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) fun h k => ?_
  rw [clm_apply_eq_sum_single B h, sum_apply, Real.norm_eq_abs]
  simp only [smul_apply, smul_eq_mul]
  calc |∑ i, h i * B (EuclideanSpace.single i 1) k|
      ≤ ∑ i, |h i * B (EuclideanSpace.single i 1) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖h‖ * (∑ j, |B (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)| * ‖k‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        refine mul_le_mul (by simpa using PiLp.norm_apply_le h i) ?_ (abs_nonneg _) (norm_nonneg _)
        rw [clm_apply_eq_sum_single (B (EuclideanSpace.single i 1)) k]
        simp only [smul_eq_mul]
        calc |∑ j, k j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)|
            ≤ ∑ j, |k j * B (EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, |B (EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1)| * ‖k‖ := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le k j) (abs_nonneg _)
    _ = (∑ i, ∑ j, |B (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)|) * ‖h‖ * ‖k‖ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end FunctionalInequalities.Analysis
