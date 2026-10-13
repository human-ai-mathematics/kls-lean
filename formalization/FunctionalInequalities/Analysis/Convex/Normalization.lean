import Mathlib

/-!
# Affine normalisation of convex bodies

Maximal-volume simplices in a convex body and the elementary geometry of the standard simplex, used for the
affine normalisation step of Caffarelli's strict convexity argument (weak Letwin route, block T11d).

* `simplexEdgeMatrix`, `exists_max_simplexEdgeMatrix_det` (task L-T11d1);
* `abs_simplexCoord_le_one_of_max` (task L-T11d2);
* `closedBall_subset_stdSimplex_and_box_subset_closedBall` (task L-T11d3).
-/

noncomputable section

open Set Matrix

namespace FunctionalInequalities.Analysis

/-- The edge matrix of a simplex with vertices `v 0, …, v n` in `ℝⁿ`: column `j` is `v (j+1) − v 0`. -/
def simplexEdgeMatrix {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (v j.succ - v 0) i

private def simplexVolume {n : ℕ} :
    (Fin (n + 1) → EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun v => |(simplexEdgeMatrix v).det|

/-- **A compact convex body contains a simplex of maximal volume with positive volume** (weak Letwin
route, Caffarelli block T11d, affine normalisation, step 1). -/
theorem exists_max_simplexEdgeMatrix_det {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hint : (interior K).Nonempty) :
    ∃ v : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, v i ∈ K) ∧
      0 < |(simplexEdgeMatrix v).det| ∧
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
        |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det| := by
  have hcoord :
      ∀ i : Fin n, Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    intro i
    exact PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i
  have hmatrix :
      Continuous
        (fun v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) =>
          simplexEdgeMatrix v) := by
    apply continuous_matrix
    intro i j
    change Continuous
      (fun v : Fin (n + 1) → EuclideanSpace ℝ (Fin n) => (v j.succ - v 0) i)
    exact (hcoord i).comp ((continuous_apply j.succ).sub (continuous_apply 0))
  have hvolume : Continuous (@simplexVolume n) := by
    unfold simplexVolume
    exact continuous_abs.comp hmatrix.matrix_det
  let S : Set (Fin (n + 1) → EuclideanSpace ℝ (Fin n)) :=
    (Set.univ : Set (Fin (n + 1))).pi (fun _ => K)
  have hScompact : IsCompact S :=
    isCompact_univ_pi (fun _ => hK)
  obtain ⟨x₀, hx₀⟩ := hint
  have hx₀nhds : K ∈ nhds x₀ :=
    mem_interior_iff_mem_nhds.mp hx₀
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hx₀nhds
  have hhalf : 0 < δ / 2 :=
    div_pos hδ (by norm_num)
  have hSnonempty : S.Nonempty := by
    refine ⟨fun _ => x₀, ?_⟩
    exact Set.mem_univ_pi.mpr (fun _ => interior_subset hx₀)
  obtain ⟨v, hvS, hvmax⟩ :=
    hScompact.exists_isMaxOn hSnonempty hvolume.continuousOn
  have hmax :
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), w ∈ S →
        simplexVolume w ≤ simplexVolume v := by
    intro w hw
    have hev :
        ∀ᶠ z : Fin (n + 1) → EuclideanSpace ℝ (Fin n)
          in Filter.principal S, simplexVolume z ≤ simplexVolume v :=
      hvmax
    exact (Filter.mem_principal.mp (Filter.eventually_iff.mp hev)) hw
  let w : Fin (n + 1) → EuclideanSpace ℝ (Fin n) :=
    Fin.cases x₀
      (fun j => x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ))
  have hwS : w ∈ S := by
    apply Set.mem_univ_pi.mpr
    intro i
    refine Fin.cases ?_ ?_ i
    · change x₀ ∈ K
      exact interior_subset hx₀
    · intro j
      change x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ) ∈ K
      apply hball
      rw [Metric.mem_ball]
      calc
        dist (x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ)) x₀ =
            ‖(x₀ + (δ / 2) • EuclideanSpace.single j (1 : ℝ)) - x₀‖ :=
          dist_eq_norm _ _
        _ = ‖(δ / 2) • EuclideanSpace.single j (1 : ℝ)‖ := by
          rw [add_sub_cancel_left]
        _ = ‖δ / 2‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := by
          exact norm_smul (δ / 2) (EuclideanSpace.single j (1 : ℝ))
        _ = δ / 2 := by
          rw [PiLp.norm_single 2 (fun _ : Fin n => ℝ) j (1 : ℝ),
            Real.norm_eq_abs, abs_of_pos hhalf, norm_one, mul_one]
        _ < δ := half_lt_self hδ
  have hmatrix_w :
      simplexEdgeMatrix w =
        (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [simplexEdgeMatrix, w, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hdet_w :
      (simplexEdgeMatrix w).det = (δ / 2) ^ n := by
    rw [hmatrix_w, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hpos_w : 0 < simplexVolume w := by
    unfold simplexVolume
    rw [hdet_w, abs_of_pos (pow_pos hhalf n)]
    exact pow_pos hhalf n
  have hpos_v : 0 < simplexVolume v :=
    lt_of_lt_of_le hpos_w (hmax w hwS)
  have hvK : ∀ i, v i ∈ K :=
    Set.mem_univ_pi.mp hvS
  refine ⟨v, hvK, ?_, ?_⟩
  · exact hpos_v
  · intro u hu
    exact hmax u (Set.mem_univ_pi.mpr hu)

end FunctionalInequalities.Analysis

section LT11D2MaxSimplexBox

open Set Matrix

/-! Coordinates relative to a maximal simplex are bounded (task L-T11d2). -/

namespace FunctionalInequalities.Analysis

private lemma simplexEdgeMatrix_update_succ
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin n)) :
    simplexEdgeMatrix (Function.update v j.succ y) =
      (simplexEdgeMatrix v).updateCol j
        ((y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) := by
  ext i k
  by_cases h : k = j
  · subst k
    have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
      (Fin.succ_ne_zero j).symm
    simp [simplexEdgeMatrix, Matrix.updateCol, Function.update, hzero]
  · have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
      (Fin.succ_ne_zero j).symm
    simp [simplexEdgeMatrix, Matrix.updateCol, Function.update, h, hzero]

private lemma simplexEdgeMatrix_update_zero
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) :
    simplexEdgeMatrix (Function.update v 0 y) =
      simplexEdgeMatrix v -
        Matrix.of fun i _ => (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp i := by
  ext i j
  simp [simplexEdgeMatrix, Matrix.sub_apply, Function.update, Fin.succ_ne_zero]

private lemma simplexEdgeMatrix_update_succ_det
    {n : ℕ} (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin n))
    (c : Fin n → ℝ)
    (hc :
      (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp =
        fun i => ∑ k, c k • (simplexEdgeMatrix v) i k) :
    (simplexEdgeMatrix (Function.update v j.succ y)).det =
      c j * (simplexEdgeMatrix v).det := by
  rw [simplexEdgeMatrix_update_succ]
  rw [hc]
  simpa [smul_eq_mul] using
    Matrix.det_updateCol_sum (simplexEdgeMatrix v) j c

/-- **Maximality of the simplex confines the body to a box in simplex coordinates** (weak Letwin
route, Caffarelli block T11d, step 2): if `v` is a nondegenerate simplex of maximal volume in `K`,
then every `y ∈ K` has simplex coordinates `c = (M v)⁻¹ (y − v 0)` with `|cⱼ| ≤ 1` and
`|1 − ∑ cⱼ| ≤ 1`. -/
theorem abs_simplexCoord_le_one_of_max {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, v i ∈ K)
    (hdet : (simplexEdgeMatrix v).det ≠ 0)
    (hmax : ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
      |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det|)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ K) :
    (∀ j, |((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1) ∧
      |1 - ∑ j, ((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) ℝ := simplexEdgeMatrix v
  let u : Fin n → ℝ := (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp
  let c : Fin n → ℝ := M⁻¹ *ᵥ u
  have hunit : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  have hMu : M *ᵥ c = u := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv M hunit]
    simp
  have hc :
      u = fun i => ∑ k, c k * M i k := by
    funext i
    calc
      u i = (M *ᵥ c) i := (congrFun hMu i).symm
      _ = ∑ k, M i k * c k := by
        simp only [Matrix.mulVec, dotProduct]
      _ = ∑ k, c k * M i k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [mul_comm]
  have hcoord : ∀ j, |c j| ≤ 1 := by
    intro j
    let w := Function.update v j.succ y
    have hw : ∀ i, w i ∈ K := by
      intro i
      by_cases h : i = j.succ
      · subst i
        simpa [w] using hy
      · have hi : w i = v i := by
          simp [w, h]
        rw [hi]
        exact hv i
    have hdetw : |(simplexEdgeMatrix w).det| ≤ |M.det| := by
      simpa [w, M] using hmax w hw
    have hformula : (simplexEdgeMatrix w).det = c j * M.det := by
      change
        (simplexEdgeMatrix (Function.update v j.succ y)).det =
          c j * M.det
      apply simplexEdgeMatrix_update_succ_det v j y c
      simpa [M, u] using hc
    rw [hformula] at hdetw
    have hmul : |c j| * |M.det| ≤ |M.det| := by
      simpa [abs_mul] using hdetw
    have hpos : 0 < |M.det| := abs_pos.mpr (by simpa [M] using hdet)
    nlinarith
  have hsum : |1 - ∑ j, c j| ≤ 1 := by
    let w := Function.update v 0 y
    have hw : ∀ i, w i ∈ K := by
      intro i
      by_cases h : i = 0
      · subst i
        simpa [w] using hy
      · have hi : w i = v i := by
          simp [w, h]
        rw [hi]
        exact hv i
    have hdetw : |(simplexEdgeMatrix w).det| ≤ |M.det| := by
      simpa [w, M] using hmax w hw
    have hc_coord : ∀ z, c z = ∑ x, (M⁻¹) z x * u x := by
      intro z
      simp [c, Matrix.mulVec, dotProduct]
    have hsum' :
        (∑ x, (∑ z, (M⁻¹) z x) * u x) = ∑ z, c z := by
      calc
        (∑ x, (∑ z, (M⁻¹) z x) * u x) =
            ∑ x, ∑ z, (M⁻¹) z x * u x := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_mul]
        _ = ∑ z, ∑ x, (M⁻¹) z x * u x := by
              rw [Finset.sum_comm]
        _ = ∑ z, c z := by
              apply Finset.sum_congr rfl
              intro z hz
              exact (hc_coord z).symm
    have hsecond :
        (simplexEdgeMatrix w).det = M.det * (1 - ∑ j, c j) := by
      change
        (simplexEdgeMatrix (Function.update v 0 y)).det =
          M.det * (1 - ∑ j, c j)
      rw [simplexEdgeMatrix_update_zero]
      let U : Matrix (Fin n) (Fin 1) ℝ := Matrix.of fun i _ => -u i
      let V : Matrix (Fin 1) (Fin n) ℝ := Matrix.of fun _ _ => 1
      have hUV :
          M - Matrix.of (fun i _ => u i) = M + U * V := by
        ext i j
        simp [U, V, Matrix.mul_apply]
        ring
      rw [hUV]
      rw [Matrix.det_add_mul U V hunit]
      have hscalar :
          (V * M⁻¹ * U).det = -∑ j, c j := by
        rw [Matrix.det_fin_one]
        simp only [Matrix.mul_apply, V, U, Matrix.of_apply, one_mul, mul_neg,
          Finset.sum_neg_distrib]
        rw [hsum']
      have hplus :
          (1 + V * M⁻¹ * U).det = 1 - ∑ j, c j := by
        rw [Matrix.det_fin_one]
        rw [Matrix.add_apply]
        have hentry :
            (V * M⁻¹ * U) 0 0 = -∑ j, c j := by
          simpa only [Matrix.det_fin_one] using hscalar
        rw [hentry]
        simp [sub_eq_add_neg]
      rw [hplus]
    rw [hsecond] at hdetw
    have hmul : |M.det| * |1 - ∑ j, c j| ≤ |M.det| := by
      simpa [abs_mul, mul_comm] using hdetw
    have hpos : 0 < |M.det| := abs_pos.mpr (by simpa [M] using hdet)
    nlinarith
  simpa [M, c, u] using ⟨hcoord, hsum⟩

end FunctionalInequalities.Analysis

end LT11D2MaxSimplexBox

section LT11D3SimplexBall

open Set Metric

/-! A ball inside the standard simplex and the box inside a ball (task L-T11d3). -/

namespace FunctionalInequalities.Analysis

private lemma sum_abs_sub_le_sqrt_mul_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, |x i| ≤ Real.sqrt n * ‖x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => |x i|) (fun _ => (1 : ℝ))
  have hcs' : (∑ i, |x i|) ^ 2 ≤ (∑ i, x i ^ 2) * (n : ℝ) := by
    simpa only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul] using hcs
  have hnorm : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    calc
      ‖x‖ ^ 2 = (Real.sqrt (∑ i, ‖x i‖ ^ 2)) ^ 2 := by
        rw [EuclideanSpace.norm_eq]
      _ = ∑ i, ‖x i‖ ^ 2 := by
        rw [Real.sq_sqrt]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg (‖x i‖))
      _ = ∑ i, x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.norm_eq_abs, sq_abs]
  have hsq : (∑ i, |x i|) ^ 2 ≤ (Real.sqrt n * ‖x‖) ^ 2 := by
    calc
      (∑ i, |x i|) ^ 2 ≤ (∑ i, x i ^ 2) * (n : ℝ) := hcs'
      _ = ‖x‖ ^ 2 * (n : ℝ) := by rw [← hnorm]
      _ = (Real.sqrt n * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        ring
  exact
    (sq_le_sq₀
      (Finset.sum_nonneg (fun i _ => abs_nonneg (x i)))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq

private lemma barycentre_ofLp_apply {n : ℕ} (i : Fin n) :
    (((1 / ((n : ℝ) + 1)) • ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i)
      = 1 / ((n : ℝ) + 1) := by
  simp [Finset.sum_apply]

/-- **The standard simplex contains a ball around its barycentre, and the coordinate box lies in a
ball** (weak Letwin route, Caffarelli block T11d, step 3). -/
theorem closedBall_subset_stdSimplex_and_box_subset_closedBall {n : ℕ} (hn : 0 < n) :
    closedBall ((1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ))
        (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) ⊆
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} ∧
    {y : EuclideanSpace ℝ (Fin n) | (∀ i, |y i| ≤ 1) ∧ |1 - ∑ i, y i| ≤ 1} ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) := by
  constructor
  · intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    constructor
    · intro i
      have hi :
          |y i - 1 / ((n : ℝ) + 1)| ≤
            ‖y - ((1 / ((n : ℝ) + 1)) •
              ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        have hi' := PiLp.norm_apply_le
          (y - ((1 / ((n : ℝ) + 1)) •
            ∑ j, EuclideanSpace.single j (1 : ℝ))) i
        rw [Real.norm_eq_abs] at hi'
        have hcoord :
            (y - ((1 / ((n : ℝ) + 1)) •
              ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i =
              y.ofLp i - 1 / ((n : ℝ) + 1) := by
          change y.ofLp i -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i =
              y.ofLp i - 1 / ((n : ℝ) + 1)
          rw [barycentre_ofLp_apply]
        rw [hcoord] at hi'
        exact hi'
      have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
      have hdenpos : 0 < 2 * ((n : ℝ) + 1) := by
        positivity
      have hdenle :
          2 * ((n : ℝ) + 1) ≤
            2 * ((n : ℝ) + 1) * Real.sqrt n := by
        have hnonneg : 0 ≤ 2 * ((n : ℝ) + 1) := by
          positivity
        have hdiff : 0 ≤ Real.sqrt n - 1 := sub_nonneg.mpr hsqrt
        nlinarith [mul_nonneg hnonneg hdiff]
      have hρ :
          1 / (2 * ((n : ℝ) + 1) * Real.sqrt n) ≤
            1 / (2 * ((n : ℝ) + 1)) :=
        one_div_le_one_div_of_le hdenpos hdenle
      have hiρ :
          |y i - 1 / ((n : ℝ) + 1)| ≤
            1 / (2 * ((n : ℝ) + 1)) :=
        le_trans (le_trans hi hy) hρ
      have hlow :
          1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) ≤ y i := by
        have h := (abs_le.mp hiρ).1
        linarith
      have hnonneg :
          0 ≤ 1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) := by
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have heq :
            1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) =
              1 / (2 * ((n : ℝ) + 1)) := by
          field_simp [ne_of_gt hn1]
          ring
        rw [heq]
        positivity
      exact le_trans hnonneg hlow
    · have hsumabs :
          ∑ i, |y i - 1 / ((n : ℝ) + 1)| ≤
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        calc
          ∑ i, |y i - 1 / ((n : ℝ) + 1)| =
              ∑ i, |(y -
                ((1 / ((n : ℝ) + 1)) •
                  ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i| := by
                apply Finset.sum_congr rfl
                intro i hi
                have hcoord :
                    (y - ((1 / ((n : ℝ) + 1)) •
                      ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i =
                      y.ofLp i - 1 / ((n : ℝ) + 1) := by
                  change y.ofLp i -
                      ((1 / ((n : ℝ) + 1)) •
                        ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i =
                      y.ofLp i - 1 / ((n : ℝ) + 1)
                  rw [barycentre_ofLp_apply]
                rw [hcoord]
          _ ≤ Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ :=
            sum_abs_sub_le_sqrt_mul_norm _
      have hsum :
          ∑ i, y i ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        calc
          ∑ i, y i ≤
              ∑ i, (1 / ((n : ℝ) + 1) +
                |y i - 1 / ((n : ℝ) + 1)|) := by
            apply Finset.sum_le_sum
            intro i hi
            linarith [le_abs_self (y i - 1 / ((n : ℝ) + 1))]
          _ = ∑ i, (1 / ((n : ℝ) + 1)) +
              ∑ i, |y i - 1 / ((n : ℝ) + 1)| := by
            rw [Finset.sum_add_distrib]
          _ = n / ((n : ℝ) + 1) +
              ∑ i, |y i - 1 / ((n : ℝ) + 1)| := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            ring
          _ ≤ n / ((n : ℝ) + 1) +
              Real.sqrt n * ‖y -
                ((1 / ((n : ℝ) + 1)) •
                  ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
            simpa [add_comm] using
              add_le_add_left hsumabs (n / ((n : ℝ) + 1))
      calc
        ∑ i, y i ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := hsum
        _ ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n *
              (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) := by
          gcongr
        _ = n / ((n : ℝ) + 1) +
            1 / (2 * ((n : ℝ) + 1)) := by
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
          field_simp [ne_of_gt hsqrtpos]
        _ ≤ 1 := by
          have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          field_simp [ne_of_gt hn1]
          nlinarith
  · intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero]
    have hsq : ‖y‖ ^ 2 ≤ (n : ℝ) := by
      calc
        ‖y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
          exact Finset.sum_nonneg (fun i _ => sq_nonneg (‖y i‖))
        _ ≤ ∑ i, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Real.norm_eq_abs, sq_abs]
          exact (sq_le_one_iff_abs_le_one (y i)).mpr (hy.1 i)
        _ = (n : ℝ) := by
          simp
    have hnorm : 0 ≤ ‖y‖ := norm_nonneg _
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    exact (sq_le_sq₀ hnorm hsqrt).mp (by
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      exact hsq)

end FunctionalInequalities.Analysis

end LT11D3SimplexBall
