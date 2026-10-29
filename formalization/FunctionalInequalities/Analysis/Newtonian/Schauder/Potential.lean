import FunctionalInequalities.Analysis.EuclideanCoordinates
import FunctionalInequalities.Analysis.Newtonian.Schauder.CancelledHessian
import FunctionalInequalities.Analysis.Newtonian.Schauder.BoxCorrection

/-!
# Interior Hölder estimates for the Newtonian potential on balls (GT Lemma 4.4)

Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7), pp. 57–59. For concentric balls `B_R(c) ⊂ B_{2R}(c)`, `n ≥ 2` (including
`n = 2`), `0 < α < 1` and `f` bounded by `M` and `α`-Hölder with cap `H` on `B_{2R}(c)`,
`newtonianPotential_schauder` gives one constant `C(n, α) > 0`, chosen before `c`, `R` and `f`, such
that the Newtonian potential `w` of `f` in `B_{2R}(c)` is `C²` on `B_{2R}(c)` and, on `closedBall c R`,
`‖D²w‖ ≤ C (M + R^α H)`, `‖D²w(x) - D²w(z)‖ ≤ C (M R^(-α) + H) ‖x - z‖^α`, and the source form (4.11)
`|D²w|_{0;B_R} + R^α [D²w]_{α;B_R} ≤ 2C (|f|_{0;B_{2R}} + R^α [f]_{α;B_{2R}})`. The case `α = 1` is not
claimed.

The proof differs from GT's six-integral argument but proves the same estimate: (4.9) on the centred
coordinate box `c ± 3R` gives `D_jD_iw = T_{ij} + f Â_{ij}` on `B_{2R}`
(`iteratedFDeriv_newtonianPotential_ball_eq`), with the cancelled volume term `T` of
`Analysis/Newtonian/Schauder/CancelledHessian.lean` and the box correction `Â` of
`Analysis/Newtonian/Schauder/BoxCorrection.lean`. The constant is coarse and is not the book's intermediate
value.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace NNReal

namespace FunctionalInequalities.Analysis

section Entries

variable {m : ℕ} {c : EuclideanSpace ℝ (Fin (m + 1))} {R M : ℝ} {f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}

/-- The global Hölder input on `B_{2R}` gives the local Hölder input of Lemma 4.2 (`newtonianPotential_lemma_4_2`) at every
point of `B_{2R}`. -/
theorem localHolder_of_holderOnWith_ball {n : ℕ} {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} {g : EuclideanSpace ℝ (Fin n) → ℝ}
    {H α : ℝ≥0} (hg : HolderOnWith H α g (ball c (2 * R))) :
    ∀ x ∈ ball c (2 * R), ∃ r > 0, ∃ H' : ℝ≥0, ball x r ⊆ ball c (2 * R) ∧ HolderOnWith H' α g (ball x r) := by
  intro x hx
  have hr : 0 < 2 * R - dist x c := by rw [mem_ball] at hx; linarith
  have hsub : ball x (2 * R - dist x c) ⊆ ball c (2 * R) := fun y hy => by
    rw [mem_ball] at hy ⊢; linarith [dist_triangle y x c]
  exact ⟨_, hr, H, hsub, hg.mono hsub⟩

/-- Entry decomposition on `B_{2R}` from (4.9) on the centred box: `D_jD_iw(x) = T_{ij}(x) + f(x) Â_{ij}(x)`. -/
theorem iteratedFDeriv_newtonianPotential_ball_eq (hn : 2 ≤ m + 1) (hR : 0 < R) (hfb : ∀ y ∈ ball c (2 * R), |f y| ≤ M)
    {H α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) (hHol : HolderOnWith H α f (ball c (2 * R)))
    {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ∈ ball c (2 * R)) (i j : Fin (m + 1)) :
    iteratedFDeriv ℝ 2 (newtonianPotential (m + 1) (ball c (2 * R)) f) x
        ![EuclideanSpace.basisFun (Fin (m + 1)) ℝ j, EuclideanSpace.basisFun (Fin (m + 1)) ℝ i] =
      newtonianCancelledHessian (m + 1) (ball c (2 * R)) f i j x + f x * newtonianBoxCorrection m c R i j x := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  obtain ⟨-, -, -, h49, -⟩ := newtonianPotential_lemma_4_2 hn isOpen_ball isBounded_ball ⟨M, hfb⟩ hα0 hα1
    (localHolder_of_holderOnWith_ball hHol)
  have hab := newtonianBoxLower_le_upper (c := c) hR
  obtain ⟨hI, -, heq⟩ := h49 _ _ _ _ (divergenceAdmissible_euclideanOpenBox hab) (ball_subset_newtonianBox hR) x hx i j
  set box := euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R)
  set g := fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel (m + 1)) (x - y) (b j) (b i) *
    ((ball c (2 * R)).indicator f y - f x)
  have hs := integral_inter_add_sdiff (s := box) (t := ball c (2 * R)) (f := g) measurableSet_ball hI
  rw [inter_eq_right.mpr (ball_subset_newtonianBox hR)] at hs
  have hVm : MeasurableSet (box \ ball c (2 * R)) :=
    (divergenceAdmissible_euclideanOpenBox hab).isOpen.measurableSet.diff measurableSet_ball
  have hT : (∫ y in ball c (2 * R), g y) = newtonianCancelledHessian (m + 1) (ball c (2 * R)) f i j x := by
    unfold newtonianCancelledHessian
    refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
    simp only [g, Set.indicator_of_mem hy]
    rfl
  have hV : (∫ y in box \ ball c (2 * R), g y) =
      -f x * ∫ y in box \ ball c (2 * R), bilinearIteratedFDerivTwo ℝ (newtonianKernel (m + 1)) (x - y) (b j) (b i) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hVm fun y hy => ?_
    simp only [g, Set.indicator_of_notMem hy.2]; ring
  rw [heq, ← hs, hT, hV, newtonianBoxCorrection]
  ring

theorem newtonianBoxCorrectionSupConst_nonneg (m : ℕ) : 0 ≤ newtonianBoxCorrectionSupConst m := by
  have := euclideanUnitBallVolume_pos (m + 1); unfold newtonianBoxCorrectionSupConst; positivity

theorem newtonianBoxCorrectionLipConst_nonneg (m : ℕ) : 0 ≤ newtonianBoxCorrectionLipConst m := by
  have := euclideanUnitBallVolume_pos (m + 1); unfold newtonianBoxCorrectionLipConst; positivity

/-- `δ/R ≤ 2 R^{−α} δ^α` for `0 ≤ δ ≤ 2R`, `0 < α ≤ 1`. -/
theorem div_le_two_mul_rpow_neg_mul_rpow {δ R α : ℝ} (hR : 0 < R) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 2 * R) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : δ / R ≤ 2 * (R ^ (-α) * δ ^ α) := by
  rcases hδ0.eq_or_lt with h0 | h0
  · subst h0; rw [zero_div]; positivity
  set t := δ / R
  have ht : 0 < t := div_pos h0 hR
  have ht2 : t ≤ 2 := (div_le_iff₀ hR).mpr (by linarith)
  have hsplit : t = t ^ α * t ^ (1 - α) := by rw [← Real.rpow_add ht, add_sub_cancel, Real.rpow_one]
  have h1 : t ^ (1 - α) ≤ 2 := by
    calc t ^ (1 - α) ≤ 2 ^ (1 - α) := Real.rpow_le_rpow ht.le ht2 (by linarith)
      _ ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h2 : t ^ α = R ^ (-α) * δ ^ α := by
    rw [Real.div_rpow hδ0 hR.le, Real.rpow_neg hR.le, div_eq_inv_mul]
  calc δ / R = t ^ α * t ^ (1 - α) := hsplit
    _ ≤ t ^ α * 2 := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht.le α)
    _ = 2 * (R ^ (-α) * δ ^ α) := by rw [h2]; ring

/-- Entry sup bound on `closedBall c R`: `|D_jD_iw(x)| ≤ (S + A₀)(M + R^α H)`. -/
theorem abs_iteratedFDeriv_newtonianPotential_ball_le (hn : 2 ≤ m + 1) (hR : 0 < R)
    (hfb : ∀ y ∈ ball c (2 * R), |f y| ≤ M) {H α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (hHol : HolderOnWith H α f (ball c (2 * R))) {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ∈ closedBall c R)
    (i j : Fin (m + 1)) :
    |iteratedFDeriv ℝ 2 (newtonianPotential (m + 1) (ball c (2 * R)) f) x
        ![EuclideanSpace.basisFun (Fin (m + 1)) ℝ j, EuclideanSpace.basisFun (Fin (m + 1)) ℝ i]| ≤
      (cancelledHessianSupConst (m + 1) α + newtonianBoxCorrectionSupConst m) * (M + R ^ (α:ℝ) * H) := by
  have hx2 : x ∈ ball c (2 * R) := by
    have : dist x c ≤ R := hx; rw [mem_ball]; linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfb c (mem_ball_self (by positivity)))
  have hαr : (0:ℝ) < α := hα0
  have hαn : (α:ℝ) < ((m + 1 : ℕ) : ℝ) := by
    have h1 : (α:ℝ) < 1 := hα1
    have h2 : (2:ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hfH : ∀ y ∈ ball c (2 * R), ∀ z ∈ ball c (2 * R), |f y - f z| ≤ H * ‖y - z‖ ^ (α:ℝ) := by
    intro y hy z hz; have h := hHol.dist_le hy hz; rwa [Real.dist_eq, dist_eq_norm] at h
  rw [iteratedFDeriv_newtonianPotential_ball_eq hn hR hfb hα0 hα1.le hHol hx2 i j]
  have hT := abs_newtonianCancelledHessian_le hn hR (hHol.continuousOn hα0) hfb H.coe_nonneg hαr
    (by exact_mod_cast hα1.le) hαn hfH hx i j
  have hA := abs_newtonianBoxCorrection_le hn hR hx i j
  have hS := cancelledHessianSupConst_nonneg (m + 1) hαr
  have hA0 := newtonianBoxCorrectionSupConst_nonneg m
  have hRH : 0 ≤ R ^ (α:ℝ) * H := by positivity
  calc _ ≤ |newtonianCancelledHessian (m + 1) (ball c (2 * R)) f i j x| + |f x| * |newtonianBoxCorrection m c R i j x| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ cancelledHessianSupConst (m + 1) α * H * R ^ (α:ℝ) + M * newtonianBoxCorrectionSupConst m :=
        add_le_add hT (mul_le_mul (hfb x hx2) hA (abs_nonneg _) hM)
    _ ≤ _ := by nlinarith [mul_nonneg hS hM, mul_nonneg hA0 hRH]

/-- Entry Hölder bound on `closedBall c R`: `|D_jD_iw(x) − D_jD_iw(z)| ≤ (T₁ + A₀ + 2A₁)(M R^{−α} + H)|x−z|^α`. -/
theorem abs_iteratedFDeriv_newtonianPotential_ball_sub_le (hn : 2 ≤ m + 1) (hR : 0 < R)
    (hfb : ∀ y ∈ ball c (2 * R), |f y| ≤ M) {H α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    (hHol : HolderOnWith H α f (ball c (2 * R))) {x z : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ∈ closedBall c R)
    (hz : z ∈ closedBall c R) (i j : Fin (m + 1)) :
    |iteratedFDeriv ℝ 2 (newtonianPotential (m + 1) (ball c (2 * R)) f) x
        ![EuclideanSpace.basisFun (Fin (m + 1)) ℝ j, EuclideanSpace.basisFun (Fin (m + 1)) ℝ i] -
      iteratedFDeriv ℝ 2 (newtonianPotential (m + 1) (ball c (2 * R)) f) z
        ![EuclideanSpace.basisFun (Fin (m + 1)) ℝ j, EuclideanSpace.basisFun (Fin (m + 1)) ℝ i]| ≤
      (cancelledHessianHolderConst (m + 1) α + newtonianBoxCorrectionSupConst m + 2 * newtonianBoxCorrectionLipConst m) *
        (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ) := by
  have hxc : dist x c ≤ R := hx
  have hzc : dist z c ≤ R := hz
  have hx2 : x ∈ ball c (2 * R) := by rw [mem_ball]; linarith
  have hz2 : z ∈ ball c (2 * R) := by rw [mem_ball]; linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfb c (mem_ball_self (by positivity)))
  have hαr : (0:ℝ) < α := hα0
  have hα1r : (α:ℝ) < 1 := hα1
  have hαn : (α:ℝ) < ((m + 1 : ℕ) : ℝ) := by
    have h2 : (2:ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hfH : ∀ y ∈ ball c (2 * R), ∀ z ∈ ball c (2 * R), |f y - f z| ≤ H * ‖y - z‖ ^ (α:ℝ) := by
    intro y hy z hz; have h := hHol.dist_le hy hz; rwa [Real.dist_eq, dist_eq_norm] at h
  rw [iteratedFDeriv_newtonianPotential_ball_eq hn hR hfb hα0 hα1.le hHol hx2 i j,
    iteratedFDeriv_newtonianPotential_ball_eq hn hR hfb hα0 hα1.le hHol hz2 i j]
  set T1 := cancelledHessianHolderConst (m + 1) α
  set A0 := newtonianBoxCorrectionSupConst m
  set A1 := newtonianBoxCorrectionLipConst m
  set P := ‖x - z‖ ^ (α:ℝ)
  have hP : 0 ≤ P := Real.rpow_nonneg (norm_nonneg _) _
  have hA0 := newtonianBoxCorrectionSupConst_nonneg m
  have hA1 := newtonianBoxCorrectionLipConst_nonneg m
  have hRn : 0 ≤ R ^ (-(α:ℝ)) := Real.rpow_nonneg hR.le _
  have hT := abs_newtonianCancelledHessian_sub_le hn hR (hHol.continuousOn hα0) hfb H.coe_nonneg hαr hα1r hαn hfH hx hz i j
  have hAx := abs_newtonianBoxCorrection_le hn hR hx i j
  have hAd := abs_newtonianBoxCorrection_sub_le hn hR hx hz i j
  have hδ2 : ‖x - z‖ ≤ 2 * R := by rw [← dist_eq_norm]; linarith [dist_triangle x c z, dist_comm z c]
  have hdiv := div_le_two_mul_rpow_neg_mul_rpow hR (norm_nonneg (x - z)) hδ2 hαr hα1r.le
  have hfxz : |f x - f z| ≤ H * P := hfH x hx2 z hz2
  have hT1 : 0 ≤ T1 := by
    have := cancelledHessianSupConst_nonneg (m + 1) hαr
    unfold T1 cancelledHessianHolderConst
    have : 0 < 1 - (α:ℝ) := by linarith
    have : 0 ≤ ((m + 1 : ℕ) : ℝ) + 1 - α := by linarith
    positivity
  have e : newtonianCancelledHessian (m + 1) (ball c (2 * R)) f i j x + f x * newtonianBoxCorrection m c R i j x -
      (newtonianCancelledHessian (m + 1) (ball c (2 * R)) f i j z + f z * newtonianBoxCorrection m c R i j z) =
      (newtonianCancelledHessian (m + 1) (ball c (2 * R)) f i j x - newtonianCancelledHessian (m + 1) (ball c (2 * R)) f i j z) +
        (f x - f z) * newtonianBoxCorrection m c R i j x +
        f z * (newtonianBoxCorrection m c R i j x - newtonianBoxCorrection m c R i j z) := by ring
  rw [e]
  have b2 : |(f x - f z) * newtonianBoxCorrection m c R i j x| ≤ H * P * A0 := by
    rw [abs_mul]; exact mul_le_mul hfxz hAx (abs_nonneg _) (by positivity)
  have b3 : |f z * (newtonianBoxCorrection m c R i j x - newtonianBoxCorrection m c R i j z)| ≤
      M * (A1 * (2 * (R ^ (-(α:ℝ)) * P))) := by
    rw [abs_mul]
    refine mul_le_mul (hfb z hz2) (hAd.trans ?_) (abs_nonneg _) hM
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hdiv hA1
  refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
  refine (add_le_add (add_le_add hT b2) b3).trans ?_
  have h1 : 0 ≤ T1 * (M * R ^ (-(α:ℝ))) * P := by positivity
  have h2 : 0 ≤ A0 * (M * R ^ (-(α:ℝ))) * P := by positivity
  have h3 : 0 ≤ 2 * A1 * H * P := by positivity
  nlinarith

end Entries

/-- **GT2001 Lemma 4.4.** For `n ≥ 2` (including `n = 2`) and `0 < α < 1` there is `C > 0`, chosen before the
centre, the radius and the source, such that for every centre `c`, radius `R > 0` and source `f` with `|f| ≤ M` and
`HolderOnWith H α f` on `B_{2R}(c)`, the Newtonian potential `w` of `f` in `B_{2R}(c)` is `C²` on `B_{2R}(c)` (an open
neighbourhood of `closedBall c R`) and its Hessian operator `D²w = fderiv ℝ (fderiv ℝ w)` (entries
`iteratedFDeriv ℝ 2 w x ![e_j, e_i]`) satisfies on `closedBall c R`:
`‖D²w(x)‖ ≤ C (M + R^α H)`, `‖D²w(x) − D²w(z)‖ ≤ C (M R^{−α} + H) |x − z|^α` (hence `HolderOnWith`), and the source form (4.11)
`‖D²w(x)‖ + R^α ‖D²w(y) − D²w(z)‖ / |y − z|^α ≤ 2C (M + R^α H)`. `α = 1` is not claimed. -/
theorem newtonianPotential_schauder {n : ℕ} (hn : 2 ≤ n) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) (H : ℝ≥0),
      (∀ y ∈ ball c (2 * R), |f y| ≤ M) → HolderOnWith H α f (ball c (2 * R)) →
      ContDiffOn ℝ 2 (newtonianPotential n (ball c (2 * R)) f) (ball c (2 * R)) ∧
      (∀ x ∈ closedBall c R,
        ‖fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f)) x‖ ≤ C * (M + R ^ (α:ℝ) * H)) ∧
      (∀ x ∈ closedBall c R, ∀ z ∈ closedBall c R,
        ‖fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f)) x -
          fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f)) z‖ ≤
          C * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ)) ∧
      HolderOnWith (Real.toNNReal (C * (M * R ^ (-(α:ℝ)) + H))) α
        (fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f))) (closedBall c R) ∧
      (∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R, ∀ z ∈ closedBall c R, y ≠ z →
        ‖fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f)) x‖ +
          R ^ (α:ℝ) * (‖fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f)) y -
            fderiv ℝ (fderiv ℝ (newtonianPotential n (ball c (2 * R)) f)) z‖ / ‖y - z‖ ^ (α:ℝ)) ≤
          2 * C * (M + R ^ (α:ℝ) * H)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hαr : (0:ℝ) < α := hα0
  set C0 := cancelledHessianSupConst (m + 1) α + newtonianBoxCorrectionSupConst m
  set C1 := cancelledHessianHolderConst (m + 1) α + newtonianBoxCorrectionSupConst m + 2 * newtonianBoxCorrectionLipConst m
  have hC0 : 0 < C0 := by
    have : 0 < cancelledHessianSupConst (m + 1) α := by unfold cancelledHessianSupConst; positivity
    have := newtonianBoxCorrectionSupConst_nonneg m; linarith
  have hC1 : 0 ≤ C1 := by
    have h1 := newtonianBoxCorrectionSupConst_nonneg m
    have h2 := newtonianBoxCorrectionLipConst_nonneg m
    have h3 : 0 ≤ cancelledHessianHolderConst (m + 1) α := by
      have := cancelledHessianSupConst_nonneg (m + 1) hαr
      have h1r : (α:ℝ) < 1 := hα1
      unfold cancelledHessianHolderConst
      have : 0 < 1 - (α:ℝ) := by linarith
      have : 0 ≤ ((m + 1 : ℕ) : ℝ) + 1 - α := by
        have : (0:ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      positivity
    positivity
  set N : ℝ := ((m + 1 : ℕ) : ℝ)
  have hN : 0 < N := by positivity
  refine ⟨N * (N * (C0 + C1)), by positivity, fun c R hR f M H hfb hHol => ?_⟩
  set w := newtonianPotential (m + 1) (ball c (2 * R)) f
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfb c (mem_ball_self (by positivity)))
  have hn : 2 ≤ m + 1 := hn
  have hX0 : 0 ≤ M + R ^ (α:ℝ) * H := by positivity
  have hX1 : 0 ≤ M * R ^ (-(α:ℝ)) + H := by positivity
  obtain ⟨hC2, -⟩ := newtonianPotential_lemma_4_2 hn isOpen_ball isBounded_ball ⟨M, hfb⟩ hα0 hα1.le
    (localHolder_of_holderOnWith_ball hHol)
  have hent : ∀ x u v, fderiv ℝ (fderiv ℝ w) x u v = iteratedFDeriv ℝ 2 w x ![u, v] := by
    intro x u v; rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]; simp [bilinearIteratedFDerivTwo]
  have hsum : ∀ K : ℝ, (∑ _j : Fin (m + 1), ∑ _i : Fin (m + 1), K) = N * (N * K) := by
    intro K; simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, N]
  have hsup : ∀ x ∈ closedBall c R, ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ N * (N * (C0 + C1)) * (M + R ^ (α:ℝ) * H) := by
    intro x hx
    refine (norm_le_sum_abs_apply_basisFun_apply _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => ∑ _i : Fin (m + 1), C0 * (M + R ^ (α:ℝ) * H)) fun j _ =>
      Finset.sum_le_sum (g := fun _ => C0 * (M + R ^ (α:ℝ) * H)) fun i _ => ?_).trans ?_
    · rw [hent]
      exact abs_iteratedFDeriv_newtonianPotential_ball_le hn hR hfb hα0 hα1 hHol hx i j
    · rw [hsum]
      have : C0 * (M + R ^ (α:ℝ) * H) ≤ (C0 + C1) * (M + R ^ (α:ℝ) * H) :=
        mul_le_mul_of_nonneg_right (by linarith) hX0
      calc N * (N * (C0 * (M + R ^ (α:ℝ) * H))) ≤ N * (N * ((C0 + C1) * (M + R ^ (α:ℝ) * H))) := by gcongr
        _ = _ := by ring
  have hhol : ∀ x ∈ closedBall c R, ∀ z ∈ closedBall c R,
      ‖fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) z‖ ≤
        N * (N * (C0 + C1)) * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ) := by
    intro x hx z hz
    have hP : 0 ≤ ‖x - z‖ ^ (α:ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    refine (norm_le_sum_abs_apply_basisFun_apply _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => ∑ _i : Fin (m + 1), C1 * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ))
      fun j _ => Finset.sum_le_sum (g := fun _ => C1 * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ)) fun i _ => ?_).trans ?_
    · rw [sub_apply, sub_apply, hent, hent]
      exact abs_iteratedFDeriv_newtonianPotential_ball_sub_le hn hR hfb hα0 hα1 hHol hx hz i j
    · rw [hsum]
      have : C1 * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ) ≤ (C0 + C1) * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hX1) hP
      calc N * (N * (C1 * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ))) ≤
          N * (N * ((C0 + C1) * (M * R ^ (-(α:ℝ)) + H) * ‖x - z‖ ^ (α:ℝ))) := by gcongr
        _ = _ := by ring
  refine ⟨hC2, hsup, hhol, holderOnWith_of_dist_le (by positivity) fun x hx z hz => ?_, fun x hx y hy z hz hyz => ?_⟩
  · rw [dist_eq_norm, dist_eq_norm]; exact hhol x hx z hz
  · have hpos : 0 < ‖y - z‖ ^ (α:ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) _
    have hq : ‖fderiv ℝ (fderiv ℝ w) y - fderiv ℝ (fderiv ℝ w) z‖ / ‖y - z‖ ^ (α:ℝ) ≤
        N * (N * (C0 + C1)) * (M * R ^ (-(α:ℝ)) + H) := (div_le_iff₀ hpos).mpr (hhol y hy z hz)
    have hRα : R ^ (α:ℝ) * R ^ (-(α:ℝ)) = 1 := by
      rw [Real.rpow_neg hR.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hR _).ne']
    have hRpos : 0 ≤ R ^ (α:ℝ) := Real.rpow_nonneg hR.le _
    calc _ ≤ N * (N * (C0 + C1)) * (M + R ^ (α:ℝ) * H) +
          R ^ (α:ℝ) * (N * (N * (C0 + C1)) * (M * R ^ (-(α:ℝ)) + H)) :=
          add_le_add (hsup x hx) (mul_le_mul_of_nonneg_left hq hRpos)
      _ = 2 * (N * (N * (C0 + C1))) * (M + R ^ (α:ℝ) * H) := by
          rw [show R ^ (α:ℝ) * (N * (N * (C0 + C1)) * (M * R ^ (-(α:ℝ)) + H)) =
            N * (N * (C0 + C1)) * (M * (R ^ (α:ℝ) * R ^ (-(α:ℝ))) + R ^ (α:ℝ) * H) by ring, hRα]
          ring

end FunctionalInequalities.Analysis
