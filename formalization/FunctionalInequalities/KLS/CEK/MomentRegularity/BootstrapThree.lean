import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import FunctionalInequalities.KLS.CEK.MomentRegularity.Ellipticity
import FunctionalInequalities.Analysis.BakryEmery.EllipticGradientForcing
import FunctionalInequalities.Analysis.IteratedDerivative.HolderBootstrapStep

/-!
# The regular moment potential is `C³` with locally Hölder third derivative

Letwin, arXiv:2607.24164v1, Lemma 2.2 (strong regular class: smooth `κ`-uniformly convex `W`,
compact convex `K` with nonempty interior, normalized isotropic law `1_K e^{−W}`), first Schauder
bootstrap step, through the method of Gilbarg–Trudinger, Classics 2001 (ISBN 3-540-41160-7),
Lemma 17.16, pp. 463–464, with the interior estimate of Theorem 6.2, pp. 90–92.

`exists_regular_moment_potential_contDiff_three` (`n ≥ 2`): one call of
`exists_regular_moment_potential_holder_hessian_inverse` supplies a potential `u` with every field
of that producer, in the same order; in addition `u` is `C³` on all of `ℝⁿ`, its third derivative
is bounded and Hölder on every ball `ball 0 s`, and the gradient inverse `Ψ` is `C²` on
`interior K`. The equations used are the linearized difference-quotient equations of
`BakryEmery.exists_uniform_linearized_differenceQuotient_equations` (`W(∇u)`-forcing with Hölder
first-order coefficients, zero right-hand side), fed into the one-step gain
`contDiffOn_three_of_quotient_equations`.

Supporting lemmas: `opNorm_le_sum_sum_abs_basisFun` (operator norm of a bilinear form by its
standard-basis entries), `hessian_holder_of_entries` (entrywise Hölder Hessian gives
operator-norm Hölder Hessian), `hessianMatrix_isSymm`, `averagedInverse_symm`,
`abs_differenceQuotient_le_of_lipschitz`, and `contDiffOn_three_balls_of_regular_fields`
(the uniform `C³` bounds on all balls `ball c (1/2)`, `c ∈ ball 0 s`).

This is the `k = 2 ⇒ 3` step only: no `C^k` for `k ≥ 4`, no `C^∞`, no smooth diffeomorphism
statement, and not the merely convex Lemma 2.2.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

open Set Metric Filter Topology MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff BigOperators ENNReal


variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A continuous linear map on `ℝⁿ` applied to `h` is the sum of the coordinates of `h` times
its values on the standard basis. -/
theorem clm_apply_eq_sum_basisFun {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (h : E) :
    L h = ∑ i, h i • L (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- The operator norm of a bilinear form on `ℝⁿ` is at most the sum of the absolute values of
its standard-basis entries. -/
theorem opNorm_le_sum_sum_abs_basisFun (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖B‖ ≤ ∑ i, ∑ j, |B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| := by
  refine ContinuousLinearMap.opNorm_le_bound₂ B (by positivity) fun h k => ?_
  rw [clm_apply_eq_sum_basisFun B h, sum_apply, Real.norm_eq_abs]
  simp only [smul_apply, smul_eq_mul]
  calc |∑ i, h i * B (EuclideanSpace.basisFun (Fin n) ℝ i) k|
      ≤ ∑ i, |h i * B (EuclideanSpace.basisFun (Fin n) ℝ i) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖h‖ * (∑ j, |B (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)| * ‖k‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        refine mul_le_mul (by simpa using PiLp.norm_apply_le h i) ?_ (abs_nonneg _) (norm_nonneg _)
        rw [clm_apply_eq_sum_basisFun (B (EuclideanSpace.basisFun (Fin n) ℝ i)) k]
        simp only [smul_eq_mul]
        calc |∑ j, k j * B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)|
            ≤ ∑ j, |k j * B (EuclideanSpace.basisFun (Fin n) ℝ i)
                (EuclideanSpace.basisFun (Fin n) ℝ j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, |B (EuclideanSpace.basisFun (Fin n) ℝ i)
                (EuclideanSpace.basisFun (Fin n) ℝ j)| * ‖k‖ := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le k j) (abs_nonneg _)
    _ = (∑ i, ∑ j, |B (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)|) * ‖h‖ * ‖k‖ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Entrywise Hölder continuity of the Hessian matrix on a set gives operator-norm Hölder
continuity of the Hessian `D²u` there, with constant `n² C`. -/
theorem hessian_holder_of_entries {u : E → ℝ} {s : Set E} {C η : ℝ≥0}
    (h : ∀ i j, HolderOnWith C η (fun x => hessianMatrix u x i j) s) :
    ∀ x ∈ s, ∀ y ∈ s, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
      ((n : ℝ) ^ 2 * C) * ‖x - y‖ ^ (η : ℝ) := by
  intro x hx y hy
  refine (opNorm_le_sum_sum_abs_basisFun _).trans ?_
  have hentry : ∀ i j, |(fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      C * ‖x - y‖ ^ (η : ℝ) := by
    intro i j
    have hd := (h i j).dist_le hx hy
    rw [Real.dist_eq, dist_eq_norm] at hd
    rw [sub_apply, sub_apply]
    exact hd
  calc ∑ i, ∑ j, |(fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y)
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)|
      ≤ ∑ i : Fin n, ∑ j : Fin n, (C : ℝ) * ‖x - y‖ ^ (η : ℝ) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = ((n : ℝ) ^ 2 * C) * ‖x - y‖ ^ (η : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The Hessian matrix of a `C²` function is symmetric. -/
theorem hessianMatrix_isSymm {u : E → ℝ} (hu : ContDiff ℝ 2 u) (x : E) :
    (hessianMatrix u x).IsSymm :=
  Matrix.IsSymm.ext fun _ _ => bilinearIteratedFDerivTwo_symm hu x _ _

/-- The segment-averaged inverse of a symmetric-valued matrix field is symmetric. -/
theorem averagedInverse_symm {H : E → Matrix (Fin n) (Fin n) ℝ} (hH : ∀ x, (H x).IsSymm)
    (d x : E) (i j : Fin n) :
    averagedInverse H d x i j = averagedInverse H d x j i := by
  unfold averagedInverse
  congr 1
  funext θ
  have hs : ((1 - θ) • H x + θ • H (x + d)).IsSymm := ((hH x).smul _).add ((hH _).smul _)
  have hinv : (((1 - θ) • H x + θ • H (x + d))⁻¹).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_nonsing_inv, hs]
  exact (hinv.apply i j).symm

/-- The scalar-step finite difference of an `L`-Lipschitz function in a unit direction with a
positive step is bounded by `L`. -/
theorem abs_differenceQuotient_le_of_lipschitz {u : E → ℝ} {L : ℝ≥0} (hl : LipschitzWith L u)
    {e : E} (he : ‖e‖ = 1) {q : ℝ} (hq : 0 < q) (x : E) :
    |differenceQuotient u (q • e) q x| ≤ L := by
  unfold differenceQuotient
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
  have h := hl.dist_le_mul (x + q • e) x
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
    abs_of_pos hq] at h
  exact h

/-- **Uniform `C³` bounds on all balls of radius `1/2` inside `ball 0 s`** from the regular-class
fields: `u` is `C²`, `L`-Lipschitz, with Lipschitz gradient, positive definite Hessian satisfying
`log det D²u = −u + W(∇u)` everywhere and entrywise Hölder Hessian on every ball `ball 0 s`, and
`W` is `C²`. For every `s > 0` there are a Hölder exponent `η ∈ (0, 1)` and a constant `Kc` such
that for every centre `c ∈ ball 0 s`, `u` is `C³` on `ball c (1/2)` with third derivative bounded
by `Kc` and `η`-Hölder with constant `Kc` there. -/
theorem contDiffOn_three_balls_of_regular_fields (hn : 2 ≤ n) {u W : E → ℝ}
    (hC2 : ContDiff ℝ 2 u) (hW : ContDiff ℝ 2 W) {L G0 : ℝ≥0} (hl : LipschitzWith L u)
    (hG : LipschitzWith G0 (gradient u))
    (hEvery : ∀ x, (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + W (gradient u x))
    (hLocal : ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
      ∀ i j : Fin n, HolderWith C η (fun x : ball (0 : E) s => hessianMatrix u x.val i j))
    (s : ℝ) (hs : 0 < s) :
    ∃ (η : ℝ≥0) (Kc : ℝ), 0 < η ∧ η < 1 ∧ 0 ≤ Kc ∧ ∀ c ∈ ball (0 : E) s,
      ContDiffOn ℝ 3 u (ball c (1 / 2)) ∧
      (∀ x ∈ ball c (1 / 2), ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ Kc) ∧
      ∀ x ∈ ball c (1 / 2), ∀ y ∈ ball c (1 / 2),
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
          Kc * ‖x - y‖ ^ (η : ℝ) := by
  -- Hölder Hessian on the large closed ball
  obtain ⟨η, C₁, hη0, hη1, hC₁, hH⟩ := hLocal (s + 4) (by linarith)
  have hhol : ∀ i j, HolderOnWith C₁ η (fun x => hessianMatrix u x i j) (closedBall 0 (s + 3)) :=
    fun i j => (HolderWith.restrict_iff.mp (hH i j)).mono (closedBall_subset_ball (by linarith))
  have hHu := hessian_holder_of_entries hhol
  -- the linearized difference-quotient equations on `closedBall 0 (s + 2)`
  obtain ⟨Lc, B, Cb, a, b, hLc, hB, hCb, ha, hb, hdata⟩ :=
    exists_uniform_linearized_differenceQuotient_equations u W hC2 hW 0 (s + 2) (s + 3)
      (by linarith) G0 hG.lipschitzOnWith C₁ η hη0 hη1.le hhol (fun x _ => (hEvery x).1)
      (fun x _ => by linarith [(hEvery x).2])
  -- the one-step gain with these constants
  set K : ℝ≥0 := (n : ℝ≥0) ^ 2 * Lc ^ 2 * C₁ with hK_def
  obtain ⟨C₃, hC₃, hstep⟩ := contDiffOn_three_of_quotient_equations hn hη0 hη1 ha
    (le_max_left a b) (K := (K : ℝ)) (Kb := (B : ℝ) + Cb) (by positivity) (by positivity)
  refine ⟨η, C₃ * ((L : ℝ) * (1 / 2 : ℝ) ^ (-(2 : ℝ) - η) + 0 * (1 / 2 : ℝ) ^ (-(η : ℝ)) + 0),
    hη0, hη1, by positivity, ?_⟩
  intro c hc
  have hc' : ‖c‖ < s := mem_ball_zero_iff.mp hc
  have hsub2 : closedBall c (2 * (1 / 2)) ⊆ closedBall 0 (s + 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ s + 2 := by linarith
  have hsub3 : closedBall c (2 * (1 / 2) + 1) ⊆ closedBall 0 (s + 3) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall, dist_zero_right]
    calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ s + 3 := by linarith
  -- the uniform quotient equations on `closedBall c 1`
  have hUQE : UniformQuotientEquations η a (max a b) (K : ℝ) ((B : ℝ) + Cb) c (1 / 2) u 1
      (L : ℝ) 0 0 := by
    intro e he q hq hq1
    have hstep' : s + 2 + |q| * ‖e‖ ≤ s + 3 := by
      rw [he, mul_one, abs_of_pos hq]; linarith
    obtain ⟨hv, haHol, _hacap, hell, hbcap, hbhol, heq⟩ := hdata e q hq.ne' hstep'
    refine ⟨fun i j x => averagedInverse (hessianMatrix u) (q • e) x i j,
      fun i x => -segmentForcingCoefficient W (gradient u) (q • e) x i, fun _ => 0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x _ i j
      exact averagedInverse_symm (fun y => hessianMatrix_isSymm hC2 y) (q • e) x i j
    · intro x hx ξ
      refine ⟨(hell x (hsub2 hx) ξ).1, (hell x (hsub2 hx) ξ).2.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_right a b) (by positivity)
    · intro i j x hx y hy
      have hd := (haHol i j).dist_le (hsub2 hx) (hsub2 hy)
      rw [Real.dist_eq, dist_eq_norm] at hd
      exact hd
    · intro i x hx
      rw [abs_neg]
      exact (hbcap x (hsub2 hx) i).trans (by simp)
    · intro i x hx y hy
      rw [neg_sub_neg, abs_sub_comm]
      have hd := (hbhol i).dist_le (hsub2 hx) (hsub2 hy)
      rw [Real.dist_eq, dist_eq_norm] at hd
      refine hd.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      simp
    · intro x hx
      have h := heq x (hsub2 hx)
      have hsum : (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • e) x i j *
          hessianMatrix (differenceQuotient u (q • e) q) x j i) =
          ∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • e) x i j *
            fderiv ℝ (fderiv ℝ (differenceQuotient u (q • e) q)) x
              (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [show hessianMatrix (differenceQuotient u (q • e) q) x j i =
            fderiv ℝ (fderiv ℝ (differenceQuotient u (q • e) q)) x
              (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) from
            bilinearIteratedFDerivTwo_symm hv x _ _]
      rw [hsum] at h
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
    · intro x _
      exact abs_differenceQuotient_le_of_lipschitz hl he hq x
    · intro x _
      simp
    · intro x _ y _
      simp
  have hres := hstep c (1 / 2) (by norm_num) (by norm_num) u hC2 1 ((n : ℝ) ^ 2 * C₁) one_pos
    (by positivity) (fun x hx y hy => hHu x (hsub3 hx) y (hsub3 hy)) (L : ℝ) 0 0 hUQE
  exact hres

/-- At a given regular moment potential, locally Hölder Hessian fields yield C³ regularity
and uniform local Hölder third-derivative bounds. The potential is retained throughout. -/
theorem contDiff_three_of_regular_fields (hn : 2 ≤ n) {u W : E → ℝ}
    (hC2 : ContDiff ℝ 2 u) (hW : ContDiff ℝ 2 W)
    {L G : NNReal} (hl : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hEvery : ∀ x, (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + W (gradient u x))
    (hLocal : ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
      ∀ i j : Fin n, HolderWith C η (fun x : ball (0 : E) s => hessianMatrix u x.val i j)) :
    ContDiff ℝ 3 u ∧
      ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        (∀ x ∈ ball (0 : E) s, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C) ∧
        ∀ x ∈ ball (0 : E) s, ∀ y ∈ ball (0 : E) s,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
            C * ‖x - y‖ ^ (η : ℝ) := by
  have hkey := fun (s : ℝ) (hs : 0 < s) =>
    contDiffOn_three_balls_of_regular_fields hn hC2 hW hl hG hEvery hLocal s hs
  -- global `C³`
  have h3 : ContDiff ℝ 3 u := by
    rw [contDiff_iff_contDiffAt]
    intro x₀
    obtain ⟨_, _, _, _, _, h⟩ := hkey (‖x₀‖ + 1) (by positivity)
    have hx₀ : x₀ ∈ ball (0 : E) (‖x₀‖ + 1) := mem_ball_zero_iff.mpr (by linarith)
    exact (h x₀ hx₀).1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self (by norm_num)))
  -- local Hölder third derivative
  have hholder : ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
      (∀ x ∈ ball (0 : E) s, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C) ∧
      ∀ x ∈ ball (0 : E) s, ∀ y ∈ ball (0 : E) s,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
          C * ‖x - y‖ ^ (η : ℝ) := by
    intro s hs
    obtain ⟨η, Kc, hη0, hη1, hKc, h⟩ := hkey s hs
    have hηr : (0 : ℝ) < η := hη0
    have hη1r : (η : ℝ) ≤ 1 := by exact_mod_cast hη1.le
    refine ⟨η, Real.toNNReal (4 * Kc + 1), hη0, hη1, Real.toNNReal_pos.mpr (by positivity),
      ?_, ?_⟩
    · intro x hx
      rw [Real.coe_toNNReal _ (by positivity)]
      have := (h x hx).2.1 x (mem_ball_self (by norm_num))
      linarith
    · intro x hx y hy
      rw [Real.coe_toNNReal _ (by positivity)]
      have hpow : 0 ≤ ‖x - y‖ ^ (η : ℝ) := by positivity
      by_cases hxy : ‖x - y‖ < 1 / 2
      · have hy' : y ∈ ball x (1 / 2) := by
          rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hxy
        have := (h x hx).2.2 x (mem_ball_self (by norm_num)) y hy'
        refine this.trans (mul_le_mul_of_nonneg_right ?_ hpow)
        linarith
      · have hxy : 1 / 2 ≤ ‖x - y‖ := not_lt.mp hxy
        have hbx := (h x hx).2.1 x (mem_ball_self (by norm_num))
        have hby := (h y hy).2.1 y (mem_ball_self (by norm_num))
        have hsub := norm_sub_le (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x)
          (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y)
        -- `1 ≤ 2 ‖x - y‖^η` since `‖x - y‖ ≥ 1/2` and `η ≤ 1`
        have h1 : (1 / 2 : ℝ) ^ (η : ℝ) ≤ ‖x - y‖ ^ (η : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hxy hηr.le
        have h2 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ (η : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hη1r
        rw [Real.rpow_one] at h2
        have h3' : 1 ≤ 2 * ‖x - y‖ ^ (η : ℝ) := by linarith
        calc ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖
            ≤ 2 * Kc := by linarith
          _ = (2 * Kc) * 1 := (mul_one _).symm
          _ ≤ (2 * Kc) * (2 * ‖x - y‖ ^ (η : ℝ)) := by gcongr
          _ ≤ (4 * Kc + 1) * ‖x - y‖ ^ (η : ℝ) := by nlinarith
  exact ⟨h3, hholder⟩

section SameWitness
variable (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
  {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **Regular moment potential, `C³` with locally Hölder third derivative** (Letwin,
arXiv:2607.24164v1, Lemma 2.2 support, strong class, first Schauder bootstrap step; `n ≥ 2`).
For the same `u`, `L`, `LF` and `T`, every field of
`exists_regular_moment_potential_holder_hessian_inverse` in the same order, followed by:
`u` is `C³`; on every ball `ball 0 s` the third derivative is bounded and `η`-Hölder for some
`0 < η < 1`; and `∇u` has a `C²` left inverse on `interior K`. Not `C^k` for `k ≥ 4`, not
`C^∞`, and not the merely convex Lemma 2.2. -/
theorem exists_regular_moment_potential_contDiff_three :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ContDiff ℝ 2 u ∧ Continuous (hessianMatrix u) ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)-hessianMatrix u x).PosSemidef) ∧
      (∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        ∀ i j : Fin n, HolderWith C η
          (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s => hessianMatrix u x.val i j)) ∧
      (∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ interior K,
        ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = gradient u x) ∧
      (∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 1 Ψ (interior K)) ∧
      ContDiff ℝ 3 u ∧
      (∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C) ∧
        ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
          ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
            ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
              C * ‖x - y‖ ^ (η : ℝ)) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 2 Ψ (interior K) := by
  have hn0 : 0 < n := by omega
  obtain ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHcont, hEvery, hLocal,
      he, hΨ⟩ :=
    exists_regular_moment_potential_holder_hessian_inverse hn0 hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨h3, hholder⟩ := contDiff_three_of_regular_fields hn hC2
    (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hl hG
    (fun x => ⟨(hEvery x).1, (hEvery x).2.1⟩) hLocal
  -- the `C²` gradient inverse
  have hΨ2 := Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn0 (k := 2)
    (by norm_num) hl hconv hnorm (by convert h3 using 1; norm_num) (fun x => (hEvery x).1)
    hK hKc hKint hW.continuous (hmap.trans hμ)
  exact ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHcont, hEvery, hLocal,
    he, hΨ, h3, hholder, hΨ2⟩

end SameWitness

end FunctionalInequalities.Analysis
