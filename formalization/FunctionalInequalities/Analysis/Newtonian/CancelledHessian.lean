import FunctionalInequalities.Analysis.Newtonian.KernelBounds
import FunctionalInequalities.Analysis.Newtonian.Far
import FunctionalInequalities.Analysis.Newtonian.NearExponent
import FunctionalInequalities.Analysis.Newtonian.Annulus
import FunctionalInequalities.Analysis.Newtonian.CriticalDomain

/-!
# The cancelled Newtonian Hessian volume term

For Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
2001 (ISBN 3-540-41160-7), pp. 57–59: the cancelled volume term
`T_{ij}(x) = ∫_{B_{2R}} D_jD_iΓ(x - y)(f(y) - f(x)) dy` (`newtonianCancelledHessian`) on concentric balls
`B_R(c) ⊂ B_{2R}(c)`, for `n ≥ 2`, `0 < α < 1` and `f` bounded and `α`-Hölder with cap `H` on `B_{2R}`:

* `newtonianCancelledHessian_split`: the split at a ball `B(x, ρ) ⊆ B_{2R}`, with the near piece bounded
  by `(n/α) H ρ^α`;
* `abs_newtonianCancelledHessian_le`: the (4.12)-type sup bound `|T_{ij}| ≤ (n/α + 3·2ⁿ) H R^α` on
  `closedBall c R` (`cancelledHessianSupConst`);
* `abs_newtonianCancelledHessian_sub_le`: the (4.13)-type Hölder bound
  `|T_{ij}(x) - T_{ij}(z)| ≤ T₁(n, α) H ‖x - z‖^α` on `closedBall c R` (`cancelledHessianHolderConst`).

The Hölder bound combines the near and far estimates with the exact cancellation of `D²Γ` on a
`z`-centred annulus, through the uniform residual bound `newtonianHessian_far_integral_uniform`
(`6ⁿ + 3ⁿ`). No principal value or Calderón–Zygmund theorem is used, and the constants are not GT's
intermediate values.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped RealInnerProductSpace NNReal

namespace FunctionalInequalities.Analysis

/-- The cancelled Hessian integral `∫_Ω D_jD_iΓ(x−y)(f(y) − f(x)) dy`. -/
def newtonianCancelledHessian (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y in Ω, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
    (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (f y - f x)

/-- The sup constant `n/α + 3·2ⁿ`. -/
def cancelledHessianSupConst (n : ℕ) (α : ℝ) : ℝ := n / α + 3 * 2 ^ n

/-- The Hölder constant `5n/α + 2·(n+5)2^{n+1}(n+1−α)/(1−α) + 6ⁿ + 3ⁿ + 8(n/α + 3·2ⁿ)`. -/
def cancelledHessianHolderConst (n : ℕ) (α : ℝ) : ℝ :=
  5 * n / α + 2 * (((n:ℝ) + 5) * 2 ^ ((n:ℝ) + 1) * (((n:ℝ) + 1 - α) / (1 - α))) + 6 ^ n + 3 ^ n +
    8 * cancelledHessianSupConst n α

section Estimates

variable {n : ℕ} {c : EuclideanSpace ℝ (Fin n)} {R M H α : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

private theorem volume_ball_le_ofReal (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) ≤ ENNReal.ofReal (euclideanUnitBallVolume n * r ^ (n:ℝ)) := by
  rw [Measure.addHaar_ball_of_pos _ x hr, finrank_euclideanSpace_fin, Real.rpow_natCast]
  change ENNReal.ofReal (r ^ n) * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≤
    ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1)).toReal * r ^ n)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal measure_ball_lt_top.ne, mul_comm]

private theorem rpow_le_self_of_one_le {a s : ℝ} (ha : 1 ≤ a) (hs : s ≤ 1) : a ^ s ≤ a := by
  simpa using Real.rpow_le_rpow_of_exponent_le ha hs

/-- Split of `T` at a ball `B(x,ρ) ⊆ B_{2R}`: both pieces integrable, the near piece bounded by `(n/α) H ρ^α`. -/
theorem newtonianCancelledHessian_split (hn : 2 ≤ n) (hfc : ContinuousOn f (ball c (2 * R)))
    (hfb : ∀ y ∈ ball c (2 * R), |f y| ≤ M) (hH : 0 ≤ H) (hα : 0 < α) (hαn : α < n)
    (hfH : ∀ y ∈ ball c (2 * R), ∀ z ∈ ball c (2 * R), |f y - f z| ≤ H * ‖y - z‖ ^ α)
    {x : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hρ : 0 < ρ) (hsub : ball x ρ ⊆ ball c (2 * R)) (i j : Fin n) :
    IntegrableOn (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (f y - f x)) (ball x ρ) volume ∧
    IntegrableOn (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (f y - f x))
      (ball c (2 * R) \ ball x ρ) volume ∧
    |∫ y in ball x ρ, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (f y - f x)| ≤ n * H / α * ρ ^ α ∧
    newtonianCancelledHessian n (ball c (2 * R)) f i j x =
      (∫ y in ball x ρ, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
        (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (f y - f x)) +
      ∫ y in ball c (2 * R) \ ball x ρ, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
        (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (f y - f x) := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set K : EuclideanSpace ℝ (Fin n) → ℝ := fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y) (b j) (b i)
  have hx : x ∈ ball c (2 * R) := hsub (mem_ball_self hρ)
  have hB : MeasurableSet (ball c (2 * R)) := measurableSet_ball
  have hKm : Measurable K := (measurable_bilinear_newtonianKernel hn (b j) (b i)).comp
    (continuous_const.sub continuous_id).measurable
  have hfm : AEMeasurable f (volume.restrict (ball c (2 * R))) := hfc.aemeasurable hB
  have hnear := newtonian_near_integrable_integral_le_of_exponent_lt_dim hn x hρ hα hαn hH f
    (hfm.mono_measure (Measure.restrict_mono hsub le_rfl)) (fun y hy => hfH y (hsub hy) x hx) j i
  have hfar : IntegrableOn (fun y => K y * (f y - f x)) (ball c (2 * R) \ ball x ρ) volume := by
    have hfin : volume (ball c (2 * R) \ ball x ρ) < ⊤ := (measure_mono sdiff_subset).trans_lt measure_ball_lt_top
    refine (integrableOn_const (C := (1 / euclideanUnitBallVolume n) * ρ ^ (-(n:ℝ)) * (2 * M)) hfin.ne).mono'
      (hKm.aemeasurable.mul ((hfm.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)).sub
        aemeasurable_const)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (hB.diff measurableSet_ball)] with y hy
    have hy' : ρ ≤ ‖x - y‖ := by
      have := hy.2; rw [mem_ball, dist_eq_norm, not_lt, norm_sub_rev] at this; exact this
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (abs_bilinear_newtonianKernel_basis_le_of_le hn hρ hy' j i) ?_ (abs_nonneg _) (by
      have := euclideanUnitBallVolume_pos n; positivity)
    calc |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hfb y hy.1, hfb x hx]
  refine ⟨hnear.1, hfar, hnear.2, ?_⟩
  unfold newtonianCancelledHessian
  conv_lhs => rw [← union_sdiff_cancel hsub]
  exact setIntegral_union disjoint_sdiff_right (hB.diff measurableSet_ball) hnear.1 hfar

private theorem rpow_neg_mul_pow_eq_one {R : ℝ} (hR : 0 < R) (n : ℕ) : R ^ (-(n:ℝ)) * R ^ n = 1 := by
  rw [Real.rpow_neg hR.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero n hR.ne')]

/-- GT (4.12)-type sup bound for the cancelled term on `closedBall c R`: `|T_{ij}(x)| ≤ (n/α + 3·2ⁿ) H R^α`. -/
theorem abs_newtonianCancelledHessian_le (hn : 2 ≤ n) (hR : 0 < R) (hfc : ContinuousOn f (ball c (2 * R)))
    (hfb : ∀ y ∈ ball c (2 * R), |f y| ≤ M) (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α ≤ 1) (hαn : α < n)
    (hfH : ∀ y ∈ ball c (2 * R), ∀ z ∈ ball c (2 * R), |f y - f z| ≤ H * ‖y - z‖ ^ α)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closedBall c R) (i j : Fin n) :
    |newtonianCancelledHessian n (ball c (2 * R)) f i j x| ≤ cancelledHessianSupConst n α * H * R ^ α := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hxc : dist x c ≤ R := hx
  have hsub : ball x R ⊆ ball c (2 * R) := fun y hy => by
    rw [mem_ball] at hy ⊢; linarith [dist_triangle y x c]
  have hx2 : x ∈ ball c (2 * R) := hsub (mem_ball_self hR)
  obtain ⟨-, -, hnear, heq⟩ := newtonianCancelledHessian_split hn hfc hfb hH hα hαn hfH hR hsub i j
  have hw := euclideanUnitBallVolume_pos n
  have hfin : volume (ball c (2 * R) \ ball x R) < ⊤ := (measure_mono sdiff_subset).trans_lt measure_ball_lt_top
  have hpt : ∀ y ∈ ball c (2 * R) \ ball x R, ‖bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y) (b j) (b i) *
      (f y - f x)‖ ≤ (1 / euclideanUnitBallVolume n) * R ^ (-(n:ℝ)) * (3 * H * R ^ α) := by
    intro y hy
    have hy' : R ≤ ‖x - y‖ := by
      have := hy.2; rw [mem_ball, dist_eq_norm, not_lt, norm_sub_rev] at this; exact this
    have hy3 : ‖y - x‖ < 3 * R := by
      have := hy.1; rw [mem_ball] at this; rw [← dist_eq_norm]; linarith [dist_triangle y c x, dist_comm x c]
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (abs_bilinear_newtonianKernel_basis_le_of_le hn hR hy' j i) ?_ (abs_nonneg _) (by positivity)
    calc |f y - f x| ≤ H * ‖y - x‖ ^ α := hfH y hy.1 x hx2
      _ ≤ H * (3 * R) ^ α := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hy3.le hα.le) hH
      _ = H * (3 ^ α * R ^ α) := by rw [Real.mul_rpow (by norm_num) hR.le]
      _ ≤ H * (3 * R ^ α) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (rpow_le_self_of_one_le (by norm_num) hα1) (by positivity)) hH
      _ = 3 * H * R ^ α := by ring
  have hfar := norm_setIntegral_le_of_norm_le_const hfin hpt
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball c (2 * R) \ ball x R) ≤ euclideanUnitBallVolume n * (2 * R) ^ n := by
    rw [← volume_real_ball_eq (by omega) c (by positivity : 0 ≤ 2 * R)]
    exact measureReal_mono sdiff_subset measure_ball_lt_top.ne
  rw [Real.norm_eq_abs] at hfar
  rw [heq]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ n * H / α * R ^ α + (1 / euclideanUnitBallVolume n) * R ^ (-(n:ℝ)) * (3 * H * R ^ α) * (euclideanUnitBallVolume n * (2 * R) ^ n) :=
        add_le_add hnear (hfar.trans (mul_le_mul_of_nonneg_left hvol (by positivity)))
    _ = cancelledHessianSupConst n α * H * R ^ α := by
        have h1 := rpow_neg_mul_pow_eq_one hR n
        have key : (1 / euclideanUnitBallVolume n) * R ^ (-(n:ℝ)) * (3 * H * R ^ α) * (euclideanUnitBallVolume n * (2 * R) ^ n) =
            3 * 2 ^ n * H * R ^ α := by
          rw [mul_pow, show (1 / euclideanUnitBallVolume n) * R ^ (-(n:ℝ)) * (3 * H * R ^ α) * (euclideanUnitBallVolume n * (2 ^ n * R ^ n)) =
            3 * 2 ^ n * H * R ^ α * (R ^ (-(n:ℝ)) * R ^ n) * (euclideanUnitBallVolume n * (1 / euclideanUnitBallVolume n)) by ring, h1,
            mul_one_div_cancel hw.ne', mul_one, mul_one]
        rw [key, cancelledHessianSupConst]; ring

theorem cancelledHessianSupConst_nonneg (n : ℕ) {α : ℝ} (hα : 0 < α) : 0 ≤ cancelledHessianSupConst n α := by
  unfold cancelledHessianSupConst; positivity

/-- GT (4.13)-type Hölder bound for the cancelled term on `closedBall c R`, `0 < α < 1`:
`|T_{ij}(x) − T_{ij}(z)| ≤ T₁(n,α) H |x−z|^α`. -/
theorem abs_newtonianCancelledHessian_sub_le (hn : 2 ≤ n) (hR : 0 < R) (hfc : ContinuousOn f (ball c (2 * R)))
    (hfb : ∀ y ∈ ball c (2 * R), |f y| ≤ M) (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1) (hαn : α < n)
    (hfH : ∀ y ∈ ball c (2 * R), ∀ z ∈ ball c (2 * R), |f y - f z| ≤ H * ‖y - z‖ ^ α)
    {x z : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closedBall c R) (hz : z ∈ closedBall c R) (i j : Fin n) :
    |newtonianCancelledHessian n (ball c (2 * R)) f i j x - newtonianCancelledHessian n (ball c (2 * R)) f i j z| ≤
      cancelledHessianHolderConst n α * H * ‖x - z‖ ^ α := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set S := cancelledHessianSupConst n α with hSdef
  have hS := cancelledHessianSupConst_nonneg n hα
  set FarC := ((n:ℝ) + 5) * 2 ^ ((n:ℝ) + 1) * (((n:ℝ) + 1 - α) / (1 - α)) with hFdef
  have hFarC : 0 ≤ FarC := by
    have : 0 < 1 - α := by linarith
    have : 0 ≤ (n:ℝ) + 1 - α := by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
    positivity
  have hC : (n:ℝ) / α * 2 + n / α * 3 + FarC * 2 + (6 ^ n + 3 ^ n) + 8 * S ≤ cancelledHessianHolderConst n α := by
    rw [hSdef, hFdef]; unfold cancelledHessianHolderConst; ring_nf; exact le_rfl
  have hw := euclideanUnitBallVolume_pos n
  by_cases hxz : x = z
  · subst hxz; simp [Real.zero_rpow hα.ne']
  set δ := ‖z - x‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxz))
  have hδP : ‖x - z‖ ^ α = δ ^ α := by rw [norm_sub_rev]
  rw [hδP]
  have hP : 0 ≤ δ ^ α := Real.rpow_nonneg hδ.le α
  have hxc : dist x c ≤ R := hx
  have hzc : dist z c ≤ R := hz
  have hx2 : x ∈ ball c (2 * R) := by rw [mem_ball]; linarith
  have hz2 : z ∈ ball c (2 * R) := by rw [mem_ball]; linarith
  rcases le_or_gt R (4 * δ) with h4 | h4
  · -- two sup bounds
    have e1 := abs_newtonianCancelledHessian_le hn hR hfc hfb hH hα hα1.le hαn hfH hx i j
    have e2 := abs_newtonianCancelledHessian_le hn hR hfc hfb hH hα hα1.le hαn hfH hz i j
    have hRα : R ^ α ≤ 4 * δ ^ α := by
      calc R ^ α ≤ (4 * δ) ^ α := Real.rpow_le_rpow hR.le h4 hα.le
        _ = 4 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ.le
        _ ≤ 4 * δ ^ α := mul_le_mul_of_nonneg_right (rpow_le_self_of_one_le (by norm_num) hα1.le) hP
    calc _ ≤ _ := abs_sub _ _
      _ ≤ S * H * R ^ α + S * H * R ^ α := add_le_add e1 e2
      _ ≤ 8 * S * H * δ ^ α := by nlinarith [mul_nonneg hS hH]
      _ ≤ cancelledHessianHolderConst n α * H * δ ^ α := by
          have : 8 * S ≤ cancelledHessianHolderConst n α := by
            have : 0 ≤ (n:ℝ) / α * 2 + n / α * 3 + FarC * 2 + (6 ^ n + 3 ^ n) := by positivity
            linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hH) hP
  · -- near / far / residual decomposition
    have hsubx : ball x (2 * δ) ⊆ ball c (2 * R) := fun y hy => by
      rw [mem_ball] at hy ⊢; linarith [dist_triangle y x c]
    have hsubz : ball z (3 * δ) ⊆ ball c (2 * R) := fun y hy => by
      rw [mem_ball] at hy ⊢; linarith [dist_triangle y z c]
    have hxz3 : ball x (2 * δ) ⊆ ball z (3 * δ) := fun y hy => by
      rw [mem_ball] at hy ⊢
      have : dist x z = δ := by rw [dist_eq_norm, norm_sub_rev]
      linarith [dist_triangle y x z]
    have hfm : AEMeasurable f (volume.restrict (ball c (2 * R))) := hfc.aemeasurable measurableSet_ball
    obtain ⟨-, hFxI, hNx, hTx⟩ := newtonianCancelledHessian_split hn hfc hfb hH hα hαn hfH (by positivity) hsubx i j
    set Kz : EuclideanSpace ℝ (Fin n) → ℝ := fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z - y) (b j) (b i)
    set Kx : EuclideanSpace ℝ (Fin n) → ℝ := fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y) (b j) (b i)
    have hKzm : Measurable Kz := (measurable_bilinear_newtonianKernel hn (b j) (b i)).comp
      (continuous_const.sub continuous_id).measurable
    -- the near piece at `z` on `B(x,2δ) ⊆ B(z,3δ)`
    set k := (ball x (2 * δ)).indicator Kz
    have hc := cancelled_near_kernel_integrable_integral_le volume z hw.le (by positivity : 0 < 3 * δ) hα hαn
      (by positivity : 0 ≤ 1 / euclideanUnitBallVolume n) hH (volume_ball_le_ofReal z) k f
      (((hKzm.indicator measurableSet_ball).aemeasurable).mul
        ((hfm.mono_measure (Measure.restrict_mono hsubz le_rfl)).sub aemeasurable_const))
      (by
        intro y _ hy
        by_cases hyx : y ∈ ball x (2 * δ)
        · rw [show k y = Kz y from Set.indicator_of_mem hyx _]
          have hb := abs_bilinear_newtonianKernel_basis_le hn (z - y) (sub_ne_zero.mpr (Ne.symm hy)) j i
          rwa [norm_sub_rev] at hb
        · rw [show k y = 0 from Set.indicator_of_notMem hyx _, abs_zero]; positivity)
      (fun y hy => hfH y (hsubz hy) z (hsubz (mem_ball_self (by positivity))))
    have heqk : (fun y => k y * (f y - f z)) = (ball x (2 * δ)).indicator (fun y => Kz y * (f y - f z)) := by
      funext y; by_cases hy : y ∈ ball x (2 * δ)
      · simp only [k, Set.indicator_of_mem hy]
      · simp only [k, Set.indicator_of_notMem hy, zero_mul]
    have hNzI : IntegrableOn (fun y => Kz y * (f y - f z)) (ball x (2 * δ)) volume := by
      have h := hc.1; rw [heqk] at h
      have h' := (integrable_indicator_iff measurableSet_ball).mp h
      rwa [IntegrableOn, Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hxz3] at h'
    have hNz : |∫ y in ball x (2 * δ), Kz y * (f y - f z)| ≤ n / α * 3 * H * δ ^ α := by
      have h := hc.2
      rw [heqk, setIntegral_indicator measurableSet_ball, inter_eq_right.mpr hxz3] at h
      refine h.trans ?_
      have h3 : (3:ℝ) ^ α ≤ 3 := rpow_le_self_of_one_le (by norm_num) hα1.le
      calc 1 / euclideanUnitBallVolume n * H * (euclideanUnitBallVolume n * n / α * (3 * δ) ^ α) = n / α * H * δ ^ α * 3 ^ α := by
            rw [Real.mul_rpow (by norm_num) hδ.le]; field_simp
        _ ≤ n / α * H * δ ^ α * 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = n / α * 3 * H * δ ^ α := by ring
    -- the far piece at `z`
    set E := ball c (2 * R) \ ball x (2 * δ)
    have hEm : MeasurableSet E := measurableSet_ball.diff measurableSet_ball
    have hfarz : ∀ y ∈ E, δ ≤ ‖z - y‖ := by
      intro y hy
      have h2 : 2 * δ ≤ ‖y - x‖ := by have := hy.2; rwa [mem_ball, dist_eq_norm, not_lt] at this
      have := norm_sub_le_norm_sub_add_norm_sub y z x
      rw [norm_sub_rev y z] at this; linarith
    have hFzI : IntegrableOn (fun y => Kz y * (f y - f z)) E volume := by
      have hfin : volume E < ⊤ := (measure_mono sdiff_subset).trans_lt measure_ball_lt_top
      refine (integrableOn_const (C := (1 / euclideanUnitBallVolume n) * δ ^ (-(n:ℝ)) * (2 * M)) hfin.ne).mono'
        (hKzm.aemeasurable.mul ((hfm.mono_measure (Measure.restrict_mono sdiff_subset le_rfl)).sub
          aemeasurable_const)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem hEm] with y hy
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (abs_bilinear_newtonianKernel_basis_le_of_le hn hδ (hfarz y hy) j i) ?_ (abs_nonneg _)
        (by positivity)
      calc |f y - f z| ≤ |f y| + |f z| := abs_sub _ _
        _ ≤ 2 * M := by linarith [hfb y hy.1, hfb z hz2]
    have hTz : newtonianCancelledHessian n (ball c (2 * R)) f i j z =
        (∫ y in ball x (2 * δ), Kz y * (f y - f z)) + ∫ y in E, Kz y * (f y - f z) := by
      unfold newtonianCancelledHessian
      conv_lhs => rw [← union_sdiff_cancel hsubx]
      exact setIntegral_union disjoint_sdiff_right hEm hNzI hFzI
    -- far difference and residual (annulus)
    have hEset : ball c (2 * R) ∩ {y | 2 * ‖z - x‖ ≤ ‖y - x‖} = E := by
      ext y
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [mem_ball, dist_eq_norm, not_lt]; exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [mem_ball, dist_eq_norm, not_lt] at h2; exact h2
    obtain ⟨hDI, hD⟩ := newtonian_far_integrable_integral_le hn x z hxz hα hα1 hH (ball c (2 * R)) measurableSet_ball f
      hfm (fun y hy => hfH y hy x hx2) j i
    rw [hEset] at hDI hD
    have hEset2 : {y | y ∈ ball c (2 * R) ∧ 2 * ‖x - z‖ ≤ ‖x - y‖} = E := by
      ext y
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [norm_sub_rev x z, norm_sub_rev x y] at h2
        rw [mem_ball, dist_eq_norm, not_lt]; exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [mem_ball, dist_eq_norm, not_lt] at h2
        rw [norm_sub_rev x z, norm_sub_rev x y]; exact h2
    obtain ⟨hRzI, hRz⟩ := newtonianHessian_far_integral_uniform hn hR hz hxz j i
    rw [hEset2] at hRzI hRz
    have hFdiff : (∫ y in E, Kx y * (f y - f x)) - (∫ y in E, Kz y * (f y - f z)) =
        (∫ y in E, (Kx y - Kz y) * (f y - f x)) + (f z - f x) * ∫ y in E, Kz y := by
      rw [← integral_sub hFxI hFzI, ← integral_const_mul, ← integral_add hDI (hRzI.const_mul _)]
      congr 1; funext y; ring
    have hfzx : |f z - f x| ≤ H * δ ^ α := hfH z hz2 x hx2
    have b3 : |∫ y in E, (Kx y - Kz y) * (f y - f x)| ≤ FarC * 2 * H * δ ^ α := by
      refine hD.trans ?_
      rw [Real.mul_rpow (by norm_num) hδ.le]
      have h2 : (2:ℝ) ^ α ≤ 2 := rpow_le_self_of_one_le (by norm_num) hα1.le
      have : 0 ≤ FarC * H * δ ^ α := by positivity
      calc ((n:ℝ) + 5) * 2 ^ ((n:ℝ) + 1) * H * (((n:ℝ) + 1 - α) / (1 - α)) * (2 ^ α * δ ^ α) =
            FarC * H * δ ^ α * 2 ^ α := by ring
        _ ≤ FarC * H * δ ^ α * 2 := mul_le_mul_of_nonneg_left h2 this
        _ = FarC * 2 * H * δ ^ α := by ring
    have b1 : |∫ y in ball x (2 * δ), Kx y * (f y - f x)| ≤ n / α * 2 * H * δ ^ α := by
      refine hNx.trans ?_
      rw [Real.mul_rpow (by norm_num) hδ.le]
      have h2 : (2:ℝ) ^ α ≤ 2 := rpow_le_self_of_one_le (by norm_num) hα1.le
      have : 0 ≤ (n:ℝ) / α * H * δ ^ α := by positivity
      calc (n:ℝ) * H / α * (2 ^ α * δ ^ α) = n / α * H * δ ^ α * 2 ^ α := by ring
        _ ≤ n / α * H * δ ^ α * 2 := mul_le_mul_of_nonneg_left h2 this
        _ = n / α * 2 * H * δ ^ α := by ring
    have b4 : |(f z - f x) * ∫ y in E, Kz y| ≤ (6 ^ n + 3 ^ n) * H * δ ^ α := by
      rw [abs_mul]
      calc |f z - f x| * |∫ y in E, Kz y| ≤ (H * δ ^ α) * (6 ^ n + 3 ^ n) :=
            mul_le_mul hfzx hRz (abs_nonneg _) (by positivity)
        _ = (6 ^ n + 3 ^ n) * H * δ ^ α := by ring
    have hsplit : newtonianCancelledHessian n (ball c (2 * R)) f i j x - newtonianCancelledHessian n (ball c (2 * R)) f i j z =
        ((∫ y in ball x (2 * δ), Kx y * (f y - f x)) - ∫ y in ball x (2 * δ), Kz y * (f y - f z)) +
          ((∫ y in E, (Kx y - Kz y) * (f y - f x)) + (f z - f x) * ∫ y in E, Kz y) := by
      rw [hTx, hTz, ← hFdiff]; ring
    rw [hsplit]
    have hHP : 0 ≤ H * δ ^ α := mul_nonneg hH hP
    calc _ ≤ |(∫ y in ball x (2 * δ), Kx y * (f y - f x)) - ∫ y in ball x (2 * δ), Kz y * (f y - f z)| +
          |(∫ y in E, (Kx y - Kz y) * (f y - f x)) + (f z - f x) * ∫ y in E, Kz y| := abs_add_le _ _
      _ ≤ (n / α * 2 * H * δ ^ α + n / α * 3 * H * δ ^ α) + (FarC * 2 * H * δ ^ α + (6 ^ n + 3 ^ n) * H * δ ^ α) :=
          add_le_add ((abs_sub _ _).trans (add_le_add b1 hNz)) ((abs_add_le _ _).trans (add_le_add b3 b4))
      _ ≤ cancelledHessianHolderConst n α * H * δ ^ α := by
          have : (n:ℝ) / α * 2 + n / α * 3 + FarC * 2 + (6 ^ n + 3 ^ n) ≤ cancelledHessianHolderConst n α := by linarith
          nlinarith

end Estimates

end FunctionalInequalities.Analysis
