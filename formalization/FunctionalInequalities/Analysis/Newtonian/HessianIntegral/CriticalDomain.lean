module

public import FunctionalInequalities.Analysis.Newtonian.HessianIntegral.Annulus

/-!
# The residual Newtonian Hessian integral on critical domains

Uniform bounds for `∫_D D_ijΓ` over domains `D` that avoid a neighbourhood of `0`, lie in a ball,
and
contain a full annulus, by the annular cancellation of
`Analysis/Newtonian/HessianIntegral/Annulus.lean`, for `n ≥ 2`:

* `abs_integral_newtonianHessian_of_annulus_subset`: integrability and a bound by the two remainders
  (inner crescent and exterior);
* `abs_integral_newtonianHessian_uniform_of_annulus_subset`: the scale-free bound `6^n + L^n`;
* `newtonianHessian_far_integral_uniform`: for `z ∈ closedBall c R` and `x ≠ z`,
  `|∫_{y ∈ B_{2R}(c), ‖x - y‖ ≥ 2‖x - z‖} D_ijΓ(z - y) dy| ≤ 6^n + 3^n`.

This is the residual term of the Hölder estimate in Lemma 4.4 of Gilbarg–Trudinger, *Elliptic
Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 57–59, bounded
uniformly without the logarithm of an absolute critical-kernel integral.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Removing a full annulus leaves only two bounded remainders. This is the
critical-kernel bound used in the residual term of GT2001 Lemma 4.4. -/
theorem abs_integral_newtonianHessian_of_annulus_subset {n : ℕ} (hn : 2 ≤ n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : MeasurableSet D) {r a b R : ℝ} (hr : 0 < r)
    (ha : 0 < a) (hb : 0 < b) (hnear : ∀ z ∈ D, r ≤ ‖z‖) (hfar : D ⊆ ball 0 R)
    (hAnn : {z : EuclideanSpace ℝ (Fin n) | a < ‖z‖ ∧ ‖z‖ < b} ⊆ D) (i j : Fin n) :
    IntegrableOn
        (fun z =>
          bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z
            (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
        D volume ∧
      |∫ z in D,
            bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z
              (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
        ((1 / euclideanUnitBallVolume n) * r ^ (-(n : ℝ))) *
            volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) (2 * a)) +
          ((1 / euclideanUnitBallVolume n) * b ^ (-(n : ℝ))) *
            volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) R) := by
  let K (z : EuclideanSpace ℝ (Fin n)) :=
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  let A : Set (EuclideanSpace ℝ (Fin n)) := {z | a < ‖z‖ ∧ ‖z‖ < b}
  let L : Set (EuclideanSpace ℝ (Fin n)) := (D \ A) ∩ closedBall 0 a
  let S : Set (EuclideanSpace ℝ (Fin n)) := (D \ A) \ closedBall 0 a
  have hAm : MeasurableSet A :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hLm : MeasurableSet L := (hD.diff hAm).inter measurableSet_closedBall
  have hSm : MeasurableSet S := (hD.diff hAm).diff measurableSet_closedBall
  have hμD : (volume : Measure (EuclideanSpace ℝ (Fin n))) D < ⊤ :=
    lt_of_le_of_lt (measure_mono hfar) measure_ball_lt_top
  have hbound (t : ℝ) (ht : 0 < t) (z : EuclideanSpace ℝ (Fin n)) (hz : t ≤ ‖z‖) :
    ‖K z‖ ≤ (1 / euclideanUnitBallVolume n) * t ^ (-(n : ℝ)) := by
    rw [Real.norm_eq_abs]
    exact
      (abs_bilinear_newtonianKernel_basis_le hn z (norm_pos_iff.mp (ht.trans_le hz)) i j).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ht hz (neg_nonpos.mpr (Nat.cast_nonneg n)))
          (le_of_lt (one_div_pos.mpr (euclideanUnitBallVolume_pos n))))
  have hI : IntegrableOn K D volume :=
    (integrableOn_const hμD.ne :
          IntegrableOn
            (fun _ : EuclideanSpace ℝ (Fin n) =>
              (1 / euclideanUnitBallVolume n) * r ^ (-(n : ℝ)))
            D volume).mono'
      (measurable_bilinear_newtonianKernel hn _ _).aestronglyMeasurable
      ((ae_restrict_mem hD).mono fun z hz => hbound r hr z (hnear z hz))
  have hLD : L ⊆ D := fun _ hz => hz.1.1
  have hSD : S ⊆ D := fun _ hz => hz.1.1
  have hLB : L ⊆ ball 0 (2 * a) := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    have hza : ‖z‖ ≤ a := by simpa only [mem_closedBall, dist_zero_right] using hz.2
    linarith
  have hSb (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ S) : b ≤ ‖z‖ := by
    have hza : a < ‖z‖ :=
      lt_of_not_ge (by simpa only [mem_closedBall, dist_zero_right] using hz.2)
    exact le_of_not_gt (fun hzb => hz.1.2 ⟨hza, hzb⟩)
  have hμL : (volume : Measure (EuclideanSpace ℝ (Fin n))) L < ⊤ :=
    lt_of_le_of_lt (measure_mono hLD) hμD
  have hμS : (volume : Measure (EuclideanSpace ℝ (Fin n))) S < ⊤ :=
    lt_of_le_of_lt (measure_mono hSD) hμD
  have hBL :=
    norm_setIntegral_le_of_norm_le_const hμL (fun z hz => hbound r hr z (hnear z (hLD hz)))
  have hBS := norm_setIntegral_le_of_norm_le_const hμS (fun z hz => hbound b hb z (hSb z hz))
  have hA0 : (∫ z in A, K z) = 0 := integral_bilinear_newtonianKernel_annulus_eq_zero hn ha i j
  have hsplit : (∫ z in D, K z) = (∫ z in L, K z) + ∫ z in S, K z := by
    have h1 := setIntegral_sdiff hAm hI hAnn
    have h2 :=
      integral_inter_add_sdiff (t := closedBall (0 : EuclideanSpace ℝ (Fin n)) a)
        measurableSet_closedBall (hI.mono_set (sdiff_subset : D \ A ⊆ D))
    rw [hA0, sub_zero] at h1
    exact h1.symm.trans h2.symm
  have hw : 0 < euclideanUnitBallVolume n := euclideanUnitBallVolume_pos n
  refine ⟨hI, ?_⟩
  change |∫ z in D, K z| ≤ _
  rw [← Real.norm_eq_abs, hsplit]
  exact
    (norm_add_le _ _).trans
      ((add_le_add hBL hBS).trans
        (add_le_add
          (mul_le_mul_of_nonneg_left (measureReal_mono hLB measure_ball_lt_top.ne)
            (by positivity))
          (mul_le_mul_of_nonneg_left (measureReal_mono (hSD.trans hfar) measure_ball_lt_top.ne)
            (by positivity))))

private theorem critical_ball_mass {n : ℕ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ((1 / euclideanUnitBallVolume n) * s ^ (-(n : ℝ))) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) (t * s)) =
      t ^ n := by
  have hw : 0 < euclideanUnitBallVolume n := euclideanUnitBallVolume_pos n
  rw [Measure.real, Measure.addHaar_ball_of_pos _ _ (mul_pos ht hs), finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  change
    (1 / euclideanUnitBallVolume n) * s ^ (-(n : ℝ)) *
        ((t * s) ^ n * euclideanUnitBallVolume n) =
      t ^ n
  rw [Real.rpow_neg hs.le, Real.rpow_natCast, mul_pow]
  field_simp [hw.ne', hs.ne']

/-- Uniform critical-kernel integral bound: after annulus cancellation the
inner crescent and the exterior contribute at most 6^n and L^n. -/
theorem abs_integral_newtonianHessian_uniform_of_annulus_subset {n : ℕ} (hn : 2 ≤ n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : MeasurableSet D) {δ R L : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hL : 0 < L) (hnear : ∀ z ∈ D, δ ≤ ‖z‖) (hfar : D ⊆ ball 0 (L * R))
    (hAnn : {z : EuclideanSpace ℝ (Fin n) | 3 * δ < ‖z‖ ∧ ‖z‖ < R} ⊆ D) (i j : Fin n) :
    IntegrableOn
        (fun z =>
          bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z
            (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
        D volume ∧
      |∫ z in D,
            bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z
              (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
        (6 : ℝ) ^ n + L ^ n := by
  obtain ⟨hi, hb⟩ :=
    abs_integral_newtonianHessian_of_annulus_subset hn hD hδ (by positivity : 0 < 3 * δ) hR
      hnear hfar hAnn i j
  have h6 :
    (1 / euclideanUnitBallVolume n) * δ ^ (-(n : ℝ)) *
        volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) (2 * (3 * δ))) =
      (6 : ℝ) ^ n := by
    rw [show 2 * (3 * δ) = 6 * δ by ring]
    exact critical_ball_mass hδ (by norm_num)
  rw [h6, critical_ball_mass hR hL] at hb
  exact ⟨hi, hb⟩


/-- Actual residual integral of GT2001 Lemma 4.4, uniformly bounded without
an absolute critical-kernel logarithm. All geometric hypotheses are derived. -/
theorem newtonianHessian_far_integral_uniform {n : ℕ} (hn : 2 ≤ n)
    {c x z : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R) (hz : z ∈ closedBall c R)
    (hxz : x ≠ z) (i j : Fin n) :
    IntegrableOn
        (fun y =>
          bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z - y)
            (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
        {y | y ∈ ball c (2 * R) ∧ 2 * ‖x - z‖ ≤ ‖x - y‖} volume ∧
      |∫ y in {y | y ∈ ball c (2 * R) ∧ 2 * ‖x - z‖ ≤ ‖x - y‖},
            bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z - y)
              (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
        (6 : ℝ) ^ n + (3 : ℝ) ^ n := by
  let δ := ‖x - z‖
  let F : Set (EuclideanSpace ℝ (Fin n)) := {y | y ∈ ball c (2 * R) ∧ 2 * δ ≤ ‖x - y‖}
  let D := (fun v : EuclideanSpace ℝ (Fin n) => z - v) ⁻¹' F
  let K (v : EuclideanSpace ℝ (Fin n)) :=
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) v (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hFm : MeasurableSet F :=
    measurableSet_ball.inter
      (isClosed_le continuous_const (continuous_const.sub continuous_id).norm).measurableSet
  have hDm : MeasurableSet D := hFm.preimage (continuous_const.sub continuous_id).measurable
  have hzc : dist z c ≤ R := hz
  have hnear : ∀ v ∈ D, δ ≤ ‖v‖ := by
    intro v hv
    have h2 : 2 * δ ≤ ‖x - (z - v)‖ := hv.2
    have ht : ‖x - (z - v)‖ ≤ δ + ‖v‖ := by
      rw [show x - (z - v) = (x - z) + v by abel]
      exact norm_add_le _ _
    linarith
  have hfar : D ⊆ ball 0 (3 * R) := by
    intro v hv
    rw [mem_ball, dist_zero_right]
    have hy : dist (z - v) c < 2 * R := hv.1
    have ht := dist_triangle z c (z - v)
    have he : dist z (z - v) = ‖v‖ := by rw [dist_eq_norm, show z - (z - v) = v by abel]
    rw [he, dist_comm c (z - v)] at ht
    linarith
  have hAnn : {v : EuclideanSpace ℝ (Fin n) | 3 * δ < ‖v‖ ∧ ‖v‖ < R} ⊆ D := by
    intro v hv
    change z - v ∈ F
    constructor
    · change dist (z - v) c < 2 * R
      have ht := dist_triangle (z - v) z c
      have he : dist (z - v) z = ‖v‖ := by
        rw [dist_eq_norm, show (z - v) - z = -v by abel, norm_neg]
      rw [he] at ht
      linarith [hv.2]
    · have ht : ‖v‖ ≤ ‖x - (z - v)‖ + δ := by
        have he : v = (x - (z - v)) - (x - z) := by abel
        conv_lhs => rw [he]
        exact norm_sub_le _ _
      linarith [hv.1]
  obtain ⟨hi, hb⟩ :=
    abs_integral_newtonianHessian_uniform_of_annulus_subset hn hDm hδ hR
      (by norm_num : (0 : ℝ) < 3) hnear hfar hAnn i j
  have heq : (fun y => D.indicator K (z - y)) = F.indicator (fun y => K (z - y)) := by
    funext y
    have hyD : z - y ∈ D ↔ y ∈ F := by
      change z - (z - y) ∈ F ↔ y ∈ F
      rw [show z - (z - y) = y by abel]
    by_cases hy : y ∈ F
    · rw [indicator_of_mem (hyD.mpr hy), indicator_of_mem hy]
    · rw [indicator_of_notMem (fun h => hy (hyD.mp h)), indicator_of_notMem hy]
  have hiF : IntegrableOn (fun y => K (z - y)) F volume := by
    apply (integrable_indicator_iff hFm).mp
    rw [← heq]
    exact ((integrable_indicator_iff hDm).mpr hi).comp_sub_left z
  have he : (∫ y in F, K (z - y)) = ∫ v in D, K v := by
    rw [← integral_indicator hFm, ← integral_indicator hDm, ← heq]
    exact integral_sub_left_eq_self _ volume z
  refine ⟨hiF, ?_⟩
  change |∫ y in F, K (z - y)| ≤ _
  rw [he]
  exact hb

end FunctionalInequalities.Analysis
