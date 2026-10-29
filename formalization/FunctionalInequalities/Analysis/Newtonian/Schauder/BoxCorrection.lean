import FunctionalInequalities.Analysis.Newtonian.Schauder.KernelBounds
import FunctionalInequalities.Analysis.Newtonian.Potential.BoundaryFormula

/-!
# The box correction in the Newtonian Hessian

For Lemma 4.4 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
2001 (ISBN 3-540-41160-7), pp. 57–59, via the box form of (4.9). For concentric balls
`B_R(c) ⊂ B_{2R}(c)` in `ℝⁿ`, `n = m + 1`, and the coordinate box `Ω₀ = ∏ (c_k - 3R, c_k + 3R) ⊇ B_{2R}(c)`,
the Hessian correction multiplying `f(x)` is
`Â_{ij}(x) = -∫_{Ω₀ ∖ B_{2R}} D_jD_iΓ(x - y) dy - ∑_faces ∫ D_iΓ(x - y) ν_j dσ`
(`newtonianBoxCorrection`). On `closedBall c R`:

* `abs_newtonianBoxCorrection_le`: `|Â_{ij}(x)| ≤ A₀(n)` (`newtonianBoxCorrectionSupConst`);
* `abs_newtonianBoxCorrection_sub_le`: `|Â_{ij}(x) - Â_{ij}(z)| ≤ A₁(n) ‖x - z‖ / R`
  (`newtonianBoxCorrectionLipConst`),

because `Ω₀ ∖ B_{2R}` stays at distance `≥ R` and the faces at distance `≥ 2R` from `closedBall c R`.
The constants depend on the dimension only and are not GT's intermediate values.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace NNReal

namespace FunctionalInequalities.Analysis

/-- Lower corner `c − 3R` of the centred box. -/
def newtonianBoxLower {m : ℕ} (c : EuclideanSpace ℝ (Fin (m + 1))) (R : ℝ) : Fin (m + 1) → ℝ := fun k => c k - 3 * R

/-- Upper corner `c + 3R` of the centred box. -/
def newtonianBoxUpper {m : ℕ} (c : EuclideanSpace ℝ (Fin (m + 1))) (R : ℝ) : Fin (m + 1) → ℝ := fun k => c k + 3 * R

/-- The box correction `Â_{ij}(x)` of (4.9) on the centred box `c ± 3R`, relative to `B_{2R}(c)`. -/
def newtonianBoxCorrection (m : ℕ) (c : EuclideanSpace ℝ (Fin (m + 1))) (R : ℝ) (i j : Fin (m + 1))
    (x : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  -(∫ y in euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R) \ ball c (2 * R),
      bilinearIteratedFDerivTwo ℝ (newtonianKernel (m + 1)) (x - y)
        (EuclideanSpace.basisFun (Fin (m + 1)) ℝ j) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ i)) -
    ∑ p, ∫ y, fderiv ℝ (newtonianKernel (m + 1)) (x - y) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ i) *
      euclideanBoxFaceNormal p y j ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)

/-- `A₀(n)`, `n = m + 1`. -/
def newtonianBoxCorrectionSupConst (m : ℕ) : ℝ :=
  (1 / euclideanUnitBallVolume (m + 1)) * 6 ^ (m + 1) + 2 * (m + 1) * ((1 / ((m + 1 : ℕ) * euclideanUnitBallVolume (m + 1))) * 3 ^ m)

/-- `A₁(n)`, `n = m + 1`. -/
def newtonianBoxCorrectionLipConst (m : ℕ) : ℝ :=
  ((((m + 1 : ℕ) : ℝ) + 5) / euclideanUnitBallVolume (m + 1)) * 6 ^ (m + 1) +
    2 * (m + 1) * ((m + 1 : ℕ) * (1 / euclideanUnitBallVolume (m + 1)) * (6 ^ m / 2 ^ (m + 1)))

section Box

variable {m : ℕ} {c : EuclideanSpace ℝ (Fin (m + 1))} {R : ℝ}

theorem newtonianBoxLower_le_upper (hR : 0 < R) : newtonianBoxLower c R ≤ newtonianBoxUpper c R := fun k => by
  simp only [newtonianBoxLower, newtonianBoxUpper]; linarith

theorem ball_subset_newtonianBox (hR : 0 < R) :
    ball c (2 * R) ⊆ euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R) := by
  intro y hy k
  rw [mem_ball, dist_eq_norm] at hy
  have h := (abs_apply_le_norm_euclidean (y - c) k).trans_lt hy
  rw [PiLp.sub_apply, abs_lt] at h
  simp only [newtonianBoxLower, newtonianBoxUpper]
  constructor <;> linarith

theorem volume_real_newtonianBox (hR : 0 < R) :
    volume (euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R)) < ⊤ ∧
    (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real
      (euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R)) = (6 * R) ^ (m + 1) := by
  have he : euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R) =
      WithLp.ofLp ⁻¹' (univ.pi fun k => Ioo (newtonianBoxLower c R k) (newtonianBoxUpper c R k)) := by
    ext y; simp [euclideanOpenBox, Set.mem_pi]
  have hv : volume (euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R)) = ENNReal.ofReal (6 * R) ^ (m + 1) := by
    rw [he, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp only [newtonianBoxLower, newtonianBoxUpper, show ∀ k : Fin (m + 1), c k + 3 * R - (c k - 3 * R) = 6 * R from
      fun k => by ring, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨by rw [hv]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top, ?_⟩
  rw [measureReal_def, hv, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

/-- Face integrals are integrals over the parameter box of the face. -/
theorem integral_euclideanBoxFaceMeasure_eq (a b : Fin (m + 1) → ℝ) (p : Fin (m + 1) × Bool)
    {g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hg : Measurable g) :
    (∫ y, g y ∂(euclideanBoxFaceMeasure a b p)) =
      ∫ w in Icc (a ∘ p.1.succAbove) (b ∘ p.1.succAbove), g (WithLp.toLp 2 (p.1.insertNth (if p.2 then b p.1 else a p.1) w)) := by
  rw [euclideanBoxFaceMeasure, integral_map (continuous_toLp_insertNth _ _).aemeasurable hg.aestronglyMeasurable]

theorem volume_real_newtonianBox_face (hR : 0 < R) (p : Fin (m + 1) × Bool) :
    volume (Icc (newtonianBoxLower c R ∘ p.1.succAbove) (newtonianBoxUpper c R ∘ p.1.succAbove)) < ⊤ ∧
    (volume : Measure (Fin m → ℝ)).real
      (Icc (newtonianBoxLower c R ∘ p.1.succAbove) (newtonianBoxUpper c R ∘ p.1.succAbove)) = (6 * R) ^ m := by
  refine ⟨isCompact_Icc.measure_lt_top, ?_⟩
  rw [measureReal_def, Real.volume_Icc_pi_toReal (a := newtonianBoxLower c R ∘ p.1.succAbove)
    (b := newtonianBoxUpper c R ∘ p.1.succAbove) (fun k => newtonianBoxLower_le_upper hR _)]
  simp only [Function.comp_apply, newtonianBoxLower, newtonianBoxUpper,
    show ∀ k : Fin m, c (p.1.succAbove k) + 3 * R - (c (p.1.succAbove k) - 3 * R) = 6 * R from fun k => by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Points of `closedBall c R` are at distance `≥ 2R` from every face of the centred box. -/
theorem two_mul_le_norm_sub_newtonianBox_face (hR : 0 < R) {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ∈ closedBall c R)
    (p : Fin (m + 1) × Bool) (w : Fin m → ℝ) :
    2 * R ≤ ‖x - WithLp.toLp 2 (p.1.insertNth (α := fun _ => ℝ)
      (if p.2 then newtonianBoxUpper c R p.1 else newtonianBoxLower c R p.1) w)‖ := by
  set q := WithLp.toLp 2 (p.1.insertNth (α := fun _ => ℝ)
    (if p.2 then newtonianBoxUpper c R p.1 else newtonianBoxLower c R p.1) w)
  have hq : q p.1 = if p.2 then c p.1 + 3 * R else c p.1 - 3 * R := by
    simp only [q, Fin.insertNth_apply_same, newtonianBoxLower, newtonianBoxUpper]
  have hxk : |x p.1 - c p.1| ≤ R := by
    have h := abs_apply_le_norm_euclidean (x - c) p.1
    rw [PiLp.sub_apply] at h
    exact h.trans (by rw [← dist_eq_norm]; exact hx)
  refine le_trans ?_ (abs_apply_le_norm_euclidean (x - q) p.1)
  rw [PiLp.sub_apply, hq]
  rw [abs_le] at hxk
  split_ifs
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- Points outside `B_{2R}(c)` are at distance `≥ R` from `closedBall c R`. -/
theorem le_norm_sub_of_notMem_ball {x : EuclideanSpace ℝ (Fin (m + 1))} (hx : x ∈ closedBall c R)
    {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hy : y ∉ ball c (2 * R)) : R ≤ ‖x - y‖ := by
  rw [mem_ball, not_lt] at hy
  have hxc : dist x c ≤ R := hx
  rw [← dist_eq_norm]; linarith [dist_triangle y x c, dist_comm x y]

private theorem rpow_neg_natCast_eq {t : ℝ} (ht : 0 < t) (k : ℕ) : t ^ (-(k:ℝ)) = (t ^ k)⁻¹ := by
  rw [Real.rpow_neg ht.le, Real.rpow_natCast]

/-- A face integral of a measurable function bounded by `B` on the face is at most `B (6R)^m`. -/
theorem abs_integral_newtonianBox_face_le (hR : 0 < R) (p : Fin (m + 1) × Bool)
    {g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ w : Fin m → ℝ, |g (WithLp.toLp 2 (p.1.insertNth (α := fun _ => ℝ)
      (if p.2 then newtonianBoxUpper c R p.1 else newtonianBoxLower c R p.1) w))| ≤ B) :
    |∫ y, g y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)| ≤ B * (6 * R) ^ m := by
  rw [integral_euclideanBoxFaceMeasure_eq _ _ p hg, ← Real.norm_eq_abs, ← (volume_real_newtonianBox_face hR p).2]
  exact norm_setIntegral_le_of_norm_le_const (volume_real_newtonianBox_face hR p).1
    (fun w _ => by rw [Real.norm_eq_abs]; exact hB w)

theorem abs_euclideanBoxFaceNormal_apply_le (p : Fin (m + 1) × Bool) (y : EuclideanSpace ℝ (Fin (m + 1))) (j : Fin (m + 1)) :
    |euclideanBoxFaceNormal p y j| ≤ 1 := by
  refine (abs_apply_le_norm_euclidean _ j).trans ?_
  rcases p with ⟨k, _ | _⟩ <;> simp [euclideanBoxFaceNormal]

theorem measurable_euclideanBoxFaceNormal_apply (p : Fin (m + 1) × Bool) (j : Fin (m + 1)) :
    Measurable (fun y : EuclideanSpace ℝ (Fin (m + 1)) => euclideanBoxFaceNormal p y j) := by
  unfold euclideanBoxFaceNormal; exact measurable_const

/-- `|Â_{ij}(x)| ≤ A₀(n)` on `closedBall c R`. -/
theorem abs_newtonianBoxCorrection_le (hn : 2 ≤ m + 1) (hR : 0 < R) {x : EuclideanSpace ℝ (Fin (m + 1))}
    (hx : x ∈ closedBall c R) (i j : Fin (m + 1)) :
    |newtonianBoxCorrection m c R i j x| ≤ newtonianBoxCorrectionSupConst m := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  set ω := euclideanUnitBallVolume (m + 1)
  have hw : 0 < ω := euclideanUnitBallVolume_pos (m + 1)
  set V := euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R) \ ball c (2 * R)
  obtain ⟨hbox, hboxv⟩ := volume_real_newtonianBox (c := c) hR
  have hVfin : volume V < ⊤ := (measure_mono sdiff_subset).trans_lt hbox
  have hVv : (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real V ≤ (6 * R) ^ (m + 1) := by
    rw [← hboxv]; exact measureReal_mono sdiff_subset hbox.ne
  -- volume part
  have hvol : |∫ y in V, bilinearIteratedFDerivTwo ℝ (newtonianKernel (m + 1)) (x - y) (b j) (b i)| ≤
      (1 / ω) * R ^ (-((m + 1 : ℕ) : ℝ)) * (6 * R) ^ (m + 1) := by
    rw [← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const hVfin (C := (1 / ω) * R ^ (-((m + 1 : ℕ) : ℝ))) fun y hy => ?_).trans
      (mul_le_mul_of_nonneg_left hVv (by positivity))
    rw [Real.norm_eq_abs]
    exact abs_bilinear_newtonianKernel_basis_le_of_le hn hR (le_norm_sub_of_notMem_ball hx hy.2) j i
  -- face part
  have hface : ∀ p, |∫ y, fderiv ℝ (newtonianKernel (m + 1)) (x - y) (b i) * euclideanBoxFaceNormal p y j
      ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)| ≤
      (1 / (((m + 1 : ℕ) : ℝ) * ω)) * (2 * R) ^ ((1:ℝ) - ((m + 1 : ℕ) : ℝ)) * (6 * R) ^ m := by
    intro p
    refine abs_integral_newtonianBox_face_le hR p
      (g := fun y => fderiv ℝ (newtonianKernel (m + 1)) (x - y) (b i) * euclideanBoxFaceNormal p y j)
      (((measurable_fderiv_newtonianKernel_apply hn (b i)).comp (measurable_const.sub measurable_id)).mul
        (measurable_euclideanBoxFaceNormal_apply p j)) fun w => ?_
    beta_reduce
    rw [abs_mul]
    calc _ ≤ (1 / (((m + 1 : ℕ) : ℝ) * ω)) * (2 * R) ^ ((1:ℝ) - ((m + 1 : ℕ) : ℝ)) * 1 :=
          mul_le_mul (abs_fderiv_newtonianKernel_basis_le_of_le hn (by positivity)
            (two_mul_le_norm_sub_newtonianBox_face hR hx p w) i) (abs_euclideanBoxFaceNormal_apply_le _ _ _)
            (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hsum : |∑ p, ∫ y, fderiv ℝ (newtonianKernel (m + 1)) (x - y) (b i) * euclideanBoxFaceNormal p y j
      ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)| ≤
      2 * (m + 1) * ((1 / (((m + 1 : ℕ) : ℝ) * ω)) * (2 * R) ^ ((1:ℝ) - ((m + 1 : ℕ) : ℝ)) * (6 * R) ^ m) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun p _ => hface p).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    push_cast; ring
  have e1 : (1 / ω) * R ^ (-((m + 1 : ℕ) : ℝ)) * (6 * R) ^ (m + 1) = (1 / ω) * 6 ^ (m + 1) := by
    rw [rpow_neg_natCast_eq hR, mul_pow]; field_simp
  have e2 : (2 * R) ^ ((1:ℝ) - ((m + 1 : ℕ) : ℝ)) * (6 * R) ^ m = 3 ^ m := by
    rw [show (1:ℝ) - ((m + 1 : ℕ) : ℝ) = -((m : ℕ) : ℝ) by push_cast; ring, rpow_neg_natCast_eq (by positivity),
      show (6 * R) ^ m = 3 ^ m * (2 * R) ^ m by rw [← mul_pow]; ring_nf]
    field_simp
  unfold newtonianBoxCorrection
  calc _ ≤ |∫ y in V, bilinearIteratedFDerivTwo ℝ (newtonianKernel (m + 1)) (x - y) (b j) (b i)| +
        |∑ p, ∫ y, fderiv ℝ (newtonianKernel (m + 1)) (x - y) (b i) * euclideanBoxFaceNormal p y j
          ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)| := by
        rw [show ∀ u v : ℝ, -u - v = -(u + v) by intros; ring, abs_neg]; exact abs_add_le _ _
    _ ≤ _ := add_le_add hvol hsum
    _ = newtonianBoxCorrectionSupConst m := by
        rw [newtonianBoxCorrectionSupConst, e1, mul_assoc (1 / (((m + 1 : ℕ) : ℝ) * ω)), e2]

/-- `|Â_{ij}(x) − Â_{ij}(z)| ≤ A₁(n) |x − z| / R` on `closedBall c R`. -/
theorem abs_newtonianBoxCorrection_sub_le (hn : 2 ≤ m + 1) (hR : 0 < R) {x z : EuclideanSpace ℝ (Fin (m + 1))}
    (hx : x ∈ closedBall c R) (hz : z ∈ closedBall c R) (i j : Fin (m + 1)) :
    |newtonianBoxCorrection m c R i j x - newtonianBoxCorrection m c R i j z| ≤
      newtonianBoxCorrectionLipConst m * ‖x - z‖ / R := by
  set b := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  set ω := euclideanUnitBallVolume (m + 1)
  have hw : 0 < ω := euclideanUnitBallVolume_pos (m + 1)
  set V := euclideanOpenBox (newtonianBoxLower c R) (newtonianBoxUpper c R) \ ball c (2 * R)
  have hab := newtonianBoxLower_le_upper (c := c) hR
  have hVm : MeasurableSet V := (divergenceAdmissible_euclideanOpenBox hab).isOpen.measurableSet.diff measurableSet_ball
  obtain ⟨hbox, hboxv⟩ := volume_real_newtonianBox (c := c) hR
  have hVfin : volume V < ⊤ := (measure_mono sdiff_subset).trans_lt hbox
  have hVv : (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))).real V ≤ (6 * R) ^ (m + 1) := by
    rw [← hboxv]; exact measureReal_mono sdiff_subset hbox.ne
  set K := fun (u y : EuclideanSpace ℝ (Fin (m + 1))) => bilinearIteratedFDerivTwo ℝ (newtonianKernel (m + 1)) (u - y) (b j) (b i)
  have hKI : ∀ u ∈ closedBall c R, IntegrableOn (K u) V volume := fun u hu =>
    (integrableOn_const (C := (1 / ω) * R ^ (-((m + 1 : ℕ) : ℝ))) hVfin.ne).mono'
      ((measurable_bilinear_newtonianKernel hn (b j) (b i)).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      ((ae_restrict_mem hVm).mono fun y hy => by
        rw [Real.norm_eq_abs]; exact abs_bilinear_newtonianKernel_basis_le_of_le hn hR (le_norm_sub_of_notMem_ball hu hy.2) j i)
  have hvol : |(∫ y in V, K x y) - ∫ y in V, K z y| ≤
      (((m + 1 : ℕ) : ℝ) + 5) / ω * R ^ (-((m + 1 : ℕ) : ℝ) - 1) * ‖x - z‖ * (6 * R) ^ (m + 1) := by
    rw [← integral_sub (hKI x hx) (hKI z hz), ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const hVfin fun y hy => ?_).trans
      (mul_le_mul_of_nonneg_left hVv (by positivity))
    rw [Real.norm_eq_abs]
    exact abs_bilinear_newtonianKernel_sub_le_of_convex hn (convex_closedBall c R) hR
      (fun q hq => le_norm_sub_of_notMem_ball hq hy.2) hx hz j i
  set G := fun (u : EuclideanSpace ℝ (Fin (m + 1))) (p : Fin (m + 1) × Bool) (y : EuclideanSpace ℝ (Fin (m + 1))) =>
    fderiv ℝ (newtonianKernel (m + 1)) (u - y) (b i) * euclideanBoxFaceNormal p y j
  have hGm : ∀ u p, Measurable (G u p) := fun u p =>
    ((measurable_fderiv_newtonianKernel_apply hn (b i)).comp (measurable_const.sub measurable_id)).mul
      (measurable_euclideanBoxFaceNormal_apply p j)
  have hGI : ∀ u ∈ closedBall c R, ∀ p, Integrable (G u p)
      (euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p) := by
    intro u hu p
    have : IsFiniteMeasure (euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p) :=
      ⟨(divergenceAdmissible_euclideanOpenBox hab).finite p⟩
    have hrw : euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p =
        Measure.map (fun w : Fin m → ℝ => WithLp.toLp 2 (p.1.insertNth (α := fun _ => ℝ)
          (if p.2 then newtonianBoxUpper c R p.1 else newtonianBoxLower c R p.1) w))
          (volume.restrict (Icc (newtonianBoxLower c R ∘ p.1.succAbove) (newtonianBoxUpper c R ∘ p.1.succAbove))) := rfl
    refine (integrable_const ((1 / (((m + 1 : ℕ) : ℝ) * ω)) * (2 * R) ^ ((1:ℝ) - ((m + 1 : ℕ) : ℝ)))).mono'
      (hGm u p).aestronglyMeasurable ?_
    rw [hrw, ae_map_iff (continuous_toLp_insertNth _ _).aemeasurable
      (measurableSet_le (hGm u p).norm measurable_const)]
    refine ae_of_all _ fun w => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc _ ≤ (1 / (((m + 1 : ℕ) : ℝ) * ω)) * (2 * R) ^ ((1:ℝ) - ((m + 1 : ℕ) : ℝ)) * 1 :=
          mul_le_mul (abs_fderiv_newtonianKernel_basis_le_of_le hn (by positivity)
            (two_mul_le_norm_sub_newtonianBox_face hR hu p w) i) (abs_euclideanBoxFaceNormal_apply_le _ _ _)
            (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hface : ∀ p, |(∫ y, G x p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)) -
      ∫ y, G z p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)| ≤
      ((m + 1 : ℕ) : ℝ) * ((1 / ω) * (2 * R) ^ (-((m + 1 : ℕ) : ℝ))) * ‖x - z‖ * (6 * R) ^ m := by
    intro p
    rw [← integral_sub (hGI x hx p) (hGI z hz p)]
    refine abs_integral_newtonianBox_face_le hR p (g := fun y => G x p y - G z p y) ((hGm x p).sub (hGm z p)) fun w => ?_
    simp only [G]
    rw [← sub_mul, abs_mul]
    calc _ ≤ ((m + 1 : ℕ) : ℝ) * ((1 / ω) * (2 * R) ^ (-((m + 1 : ℕ) : ℝ))) * ‖x - z‖ * 1 :=
          mul_le_mul (abs_fderiv_newtonianKernel_sub_le_of_convex hn (convex_closedBall c R) (by positivity)
            (fun q hq => two_mul_le_norm_sub_newtonianBox_face hR hq p w) hx hz i)
            (abs_euclideanBoxFaceNormal_apply_le _ _ _) (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hsum : |(∑ p, ∫ y, G x p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)) -
      ∑ p, ∫ y, G z p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)| ≤
      2 * (m + 1) * (((m + 1 : ℕ) : ℝ) * ((1 / ω) * (2 * R) ^ (-((m + 1 : ℕ) : ℝ))) * ‖x - z‖ * (6 * R) ^ m) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun p _ => hface p).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
    push_cast; ring
  have e1 : (((m + 1 : ℕ) : ℝ) + 5) / ω * R ^ (-((m + 1 : ℕ) : ℝ) - 1) * ‖x - z‖ * (6 * R) ^ (m + 1) =
      (((m + 1 : ℕ) : ℝ) + 5) / ω * 6 ^ (m + 1) * ‖x - z‖ / R := by
    rw [show -((m + 1 : ℕ) : ℝ) - 1 = -((m + 2 : ℕ) : ℝ) by push_cast; ring, rpow_neg_natCast_eq hR, mul_pow]
    field_simp; ring
  have e2 : (2 * R) ^ (-((m + 1 : ℕ) : ℝ)) * (6 * R) ^ m = 6 ^ m / 2 ^ (m + 1) / R := by
    rw [rpow_neg_natCast_eq (by positivity), mul_pow, mul_pow]
    field_simp; ring
  have hsplit : newtonianBoxCorrection m c R i j x - newtonianBoxCorrection m c R i j z =
      -((∫ y in V, K x y) - ∫ y in V, K z y) -
        ((∑ p, ∫ y, G x p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)) -
          ∑ p, ∫ y, G z p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)) := by
    unfold newtonianBoxCorrection; ring
  rw [hsplit]
  calc _ ≤ |(∫ y in V, K x y) - ∫ y in V, K z y| +
        |(∑ p, ∫ y, G x p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)) -
          ∑ p, ∫ y, G z p y ∂(euclideanBoxFaceMeasure (newtonianBoxLower c R) (newtonianBoxUpper c R) p)| := by
        rw [show ∀ u v : ℝ, -u - v = -(u + v) by intros; ring, abs_neg]; exact abs_add_le _ _
    _ ≤ _ := add_le_add hvol hsum
    _ = newtonianBoxCorrectionLipConst m * ‖x - z‖ / R := by
        have e3 : ((m + 1 : ℕ) : ℝ) * ((1 / ω) * (2 * R) ^ (-((m + 1 : ℕ) : ℝ))) * ‖x - z‖ * (6 * R) ^ m =
            ((m + 1 : ℕ) : ℝ) * (1 / ω) * ‖x - z‖ * ((2 * R) ^ (-((m + 1 : ℕ) : ℝ)) * (6 * R) ^ m) := by ring
        rw [e1, e3, e2]
        change _ = (((((m + 1 : ℕ) : ℝ) + 5) / ω) * 6 ^ (m + 1) +
          2 * (m + 1) * ((m + 1 : ℕ) * (1 / ω) * (6 ^ m / 2 ^ (m + 1)))) * ‖x - z‖ / R
        field_simp

end Box

end FunctionalInequalities.Analysis
