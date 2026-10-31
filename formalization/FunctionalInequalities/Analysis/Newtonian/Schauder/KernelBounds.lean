module

public import FunctionalInequalities.Analysis.Newtonian.Kernel.Difference
public import FunctionalInequalities.Analysis.Newtonian.Truncation.Error
public import FunctionalInequalities.Analysis.Holder.Cutoff

/-!
# Kernel estimates for the Newtonian Hölder estimate

Estimates for the normalized Newtonian kernel used in Lemma 4.4 of Gilbarg–Trudinger, *Elliptic
Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), pp. 57–59, for `n ≥ 2`:

* `volume_real_ball_eq`, `volume_real_closedBall_eq`: `|B_r(x)| = ω_n r^n`;
* far bounds `|D_ijΓ(q)| ≤ ω_n⁻¹ r^(-n)` and `|D_iΓ(q)| ≤ (n ω_n)⁻¹ r^(1-n)` for `‖q‖ ≥ r > 0`;
* the second derivative of `D_iΓ` and its norm bound, and the mean-value bound
  `|D_iΓ(x - y) - D_iΓ(z - y)| ≤ n ω_n⁻¹ r^(-n) ‖x - z‖` on a convex set kept at distance `r` from
  `y`;
* `abs_bilinear_newtonianKernel_sub_le_of_convex`: the Hessian-entry difference bound transported to
  translated segments.

The generic `norm_le_sum_norm_apply_basisFun` bounds a continuous linear map on `ℝⁿ`
by the sum of its standard-basis values. The real-distance-to-Hölder conversion
`holderOnWith_of_dist_le` is imported from the generic Hölder cutoff family.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace NNReal

namespace FunctionalInequalities.Analysis

section Generic

/--
A continuous linear map on `ℝⁿ` is bounded by the sum of the norms of its values on the standard
basis. -/
theorem norm_le_sum_norm_apply_basisFun {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : EuclideanSpace ℝ (Fin n) →L[ℝ] F) :
    ‖L‖ ≤ ∑ j : Fin n, ‖L (EuclideanSpace.basisFun (Fin n) ℝ j)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun j _ => norm_nonneg _) fun v => ?_
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [EuclideanSpace.basisFun_repr, Real.norm_eq_abs]
  have h := abs_real_inner_le_norm v (EuclideanSpace.basisFun (Fin n) ℝ j)
  rwa [EuclideanSpace.inner_basisFun_real,
    show ‖EuclideanSpace.basisFun (Fin n) ℝ j‖ = 1 by simp, mul_one] at h

end Generic

section Kernel

variable {n : ℕ}

theorem volume_real_ball_eq (hn : 1 ≤ n) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball x r) =
      euclideanUnitBallVolume n * r ^ n := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    nontrivial_of_ne (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)) 0 (by simp)
  rw [measureReal_def, Measure.addHaar_ball _ x hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n), mul_comm]
  rfl

theorem volume_real_closedBall_eq (hn : 1 ≤ n) (x : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (closedBall x r) =
      euclideanUnitBallVolume n * r ^ n := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    nontrivial_of_ne (EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℝ)) 0 (by simp)
  rw [measureReal_def, Measure.addHaar_closedBall _ x hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n), mul_comm]
  rfl

/-- Far bound for every Hessian entry: `|D²Γ(q)(e_i,e_j)| ≤ ω_n⁻¹ r^{−n}` when `|q| ≥ r > 0`. -/
theorem abs_bilinear_newtonianKernel_basis_le_of_le (hn : 2 ≤ n) {q : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hq : r ≤ ‖q‖) (i j : Fin n) :
    |bilinearIteratedFDerivTwo ℝ (newtonianKernel n) q (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      (1 / euclideanUnitBallVolume n) * r ^ (-(n : ℝ)) :=
  (abs_bilinear_newtonianKernel_basis_le hn q (norm_pos_iff.mp (hr.trans_le hq)) i j).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hq (by simp))
      (by have := euclideanUnitBallVolume_pos n; positivity))

/-- Far bound for the first derivative: `|D_iΓ(q)| ≤ (nω_n)⁻¹ r^{1−n}` when `|q| ≥ r > 0`. -/
theorem abs_fderiv_newtonianKernel_basis_le_of_le (hn : 2 ≤ n) {q : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hq : r ≤ ‖q‖) (i : Fin n) :
    |fderiv ℝ (newtonianKernel n) q (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
      (1 / ((n : ℝ) * euclideanUnitBallVolume n)) * r ^ ((1 : ℝ) - n) := by
  have hn1 : (1 : ℝ) - n ≤ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  exact
    (abs_fderiv_newtonianKernel_basis_le hn q (norm_pos_iff.mp (hr.trans_le hq)) i).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hq hn1)
        (by have := euclideanUnitBallVolume_pos n; positivity))

theorem hasFDerivAt_fderiv_newtonianKernel_apply (hn : 2 ≤ n) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ≠ 0) (v : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun p => fderiv ℝ (newtonianKernel n) p v)
      (fderiv ℝ (fun p => fderiv ℝ (newtonianKernel n) p v) q) q := by
  have h : ContDiffAt ℝ 1 (fderiv ℝ (newtonianKernel n)) q :=
    (contDiffAt_newtonianKernel hn q hq 2).fderiv_right (by norm_num)
  exact ((h.differentiableAt one_ne_zero).clm_apply (differentiableAt_const v)).hasFDerivAt

theorem fderiv_fderiv_newtonianKernel_apply (hn : 2 ≤ n) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ≠ 0) (u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun p => fderiv ℝ (newtonianKernel n) p v) q u =
      bilinearIteratedFDerivTwo ℝ (newtonianKernel n) q u v := by
  have h : ContDiffAt ℝ 1 (fderiv ℝ (newtonianKernel n)) q :=
    (contDiffAt_newtonianKernel hn q hq 2).fderiv_right (by norm_num)
  rw [fderiv_clm_apply (h.differentiableAt one_ne_zero) (differentiableAt_const v)]
  simp [bilinearIteratedFDerivTwo]

theorem norm_fderiv_fderiv_newtonianKernel_basis_le (hn : 2 ≤ n) {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ≠ 0) (i : Fin n) :
    ‖fderiv ℝ (fun p => fderiv ℝ (newtonianKernel n) p (EuclideanSpace.basisFun (Fin n) ℝ i))
          q‖ ≤
      n * ((1 / euclideanUnitBallVolume n) * ‖q‖ ^ (-(n : ℝ))) := by
  refine (opNorm_le_sum_abs_basisFun _).trans ?_
  calc
    (∑ l : Fin n,
          |fderiv ℝ
              (fun p => fderiv ℝ (newtonianKernel n) p (EuclideanSpace.basisFun (Fin n) ℝ i)) q
              (EuclideanSpace.basisFun (Fin n) ℝ l)|) ≤
        ∑ _l : Fin n, (1 / euclideanUnitBallVolume n) * ‖q‖ ^ (-(n : ℝ)) := by
      refine Finset.sum_le_sum fun l _ => ?_
      rw [fderiv_fderiv_newtonianKernel_apply hn hq]
      exact abs_bilinear_newtonianKernel_basis_le hn q hq l i
    _ = n * ((1 / euclideanUnitBallVolume n) * ‖q‖ ^ (-(n : ℝ))) := by simp

/-- Mean-value bound for the first derivative on a convex set kept at distance `r` from `y`:
`|D_iΓ(x−y) − D_iΓ(z−y)| ≤ n ω_n⁻¹ r^{−n} |x−z|`. -/
theorem abs_fderiv_newtonianKernel_sub_le_of_convex (hn : 2 ≤ n)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : Convex ℝ s) {y : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hfar : ∀ p ∈ s, r ≤ ‖p - y‖) {x z : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ s) (hz : z ∈ s) (i : Fin n) :
    |fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (newtonianKernel n) (z - y) (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
      n * ((1 / euclideanUnitBallVolume n) * r ^ (-(n : ℝ))) * ‖x - z‖ := by
  set g := fun p => fderiv ℝ (newtonianKernel n) p (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hne : ∀ p ∈ s, p - y ≠ 0 := fun p hp => norm_pos_iff.mp (hr.trans_le (hfar p hp))
  have hd : ∀ p ∈ s, HasFDerivWithinAt (fun p => g (p - y)) (fderiv ℝ g (p - y)) s p := by
    intro p hp
    have h1 :=
      hasFDerivAt_fderiv_newtonianKernel_apply hn (hne p hp)
        (EuclideanSpace.basisFun (Fin n) ℝ i)
    have h2 :
      HasFDerivAt (fun p : EuclideanSpace ℝ (Fin n) => p - y)
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) p :=
      (hasFDerivAt_id p).sub_const y
    have h3 := h1.comp p h2
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3.hasFDerivWithinAt
  have hb :
    ∀ p ∈ s, ‖fderiv ℝ g (p - y)‖ ≤ n * ((1 / euclideanUnitBallVolume n) * r ^ (-(n : ℝ))) := by
    intro p hp
    refine (norm_fderiv_fderiv_newtonianKernel_basis_le hn (hne p hp) i).trans ?_
    have hw := euclideanUnitBallVolume_pos n
    exact
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr (hfar p hp) (by simp))
          (by positivity))
        (Nat.cast_nonneg n)
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb hz hx
  rw [Real.norm_eq_abs] at h
  exact h

/-- A translated segment between points of a convex set stays in the translated set. -/
theorem sub_mem_of_mem_segment_sub {s : Set (EuclideanSpace ℝ (Fin n))} (hs : Convex ℝ s)
    {x z y q : EuclideanSpace ℝ (Fin n)} (hx : x ∈ s) (hz : z ∈ s)
    (hq : q ∈ segment ℝ (x - y) (z - y)) : q + y ∈ s := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
  have he : a • (x - y) + b • (z - y) + y = a • x + b • z := by
    rw [smul_sub, smul_sub,
      show a • x - a • y + (b • z - b • y) + y = a • x + b • z + (y - (a + b) • y) by
        rw [add_smul]; abel,
      hab, one_smul, sub_self, add_zero]
  rw [he]; exact hs hx hz ha hb hab

/--
The segment difference lemma `newtonianKernel_entry_difference_le_of_segment_norm` for Hessian
entries, for two points of a convex set kept at distance `r` from `y`. -/
theorem abs_bilinear_newtonianKernel_sub_le_of_convex (hn : 2 ≤ n)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : Convex ℝ s) {y : EuclideanSpace ℝ (Fin n)}
    {r : ℝ} (hr : 0 < r) (hfar : ∀ p ∈ s, r ≤ ‖p - y‖) {x z : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ s) (hz : z ∈ s) (i j : Fin n) :
    |bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
            (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) -
          bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (z - y)
            (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
      (((n : ℝ) + 5) / euclideanUnitBallVolume n * r ^ (-(n : ℝ) - 1)) * ‖x - z‖ := by
  have h :=
    newtonianKernel_entry_difference_le_of_segment_norm hn (x - y) (z - y) hr
      (fun q hq => by
        have hm := hfar _ (sub_mem_of_mem_segment_sub hs hx hz hq)
        simpa only [add_sub_cancel_right] using hm)
      i j
  rwa [sub_sub_sub_cancel_right] at h

end Kernel

end FunctionalInequalities.Analysis
