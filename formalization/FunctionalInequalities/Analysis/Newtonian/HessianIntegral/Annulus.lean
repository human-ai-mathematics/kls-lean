module

public import FunctionalInequalities.Analysis.Newtonian.Kernel.Measurable
public import FunctionalInequalities.Analysis.Newtonian.Kernel.Trace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Annular cancellation of the Newtonian kernel Hessian

For `n ≥ 2` and `0 < r`, the Hessian entries `D_ijΓ` of the kernel of Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), (2.12):

* `integrableOn_bilinear_newtonianKernel_annulus`: are integrable on the annulus `r < ‖z‖ < R`;
* `integral_bilinear_newtonianKernel_annulus_eq_zero`: have integral zero over it. Off-diagonal
  entries
  vanish by a coordinate sign flip; diagonal entries are equal by coordinate symmetry and sum to
  zero
  by harmonicity.

This exact cancellation replaces the boundary integral over a sphere in the proof of Lemma 4.4
(pp. 57–59).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

theorem integrableOn_bilinear_newtonianKernel_annulus {n : ℕ} (hn : 2 ≤ n) {r R : ℝ}
    (hr : 0 < r) (i j : Fin n) :
    IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin n) =>
        bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j))
      {z | r < ‖z‖ ∧ ‖z‖ < R} volume := by
  let A : Set (EuclideanSpace ℝ (Fin n)) := {z | r < ‖z‖ ∧ ‖z‖ < R}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hsub : A ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro z hz
    simpa only [mem_ball, dist_zero_right] using hz.2
  have hμ : (volume : Measure (EuclideanSpace ℝ (Fin n))) A < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) measure_ball_lt_top
  have hI :
    IntegrableOn
      (fun _ : EuclideanSpace ℝ (Fin n) => (1 / euclideanUnitBallVolume n) * r ^ (-(n : ℝ))) A
      volume :=
    integrableOn_const hμ.ne
  refine hI.mono' (measurable_bilinear_newtonianKernel hn _ _).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hA] with z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans hz.1)
  rw [Real.norm_eq_abs]
  exact
    (abs_bilinear_newtonianKernel_basis_le hn z hz0 i j).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr hz.1.le (neg_nonpos.mpr (Nat.cast_nonneg n)))
        (le_of_lt (one_div_pos.mpr (euclideanUnitBallVolume_pos n))))

private def coordinateSignFlip {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin n =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

private theorem diagonal_annulus_integral_eq {n : ℕ} (hn : 2 ≤ n) {r R : ℝ} (hr : 0 < r)
    (i j : Fin n) :
    (∫ z in {z : EuclideanSpace ℝ (Fin n) | r < ‖z‖ ∧ ‖z‖ < R},
        bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      ∫ z in {z : EuclideanSpace ℝ (Fin n) | r < ‖z‖ ∧ ‖z‖ < R},
        bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ j)
          (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  let A : Set (EuclideanSpace ℝ (Fin n)) := {z | r < ‖z‖ ∧ ‖z‖ < R}
  let S : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  let K (a : Fin n) (z : EuclideanSpace ℝ (Fin n)) :=
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ a)
      (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hfun : (fun z => A.indicator (K i) (S z)) = A.indicator (K j) := by
    funext z
    have hmem : S z ∈ A ↔ z ∈ A := by simp only [A, mem_ofPred_eq, S.norm_map]
    by_cases hz : z ∈ A
    · rw [indicator_of_mem (hmem.mpr hz), indicator_of_mem hz]
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans hz.1)
      have hS0 : S z ≠ 0 := norm_pos_iff.mp (by rw [S.norm_map]; exact norm_pos_iff.mpr hz0)
      have hcoord : (S z) i = z j := by
        simp [S, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
      have hii :
        ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ i⟫ = (1 : ℝ) := by
        simp
      have hjj :
        ⟪EuclideanSpace.basisFun (Fin n) ℝ j, EuclideanSpace.basisFun (Fin n) ℝ j⟫ = (1 : ℝ) := by
        simp
      dsimp only [K]
      rw [bilinear_newtonianKernel hn (S z) _ _ hS0, bilinear_newtonianKernel hn z _ _ hz0,
        S.norm_map, hii, hjj]
      simp only [EuclideanSpace.inner_basisFun_real, hcoord]
    · rw [indicator_of_notMem (fun h => hz (hmem.mp h)), indicator_of_notMem hz]
  have h :=
    S.measurePreserving.integral_comp S.toHomeomorph.measurableEmbedding (A.indicator (K i))
  rw [hfun, integral_indicator hA, integral_indicator hA] at h
  exact h.symm

private theorem offdiag_annulus_integral_eq_zero {n : ℕ} (hn : 2 ≤ n) {r R : ℝ} (hr : 0 < r)
    (i j : Fin n) (hij : i ≠ j) :
    (∫ z in {z : EuclideanSpace ℝ (Fin n) | r < ‖z‖ ∧ ‖z‖ < R},
        bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      0 := by
  let A : Set (EuclideanSpace ℝ (Fin n)) := {z | r < ‖z‖ ∧ ‖z‖ < R}
  let S := coordinateSignFlip i
  let K (z : EuclideanSpace ℝ (Fin n)) :=
    bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_lt continuous_norm.measurable measurable_const)
  have hfun : (fun z => A.indicator K (S z)) = fun z => -(A.indicator K z) := by
    funext z
    have hmem : S z ∈ A ↔ z ∈ A := by simp only [A, mem_ofPred_eq, S.norm_map]
    by_cases hz : z ∈ A
    · rw [indicator_of_mem (hmem.mpr hz), indicator_of_mem hz]
      have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans hz.1)
      have hS0 : S z ≠ 0 := norm_pos_iff.mp (by rw [S.norm_map]; exact norm_pos_iff.mpr hz0)
      have hci : (S z) i = -(z i) := by simp [S, coordinateSignFlip]
      have hcj : (S z) j = z j := by simp [S, coordinateSignFlip, hij.symm]
      have hδ :
        ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ j⟫ = (0 : ℝ) :=
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.inner_eq_zero hij
      dsimp only [K]
      rw [bilinear_newtonianKernel hn (S z) _ _ hS0, bilinear_newtonianKernel hn z _ _ hz0,
        S.norm_map]
      rw [hδ]
      simp only [EuclideanSpace.inner_basisFun_real, hci, hcj]
      ring
    · rw [indicator_of_notMem (fun h => hz (hmem.mp h)), indicator_of_notMem hz, neg_zero]
  have h := S.measurePreserving.integral_comp S.toHomeomorph.measurableEmbedding (A.indicator K)
  rw [hfun, integral_neg, integral_indicator hA] at h
  linarith

/-- Exact spherical-annulus cancellation of every actual Newtonian Hessian entry. -/
theorem integral_bilinear_newtonianKernel_annulus_eq_zero {n : ℕ} (hn : 2 ≤ n) {r R : ℝ}
    (hr : 0 < r) (i j : Fin n) :
    (∫ z in {z : EuclideanSpace ℝ (Fin n) | r < ‖z‖ ∧ ‖z‖ < R},
        bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      0 := by
  by_cases hij : i = j
  · subst j
    let A : Set (EuclideanSpace ℝ (Fin n)) := {z | r < ‖z‖ ∧ ‖z‖ < R}
    let K (j : Fin n) (z : EuclideanSpace ℝ (Fin n)) :=
      bilinearIteratedFDerivTwo ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ j)
        (EuclideanSpace.basisFun (Fin n) ℝ j)
    have hA : MeasurableSet A :=
      (measurableSet_lt measurable_const continuous_norm.measurable).inter
        (measurableSet_lt continuous_norm.measurable measurable_const)
    have h0 : (∫ z in A, ∑ j : Fin n, K j z) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem hA] with z hz
      exact
        sum_bilinear_newtonianKernel_basis_self_eq_zero hn z (norm_pos_iff.mp (hr.trans hz.1))
    rw [integral_finsetSum Finset.univ
        (fun j _ => integrableOn_bilinear_newtonianKernel_annulus hn hr j j)] at h0
    have hd (j : Fin n) : (∫ z in A, K j z) = ∫ z in A, K i z :=
      diagonal_annulus_integral_eq hn hr j i
    change (∑ j : Fin n, ∫ z in A, K j z) = 0 at h0
    simp_rw [hd] at h0
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h0
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    exact (mul_eq_zero.mp h0).resolve_left hn0
  · exact offdiag_annulus_integral_eq_zero hn hr i j hij

end FunctionalInequalities.Analysis
