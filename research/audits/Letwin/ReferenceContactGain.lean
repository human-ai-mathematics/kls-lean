module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped RealInnerProductSpace Topology ENNReal
namespace ReferenceContactGainAudit
open FunctionalInequalities.Analysis
/-- Actual quadratic unit-MA reference, positive Hessian, zero boundary and
unknown solution data constructed before applying the general compact gain. -/
theorem actual_quadratic_gain {n : ℕ} (hn : 0 < n) {r δ η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) (hη1 : η < 1) :
    let q :=
      quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : EuclideanSpace ℝ (Fin n)) 0 (-1 / 2)
    ENNReal.ofReal (1 - η) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤
      volume
        {x |
          x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
            ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
              q x - (1 - δ) * q x + ⟪gradient q x - (1 - δ) • gradient q x, y - x⟫ ≤
                q y - (1 - δ) * q y} := by
  let E := EuclideanSpace ℝ (Fin n)
  let q : E → ℝ := quadraticAt 1 0 0 (-1 / 2)
  have hv : ContDiff ℝ 2 q := contDiff_quadraticAt _ _ _ _
  have hc : StrictConvexOn ℝ univ q := strictConvexOn_quadraticAt Matrix.PosDef.one _ _ _
  have hv1 : ContDiff ℝ 1 q := hv.of_le (by norm_num)
  have hqgradient : gradient q = (fun x : E => x) := by
    funext x
    dsimp [q]
    rw [gradient_quadraticAt Matrix.isHermitian_one]
    simp [Matrix.toEuclideanLin]
  have hPD : ∀ x ∈ ball (0 : E) 1, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ q x z z := by
    intro x _ z hz
    rw [BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator hv]
    change 0 < ⟪(fderiv ℝ (gradient q) x) z, z⟫
    rw [hqgradient]
    simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
      sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hv0 : ∀ x ∈ frontier (ball (0 : E) 1), q x = 0 := by
    intro x hx
    rw [frontier_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hx
    have hnorm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    simp only [q, quadraticAt, sub_zero, inner_zero_left, add_zero, Matrix.toEuclideanLin,
      Matrix.toLpLin_one, LinearMap.id_apply, real_inner_self_eq_norm_sq, hnorm]
    norm_num
  have hMAv :
    ∀ H : Set E, IsOpen H → H ⊆ ball (0 : E) 1 → volume (subgradientImage q H) = volume H := by
    intro H hH _
    dsimp [q]
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 (-1 / 2)
        hH.measurableSet,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
  have hGc : IsCompact (closure (ball (0 : E) r)) := by
    rw [closure_ball (0 : E) (ne_of_gt hr)]
    exact isCompact_closedBall _ _
  have hGO : closure (ball (0 : E) r) ⊆ ball (0 : E) 1 := by
    rw [closure_ball (0 : E) (ne_of_gt hr)]
    exact closedBall_subset_ball hr1
  obtain ⟨ε, hε, hε1, hg⟩ :=
    exists_contact_volume_gain_of_posDef_reference hn hc hv isOpen_ball isBounded_ball hv0 hPD
      hMAv isOpen_ball hGc hGO hδ hδ1 hη hη1
  apply hg q (fun _ => 1) hc.convexOn hv1 continuousOn_const (fun _ _ => zero_lt_one) hv0
  · intro x _
    constructor
    · calc
        (1 - ε) ^ n ≤ (1 : ℝ) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
        _ = 1 := one_pow n
    · calc
        (1 : ℝ) = 1 ^ n := (one_pow n).symm
        _ ≤ (1 + ε) ^ n := pow_le_pow_left₀ zero_le_one (by linarith) n
  · intro H hH hHO
    rw [hMAv H hH hHO]
    simp
end ReferenceContactGainAudit
#print axioms ReferenceContactGainAudit.actual_quadratic_gain

namespace ReferenceContactGainAudit
open FunctionalInequalities.Analysis
/-- The generic shared subgradient lemma really includes dimension zero. -/
theorem zero_dimensional_subgradient :
    (0 : EuclideanSpace ℝ (Fin 0)) =
      gradient (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) 0 := by
  apply subgradient_eq_gradient (differentiableAt_const (0 : ℝ))
  intro y
  simp
/-- The old generic private tangent-support type is retained by an actual
client of the shared increment theorem, without finite-dimensional hypotheses. -/
theorem legacy_tangent_type {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ}
    (hc : ConvexOn ℝ univ u) {x : E} (hx : DifferentiableAt ℝ u x) (y : E) :
    u x + ⟪gradient u x, y - x⟫ ≤ u y := by
  have ht := gradient_le_increment hc x (y - x) hx
  rw [add_sub_cancel] at ht
  linarith
end ReferenceContactGainAudit
#print axioms ReferenceContactGainAudit.zero_dimensional_subgradient
#print axioms FunctionalInequalities.Analysis.subgradient_eq_gradient
#print axioms FunctionalInequalities.Analysis.exists_inverse_subgradient_volume_bounds

#print axioms ReferenceContactGainAudit.legacy_tangent_type
