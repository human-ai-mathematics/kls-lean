module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped RealInnerProductSpace Topology
namespace LetwinContactDensityAudit
open FunctionalInequalities.Analysis

/-- A genuinely constructed unit-density Dirichlet input; the gain is not
an assumption. Reference C1/convexity/boundary/MA and density bounds are built. -/
theorem unit_quadratic {n : ℕ} (hn : 0 < n) {r δ η : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hη : 0 < η) (hη1 : η < 1) :
    let u := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ)
      (0 : EuclideanSpace ℝ (Fin n)) 0 (-1 / 2)
    ENNReal.ofReal (1 - η) * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) ≤
      volume {x | x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
        ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          u x - ((1 - δ) / 2) * ‖x‖ ^ 2 +
            ⟪gradient u x - (1 - δ) • x, y - x⟫ ≤
              u y - ((1 - δ) / 2) * ‖y‖ ^ 2} := by
  let E := EuclideanSpace ℝ (Fin n)
  let u : E → ℝ := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
  obtain ⟨ε, hε, hε1, hg⟩ := exists_contact_volume_gain_unitBall hn hr hr1 hδ hδ1 hη hη1
  apply hg u (fun _ => 1) (convexOn_quadraticAt Matrix.PosSemidef.one _ _ _)
    ((contDiff_quadraticAt _ _ _ _).of_le (by norm_num)) continuousOn_const
    (fun _ _ => zero_lt_one)
  · intro x hx
    rw [frontier_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hx
    have hnorm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    simp only [u, quadraticAt, sub_zero, inner_zero_left, add_zero,
      Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply,
      real_inner_self_eq_norm_sq, hnorm]
    norm_num
  · intro x _hx
    constructor
    · calc
        (1 - ε) ^ n ≤ (1 : ℝ) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith) n
        _ = 1 := one_pow n
    · calc
        (1 : ℝ) = 1 ^ n := (one_pow n).symm
        _ ≤ (1 + ε) ^ n := pow_le_pow_left₀ zero_le_one (by linarith) n
  · intro G hG _
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 (-1 / 2)
      hG.measurableSet, Matrix.det_one, ENNReal.ofReal_one, one_mul]
    simp

/-- The primitive strictness theorem really specializes to dimension zero. -/
theorem zero_dimensional_strict :
    StrictConvexOn ℝ univ (quadraticAt (1 : Matrix (Fin 0) (Fin 0) ℝ)
      (0 : EuclideanSpace ℝ (Fin 0)) 0 (-1 / 2)) :=
  strictConvexOn_quadraticAt Matrix.PosDef.one _ _ _

/-- The actual gradient formula also constructs the zero-dimensional value. -/
theorem zero_dimensional_gradient :
    gradient (quadraticAt (1 : Matrix (Fin 0) (Fin 0) ℝ)
      (0 : EuclideanSpace ℝ (Fin 0)) 0 (-1 / 2)) 0 = 0 := by
  rw [gradient_quadraticAt Matrix.isHermitian_one]
  simp

end LetwinContactDensityAudit
#print axioms LetwinContactDensityAudit.unit_quadratic

#check FunctionalInequalities.Analysis.strictConvexOn_quadraticAt (n := 0)
#check FunctionalInequalities.Analysis.gradient_quadraticAt (n := 0)
#print axioms FunctionalInequalities.Analysis.exists_contact_volume_gain_unitBall
#print axioms FunctionalInequalities.Analysis.strictConvexOn_quadraticAt
#print axioms FunctionalInequalities.Analysis.gradient_quadraticAt

#print axioms LetwinContactDensityAudit.zero_dimensional_strict
#print axioms LetwinContactDensityAudit.zero_dimensional_gradient
