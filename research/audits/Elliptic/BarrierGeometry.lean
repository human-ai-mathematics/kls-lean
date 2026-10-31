module

public import FunctionalInequalities.Analysis.OrthonormalPair
public import FunctionalInequalities.Analysis.LogRadial.Geometry
public import FunctionalInequalities.Analysis.Elliptic.HalfBall
@[expose] public section

noncomputable section
open scoped RealInnerProductSpace
namespace FunctionalInequalities.Analysis.BarrierGeometryAudit
lemma actual_frame (a b : ℝ) :
    ‖a • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) +
            b • EuclideanSpace.single 1 1‖ ^
        2 =
      a ^ 2 + b ^ 2 := by
  exact
    orthogonal_pair_norm_sq (by simp) (by simp)
      (by rw [EuclideanSpace.inner_single_right]; norm_num) a b
lemma actual_shifted_radius : Real.sqrt (17 : ℝ) ≤ 7 := by
  let z : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![(3 : ℝ), 4]
  have hn2 : ‖x‖ ^ 2 = (5 : ℝ) ^ 2 := by
    norm_num [x, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hn : ‖x‖ = (5 : ℝ) := by nlinarith [norm_nonneg x]
  have h := tangent_normal_radius_le (m := 0) z (by simp [z]) (by norm_num [z, Fin.last]) 2 x
  convert h using 1 <;> norm_num [z, x, hn, Fin.sum_univ_two, Fin.last]
lemma actual_flat_and_curved :
    (0 : EuclideanSpace ℝ (Fin 1)) ∈ frontier {x | ‖x‖ < (1 : ℝ) ∧ 0 < x (Fin.last 0)} ∧
      EuclideanSpace.single 0 (1 : ℝ) ∈
        frontier {x : EuclideanSpace ℝ (Fin 1) | ‖x‖ < 1 ∧ 0 < x (Fin.last 0)} := by
  rw [frontier_halfBall (by norm_num)]
  simp
end FunctionalInequalities.Analysis.BarrierGeometryAudit
#print axioms FunctionalInequalities.Analysis.BarrierGeometryAudit.actual_frame
#print axioms FunctionalInequalities.Analysis.BarrierGeometryAudit.actual_shifted_radius
#print axioms FunctionalInequalities.Analysis.BarrierGeometryAudit.actual_flat_and_curved
