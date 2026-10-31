module

public import FunctionalInequalities.Analysis.Elliptic.Maximum
@[expose] public section

noncomputable section
open Set MeasureTheory Filter Metric
open scoped RealInnerProductSpace Topology
namespace LinearizedMaximumClient
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

private lemma quad_value (x : EuclideanSpace ℝ (Fin 1)) :
    quadraticAt 1 0 0 (-1 / 2) x = (‖x‖ ^ 2 - 1) / 2 := by
  have hI : Matrix.toEuclideanLin (1 : Matrix (Fin 1) (Fin 1) ℝ) x = x := by
    exact
      congrArg (fun L : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) => L x)
        (Matrix.toLpLin_one 2)
  simp only [quadraticAt, sub_zero, inner_zero_left, add_zero, hI, real_inner_self_eq_norm_sq]
  ring

/-- Actual quadratic data invoke BOTH new analytic results, including the sharp C0 barrier. -/
theorem quadratic_interval_actual :
    let u : EuclideanSpace ℝ (Fin 1) → ℝ := quadraticAt 1 0 0 (-1 / 2)
    ∀ x ∈ closure (ball (0 : EuclideanSpace ℝ (Fin 1)) 1),
      u x ≤ 0 ∧ |u x| ≤ (1 / 2 : ℝ) * (1 - ‖x‖ ^ 2) := by
  dsimp only
  let u : EuclideanSpace ℝ (Fin 1) → ℝ := quadraticAt 1 0 0 (-1 / 2)
  let D : Set (EuclideanSpace ℝ (Fin 1)) := ball 0 1
  have hC : ContDiff ℝ 2 u := contDiff_quadraticAt 1 0 0 (-1 / 2)
  have hH : ∀ x, hessianMatrix u x = 1 := fun x =>
    hessianMatrix_quadraticAt (by simp) 0 0 (-1 / 2) x
  have hz : ∀ x ∈ frontier D, u x = 0 := by
    intro x hx
    have hn : ‖x‖ = 1 := by simpa [D, frontier_ball, mem_sphere, dist_eq_norm] using hx
    dsimp only [u]
    rw [quad_value, hn]
    norm_num
  have ha :
    ∀ x ∈ D,
      (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef ∧ 0 < (1 : Matrix (Fin 1) (Fin 1) ℝ).trace := by
    intros; exact ⟨Matrix.PosSemidef.one, by simp⟩
  have hL : ∀ x ∈ D, 0 ≤ Matrix.trace ((1 : Matrix (Fin 1) (Fin 1) ℝ) * hessianMatrix u x) := by
    intros x hx
    simp [hH]
  have hm :=
    linearized_maximum_principle isOpen_ball isBounded_ball hC.contDiffOn
      hC.continuous.continuousOn ha hL (fun x hx => (hz x hx).le)
  have hb :=
    abs_le_linearized_c0_barrier (Ω := D) (u := u) (A := fun _ =>
      (1 : Matrix (Fin 1) (Fin 1) ℝ)) (c := 0) (R := 1) (B := 0) (F := 1) (τ := 1) isOpen_ball
      isBounded_ball (by exact closure_minimal ball_subset_closedBall isClosed_closedBall)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hC.contDiffOn
      hC.continuous.continuousOn (by intros; exact ⟨Matrix.PosSemidef.one, by simp⟩)
      (by intros; simp [hH]) (by intros x hx; rw [hz x hx]; norm_num)
  intro x hx
  exact ⟨hm x hx, by simpa using hb x hx⟩

/-- The genuine empty Fin0 domain satisfies both sources; no nonempty trace or mass claim. -/
theorem finZero_empty_actual (u : EuclideanSpace ℝ (Fin 0) → ℝ) :
    ∀ x ∈ closure (∅ : Set (EuclideanSpace ℝ (Fin 0))), u x ≤ 7 ∧ |u x| ≤ (0 : ℝ) := by
  have hm :=
    linearized_maximum_principle (Ω := ∅) (u := u) (A := fun _ =>
      (0 : Matrix (Fin 0) (Fin 0) ℝ)) (M := 7) isOpen_empty Bornology.isBounded_empty
      contDiffOn_empty (by simpa only [closure_empty] using continuousOn_empty u) (by simp)
      (by simp) (by simp)
  have hb :=
    abs_le_linearized_c0_barrier (Ω := ∅) (u := u) (A := fun _ =>
      (0 : Matrix (Fin 0) (Fin 0) ℝ)) (c := 0) (R := 0) (B := 0) (F := 0) (τ := 1) isOpen_empty
      Bornology.isBounded_empty (by simp) le_rfl le_rfl le_rfl zero_lt_one contDiffOn_empty
      (by simpa only [closure_empty] using continuousOn_empty u) (by simp) (by simp) (by simp)
  intro x hx
  exact ⟨hm x hx, by simpa using hb x hx⟩


#print axioms LinearizedMaximumClient.quadratic_interval_actual
#print axioms LinearizedMaximumClient.finZero_empty_actual
end LinearizedMaximumClient
