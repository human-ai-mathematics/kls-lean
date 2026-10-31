module

public import FunctionalInequalities.Analysis.Elliptic.Maximum
public import examples.EllipticDrift

/-!
# Clients of the nonsymmetric-coefficient maximum principle

The audit fixture `CNSCoefficientScope` (client-only import) supplies the skew coefficient
`coefficient k = [[1, k], [-k, 1]]`, its quadratic identity `∑ aᵢⱼ xᵢ xⱼ = ‖x‖²`, its trace identity
against
Hermitian matrices, and the `k = 7` counterexample (not positive semidefinite, entry norm `> 1`).

* `skew_coefficient_norm_sq_client`: for an ARBITRARY function `k` on `ℝ²` (no continuity or bound),
  the
  coefficient field `A x = coefficient (k x)`, the nonzero drift `bᵢ(x) = xᵢ` and `u = ‖x‖²` on the
  unit ball: the
  original operator `tr(A D²u) + ∑ bᵢ ∂ᵢu = 4 + 2‖x‖²` is strictly positive, and the new principle
  gives `‖x‖² ≤ 1`.
* `coefficient_seven_symmetric_part_client`: for `k = 7` the symmetric part has elementwise norm `≤
  1`, while the raw
  matrix is not positive semidefinite and has norm `> 1`.
* `fin_zero_constant_client`: the one-point space `ℝ⁰`, `Ω = univ`, `u = 7`, threshold `7`,
  arbitrary coefficients.
* `empty_domain_client`: `Ω = ∅`, every `n`, arbitrary `u`, `A`, `b`, `M`.
* `empty_index_symmetric_part_client`: both matrix statements over the empty index type.
-/

@[expose] public section

noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise

namespace FunctionalInequalities.Analysis.CoefficientMaximumClient

open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
  CNSCoefficientScopeAudit

/-- **Skew coefficients with an arbitrary `k`, nonzero drift, `u = ‖x‖²`.** -/
theorem skew_coefficient_norm_sq_client (k : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ∀ x ∈ closure (ball (0 : EuclideanSpace ℝ (Fin 2)) 1), ‖x‖ ^ 2 ≤ 1 := by
  have hq : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have hH :
    ∀ x : EuclideanSpace ℝ (Fin 2),
      hessianMatrix (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2) x = (2 : ℝ) • 1 :=
    fun x => by
    simpa only [one_mul, sub_zero, mul_one] using hessianMatrix_mul_norm_sub_sq 1 0 x
  have hD :
    ∀ (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2),
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2) x (EuclideanSpace.single i 1) =
        2 * x i :=
    fun x i => by
    rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
    simp [EuclideanSpace.inner_single_right]
  have hherm : ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsHermitian :=
    (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 2)).isHermitian
      -- strict positivity of the ORIGINAL operator, computed before the maximum principle is
      -- applied

  have hL :
    ∀ x : EuclideanSpace ℝ (Fin 2),
      0 <
        Matrix.trace
            (coefficient (k x) *
              hessianMatrix (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2) x) +
          ∑ i,
            x i *
              fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖ ^ 2) x
                (EuclideanSpace.single i 1) := by
    intro x
    rw [hH, trace_identity (k x) _ hherm]
    simp only [hD, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    norm_num
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  exact
    strict_drift_maximum_principle_of_quadratic_nonneg (A := fun x => coefficient (k x)) (b :=
      fun x i => x i) (M := 1) isOpen_ball isBounded_ball hq.contDiffOn
      hq.continuous.continuousOn
      (fun x _ v => by
        have h :
          ∑ i, ∑ j, coefficient (k x) i j * v i * v j =
            ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ ^ 2 :=
          quadratic_identity (k x) (WithLp.toLp 2 v)
        rw [h]
        positivity)
      (fun x _ _ => hL x)
      (fun x hx => by
        have h1 : ‖x‖ ≤ 1 := by
          simpa using closure_ball_subset_closedBall (frontier_subset_closure hx)
        nlinarith [norm_nonneg x])

/-- **`k = 7`**: the symmetric part obeys the quadratic ceiling `1`; the raw matrix does not. -/
theorem coefficient_seven_symmetric_part_client :
    ‖(1 / 2 : ℝ) • (coefficient 7 + (coefficient 7).transpose)‖ ≤ 1 ∧
      ¬ (coefficient 7).PosSemidef ∧ 1 < ‖coefficient 7‖ := by
  have hqf : ∀ v : Fin 2 → ℝ, ∑ i, ∑ j, coefficient 7 i j * v i * v j = ∑ i, (v i) ^ 2 := by
    intro v
    have h : ∑ i, ∑ j, coefficient 7 i j * v i * v j =
        ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ ^ 2 :=
      quadratic_identity 7 (WithLp.toLp 2 v)
    rw [h, EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  exact ⟨norm_symmetricPart_le_of_quadratic_le (coefficient 7) zero_le_one
      (fun v => by rw [hqf]; positivity) (fun v => by rw [hqf, one_mul]),
    elliptic_quadratic_bounds_do_not_bound_original_entries.2⟩

/-- **The one-point space `ℝ⁰`** with arbitrary coefficients. -/
theorem fin_zero_constant_client (A : EuclideanSpace ℝ (Fin 0) → Matrix (Fin 0) (Fin 0) ℝ)
    (b : EuclideanSpace ℝ (Fin 0) → Fin 0 → ℝ) :
    ∀ x ∈ closure (univ : Set (EuclideanSpace ℝ (Fin 0))), (fun _ => (7 : ℝ)) x ≤ 7 :=
  strict_drift_maximum_principle_of_quadratic_nonneg (A := A) (b := b) isOpen_univ
    Set.finite_univ.isBounded contDiffOn_const continuousOn_const (fun _ _ _ => by simp)
    (fun _ _ h => absurd h (lt_irrefl 7))
    (fun _ hx => by rw [frontier_univ] at hx)

/-- **Empty domain**: every `n`, arbitrary `u`, `A`, `b`, `M`. -/
theorem empty_domain_client {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) (M : ℝ) :
    ∀ x ∈ closure (∅ : Set (EuclideanSpace ℝ (Fin n))), u x ≤ M :=
  strict_drift_maximum_principle_of_quadratic_nonneg (A := A) (b := b) isOpen_empty
    Bornology.isBounded_empty contDiffOn_empty (by rw [closure_empty]; exact continuousOn_empty u)
    (fun _ hx => hx.elim) (fun _ hx => hx.elim)
    (fun _ hx => by rw [frontier_empty] at hx; exact hx.elim)

/-- **Empty index type**: both matrix statements, for every matrix over `Empty`. -/
theorem empty_index_symmetric_part_client (A : Matrix Empty Empty ℝ) :
    ((1 / 2 : ℝ) • (A + A.transpose)).PosSemidef ∧ ‖((1 / 2 : ℝ) • (A + A.transpose))‖ ≤ 0 :=
  ⟨(posSemidef_symmetricPart_of_quadratic_nonneg A fun _ => by simp).1,
    norm_symmetricPart_le_of_quadratic_le A le_rfl (fun _ => by simp) (fun _ => by simp)⟩

end FunctionalInequalities.Analysis.CoefficientMaximumClient

#print axioms
  FunctionalInequalities.Analysis.CoefficientMaximumClient.skew_coefficient_norm_sq_client
#print axioms
  FunctionalInequalities.Analysis.CoefficientMaximumClient.coefficient_seven_symmetric_part_client
#print axioms FunctionalInequalities.Analysis.CoefficientMaximumClient.fin_zero_constant_client
#print axioms FunctionalInequalities.Analysis.CoefficientMaximumClient.empty_domain_client
#print axioms
  FunctionalInequalities.Analysis.CoefficientMaximumClient.empty_index_symmetric_part_client
