import FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative
import FunctionalInequalities.Analysis.Convex.Legendre
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: the first variation of the Legendre transform on real clients

Source: Cordero-Erausquin–Klartag, arXiv:1304.0630v1, (42) (pointwise form), the moment-map prerequisite of Letwin,
arXiv:2607.24164v1, Theorem 2.5. Real clients with every premise derived:

* the interval potential `0` on `[−1, 1]` and `⊤` outside (infinite exterior, nondifferentiable at the boundary) has
  conjugate `|y|` (`DirectVariationBoundaryClient.interval_conjugate`), and the bounded continuous, non-`C¹` perturbation
  `min |z| 1` gives the derivative `−1` at `y = 1`;
* the constant potential `−3` on the zero-dimensional space with perturbation `−2` gives the derivative `2` (signed, `Fin 0`).

Both invoke `hasDerivAt_legendre_add_smul_of_dualDifferentiable`. Not a source-law Euler–Lagrange, push-forward or
moment-map client. Client bodies: strong-API constructions (reviewed; revalidated literal sources `IntervalConjugate`,
`VariationInputs`, `VariationClients`), verbatim up to the namespace `KLSConstruction.API.FirstVariation.BoundaryClient` →
`DirectVariationBoundaryClient`.
-/

noncomputable section

section BoundaryClient

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set

namespace DirectVariationBoundaryClient

/-- The actual bounded-domain potential, including its infinite exterior. -/
def intervalPotential (x : ℝ) : EReal := if x ∈ Icc (-1 : ℝ) 1 then 0 else ⊤

/-- Actual conjugate computation for the nondifferentiable/boundary consumer
of the dual-only identification argument from Berman--Berndtsson
arXiv:1207.6128v1 Lemma 2.7, used in CEK arXiv:1304.0630v1 first variation.
No selected maximizer, supplied conjugate identity or global primal-finiteness
assumption is substituted for this actual iSup calculation. -/
theorem interval_conjugate (y : ℝ) :
    FunctionalInequalities.Analysis.legendre intervalPotential y = ((|y| : ℝ) : EReal) := by
    unfold FunctionalInequalities.Analysis.legendre
    apply le_antisymm
    · apply iSup_le
      intro x
      by_cases hx : x ∈ Icc (-1 : ℝ) 1
      · simp only [intervalPotential, if_pos hx, sub_zero, Real.inner_apply]
        apply EReal.coe_le_coe_iff.mpr
        by_cases hy : 0 ≤ y
        · rw [abs_of_nonneg hy]
          have h := mul_le_mul_of_nonneg_right hx.2 hy
          simpa using h
        · have hy' : y ≤ 0 := le_of_not_ge hy
          rw [abs_of_nonpos hy']
          have h := mul_le_mul_of_nonpos_right hx.1 hy'
          simpa using h
      · simp only [intervalPotential, if_neg hx, EReal.sub_top]
        exact bot_le
    · by_cases hy : 0 ≤ y
      · calc
          ((|y| : ℝ) : EReal) =
              (↑(inner ℝ (1 : ℝ) y) : EReal) - intervalPotential 1 := by
                norm_num [intervalPotential, Real.inner_apply, abs_of_nonneg hy]
          _ ≤ ⨆ x : ℝ, (↑(inner ℝ x y) : EReal) - intervalPotential x :=
            le_iSup (fun x : ℝ =>
              (↑(inner ℝ x y) : EReal) - intervalPotential x) 1
      · have hy' : y ≤ 0 := le_of_not_ge hy
        calc
          ((|y| : ℝ) : EReal) =
              (↑(inner ℝ (-1 : ℝ) y) : EReal) - intervalPotential (-1) := by
                norm_num [intervalPotential, Real.inner_apply, abs_of_nonpos hy']
          _ ≤ ⨆ x : ℝ, (↑(inner ℝ x y) : EReal) - intervalPotential x :=
            le_iSup (fun x : ℝ =>
              (↑(inner ℝ x y) : EReal) - intervalPotential x) (-1)

end DirectVariationBoundaryClient

end BoundaryClient

section Inputs

open Set Filter
open scoped Topology
open FunctionalInequalities.Analysis
open DirectVariationBoundaryClient

namespace DirectVariationInputs

abbrev E0 := EuclideanSpace ℝ (Fin 0)
def negativePotential (_ : E0) : EReal := ((-3 : ℝ) : EReal)
def negativePerturbation (_ : E0) : ℝ := -2

theorem negative_proper : ProperPotential negativePotential :=
  ⟨fun _ => EReal.coe_ne_bot _, 0, EReal.coe_ne_top _⟩
theorem negative_lsc : LowerSemicontinuous negativePotential := lowerSemicontinuous_const
theorem negative_continuous : Continuous negativePerturbation := continuous_const
theorem negative_bounded : BddAbove (range fun z : E0 => |negativePerturbation z|) := by
  refine ⟨2, ?_⟩
  rintro _ ⟨z, rfl⟩
  norm_num [negativePerturbation]
theorem negative_dual_constant (q : E0) : legendre negativePotential q = ((3 : ℝ) : EReal) := by
  rw [show q = 0 from Subsingleton.elim _ _]
  simp [legendre, negativePotential]
theorem negative_dual_domain : {q : E0 | legendre negativePotential q ≠ ⊤} = univ := by
  apply eq_univ_of_forall
  intro q
  rw [mem_ofPred_eq, negative_dual_constant]
  exact EReal.coe_ne_top _
theorem negative_dual_differentiable :
    DifferentiableAt ℝ (fun q : E0 => (legendre negativePotential q).toReal) 0 := by
  simpa only [negative_dual_constant, EReal.toReal_coe] using
    (differentiableAt_const (c := (3 : ℝ)) : DifferentiableAt ℝ (fun _ : E0 => (3 : ℝ)) 0)

def clippedAbs (z : ℝ) : ℝ := min |z| 1
theorem clippedAbs_continuous : Continuous clippedAbs := continuous_abs.min continuous_const
theorem clippedAbs_nonneg (z : ℝ) : 0 ≤ clippedAbs z :=
  le_min (abs_nonneg z) (by norm_num)
theorem clippedAbs_abs_bound (z : ℝ) : |clippedAbs z| ≤ 1 := by
  rw [abs_of_nonneg (clippedAbs_nonneg z)]
  exact min_le_right _ _
theorem clippedAbs_bounded : BddAbove (range fun z : ℝ => |clippedAbs z|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact clippedAbs_abs_bound z
theorem clippedAbs_one : clippedAbs 1 = 1 := by norm_num [clippedAbs]
theorem clippedAbs_not_differentiable_zero : ¬ DifferentiableAt ℝ clippedAbs 0 := by
  have heq : clippedAbs =ᶠ[𝓝 (0 : ℝ)] (abs : ℝ → ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hz' : |z| ≤ 1 := le_of_lt (by
      simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz)
    exact min_eq_left hz'
  intro h
  exact not_differentiableAt_abs_zero (h.congr_of_eventuallyEq heq.symm)
theorem clippedAbs_not_C1 : ¬ ContDiff ℝ 1 clippedAbs := by
  intro h
  exact clippedAbs_not_differentiable_zero (h.differentiable (by norm_num)).differentiableAt

theorem interval_proper : ProperPotential intervalPotential := by
  constructor
  · intro x
    simp only [intervalPotential]
    split <;> simp
  · exact ⟨0, by norm_num [intervalPotential]⟩
theorem interval_lsc : LowerSemicontinuous intervalPotential := by
  intro x y hy
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hy0 : y < (0 : EReal) := by simpa [intervalPotential, hx] using hy
    filter_upwards [] with x'
    by_cases hx' : x' ∈ Icc (-1 : ℝ) 1
    · simpa [intervalPotential, hx'] using hy0
    · rw [intervalPotential, if_neg hx']
      exact hy0.trans (EReal.coe_lt_top 0)
  · filter_upwards [isOpen_compl_iff.mpr isClosed_Icc |>.mem_nhds hx] with x' hx'
    have hx' : x' ∉ Icc (-1 : ℝ) 1 := by simpa using hx'
    simpa [intervalPotential, hx, hx'] using hy
theorem interval_dual_domain : {q : ℝ | legendre intervalPotential q ≠ ⊤} = univ := by
  apply eq_univ_of_forall
  intro q
  rw [mem_ofPred_eq, interval_conjugate]
  exact EReal.coe_ne_top _
theorem interval_dual_differentiable_one :
    DifferentiableAt ℝ (fun q : ℝ => (legendre intervalPotential q).toReal) 1 := by
  simpa only [interval_conjugate, EReal.toReal_coe] using
    differentiableAt_abs_pos (by norm_num : (0 : ℝ) < 1)
theorem interval_gradient_one :
    gradient (fun q : ℝ => (legendre intervalPotential q).toReal) 1 = 1 := by
  rw [show (fun q : ℝ => (legendre intervalPotential q).toReal) = fun q => |q| by
    funext q
    rw [interval_conjugate, EReal.toReal_coe]]
  rw [gradient_eq_deriv, deriv_abs_pos (by norm_num), map_one]
theorem interval_boundary_and_infinite_exterior :
    intervalPotential 1 = 0 ∧ intervalPotential 2 = ⊤ := by
  norm_num [intervalPotential]

end DirectVariationInputs

end Inputs

section Clients

open Set
open FunctionalInequalities.Analysis DirectVariationInputs
open DirectVariationBoundaryClient

namespace DirectVariationClients

theorem signed_negative_zero_dimension_actual_derivative :
    HasDerivAt
      (fun t : ℝ =>
        (legendre (fun z : E0 => negativePotential z +
          ((t * negativePerturbation z : ℝ) : EReal)) 0).toReal)
      2 0 := by
  have hy : (0 : E0) ∈ interior {q : E0 | legendre negativePotential q ≠ ⊤} := by
    rw [negative_dual_domain, interior_univ]
    exact mem_univ 0
  have h := hasDerivAt_legendre_add_smul_of_dualDifferentiable
    negativePotential negative_proper negative_lsc 0 hy negative_dual_differentiable
    negativePerturbation negative_continuous negative_bounded
  simpa only [negativePerturbation, neg_neg] using h

theorem boundary_infinite_primal_nonsmooth_bounded_perturbation :
    intervalPotential 2 = ⊤ ∧
      gradient (fun q : ℝ => (legendre intervalPotential q).toReal) 1 = 1 ∧
      ¬ ContDiff ℝ 1 clippedAbs ∧
      HasDerivAt
        (fun t : ℝ =>
          (legendre (fun z : ℝ => intervalPotential z +
            ((t * clippedAbs z : ℝ) : EReal)) 1).toReal)
        (-1) 0 := by
  have hy : (1 : ℝ) ∈ interior {q : ℝ | legendre intervalPotential q ≠ ⊤} := by
    rw [interval_dual_domain, interior_univ]
    exact mem_univ 1
  have h := hasDerivAt_legendre_add_smul_of_dualDifferentiable
    intervalPotential interval_proper interval_lsc 1 hy interval_dual_differentiable_one
    clippedAbs clippedAbs_continuous clippedAbs_bounded
  refine ⟨interval_boundary_and_infinite_exterior.2, interval_gradient_one,
    clippedAbs_not_C1, ?_⟩
  simpa only [interval_gradient_one, clippedAbs_one] using h

end DirectVariationClients

end Clients

#print axioms FunctionalInequalities.Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay
#print axioms FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient
#print axioms FunctionalInequalities.Analysis.exists_coercive_tilt_of_mem_interior_legendre_domain
#print axioms FunctionalInequalities.Analysis.tiltedObjective_data
#print axioms FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity
#print axioms FunctionalInequalities.Analysis.legendre_bounded_perturbation
#print axioms FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve
#print axioms FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt
#print axioms FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable
#print axioms DirectVariationBoundaryClient.interval_conjugate
#print axioms DirectVariationClients.signed_negative_zero_dimension_actual_derivative
#print axioms DirectVariationClients.boundary_infinite_primal_nonsmooth_bounded_perturbation
