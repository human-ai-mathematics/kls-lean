import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Poincaré constants (`KLS.pdf`, Definition 2.1)

The reference fixes the normalization
`Var_P(f) ≤ C_P E_P ‖∇f‖²` for smooth real-valued `f ∈ L²(P)`.  This module gives that formula
a machine-safe finite-energy reading on a real Hilbert space.  The Dirichlet energy uses
Mathlib's canonical gradient, and a bridge theorem identifies it with the operator-norm
formulation using the Fréchet derivative.

A candidate Poincaré constant and the Dirichlet energy are real-valued.  The optimal constant is
extended-nonnegative-real-valued, so it is `⊤` exactly when there is no finite valid constant.
The reference also identifies the optimal constant with the reciprocal spectral gap; that
operator-theoretic equivalence is not asserted in this module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]

namespace Poincare

/-- The finite-energy reading of the smooth `f ∈ L²(P)` test class in `KLS.pdf`, Definition 2.1.

The explicit energy-integrability field prevents the real-valued Bochner integral from
totalizing a nonintegrable gradient energy to zero.  This module uses the conventional
finite-energy core; identifying it with a closed Sobolev or spectral-gap definition would be a
separate theorem. -/
structure Admissible (μ : Measure E) (f : E → ℝ) : Prop where
  smooth' : ContDiff ℝ ⊤ f
  memLp_two : MemLp f 2 μ
  energy_integrable : Integrable (fun x ↦ ‖gradient f x‖ ^ 2) μ

/-- The Dirichlet energy `E_P ‖∇f‖²` on the right-hand side of Definition 2.1. -/
def energy (μ : Measure E) (f : E → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

theorem energy_nonneg (μ : Measure E) (f : E → ℝ) :
    0 ≤ energy μ f := by
  exact integral_nonneg fun _ ↦ sq_nonneg _

omit [MeasurableSpace E] in
/-- On a real Hilbert space, the Riesz duality map identifies the norm of the Fréchet derivative
with the norm of Mathlib's canonical gradient. -/
theorem norm_fderiv_eq_norm_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by
  rw [← toDual_gradient]
  exact (InnerProductSpace.toDual ℝ E).norm_map _

/-- The gradient-energy definition agrees with the Fréchet-derivative operator-norm formula. -/
theorem energy_eq_fderiv (μ : Measure E) (f : E → ℝ) :
    energy μ f = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖gradient f x‖ ^ 2 = ‖fderiv ℝ f x‖ ^ 2
    rw [norm_fderiv_eq_norm_gradient]

/-- Lean form of `KLS.pdf`, Definition 2.1: `μ` is a probability measure and every smooth
square-integrable real-valued test function with finite gradient energy satisfies
`Var_μ(f) ≤ C E_μ ‖∇f‖²`.  The nonnegativity of `C` is recorded explicitly. -/
structure Holds (μ : Measure E) (C : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  constant_nonneg : 0 ≤ C
  variance_le : ∀ ⦃f : E → ℝ⦄, Admissible μ f →
    variance f μ ≤ C * energy μ f

namespace Holds

/-- Increasing a valid Poincaré constant preserves the inequality. -/
theorem mono {μ : Measure E} {C C' : ℝ} (h : Holds μ C) (hCC' : C ≤ C') :
    Holds μ C' := by
  refine ⟨h.probability, h.constant_nonneg.trans hCC', ?_⟩
  intro f hf
  exact (h.variance_le hf).trans
    (mul_le_mul_of_nonneg_right hCC' (energy_nonneg μ f))

end Holds

/-- The optimal `C_P` from Definition 2.1, represented as the `ENNReal` infimum of all finite
nonnegative valid constants.  If there is no finite valid constant, the indexing subtype is empty
and the infimum is `⊤`. -/
def constant (μ : Measure E) : ENNReal :=
  ⨅ C : {C : NNReal // Holds μ (C : ℝ)}, (C.1 : ENNReal)

/-- The optimal constant is no larger than any finite valid Poincaré constant. -/
theorem constant_le {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl

/-- To lower-bound the optimal constant, it suffices to lower-bound every finite valid
constant.  This is the direction needed by the linear-test proof. -/
theorem le_constant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, Holds μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ constant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2

theorem constant_eq_top_of_no_finite {μ : Measure E}
    (h : ∀ C : NNReal, ¬ Holds μ (C : ℝ)) :
    constant μ = ⊤ := by
  apply top_unique
  refine le_iInf fun C ↦ ?_
  exact (h C.1 C.2).elim

theorem constant_ne_top_of_holds {μ : Measure E} {C : NNReal}
    (hC : Holds μ (C : ℝ)) :
    constant μ ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (constant_le hC)

/-- The extended optimal constant is infinite exactly when no finite Poincaré inequality holds. -/
theorem constant_eq_top_iff {μ : Measure E} :
    constant μ = ⊤ ↔
      ∀ C : NNReal, ¬ Holds μ (C : ℝ) := by
  constructor
  · intro htop C hC
    exact (constant_ne_top_of_holds hC htop).elim
  · exact constant_eq_top_of_no_finite

end Poincare

end FunctionalInequalities
