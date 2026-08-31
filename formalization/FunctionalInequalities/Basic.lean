import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Basic functional-inequality vocabulary

This module makes explicit a finite-energy interpretation of the manuscript's smooth
real-valued `L²` test-function convention on a real Hilbert space.  The Dirichlet energy uses
Mathlib's canonical gradient, and a bridge theorem identifies it with the operator-norm
formulation using the Fréchet derivative.

A candidate Poincaré constant and the Dirichlet energy are real-valued.  The optimal constant is
extended-nonnegative-real-valued, so it is `⊤` exactly when there is no finite valid constant.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]

/-- `IsAdmissible μ f` is the finite-energy part of the manuscript's smooth `L²` test core.

The explicit energy-integrability field prevents the real-valued Bochner integral from
totalizing a nonintegrable gradient energy to zero.  This module uses the conventional
finite-energy core; identifying it with a closed Sobolev or spectral-gap definition would be a
separate theorem. -/
structure IsAdmissible (μ : Measure E) (f : E → ℝ) : Prop where
  smooth' : ContDiff ℝ ⊤ f
  memLp_two : MemLp f 2 μ
  energy_integrable : Integrable (fun x ↦ ‖gradient f x‖ ^ 2) μ

/-- The canonical gradient Dirichlet energy of a real-valued function. -/
def dirichletEnergy (μ : Measure E) (f : E → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

theorem dirichletEnergy_nonneg (μ : Measure E) (f : E → ℝ) :
    0 ≤ dirichletEnergy μ f := by
  exact integral_nonneg fun _ ↦ sq_nonneg _

omit [MeasurableSpace E] in
/-- On a real Hilbert space, the Riesz duality map identifies the norm of the Fréchet derivative
with the norm of Mathlib's canonical gradient. -/
theorem norm_fderiv_eq_norm_gradient (f : E → ℝ) (x : E) :
    ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by
  rw [← toDual_gradient]
  exact (InnerProductSpace.toDual ℝ E).norm_map _

/-- The gradient-energy definition agrees with the Fréchet-derivative operator-norm formula. -/
theorem dirichletEnergy_eq_fderiv (μ : Measure E) (f : E → ℝ) :
    dirichletEnergy μ f = ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖gradient f x‖ ^ 2 = ‖fderiv ℝ f x‖ ^ 2
    rw [norm_fderiv_eq_norm_gradient]

/-- `HasPoincare μ C` means that `μ` is a probability measure, `C` is nonnegative, and every
smooth square-integrable real-valued test function with finite gradient energy satisfies the
Poincaré inequality with constant `C`. -/
def HasPoincare (μ : Measure E) (C : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ 0 ≤ C ∧
    ∀ ⦃f : E → ℝ⦄, IsAdmissible μ f →
      variance f μ ≤ C * dirichletEnergy μ f

namespace HasPoincare

theorem isProbabilityMeasure {μ : Measure E} {C : ℝ} (h : HasPoincare μ C) :
    IsProbabilityMeasure μ :=
  h.1

theorem constant_nonneg {μ : Measure E} {C : ℝ} (h : HasPoincare μ C) :
    0 ≤ C :=
  h.2.1

theorem variance_le {μ : Measure E} {C : ℝ} (h : HasPoincare μ C)
    {f : E → ℝ} (hf : IsAdmissible μ f) :
    variance f μ ≤ C * dirichletEnergy μ f :=
  h.2.2 hf

/-- Increasing a valid Poincaré constant preserves the inequality. -/
theorem mono {μ : Measure E} {C C' : ℝ} (h : HasPoincare μ C) (hCC' : C ≤ C') :
    HasPoincare μ C' := by
  refine ⟨h.isProbabilityMeasure, h.constant_nonneg.trans hCC', ?_⟩
  intro f hf
  exact (h.variance_le hf).trans
    (mul_le_mul_of_nonneg_right hCC' (dirichletEnergy_nonneg μ f))

end HasPoincare

/-- The optimal Poincaré constant is the infimum, in `ENNReal`, of all finite nonnegative valid
constants.  If there is no finite valid constant, the indexing subtype is empty and the infimum
is `⊤`. -/
def optimalPoincareConstant (μ : Measure E) : ENNReal :=
  ⨅ C : {C : NNReal // HasPoincare μ (C : ℝ)}, (C.1 : ENNReal)

/-- The optimal constant is no larger than any finite valid Poincaré constant. -/
theorem optimalPoincareConstant_le {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≤ (C : ENNReal) := by
  exact iInf_le_of_le ⟨C, hC⟩ le_rfl

/-- To lower-bound the optimal constant, it suffices to lower-bound every finite valid
constant.  This is the direction needed by the linear-test proof. -/
theorem le_optimalPoincareConstant {μ : Measure E} {L : ENNReal}
    (hL : ∀ C : NNReal, HasPoincare μ (C : ℝ) → L ≤ (C : ENNReal)) :
    L ≤ optimalPoincareConstant μ := by
  refine le_iInf fun C ↦ ?_
  exact hL C.1 C.2

theorem optimalPoincareConstant_eq_top_of_no_finite {μ : Measure E}
    (h : ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ = ⊤ := by
  apply top_unique
  refine le_iInf fun C ↦ ?_
  exact (h C.1 C.2).elim

theorem optimalPoincareConstant_ne_top_of_hasPoincare {μ : Measure E} {C : NNReal}
    (hC : HasPoincare μ (C : ℝ)) :
    optimalPoincareConstant μ ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (optimalPoincareConstant_le hC)

/-- The extended optimal constant is infinite exactly when no finite Poincaré inequality holds. -/
theorem optimalPoincareConstant_eq_top_iff {μ : Measure E} :
    optimalPoincareConstant μ = ⊤ ↔
      ∀ C : NNReal, ¬ HasPoincare μ (C : ℝ) := by
  constructor
  · intro htop C hC
    exact (optimalPoincareConstant_ne_top_of_hasPoincare hC htop).elim
  · exact optimalPoincareConstant_eq_top_of_no_finite

end FunctionalInequalities
