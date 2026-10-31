module

public import Mathlib

/-!
# Palomar challenge: the dimension-free KLS bound (smooth compactly supported tests)

This is the complete trusted statement surface of this Palomar entry. It imports only
Mathlib and nothing from this repository's proof library.

The ordinary definitions below are the pinned OpenAI statement model
`lean/OAI/Analysis/KLS/Model.lean` of https://github.com/openai/math at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (Apache-2.0, © OpenAI), with the same
declaration names, binders and bodies. The only adaptations are the Lean module header,
`public import Mathlib` and the `@[expose] public section` required by the module system;
`integrations/openai/UPSTREAM.json` records the original hash of that file.
Comparator compares these definitions body-for-body with the copy used by the solution.

`KLSStatement` asks for one positive real constant `C`, chosen before the dimension, such that
for every dimension `n ≥ 1`, every measurable probability density `ρ` on `ℝⁿ` that is
log-concave on its positive support and whose law has zero mean and identity covariance (with
all first and second coordinate moments integrable), and every smooth compactly supported
real test function `f`, the variance of `f` is at most `C` times its Dirichlet energy
`∫ ‖∇f‖²`. The test class is exactly `C^∞` functions with compact support; this entry does not
claim the locally Lipschitz `L²` test class of the Bizeul–Klartag–Lehec paper.

The theorem `KLSOpenAI.kls` below is the only deliberate placeholder (`sorry`); it is the
statement Palomar compares against the solution's proved `KLSOpenAI.kls`.
-/

@[expose] public section

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace LeanBlast.KLS

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ordinary Lebesgue-density measure. -/
def densityMeasure {n : ℕ} (ρ : Space n → ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

/-- Probability-density and log-concavity conditions.
`ConcaveOn` includes convexity of the positive support. -/
structure IsLogConcaveDensity {n : ℕ} (ρ : Space n → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ ρ x
  measurable : Measurable ρ
  probability : IsProbabilityMeasure (densityMeasure ρ)
  log_concave : ConcaveOn ℝ {x | 0 < ρ x} (fun x => Real.log (ρ x))

/-- Zero mean and identity covariance, with all moment integrability explicit. -/
structure IsIsotropic {n : ℕ} (μ : Measure (Space n)) : Prop where
  integrable_coordinate : ∀ i : Fin n, Integrable (fun x : Space n => x i) μ
  integrable_product : ∀ i j : Fin n, Integrable (fun x : Space n => x i * x j) μ
  mean_zero : ∀ i : Fin n, (∫ x : Space n, x i ∂μ) = 0
  second_moment : ∀ i j : Fin n,
    (∫ x : Space n, x i * x j ∂μ) = if i = j then 1 else 0

def expectation {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, f x ∂μ

def variance {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, (f x - expectation μ f) ^ 2 ∂μ

def dirichletEnergy {n : ℕ} (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ

/-- The exact compactly supported smooth real test-function class. -/
def IsTestFunction {n : ℕ} (f : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

/-- Direct Poincare inequality, avoiding an infimum convention for the constant. -/
def PoincareBound {n : ℕ} (μ : Measure (Space n)) (C : ℝ) : Prop :=
  ∀ f : Space n → ℝ, IsTestFunction f → variance μ f ≤ C * dirichletEnergy μ f

/-- The full dimension-free statement: one constant works for every dimension,
every isotropic log-concave density, and every smooth compactly supported test. -/
def KLSStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ∀ ρ : Space n → ℝ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) →
      PoincareBound (densityMeasure ρ) C

abbrev FullStatement := KLSStatement

end LeanBlast.KLS

end

end OAI

namespace KLSOpenAI

/-- **Dimension-free Kannan–Lovász–Simonovits bound** in the exact pinned OpenAI form.

There is one constant `C > 0` such that for every `n ≥ 1`, every measurable log-concave
probability density `ρ` on `ℝⁿ` whose law is isotropic, and every `C^∞` compactly supported
test `f : ℝⁿ → ℝ`, `Var_ρ(f) ≤ C · ∫ ‖∇f‖² ρ`. -/
theorem kls : OAI.LeanBlast.KLS.KLSStatement := by
  sorry

end KLSOpenAI
