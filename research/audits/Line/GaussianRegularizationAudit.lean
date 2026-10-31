module

public import FunctionalInequalities.Probability.Line.GaussianProfile
public import FunctionalInequalities.Analysis.BakryEmery.Gamma

/-! Actual scalar regularization and a smooth-input chain-rule client, not a heat theorem. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
open FunctionalInequalities.Probability.Line.GaussianProfile
open FunctionalInequalities.Analysis.BakryEmery
namespace GaussianRegularizationAudit

theorem smooth_interior (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ profile p := contDiffAt_profile hp

theorem symmetry (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    profile (1 - p) = profile p := profile_one_sub hp

theorem peak : profile (1 / 2) = (Real.sqrt (2 * Real.pi))⁻¹ := profile_half

theorem nonnegative (ε x : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hx : x ∈ Icc (0 : ℝ) (1 - 2 * ε)) : 0 ≤ shifted ε x := shifted_nonneg hε hε' hx

theorem reciprocal (ε x : ℝ) (hx : x + ε ∈ Ioo (0 : ℝ) 1) :
    shifted ε x * (-deriv (deriv (shifted ε)) x) =
      1 - profile ε / profile (x + ε) := shifted_mul_neg_second_deriv hx

theorem bounds (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (0 : ℝ) (1 - 2 * ε),
      |deriv (shifted ε) x| ≤ C ∧ |deriv (deriv (shifted ε)) x| ≤ C :=
  exists_shifted_derivative_bound hε

theorem uniform_bound (ε x : ℝ) : |shifted ε x| ≤ (Real.sqrt (2 * Real.pi))⁻¹ :=
  abs_shifted_le ε x

theorem lipschitz (ε : ℝ) (hε : 0 < ε) :
    ∃ K : NNReal, LipschitzOnWith K (shifted ε) (Icc (0 : ℝ) (1 - 2 * ε)) :=
  exists_lipschitzOnWith_shifted hε

theorem limit (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun ε ↦ shifted ε x) (𝓝[>] 0) (𝓝 (profile x)) := tendsto_shifted_of_mem_Ico hx

theorem global_extension (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ Φ 0 = 0 ∧
      (∀ x ∈ Icc (0 : ℝ) (1 - 2 * ε), Φ =ᶠ[𝓝 x] shifted ε) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x, |Φ x| ≤ C ∧ |deriv Φ x| ≤ C ∧
        |deriv (deriv Φ) x| ≤ C := exists_smooth_shifted_extension hε hε'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem compact_composition {f : E → ℝ} {ε : ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hr : ∀ x, f x + ε ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x ↦ shifted ε (f x)) ∧
      HasCompactSupport (fun x ↦ shifted ε (f x)) :=
  ⟨contDiff_shifted_comp hf hr, hasCompactSupport_shifted_comp hfc ε⟩

/-- An actual pointwise chain-rule instantiation, explicitly restricted to smooth inputs. -/
theorem smooth_chain (U : E → ℝ) {f : E → ℝ} {ε : ℝ} (hf : ContDiff ℝ 2 f)
    (hr : ∀ x, f x + ε ∈ Ioo (0 : ℝ) 1) (x : E) :
    weightedLaplacian U (fun y ↦ shifted ε (f y)) x =
      deriv (shifted ε) (f x) * weightedLaplacian U f x -
        (profile (f x + ε))⁻¹ * gamma f f x := by
  have h := weightedLaplacian_comp U (x := x)
    (h'' := fun r ↦ -(profile (r + ε))⁻¹) hf
    (fun y ↦ (hasDerivAt_shifted (hr y)).differentiableAt.hasDerivAt)
    (hasDerivAt_deriv_shifted (hr x))
  simpa only [neg_mul, sub_eq_add_neg] using h

#print axioms smooth_interior
#print axioms symmetry
#print axioms peak
#print axioms nonnegative
#print axioms reciprocal
#print axioms bounds
#print axioms uniform_bound
#print axioms lipschitz
#print axioms limit
#print axioms global_extension
#print axioms compact_composition
#print axioms smooth_chain
end GaussianRegularizationAudit
