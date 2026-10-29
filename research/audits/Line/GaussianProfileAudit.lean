import FunctionalInequalities.Probability.Line.GaussianProfile

/-! Independent scalar inputs for the Gaussian-profile BGL route. No heat estimate is claimed. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory ProbabilityTheory
open FunctionalInequalities.Probability.Line.GaussianProfile

namespace GaussianProfileAudit

theorem actual_gaussian (x : ℝ) :
    profile (distribution x) = gaussianPDFReal 0 1 x := profile_distribution x

theorem inverse (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    distribution (quantile p) = p := distribution_quantile hp

theorem ode (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    profile p * deriv (deriv profile) p = -1 := profile_mul_second_deriv hp

theorem scalar_range (p : ℝ) : 0 ≤ profile p ∧ profile p ≤ (Real.sqrt (2 * Real.pi))⁻¹ :=
  ⟨profile_nonneg p, profile_le p⟩

theorem bound_attained : ∃ p ∈ Ioo (0 : ℝ) 1,
    profile p = (Real.sqrt (2 * Real.pi))⁻¹ :=
  ⟨distribution 0, distribution_mem 0, profile_distribution_zero⟩

theorem endpoints : profile 0 = 0 ∧ profile 1 = 0 := ⟨profile_zero, profile_one⟩

theorem closed_interval_continuity : ContinuousOn profile (Icc (0 : ℝ) 1) :=
  continuousOn_profile

theorem strict_concavity : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) profile :=
  strictConcaveOn_profile

#print axioms actual_gaussian
#print axioms inverse
#print axioms ode
#print axioms scalar_range
#print axioms bound_attained
#print axioms endpoints
#print axioms closed_interval_continuity
#print axioms strict_concavity
end GaussianProfileAudit
