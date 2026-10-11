import FunctionalInequalities.Poincare.SmoothTest.Linear

/-!
# Lean certificate for `KLS.pdf`, Remark 3.8 (`lem:linear-test-lower`)

Source: the Poincaré lower-bound part of Remark 3.8 in the combined manuscript at commit
`cd4a894a0faf40c0180f80b1a31eec1fdb6cb576`:
https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L108-L117
The accompanying linear-baseline dossier states the finite-covariance setting and computes the
variance and gradient energy of linear tests:
https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/solutions/glm-linear-baselines.tex#L39-L68

This certificate combines the admissible-test Rayleigh lower bound and the covariance lower
bound on `ℝ^D`. The explicit `MemLp id 2 μ` premise, the zero-dimensional convention, and the
`ENNReal` encoding are local specifications; the test domain is the one in `Poincare.SmoothTest.Basic`.
The Gaussian equality and mode-indicator claims in the same remark are outside this certificate.
The ledger binds this file through `lean_solution`.
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities

namespace Solutions.LemLinearTestLower

/-- Source: the two Poincaré lower bounds in manuscript Remark 3.8, linked above, with the
finite-second-moment premise made explicit as in the linear-baseline dossier. This local
certificate combines `Poincare.SmoothTest.rayleigh_le_constant` and `Covariance.lambdaMax_le_constant`
for the repository's admissible tests, including `D = 0`. -/
theorem certificate {D : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)) 2 μ) :
    (∀ ⦃f : EuclideanSpace ℝ (Fin D) → ℝ⦄,
      Poincare.SmoothTest.Admissible μ f → Poincare.SmoothTest.rayleigh μ f ≤ Poincare.SmoothTest.constant μ) ∧
      Covariance.lambdaMax μ ≤ Poincare.SmoothTest.constant μ := by
  constructor
  · intro f hf
    exact Poincare.SmoothTest.rayleigh_le_constant hf
  · exact Covariance.lambdaMax_le_constant hμ

end Solutions.LemLinearTestLower

/--
info: 'Solutions.LemLinearTestLower.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemLinearTestLower.certificate
