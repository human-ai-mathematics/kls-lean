import FunctionalInequalities.KLS.BKL.Poincare
/-!
# Lean source-form certificate: `thm:bkl-poincare` (BKL Theorem 1.1)

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Theorem 1.1, p. 2: there is a universal constant `C > 0` such that
for every `n ≥ 1` and every isotropic log-concave probability measure `μ` on `ℝⁿ`, the Poincaré constant
satisfies `C_P(μ) ≤ C`. Here `C_P` is the literature local-slope constant `Poincare.LocalSlope.Intrinsic.constant`.
The constant is chosen before every dimension and law. There is no compactness, regularity or moment premise
beyond isotropy.

The proof is the closed producer `KLS.BKL.Localization.exists_isotropicBound`. It runs through the compact Letwin bound,
the cutoff stochastic-localization Theorem 4.1, Theorem 3.1, Proposition 7.1 and the regular approximation.
The uncut Eldan process is not constructed.
-/

open MeasureTheory
namespace Solutions.ThmBklPoincare

/-- The named isotropic form: one `C > 0` with `KLS.IsotropicBound C` on every finite-dimensional space. -/
theorem bound : ∃ C : NNReal, 0 < C ∧ FunctionalInequalities.KLS.IsotropicBound.{0} C :=
  FunctionalInequalities.KLS.BKL.Localization.exists_isotropicBound

/-- **BKL Theorem 1.1** in the source form. -/
theorem certificate :
    ∃ C : NNReal, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
        FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
          FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant μ ≤ (C : ENNReal) := by
  obtain ⟨C, hC, h⟩ := bound
  exact ⟨C, hC, fun n _ μ hLC hiso => h (EuclideanSpace ℝ (Fin n)) μ hLC hiso⟩

/--
info: 'Solutions.ThmBklPoincare.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmBklPoincare.bound

/--
info: 'Solutions.ThmBklPoincare.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmBklPoincare.certificate

end Solutions.ThmBklPoincare
