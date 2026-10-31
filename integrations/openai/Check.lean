module

public import KLSOpenAI

@[expose] public section

noncomputable section

open MeasureTheory OAI.LeanBlast.KLS
open scoped ContDiff

namespace KLSOpenAI.Check

example : FunctionalInequalities.KLS.Conjecture → KLSStatement := of_conjecture

/-- A downstream consumer can use the result in ordinary integrals, retaining one
constant chosen before the dimension, density and compactly supported smooth test. -/
theorem integral_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ ρ : Space n → ℝ, IsLogConcaveDensity ρ → IsIsotropic (densityMeasure ρ) →
        ∀ f : Space n → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
          (∫ x, (f x - ∫ y, f y ∂densityMeasure ρ) ^ 2 ∂densityMeasure ρ) ≤
            C * ∫ x, ‖gradient f x‖ ^ 2 ∂densityMeasure ρ := by
  obtain ⟨C, hC, h⟩ := KLSOpenAI.kls
  exact ⟨C, hC, fun n hn ρ hρ hi f hf hc => h n hn ρ hρ hi f ⟨hf, hc⟩⟩

/-- The conversion lemmas themselves impose no positive-dimension restriction. -/
theorem zero_dimensional_conversion {ρ : Space 0 → ℝ} (hρ : IsLogConcaveDensity ρ)
    (hi : IsIsotropic (densityMeasure ρ)) :
    FunctionalInequalities.KLS.LogConcave
        (⟨densityMeasure ρ, hρ.probability⟩ : ProbabilityMeasure (Space 0)) ∧
      FunctionalInequalities.KLS.Isotropic
        (⟨densityMeasure ρ, hρ.probability⟩ : ProbabilityMeasure (Space 0)) :=
  ⟨logConcave hρ, isotropic hρ hi⟩

#print axioms integral_bound
#print axioms zero_dimensional_conversion
#print axioms KLSOpenAI.of_conjecture
#print axioms KLSOpenAI.kls

end KLSOpenAI.Check
