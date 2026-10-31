module

public import FunctionalInequalities.KLS.LogConcave.Line.Density
public import FunctionalInequalities.Probability.Line.BrunnMinkowski

/-!
# From a log-concave Lebesgue density to compact-set log-concavity on the line

Source: the converse direction of Blueprint `thm:borell-logconcave-density` in dimension one.
Read `LineDensity.logConcave`.

`LogConcave.exists_lineDensity` produces a Borell density from compact-set log-concavity. This
module proves the reverse implication on the real line: a probability law with a log-concave
Lebesgue density is compact-set log-concave. The proof applies the one-dimensional
Prekopa-Leindler inequality of `Probability/Line/BrunnMinkowski.lean` to the density restricted to
the two compact sets and to their Minkowski combination.

No ledger, certificate, or Blueprint claim is made by this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace FunctionalInequalities.KLS

namespace LineDensity

variable {μ : ProbabilityMeasure ℝ}

/-- A law on the line with a log-concave Lebesgue density is compact-set log-concave. -/
theorem logConcave (d : LineDensity μ) : LogConcave μ := by
  intro K₀ K₁ hK₀ hK₁ t ht0 ht1
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  set C := {z : ℝ | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y} with hC
  have hCc : IsCompact C := isCompact_combination hK₀ hK₁ t
  have hmass :
    ∀ S : Set ℝ,
      MeasurableSet S → (μ : Measure ℝ) S = ∫⁻ x, ENNReal.ofReal (S.indicator d.ρ x) := by
    intro S hS
    have hind :
      ∀ x,
        ENNReal.ofReal (S.indicator d.ρ x) = S.indicator (fun y ↦ ENNReal.ofReal (d.ρ y)) x := by
      intro x
      by_cases hx : x ∈ S <;> simp [hx]
    simp_rw [hind]
    rw [lintegral_indicator hS, ← d.isBorell.withDensity_eq, withDensity_apply _ hS]
  rw [hmass K₀ hK₀.measurableSet, hmass K₁ hK₁.measurableSet, hmass C hCc.measurableSet]
  refine
    Probability.Line.prekopaLeindler (d.isBorell.measurable.indicator hK₀.measurableSet)
      (d.isBorell.measurable.indicator hK₁.measurableSet)
      (d.isBorell.measurable.indicator hCc.measurableSet)
      (fun x ↦ Set.indicator_nonneg (fun y _ ↦ d.isBorell.nonneg y) x)
      (fun y ↦ Set.indicator_nonneg (fun z _ ↦ d.isBorell.nonneg z) y) ht0 ht1 ?_
  intro x y
  have hh0 : ∀ z, 0 ≤ C.indicator d.ρ z := fun z ↦
    Set.indicator_nonneg (fun w _ ↦ d.isBorell.nonneg w) z
  by_cases hx : x ∈ K₀
  · by_cases hy : y ∈ K₁
    · have hz : t * x + (1 - t) * y ∈ C := ⟨x, hx, y, hy, by simp [smul_eq_mul]⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hz]
      simpa [smul_eq_mul] using d.isBorell.logConcave x y t ht0 ht1
    · rw [Set.indicator_of_notMem hy, Real.zero_rpow ht1'.ne', mul_zero]
      exact hh0 _
  · rw [Set.indicator_of_notMem hx, Real.zero_rpow ht0.ne', zero_mul]
    exact hh0 _

end LineDensity

end FunctionalInequalities.KLS
