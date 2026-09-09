import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

/-!
# Lean certificate: `lem:covariance-test-core-density`

Status: proved / checked_by: lean. The certificate packages all four approximation contracts.
Source: Blueprint Appendix A and `research/decisions/2026-09-06-weighted-approximation-acceptance.md`.
The reusable declarations retain their original hypotheses, including arbitrary singular B,
absolute continuity with respect to any Haar reference measure, and dimension zero.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

namespace Solutions.LemCovarianceTestCoreDensity

/-- Cutoff, mollification, weighted L2 approximation and interval-preserving L1 smoothing. -/
theorem certificate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) :
    (∀ (B : E →L[ℝ] E) (g : E → ℝ)
    (_ : LocallyLipschitz g) (_ : MemLp g 2 (ν : Measure E))
    (_ : MemLp (fun x ↦ B (gradient g x)) 2 (ν : Measure E)),
    ∃ gSeq : ℕ → E → ℝ,
      (∀ j, HasCompactSupport (gSeq j) ∧
        (∃ K : NNReal, LipschitzWith K (gSeq j)) ∧
        MemLp (gSeq j) 2 (ν : Measure E) ∧
        MemLp (fun x ↦ B (gradient (gSeq j) x)) 2 (ν : Measure E)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
        atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm
        (fun x ↦ B (gradient (gSeq j) x) - B (gradient g x)) 2 (ν : Measure E))
        atTop (𝓝 0)) ∧
    (∀ (g : E → ℝ) (K : NNReal)
    (_ : LipschitzWith K g) (_ : HasCompactSupport g),
    MemLp g 2 (ν : Measure E) ∧ MemLp (gradient g) 2 (ν : Measure E) ∧
      ∃ gSeq : ℕ → E → ℝ,
        (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ HasCompactSupport (gSeq j) ∧
          LipschitzWith K (gSeq j) ∧ MemLp (gSeq j) 2 (ν : Measure E) ∧
          MemLp (gradient (gSeq j)) 2 (ν : Measure E)) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
          atTop (𝓝 0) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gradient (gSeq j) x - gradient g x)
          2 (ν : Measure E)) atTop (𝓝 0)) ∧
    (∀ (B : E →L[ℝ] E) (g : E → ℝ)
    (_ : LocallyLipschitz g) (_ : MemLp g 2 (ν : Measure E))
    (_ : MemLp (fun x ↦ B (gradient g x)) 2 (ν : Measure E)),
    ∃ gSeq : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ HasCompactSupport (gSeq j) ∧
        MemLp (gSeq j) 2 (ν : Measure E) ∧
        MemLp (fun x ↦ B (gradient (gSeq j) x)) 2 (ν : Measure E)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
        atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm
        (fun x ↦ B (gradient (gSeq j) x) - B (gradient g x)) 2 (ν : Measure E))
        atTop (𝓝 0)) ∧
    (∀ (g : E → ℝ) (K : NNReal)
    (_ : LipschitzWith K g) (a b : ℝ) (_ : ∀ x, a ≤ g x ∧ g x ≤ b),
    MemLp g 1 (ν : Measure E) ∧ MemLp (gradient g) 1 (ν : Measure E) ∧
      ∃ gSeq : ℕ → E → ℝ,
        (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ LipschitzWith K (gSeq j) ∧
          (∀ x, a ≤ gSeq j x ∧ gSeq j x ≤ b) ∧
          MemLp (gSeq j) 1 (ν : Measure E) ∧
          MemLp (gradient (gSeq j)) 1 (ν : Measure E)) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 1 (ν : Measure E))
          atTop (𝓝 0) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gradient (gSeq j) x - gradient g x)
          1 (ν : Measure E)) atTop (𝓝 0)) :=
  ⟨exists_compactSupport_weighted_L2 ν m hν,
    exists_smooth_compactSupport_L2 ν m hν,
    exists_smooth_weighted_L2 ν m hν,
    exists_smooth_bounded_L1 ν m hν⟩

end Solutions.LemCovarianceTestCoreDensity

#check @exists_compactSupport_weighted_L2
#check @exists_smooth_compactSupport_L2
#check @exists_smooth_weighted_L2
#check @exists_smooth_bounded_L1

/--
info: 'FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_compactSupport_weighted_L2'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_compactSupport_weighted_L2

/--
info: 'FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_smooth_compactSupport_L2'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_smooth_compactSupport_L2

/--
info: 'FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_smooth_weighted_L2

/--
info: 'FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_smooth_bounded_L1

/--
info: 'Solutions.LemCovarianceTestCoreDensity.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemCovarianceTestCoreDensity.certificate
