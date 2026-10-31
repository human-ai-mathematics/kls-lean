module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.Potential
public import FunctionalInequalities.Analysis.Convex.Section.Growth

@[expose] public section

noncomputable section
namespace LetwinSectionVolumeAudit
open Set MeasureTheory FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The literal convex-body source produces an actual moment witness whose sections satisfy
an upper volume bound. The dimensional constant precedes the source law; the compact-local
density floor precedes the section centre, slope and height. No MA or volume estimate is input. -/
theorem source_section_volume_bound (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {K : Set E}, Bornology.IsBounded K → IsOpen K → Convex ℝ K →
      K.Nonempty → ∀ {W : E → ℝ}, ContinuousOn W (closure K) → ∀ μ : ProbabilityMeasure E,
      (μ : Measure E) = (volume : Measure E).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) →
      FunctionalInequalities.KLS.Isotropic μ →
      ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
        (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
        ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
        ContDiff ℝ 1 u ∧ ∀ Q : Set E, IsCompact Q → ∃ a : ℝ, 0 < a ∧
          (∀ y ∈ Q, a ≤ Real.exp (-u y + W (gradient u y))) ∧
          ∀ (x p : E) (h : ℝ), 0 < h → (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
            {y | u y < u x + ⟪p, y - x⟫ + h} ⊆ Q →
            volume {y | u y < u x + ⟪p, y - x⟫ + h} ≤
              ENNReal.ofReal (C * Real.sqrt (h ^ n / a)) := by
  obtain ⟨C, hC, hbound⟩ := exists_section_volume_bound_of_continuous_density hn
  refine ⟨C, hC, fun {K} hKb hKo hKc hKne {W} hW μ hμ hiso => ?_⟩
  obtain ⟨u, L, hstrict, hl, hnorm, hm, hC1, _he, hf, hMA, _hae, _hUpper, _hLower⟩ :=
    exists_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  exact ⟨u, L, hstrict, hl, hnorm, hm, hC1,
    hbound u _ hstrict.convexOn hC1.continuous hf (fun x => Real.exp_pos _) hMA⟩
end LetwinSectionVolumeAudit

#print axioms LetwinSectionVolumeAudit.source_section_volume_bound
#print axioms FunctionalInequalities.Analysis.exists_section_volume_upper_bound
#print axioms FunctionalInequalities.Analysis.subgradient_volume_lower_bound_of_compact
#print axioms FunctionalInequalities.Analysis.exists_section_volume_bound_of_continuous_density
