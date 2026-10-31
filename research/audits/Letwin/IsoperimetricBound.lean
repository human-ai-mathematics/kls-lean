module

public import solutions.ThmLetwinIsoperimetricBound

@[expose] public section

noncomputable section
open MeasureTheory
namespace LetwinLogQuarterBoundAudit
open FunctionalInequalities FunctionalInequalities.KLS

/--
A single constant works before the dimension and each law, from the explicit supremum theorem. -/
theorem law_bound_client :
    ∃ C : ℝ,
      0 < C ∧
        ∀ n : ℕ,
          2 ≤ n →
            ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
              LogConcave μ →
                Isotropic μ →
                  Isoperimetry.inverseScale μ ≤
                    ENNReal.ofReal (C * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := Solutions.ThmLetwinIsoperimetricBound.certificate
  refine ⟨C, hC, fun n hn μ hLC hiso => ?_⟩
  have hμ :
    (⨆ (_ : LogConcave μ) (_ : Isotropic μ), Isoperimetry.inverseScale μ) ≤
      ENNReal.ofReal (C * (Real.log (n : ℝ)) ^ (1 / 4 : ℝ)) :=
    (le_iSup (f := fun ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) =>
          ⨆ (_ : LogConcave ν) (_ : Isotropic ν), Isoperimetry.inverseScale ν) μ).trans
      (h n hn)
  simpa only [iSup_pos hLC, iSup_pos hiso] using hμ
end LetwinLogQuarterBoundAudit
#print axioms LetwinLogQuarterBoundAudit.law_bound_client
