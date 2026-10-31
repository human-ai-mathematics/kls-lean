module

public import FunctionalInequalities.KLS.Geometry.Cheeger.BVIdentification

/-! Independent full-signature clients for the compact-local relaxation infimum: the class asks
only for local Lipschitz continuity and bare indicator-`L¹` convergence on every compact set (no
integrability field); its infimum of liminf slope integrals equals the perimeter for every finite
Borel measure on a proper metric space. Both directions are used (a global-`L¹` locally Lipschitz
sequence bounds the compact relaxation; a compact-convergent sequence bounds the perimeter);
the compact/closed-ball premise equivalence; empty class `⊤`, `⊤` transfer, the zero measure and
the empty carrier; the closed-support law of a proper law and the actual closed intrinsic support
of a finite-dimensional law, without convexity or log-concavity. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVLocalL1RelaxationAudit

open FunctionalInequalities
open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

section Generic

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Inclusions hold for every measure. -/
theorem inclusions (ν : Measure X) (B : Set X) :
    compactLocallyLipschitzRelaxation ν B ≤ locallyLipschitzRelaxation ν B ∧
      compactLocallyLipschitzRelaxation ν B ≤ perimeter ν B :=
  ⟨compactLocallyLipschitzRelaxation_le_locallyLipschitzRelaxation ν B,
    compactLocallyLipschitzRelaxation_le_perimeter ν B⟩

omit [BorelSpace X] in
/-- Direction one used: a global-`L¹` locally Lipschitz sequence bounds the compact relaxation. -/
theorem globalSequenceBound (ν : Measure X) (B : Set X)
    (f : LocallyLipschitzApproximatingSequence ν B) :
    compactLocallyLipschitzRelaxation ν B ≤
      liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  compactLocallyLipschitzRelaxation_le_liminf ν B f.toCompact

variable [ProperSpace X]

theorem identity (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    compactLocallyLipschitzRelaxation ν B = perimeter ν B := by
  exact compactLocallyLipschitzRelaxation_eq_perimeter ν B

/-- Direction two used: a compact-convergent sequence bounds the perimeter through the identity. -/
theorem compactSequenceBound (ν : Measure X) [IsFiniteMeasure ν] (B : Set X)
    (f : CompactLocallyLipschitzApproximatingSequence ν B) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f.1 n) x ∂ν) atTop :=
  (compactLocallyLipschitzRelaxation_eq_perimeter ν B).symm.le.trans
    (compactLocallyLipschitzRelaxation_le_liminf ν B f)

omit [BorelSpace X] in
theorem premiseEquivalence (ν : Measure X) (g : ℕ → X → ℝ≥0∞) :
    (∀ K : Set X, IsCompact K → Tendsto (fun n => ∫⁻ x in K, g n x ∂ν) atTop (𝓝 0)) ↔
      ∀ (x₀ : X) (r : ℝ), 0 < r →
        Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ r, g n x ∂ν) atTop (𝓝 0) := by
  exact forall_isCompact_iff_forall_closedBall ν g

/-- An empty class gives `⊤` and forces infinite perimeter; infinite perimeter transfers. -/
theorem topCases (ν : Measure X) [IsFiniteMeasure ν] (B : Set X) :
    (IsEmpty (CompactLocallyLipschitzApproximatingSequence ν B) →
      compactLocallyLipschitzRelaxation ν B = ⊤ ∧ perimeter ν B = ⊤) ∧
      (perimeter ν B = ⊤ → compactLocallyLipschitzRelaxation ν B = ⊤) := by
  refine ⟨fun h => ?_, fun h => (compactLocallyLipschitzRelaxation_eq_perimeter ν B).trans h⟩
  have := h
  have htop : compactLocallyLipschitzRelaxation ν B = ⊤ := by
    unfold compactLocallyLipschitzRelaxation
    exact iInf_of_empty _
  exact ⟨htop, (compactLocallyLipschitzRelaxation_eq_perimeter ν B).symm.trans htop⟩

end Generic

/-- The zero measure on `ℝ`. -/
theorem zeroMeasure (B : Set ℝ) : compactLocallyLipschitzRelaxation (0 : Measure ℝ) B = 0 := by
  have hz : perimeter (0 : Measure ℝ) B = 0 := by
    have h := perimeter_le_liminf_of_lipschitz (0 : Measure ℝ) (B := B)
      (f := fun _ _ => (0 : ℝ)) (fun _ => ⟨0, LipschitzWith.const 0⟩) (by simp)
    simp only [lintegral_zero_measure, liminf_const] at h
    exact le_antisymm h bot_le
  rw [compactLocallyLipschitzRelaxation_eq_perimeter, hz]

/-- The empty carrier. -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) :
    compactLocallyLipschitzRelaxation ν B = perimeter ν B := by
  have : IsFiniteMeasure ν := ⟨by simp [Measure.eq_zero_of_isEmpty ν]⟩
  exact compactLocallyLipschitzRelaxation_eq_perimeter ν B

/-- The uniform law on `[0, 1]`, a proper law on `ℝ`: the closed-support instance. -/
def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Set.Icc 0 1), ⟨by simp⟩⟩

theorem uniformSupportIdentity (B : Set (uniformInterval : Measure ℝ).support) :
    compactLocallyLipschitzRelaxation (closedSupportLaw uniformInterval : Measure _) B =
      perimeter (closedSupportLaw uniformInterval : Measure _) B :=
  compactLocallyLipschitzRelaxation_closedSupportLaw _ B

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The actual closed intrinsic support of every finite-dimensional probability law, with no
convexity or log-concavity. -/
theorem intrinsicIdentity (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    compactLocallyLipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B =
      perimeter (intrinsicClosedSupportLaw μ : Measure _) B := by
  exact compactLocallyLipschitzRelaxation_intrinsicClosedSupportLaw μ B

end Intrinsic

#print axioms inclusions
#print axioms globalSequenceBound
#print axioms identity
#print axioms compactSequenceBound
#print axioms premiseEquivalence
#print axioms topCases
#print axioms zeroMeasure
#print axioms emptyCarrier
#print axioms uniformSupportIdentity
#print axioms intrinsicIdentity

end MetricBVLocalL1RelaxationAudit
