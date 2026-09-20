import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain

/-! Independent statement audit D0–D4. The final two propositions are only type-checked;
no arbitrary-input smoothing theorem is assumed or declared. -/
noncomputable section
open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace LinearPMap
namespace SemigroupDomainStabilityAudit
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

theorem D0 (y z : H₀)
    (hz : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd h y - y) - z‖ < ε) :
    ∃ hy : y ∈ (adjointComp T).domain, adjointComp T ⟨y, hy⟩ = -z :=
  FunctionalInequalities.Analysis.Semigroup.Generated.mem_domain_of_generator_limit T hT hd y z hz

theorem D1 (f : (adjointComp T).domain)
    {t : ℝ} (ht : 0 ≤ t) : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f ∈ (adjointComp T).domain :=
  FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f ht

theorem D2 (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f,
      FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f ht⟩ =
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (adjointComp T f) :=
  FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm T hT hd f ht

theorem D3
    (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t + h) f - FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f) +
        adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f,
          FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain T hT hd f ht⟩‖ < ε :=
  FunctionalInequalities.Analysis.Semigroup.Generated.right_derivative T hT hd f ht hε

-- Candidates only: positive-time smoothing and a numerical constant suggested by
-- max_{λ≥0} λ exp(-tλ) = 1 / (exp(1) t). Neither bound nor scalar maximization is proved here.
#check (∀ (f : H₀) (t : ℝ), 0 < t → FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f ∈ (adjointComp T).domain)
#check (∀ (f : H₀) (t : ℝ), 0 < t → ∃ hf : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f ∈ (adjointComp T).domain,
  ‖adjointComp T ⟨FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f, hf⟩‖ ≤ (1 / Real.exp 1) / t * ‖f‖)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : KLS.LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

theorem D4_0
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f ∈ (adjointComp (hν.closedWeightedOperator m B hi)).domain :=
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.preserves_domain m B hν hi f ht

theorem D4_1
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    adjointComp (hν.closedWeightedOperator m B hi)
      ⟨FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f, FunctionalInequalities.KLS.LogConcave.HeatSemigroup.preserves_domain m B hν hi f ht⟩ =
      FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi ht (adjointComp (hν.closedWeightedOperator m B hi) f) :=
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.generator_comm m B hν hi f ht

theorem D4_2
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f ∈ (hν.closedWeightedOperator m B hi).domain :=
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain m B hν hi f ht

theorem D4_3
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, ∀ hh : 0 < h, h < δ →
      ‖h⁻¹ • (FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi (add_nonneg ht hh.le) f -
        FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f) + adjointComp (hν.closedWeightedOperator m B hi)
          ⟨FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f, FunctionalInequalities.KLS.LogConcave.HeatSemigroup.preserves_domain m B hν hi f ht⟩‖ < ε :=
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.right_derivative m B hν hi f ht hε

end SemigroupDomainStabilityAudit

#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.mem_domain_of_generator_limit
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.generator_limit_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.preserves_domain
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.generator_comm
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.right_derivative
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.preserves_domain
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.generator_comm
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.right_derivative
#print axioms SemigroupDomainStabilityAudit.D0
#print axioms SemigroupDomainStabilityAudit.D1
#print axioms SemigroupDomainStabilityAudit.D2
#print axioms SemigroupDomainStabilityAudit.D3
#print axioms SemigroupDomainStabilityAudit.D4_0
#print axioms SemigroupDomainStabilityAudit.D4_1
#print axioms SemigroupDomainStabilityAudit.D4_2
#print axioms SemigroupDomainStabilityAudit.D4_3
