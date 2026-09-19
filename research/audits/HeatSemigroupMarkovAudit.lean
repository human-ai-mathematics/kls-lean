import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov

/-!
# Audit: Markov property of the log-concave heat semigroup

This file contains declaration checks, anonymous examples reproducing and discharging the seven
route statements, and axiom checks. It is not imported by the library and adds no named theorem.
-/

open MeasureTheory FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace

#check FunctionalInequalities.KLS.LogConcave.weighted_relaxation_markovian
#check FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_markovian
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_positive
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_le_one
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_one
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.isPositive_exp_neg_smul_yosida
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_neg_smul_yosida_one
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_neg_smul_yosida_le_one
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.semigroupApply_subMarkov
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.semigroupApply_one
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.mean_semigroupApply
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.abs_semigroupApply_le
#check FunctionalInequalities.Analysis.Semigroup.LpMarkov.abs_semigroupApply_le_const

#check FunctionalInequalities.KLS.LogConcave.heatSemigroup_positive
#check FunctionalInequalities.KLS.LogConcave.heatSemigroup_one
#check FunctionalInequalities.KLS.LogConcave.heatSemigroup_subMarkov
#check FunctionalInequalities.KLS.LogConcave.integral_heatSemigroup
#check FunctionalInequalities.KLS.LogConcave.abs_heatSemigroup_le
#check FunctionalInequalities.KLS.LogConcave.abs_heatSemigroup_le_const

namespace FunctionalInequalities

/-! The following anonymous examples reproduce `M1`--`M7` from `MarkovRouteStatements.lean`. -/

example : (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
    (hν : KLS.LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty),
      Energy.Markovian (ν : Measure V)
        ((Energy.PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).sequentialRelaxation)) := by
  intro V _ _ _ _ _ _ _ ν m _ B hν hi
  exact KLS.LogConcave.weighted_relaxation_markovian m B hν hi

example : (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) {s : ℝ} (hs : 0 < s),
      Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T) →
      ∀ f : Lp ℝ 2 (μ : Measure α), 0 ≤ f → 0 ≤ resolventCLM T hT hs f) := by
  intro α H _ _ _ _ μ T hT s hs hM f hf
  exact LpMarkov.resolventCLM_positive hT hM hs hf

example : (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) {s : ℝ} (hs : 0 < s),
      Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T) →
      ∀ f : Lp ℝ 2 (μ : Measure α), f ≤ L2.const μ 1 →
        resolventCLM T hT hs f ≤ L2.const μ 1) := by
  intro α H _ _ _ _ μ T hT s hs hM f hf
  exact LpMarkov.resolventCLM_le_one hT hM hs hf

example : (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) {s : ℝ} (hs : 0 < s),
      ∀ (hone : L2.const μ 1 ∈ T.domain), T ⟨L2.const μ 1, hone⟩ = 0 →
        resolventCLM T hT hs (L2.const μ 1) = L2.const μ 1 ∧
        ∀ t : ℝ,
          NormedSpace.exp (-t • yosida T hT hs) (L2.const μ 1) = L2.const μ 1) := by
  intro α H _ _ _ _ μ T hT s hs hone hTone
  exact ⟨LpMarkov.resolventCLM_one hT hs hone hTone,
    fun t ↦ LpMarkov.exp_neg_smul_yosida_one hT hs t hone hTone⟩

example : (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) (_hM : Energy.Markovian (μ : Measure α)
      (Energy.PreEnergy.normSqEnergy T)) {s t : ℝ} (hs : 0 < s) (_ht : 0 ≤ t)
    (hone : L2.const μ 1 ∈ T.domain) (_hTone : T ⟨L2.const μ 1, hone⟩ = 0),
      (∀ f, 0 ≤ f → 0 ≤ NormedSpace.exp (-t • yosida T hT hs) f) ∧
      (∀ f, f ≤ L2.const μ 1 →
        NormedSpace.exp (-t • yosida T hT hs) f ≤ L2.const μ 1)) := by
  intro α H _ _ _ _ μ T hT hM s t hs ht hone hTone
  exact ⟨fun _ hf ↦ LpMarkov.isPositive_exp_neg_smul_yosida hT hM hs ht hf,
    fun _ hf ↦ LpMarkov.exp_neg_smul_yosida_le_one hT hM hs ht hone hTone hf⟩

example : (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2 (μ : Measure α))))
    (_hM : Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T))
    {t : ℝ} (_ht : 0 ≤ t) (hone : L2.const μ 1 ∈ T.domain)
    (_hTone : T ⟨L2.const μ 1, hone⟩ = 0),
      (∀ f, 0 ≤ f → 0 ≤ semigroupApply T hT hd t f) ∧
      (∀ f, f ≤ L2.const μ 1 → semigroupApply T hT hd t f ≤ L2.const μ 1) ∧
      semigroupApply T hT hd t (L2.const μ 1) = L2.const μ 1) := by
  intro α H _ _ _ _ μ T hT hd hM t ht hone hTone
  exact ⟨fun _ hf ↦ LpMarkov.semigroupApply_positive hT hd hM ht hf,
    fun _ hf ↦ LpMarkov.semigroupApply_le_one hT hd hM ht hone hTone hf,
    LpMarkov.semigroupApply_one hT hd ht hone hTone⟩

example : (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2 (μ : Measure α))))
    (_hM : Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T))
    {t : ℝ} (_ht : 0 ≤ t) (hone : L2.const μ 1 ∈ T.domain)
    (_hTone : T ⟨L2.const μ 1, hone⟩ = 0) (f : Lp ℝ 2 (μ : Measure α)),
      L2.mean μ (semigroupApply T hT hd t f) = L2.mean μ f ∧
      |semigroupApply T hT hd t f| ≤ semigroupApply T hT hd t |f| ∧
      ∀ {C : ℝ}, 0 ≤ C → |f| ≤ C • L2.const μ 1 →
        |semigroupApply T hT hd t f| ≤ C • L2.const μ 1) := by
  intro α H _ _ _ _ μ T hT hd hM t ht hone hTone f
  exact ⟨LpMarkov.mean_semigroupApply hT hd ht hone hTone f,
    LpMarkov.abs_semigroupApply_le hT hd hM ht f,
    by
      intro C hC hf
      exact LpMarkov.abs_semigroupApply_le_const hT hd hM ht hone hTone f
        (C := C) hC hf⟩

end FunctionalInequalities

#print axioms FunctionalInequalities.KLS.LogConcave.weighted_relaxation_markovian
#print axioms FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_markovian
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_positive
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_le_one
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.resolventCLM_one
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.isPositive_exp_neg_smul_yosida
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_neg_smul_yosida_one
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.exp_neg_smul_yosida_le_one
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.semigroupApply_subMarkov
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.semigroupApply_one
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.mean_semigroupApply
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.abs_semigroupApply_le
#print axioms FunctionalInequalities.Analysis.Semigroup.LpMarkov.abs_semigroupApply_le_const
#print axioms FunctionalInequalities.KLS.LogConcave.heatSemigroup_positive
#print axioms FunctionalInequalities.KLS.LogConcave.heatSemigroup_one
#print axioms FunctionalInequalities.KLS.LogConcave.heatSemigroup_subMarkov
#print axioms FunctionalInequalities.KLS.LogConcave.integral_heatSemigroup
#print axioms FunctionalInequalities.KLS.LogConcave.abs_heatSemigroup_le
#print axioms FunctionalInequalities.KLS.LogConcave.abs_heatSemigroup_le_const
