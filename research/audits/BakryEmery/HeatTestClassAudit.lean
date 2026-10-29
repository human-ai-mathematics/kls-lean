import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.BakryEmery.TestClass

/-! Semantic clients for the partial heat-test extension. The full target, with arbitrary
`F = P_r g`, is not proved by this audit. In particular the smooth-data client below does not
assume or construct a classical representative of heat data. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Energy.WeightedGradient
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace

namespace BakryEmeryHeatTestClassAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- Essential bounds are preserved for arbitrary weights and include time zero. -/
theorem bounded_orbit (B : V →L[ℝ] V) {t : ℝ} (ht : 0 ≤ t)
    (f : Lp ℝ 2 (ν : Measure V)) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ C) :
    ∀ᵐ x ∂(ν : Measure V), |HeatSemigroup.operator m B hν hi ht f x| ≤ C :=
  ae_abs_operator_le m B hν hi ht f hC hf

/-- Both integrals needed for interpolation are legal for arbitrary vector fields; no
inequality on arbitrary heat data is inferred from this integrability statement. -/
theorem pairings_integrable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {s : ℝ} (hs : 0 ≤ s) (u w : Lp V 2 (ν : Measure V)) :
    Integrable (fun x => HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi hs
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * WeakGamma.apply u w x)
      (ν : Measure V) ∧
    Integrable (fun x => (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
      ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi hs
        ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
        preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
          ⟨(memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ,
            hν.toLp_mem_adjointComp_domain m hi hνU hU hφ hφc⟩ hs⟩) x * WeakGamma.apply u u x)
      (ν : Measure V) :=
  integrable_operator_toLp_weakGamma m hν hi hνU hU hφ hφc hs u w

/-- The `A = -ℒ` sign is negative in the first term. Only the data are smooth; the test is
an arbitrary a.e. nonnegative generator-domain element. -/
theorem domain_test_sign
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψ : ∀ᵐ x ∂(ν : Measure V), 0 ≤ (ψ : Lp ℝ 2 (ν : Measure V)) x)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      gamma f f x ∂(ν : Measure V)) / 2 -
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * gamma f (weightedLaplacian U f) x
        ∂(ν : Measure V) :=
  integral_gammaTwo_nonneg_of_mem_domain m hν hi hνU hU hconv ψ hψ hf hfc

/-- A smooth datum has the new test-class inequality on its actual closed-gradient fields. -/
theorem smooth_data_heat_test
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {s : ℝ} (hs : 0 ≤ s) {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let u := T ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩
    let w := T ⟨_, hν.adjointComp_toLp_mem_closedWeightedOperator_domain m hi hνU hU hf hfc⟩
    let ψ := HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi hs
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ)
    let hψ := preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
      ⟨(memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ,
        hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hφ hφc⟩ hs
    0 ≤ -(∫ x, (adjointComp T ⟨ψ, hψ⟩) x * WeakGamma.apply u u x ∂(ν : Measure V)) / 2 +
      ∫ x, ψ x * WeakGamma.apply u w x ∂(ν : Measure V) := by
  dsimp only
  exact integral_weakGamma_operator_test_nonneg m hν hi hνU hU hconv hφ hφc hφ0 hs hf hfc
    (hν.coeFn_closedWeightedOperator_toLp_gradient m hi hf hfc)
    (hν.coeFn_closedWeightedOperator_adjointComp_toLp m hi hνU hU hf hfc _)

/-- Zero initial test remains zero, so the boundedness result has its expected degenerate case. -/
theorem zero_test (B : V →L[ℝ] V) {s : ℝ} (hs : 0 ≤ s) :
    HeatSemigroup.operator m B hν hi hs (0 : Lp ℝ 2 (ν : Measure V)) = 0 :=
  map_zero _

end BakryEmeryHeatTestClassAudit

#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.abs_le_const_smul_one_of_ae
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ae_abs_le_of_abs_le_const_smul_one
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ae_nonneg_operator
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ae_abs_operator_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ae_abs_adjointComp_operator_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.exists_bounds_operator_toLp
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integrable_operator_toLp_weakGamma
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_adjointComp_mul_toLp_eq
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_gammaTwo_nonneg_of_mem_domain
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_weakGamma_nonneg_of_mem_domain
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_weakGamma_nonneg_of_mem_domain_of_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_weakGamma_operator_test_nonneg
#print axioms BakryEmeryHeatTestClassAudit.bounded_orbit
#print axioms BakryEmeryHeatTestClassAudit.pairings_integrable
#print axioms BakryEmeryHeatTestClassAudit.domain_test_sign
#print axioms BakryEmeryHeatTestClassAudit.smooth_data_heat_test
#print axioms BakryEmeryHeatTestClassAudit.zero_test
