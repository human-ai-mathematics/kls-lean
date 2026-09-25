import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.TestClass

/-! Independent clients for partial progress only. No client here proves the requested
arbitrary-data inequality at positive test time. In particular, a heat evolution of a smooth
compactly supported function is not assumed to be a compactly supported smooth function. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Energy.WeightedGradient
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.KLS.LogConcave.HeatSemigroup
open scoped ContDiff RealInnerProductSpace
namespace BakryEmeryHeatApproximationAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

theorem regularized_approximation
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
    (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ} (hr : 0 < r) :
    let T := hν.closedWeightedOperator m B hi
    let u := fun (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (ν : Measure V)) =>
      T ⟨operator m B hν hi ht.le f, mem_closedWeightedOperator_domain_of_pos m B hν hi f ht⟩
    let w := fun (t : ℝ) (ht : 0 < t) (f : Lp ℝ 2 (ν : Measure V)) =>
      T ⟨adjointComp T ⟨operator m B hν hi ht.le f,
        mem_adjointComp_domain_of_pos m B hν hi f ht⟩,
        mem_closedWeightedOperator_domain_adjointComp_of_pos m B hν hi f ht _⟩
    ∃ (f : ℕ → V → ℝ) (hf : ∀ n, ContDiff ℝ ∞ (f n))
      (hfc : ∀ n, HasCompactSupport (f n)),
      Tendsto (fun n => u (r / 2) (half_pos hr)
        ((memLp_of_contDiff_hasCompactSupport ν (hf n) (hfc n)).toLp (f n))) atTop
          (𝓝 (u r hr g)) ∧
      Tendsto (fun n => w (r / 2) (half_pos hr)
        ((memLp_of_contDiff_hasCompactSupport ν (hf n) (hfc n)).toLp (f n))) atTop
          (𝓝 (w r hr g)) :=
  exists_seq_smooth_tendsto_regularized_fields m B hν hi g hr

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- The second-field bound applies to arbitrary heat data with arbitrary weights. -/
theorem second_field_bound (B : V →L[ℝ] V) (g : Lp ℝ 2 (ν : Measure V))
    {r : ℝ} (hr : 0 < r) :
    let T := hν.closedWeightedOperator m B hi
    r ^ 3 * ‖T ⟨adjointComp T ⟨operator m B hν hi hr.le g,
      mem_adjointComp_domain_of_pos m B hν hi g hr⟩,
      mem_closedWeightedOperator_domain_adjointComp_of_pos m B hν hi g hr _⟩‖ ^ 2 ≤
        4 * ‖g‖ ^ 2 :=
  Generated.pow_three_mul_norm_map_adjointComp_apply_sq_le _
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) g hr _ _

/-- Both actual heat integrands are integrable, including test time zero. -/
theorem arbitrary_heat_pairings
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (g : Lp ℝ 2 (ν : Measure V)) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let u := T ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g,
      mem_closedWeightedOperator_domain_of_pos m _ hν hi g hr⟩
    let w := T ⟨adjointComp T ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g,
      mem_adjointComp_domain_of_pos m _ hν hi g hr⟩,
      mem_closedWeightedOperator_domain_adjointComp_of_pos m _ hν hi g hr _⟩
    let ψ := operator m (ContinuousLinearMap.id ℝ V) hν hi hs
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ)
    let hψ := preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hφ hφc⟩ hs
    Integrable (fun x => ψ x * WeakGamma.apply u w x) (ν : Measure V) ∧
      Integrable (fun x => (adjointComp T ⟨ψ, hψ⟩) x * WeakGamma.apply u u x)
        (ν : Measure V) := by
  dsimp only
  exact integrable_operator_toLp_weakGamma m hν hi hνU hU hφ hφc hs _ _

/-- The arbitrary-data inequality at test time zero is an existing compact-test theorem,
expressed here with the nonnegative generator sign and the evolved L² test. -/
theorem test_time_zero
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ} (hr : 0 < r) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let u := T ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g,
      mem_closedWeightedOperator_domain_of_pos m _ hν hi g hr⟩
    let w := T ⟨adjointComp T ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g,
      mem_adjointComp_domain_of_pos m _ hν hi g hr⟩,
      mem_closedWeightedOperator_domain_adjointComp_of_pos m _ hν hi g hr _⟩
    let ψ := operator m (ContinuousLinearMap.id ℝ V) hν hi (le_refl 0)
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ)
    let hψ := preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hφ hφc⟩ (le_refl 0)
    0 ≤ -(∫ x, (adjointComp T ⟨ψ, hψ⟩) x * WeakGamma.apply u u x ∂(ν : Measure V)) / 2 +
      ∫ x, ψ x * WeakGamma.apply u w x ∂(ν : Measure V) := by
  dsimp only
  simp only [HeatSemigroup.zero]
  rw [hν.adjointComp_toLp_eq m hi hνU (hU.of_le (by decide)) hφ hφc]
  have ha := (memLp_neg_weightedLaplacian (ν := ν) (hU.of_le (by decide)) hφ hφc).coeFn_toLp
  have hp := (memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp
  have hbase := integral_mul_weakGamma_apply_nonneg m hν hi hνU hU hconv hφ hφc hφ0 g hr
  convert hbase using 1
  congr 1
  · rw [← integral_neg]
    congr 1
    apply integral_congr_ae
    filter_upwards [ha] with x hx
    simp only [hx, neg_mul, neg_neg]
  · apply integral_congr_ae
    filter_upwards [hp] with x hx
    rw [hx]

/-- The zero L² test has zero generator and both pairings vanish at every test time,
for the actual fields of arbitrary positive-time heat data. -/
theorem zero_test (g : Lp ℝ 2 (ν : Measure V)) {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    let u := T ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g,
      mem_closedWeightedOperator_domain_of_pos m _ hν hi g hr⟩
    let w := T ⟨adjointComp T ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g,
      mem_adjointComp_domain_of_pos m _ hν hi g hr⟩,
      mem_closedWeightedOperator_domain_adjointComp_of_pos m _ hν hi g hr _⟩
    let ψ := operator m (ContinuousLinearMap.id ℝ V) hν hi hs (0 : Lp ℝ 2 (ν : Measure V))
    let hψ := preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
      (0 : (adjointComp T).domain) hs;
    -(∫ x, (adjointComp T ⟨ψ, hψ⟩) x * WeakGamma.apply u u x ∂(ν : Measure V)) / 2 +
      (∫ x, ψ x * WeakGamma.apply u w x ∂(ν : Measure V)) = 0 := by
  dsimp only
  simp only [map_zero]
  have hz : (⟨0, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain.zero_mem⟩ :
      (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) = 0 := rfl
  rw [hz, LinearPMap.map_zero]
  have hzero := Lp.coeFn_zero ℝ 2 (ν : Measure V)
  have h1 : ∀ a : V → ℝ, (∫ x, (0 : Lp ℝ 2 (ν : Measure V)) x * a x ∂(ν : Measure V)) = 0 := by
    intro a
    calc
      _ = ∫ _x, (0 : ℝ) ∂(ν : Measure V) := integral_congr_ae (by
        filter_upwards [hzero] with x hx
        simp only [hx, Pi.zero_apply, zero_mul])
      _ = 0 := integral_zero _ _
  rw [h1, h1]
  norm_num

end BakryEmeryHeatApproximationAudit

#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.pow_three_mul_norm_map_adjointComp_apply_sq_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_map_apply_of_pos
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_map_adjointComp_apply_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.exists_seq_smooth_tendsto_regularized_fields
#print axioms BakryEmeryHeatApproximationAudit.regularized_approximation
#print axioms BakryEmeryHeatApproximationAudit.second_field_bound
#print axioms BakryEmeryHeatApproximationAudit.arbitrary_heat_pairings
#print axioms BakryEmeryHeatApproximationAudit.test_time_zero
#print axioms BakryEmeryHeatApproximationAudit.zero_test
