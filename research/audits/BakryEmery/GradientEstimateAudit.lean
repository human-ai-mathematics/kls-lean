module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate.Basic

/-! Independent clients of the time interpolation and the integrated square gradient estimate
`∫ φ Γ(T̄P_t f) dν ≤ ∫ (P_t φ) Γ(T̄f) dν`. The law is `ν = m.tilted (-U)` for a smooth convex
potential, with unit weight. The clients instantiate arbitrary `L²` data at positive times,
arbitrary form-domain data, heat data `f = P_ε g`, the time `t = 0`, the zero test, and the
difference-quotient bound for smooth tests. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup
  FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff
namespace BakryEmeryGradientEstimateAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **Arbitrary `L²` data, positive times**: the interpolation between `a` and `t`. -/
theorem arbitrary_data (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (g : Lp ℝ 2 (ν : Measure V)) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {a t : ℝ}
    (ha : 0 < a) (hat : a ≤ t) :
    ∫ x,
        φ x *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                  (ha.trans_le hat)⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                  (ha.trans_le hat)⟩)
            x ∂(ν : Measure V) ≤
      ∫ x,
        operator m (ContinuousLinearMap.id ℝ V) hν hi (sub_nonneg.mpr hat)
            ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                  ha⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                  ha⟩)
            x ∂(ν : Measure V) :=
  integral_mul_weakGamma_le_of_pos m hν hi hνU hU hconv g hφ hφc hφ0 ha hat

/-- **Form-domain data**: `∫ φ Γ(T̄P_t f) ≤ ∫ (P_t φ) Γ(T̄f)` for every `f ∈ D(T̄)`, `t ≥ 0`. -/
theorem form_domain (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, φ x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f) x ∂(ν : Measure V) :=
  integral_mul_weakGamma_le m hν hi hνU hU hconv f hφ hφc hφ0 ht

/-- **Heat data**: `f = P_ε g` for arbitrary `g ∈ L²` and `ε > 0` lies in `D(T̄)`, so the
estimate holds for it at every `t ≥ 0`. -/
theorem heat_data (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (g : Lp ℝ 2 (ν : Measure V)) {ε : ℝ} (hε : 0 < ε)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ x,
        φ x *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi
                  ⟨_,
                    mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν
                      hi g hε⟩
                  ht⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi
                  ⟨_,
                    mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν
                      hi g hε⟩
                  ht⟩)
            x ∂(ν : Measure V) ≤
      ∫ x,
        operator m (ContinuousLinearMap.id ℝ V) hν hi ht
            ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                  hε⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_,
                mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                  hε⟩)
            x ∂(ν : Measure V) :=
  integral_mul_weakGamma_le m hν hi hνU hU hconv _ hφ hφc hφ0 ht

/-- **Time zero**: at `t = 0` both sides are `∫ φ Γ(T̄f, T̄f) dν`. -/
theorem time_zero (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi le_rfl
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f) x ∂(ν : Measure V) =
      ∫ x, φ x * WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f) x ∂(ν : Measure V) := by
  refine integral_congr_ae ?_
  filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
  rw [HeatSemigroup.zero m _ hν hi, hx]

/-- **Zero test**: for `φ = 0` both sides of the estimate vanish, and the estimate applies. -/
theorem zero_test (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
            HasCompactSupport.zero).toLp (fun _ : V => (0 : ℝ))) x *
        WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f) x ∂(ν : Measure V) = 0 ∧
    ∫ x, (0 : ℝ) * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) = 0 ∧
    ∫ x, (fun _ : V => (0 : ℝ)) x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
            HasCompactSupport.zero).toLp (fun _ : V => (0 : ℝ))) x *
        WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f) x ∂(ν : Measure V) := by
  have h0 : (memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
      HasCompactSupport.zero).toLp (fun _ : V => (0 : ℝ)) = 0 := MemLp.toLp_zero _
  refine ⟨?_, by simp, integral_mul_weakGamma_le m hν hi hνU hU hconv f contDiff_const
    HasCompactSupport.zero (fun _ => le_rfl) ht⟩
  rw [h0, map_zero]
  refine (integral_congr_ae ?_).trans (integral_zero _ _)
  filter_upwards [Lp.coeFn_zero ℝ 2 (ν : Measure V)] with x hx
  rw [hx, Pi.zero_apply, zero_mul]

/-- **Difference-quotient bound for smooth tests**: `|P_h φ - φ| ≤ h D` with one `D` for all
`h ≥ 0`. -/
theorem difference_bound (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : ℝ) (hh : 0 ≤ h), ∀ᵐ x ∂(ν : Measure V),
      |operator m (ContinuousLinearMap.id ℝ V) hν hi hh
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x -
        ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ : Lp ℝ 2 (ν : Measure V)) x| ≤
        h * D := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  obtain ⟨C, D, -, hD, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  refine ⟨D, hD, fun h hh => ?_⟩
  have h0 := (hb 0 le_rfl).2
  have e : (⟨operator m (ContinuousLinearMap.id ℝ V) hν hi le_rfl
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
      preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 hφ hφc⟩ le_rfl⟩ :
      (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) =
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 hφ hφc⟩ :=
    Subtype.ext (HeatSemigroup.zero m _ hν hi _)
  rw [e] at h0
  exact ae_abs_operator_sub_le m _ hν hi ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 hφ hφc⟩
    hD h0 hh

#print axioms arbitrary_data
#print axioms form_domain
#print axioms heat_data
#print axioms time_zero
#print axioms zero_test
#print axioms difference_bound
#print axioms FunctionalInequalities.L2.exists_clamp_integral_lt
#print axioms FunctionalInequalities.L2.tendsto_integral_mul_of_tendsto
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.WeakGamma.tendsto_integral_mul_of_tendsto_multiplier
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.WeakGamma.hasDerivWithinAt_integral_mul_apply_self
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_sq_le_mul
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.generator_limit
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Ici
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_apply_Iic
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivAt_apply
#print axioms
  FunctionalInequalities.Analysis.Semigroup.Generated.adjointComp_apply_mem_adjointComp_domain_of_pos
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.hasDerivWithinAt_map_apply_Ici
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn_map_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_map_apply_zero
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ae_abs_operator_sub_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_le_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_le
end BakryEmeryGradientEstimateAudit
