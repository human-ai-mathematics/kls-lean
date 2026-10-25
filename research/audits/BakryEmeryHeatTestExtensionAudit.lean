import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.TestClassExtension

/-! Independent clients of the two-field smooth core and the arbitrary-data heat-test frontend.
The law is `ν = m.tilted (-U)` for a smooth convex potential and the closed gradient has unit
weight. The clients instantiate arbitrary `g ∈ L²(ν)`, `r > 0`, `s ≥ 0` and nonnegative
`φ ∈ C_c^∞`, check the time-zero test `ψ = [φ]` with `Aψ = [-ℒφ]`, evaluate the zero test, and
use the graph-norm identity and the two-field core at actual heat data `F = P_r g`. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup
  FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff
namespace BakryEmeryHeatTestExtensionAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **Arbitrary data.** The frontend for arbitrary `g`, `r > 0`, `s ≥ 0` and `φ ≥ 0`. -/
theorem arbitrary_data (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ} (hr : 0 < r)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hs
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
          preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hφ hφc⟩ hs⟩) x *
      WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩) x
        ∂(ν : Measure V)) / 2 +
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi hs
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
              ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩,
              mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
                hν hi g hr _⟩) x ∂(ν : Measure V) :=
  (integral_weakGamma_operator_nonneg m hν hi hνU hU hconv g hr hφ hφc hφ0 hs).2.2

/-- **Time zero.** At `s = 0` the test is the classical `φ` itself, with `Aψ = -ℒφ`:
`0 ≤ -(1/2) ∫ (-ℒφ) Γ(T̄F, T̄F) dν + ∫ φ Γ(T̄F, T̄(AF)) dν` for `F = P_r g`. -/
theorem time_zero (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ} (hr : 0 < r)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ -(∫ x, -weightedLaplacian U φ x *
      WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩) x
        ∂(ν : Measure V)) / 2 +
      ∫ x, φ x *
        WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
              ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩,
              mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
                hν hi g hr _⟩) x ∂(ν : Measure V) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have h := (integral_weakGamma_operator_nonneg m hν hi hνU hU hconv g hr hφ hφc hφ0
    (le_refl 0)).2.2
  have e0 : (⟨operator m (ContinuousLinearMap.id ℝ V) hν hi (le_refl 0)
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
      preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 hφ hφc⟩ (le_refl 0)⟩ :
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) =
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 hφ hφc⟩ :=
    Subtype.ext (HeatSemigroup.zero m (ContinuousLinearMap.id ℝ V) hν hi _)
  rw [e0, hν.adjointComp_toLp_eq m hi hνU hU1 hφ hφc,
    HeatSemigroup.zero m (ContinuousLinearMap.id ℝ V) hν hi] at h
  have i₁ (G : V → ℝ) : ∫ x, ((memLp_neg_weightedLaplacian (ν := ν) hU1 hφ hφc).toLp
      (fun y => -weightedLaplacian U φ y) : Lp ℝ 2 (ν : Measure V)) x * G x ∂(ν : Measure V) =
      ∫ x, -weightedLaplacian U φ x * G x ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU1 hφ hφc).coeFn_toLp] with x hx
    rw [hx]
  have i₂ (G : V → ℝ) : ∫ x, ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ :
      Lp ℝ 2 (ν : Measure V)) x * G x ∂(ν : Measure V) = ∫ x, φ x * G x ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [hx]
  simp only [i₁, i₂] at h
  exact h

/-- **Zero test.** For `φ = 0` both pairings of the frontend vanish, so it reads `0 ≤ 0`. -/
theorem zero_test (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 ≤ s) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hs
          ((memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
            (HasCompactSupport.zero)).toLp (fun _ : V => (0 : ℝ))),
          preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide))
              (contDiff_const (c := (0 : ℝ))) HasCompactSupport.zero⟩ hs⟩) x *
      WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩) x
        ∂(ν : Measure V)) = 0 ∧
    (∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi hs
          ((memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
            (HasCompactSupport.zero)).toLp (fun _ : V => (0 : ℝ))) x *
        WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
              ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩,
              mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
                hν hi g hr _⟩) x ∂(ν : Measure V)) = 0 := by
  have h0 : (memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
      (HasCompactSupport.zero)).toLp (fun _ : V => (0 : ℝ)) = 0 := by
    exact MemLp.toLp_zero _
  have hψ : operator m (ContinuousLinearMap.id ℝ V) hν hi hs
      ((memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
        (HasCompactSupport.zero)).toLp (fun _ : V => (0 : ℝ))) = 0 := by
    rw [h0, map_zero]
  have e : (⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hs
      ((memLp_of_contDiff_hasCompactSupport ν (contDiff_const (c := (0 : ℝ)))
        (HasCompactSupport.zero)).toLp (fun _ : V => (0 : ℝ))),
      preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide))
          (contDiff_const (c := (0 : ℝ))) HasCompactSupport.zero⟩ hs⟩ :
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) = 0 :=
    Subtype.ext hψ
  constructor
  · rw [e, LinearPMap.map_zero]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [Lp.coeFn_zero ℝ 2 (ν : Measure V)] with x hx
    rw [hx, Pi.zero_apply, zero_mul]
  · rw [hψ]
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [Lp.coeFn_zero ℝ 2 (ν : Measure V)] with x hx
    rw [hx, Pi.zero_apply, zero_mul]

/-- **Graph-norm identity at heat data.** For `F = P_r g`, the second-order expansion
`‖JF‖² + ‖T̄JF‖² = ‖F‖² + 3‖T̄F‖² + 3‖AF‖² + ‖T̄AF‖²`. -/
theorem graph_norm_identity (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ} (hr : 0 < r) :
    ‖operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g +
        adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩‖ ^ 2 +
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩ +
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
            hν hi g hr (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr)⟩‖ ^ 2 =
    ‖operator m (ContinuousLinearMap.id ℝ V) hν hi hr.le g‖ ^ 2 +
      3 * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩‖ ^ 2 +
      3 * ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩‖ ^ 2 +
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
            hν hi g hr (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr)⟩‖ ^ 2 :=
  norm_add_adjointComp_sq_add_norm_sq
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
    ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩
    (mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
      hν hi g hr _)

/-- **Two-field core at heat data.** `F = P_r g` is approximated by `qₙ ∈ C_c^∞` with
`[∇qₙ] → T̄F` and `[∇(-ℒqₙ)] → T̄(AF)`, the two fields required by the transfer. -/
theorem two_field_core (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ} (hr : 0 < r) :
    ∃ (q : ℕ → V → ℝ) (hq : ∀ n, ContDiff ℝ ∞ (q n)) (hqc : ∀ n, HasCompactSupport (q n)),
      Tendsto (fun n => (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n)
          (hqc n)).toLp (gradient (q n))) atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)) ∧
      Tendsto (fun n => (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_weightedLaplacian hU (hq n) (by decide) (by decide)).neg
          (hasCompactSupport_weightedLaplacian U (hqc n)).neg).toLp
            (gradient (fun x => -weightedLaplacian U (q n) x))) atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
            hν hi g hr (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr)⟩)) := by
  obtain ⟨q, hq, hqc, -, c₂, -, c₄⟩ := hν.exists_seq_smooth_tendsto_two_fields hνU hU
    ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩
    (mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V)
      hν hi g hr _)
  exact ⟨q, hq, hqc, c₂, c₄⟩

#print axioms arbitrary_data
#print axioms time_zero
#print axioms zero_test
#print axioms graph_norm_identity
#print axioms two_field_core
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_add_adjointComp_sq_add_norm_sq
#print axioms FunctionalInequalities.Analysis.Semigroup.tendsto_of_tendsto_add_adjointComp
#print axioms FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_two_fields
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_weakGamma_operator_nonneg
end BakryEmeryHeatTestExtensionAudit
