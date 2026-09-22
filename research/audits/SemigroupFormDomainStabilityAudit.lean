import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain

/-! Independent statement audit for the form-domain stage F0–F4.

Every proposition below is restated in full and **proved** from the library; nothing here is a
type-checked candidate. The inputs are only `f ∈ D(T†T)` (F0) or `f ∈ D(T)` (F1–F4): no smooth
test class, no compact support and no positive-time smoothing is assumed, and `t = 0` and the
zero vector are exercised explicitly. The gradient is the closed operator `T` (concretely the
closed weighted gradient with an arbitrary weight `B`), not a classical representative. -/
noncomputable section
open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace LinearPMap
namespace SemigroupFormDomainStabilityAudit
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

/-! ### F0: energy contraction on the generator domain -/

/-- `f ∈ D(T†T)`, `t ≥ 0` implies `‖T (P_t f)‖ ≤ ‖T f‖`, with the membership witness of
`P_t f ∈ D(T)` supplied by the caller. -/
theorem F0 (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : Generated.apply T hT hd t (f : H₀) ∈ T.domain) :
    ‖T ⟨Generated.apply T hT hd t (f : H₀), hft⟩‖ ≤ ‖T ⟨(f : H₀), f.2.2⟩‖ :=
  Generated.norm_map_apply_le_of_generator T hT hd f ht hft

/-- The Dirichlet-form phrasing of F0: `⟪T†T (P_t f), P_t f⟫ ≤ ⟪T†T f, f⟫`. -/
theorem F0_form (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    ⟪adjointComp T ⟨Generated.apply T hT hd t (f : H₀),
        Generated.preserves_domain T hT hd f ht⟩, Generated.apply T hT hd t (f : H₀)⟫
      ≤ ⟪adjointComp T f, (f : H₀)⟫ :=
  Generated.inner_adjointComp_apply_le T hT hd f ht

/-! ### F1: `D(T†T)` is dense in `D(T)` for the graph norm -/

include hT hd in
/-- Both convergences are asserted: `u n → f` in `H₀` **and** `T (u n) → T f` in `H₁`, with
every `u n` in the generator domain. -/
theorem F1 (f : T.domain) :
    ∃ (u : ℕ → H₀) (hu : ∀ n, u n ∈ (adjointComp T).domain),
      Filter.Tendsto u Filter.atTop (nhds (f : H₀)) ∧
        Filter.Tendsto (fun n => T ⟨u n, (hu n).2⟩) Filter.atTop (nhds (T f)) :=
  Generated.exists_seq_mem_adjointComp_domain_tendsto_graph T hT hd f

include hT hd in
/-- The `ε` form of F1: every `f ∈ D(T)` has generator-domain approximants that are close in
both components of the graph norm at once. -/
theorem F1_eps (f : T.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : H₀) (hg : g ∈ (adjointComp T).domain),
      ‖g - (f : H₀)‖ < ε ∧ ‖T ⟨g, hg.2⟩ - T f‖ < ε := by
  obtain ⟨u, hu, hu₀, hu₁⟩ := F1 T hT hd f
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hu₀ ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hu₁ ε hε
  refine ⟨u (max N₀ N₁), hu (max N₀ N₁), ?_, ?_⟩
  · have h := hN₀ (max N₀ N₁) (le_max_left _ _)
    rwa [dist_eq_norm] at h
  · have h := hN₁ (max N₀ N₁) (le_max_right _ _)
    rwa [dist_eq_norm] at h

/-! ### F2: invariance of the full form domain -/

/-- For every `f ∈ D(T)` and every `t ≥ 0`, `P_t f ∈ D(T)`. -/
theorem F2 (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    Generated.apply T hT hd t (f : H₀) ∈ T.domain :=
  Generated.preserves_form_domain T hT hd f ht

include hT hd in
/-- Time zero is allowed and returns the datum. -/
theorem F2_zero_time (f : T.domain) : (f : H₀) ∈ T.domain := by
  have h := Generated.preserves_form_domain T hT hd f (le_refl (0 : ℝ))
  rwa [Generated.zero_time T hT hd (f : H₀)] at h

/-- The zero vector is allowed. -/
theorem F2_zero_vector {t : ℝ} (ht : 0 ≤ t) :
    Generated.apply T hT hd t (0 : H₀) ∈ T.domain := by
  have h := Generated.preserves_form_domain T hT hd (0 : T.domain) ht
  simpa using h

/-! ### F3: energy contraction on the full form domain -/

/-- For every `f ∈ D(T)`, every `t ≥ 0` and every witness of `P_t f ∈ D(T)`,
`‖T (P_t f)‖ ≤ ‖T f‖`. -/
theorem F3 (f : T.domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : Generated.apply T hT hd t (f : H₀) ∈ T.domain) :
    ‖T ⟨Generated.apply T hT hd t (f : H₀), hft⟩‖ ≤ ‖T f‖ :=
  Generated.norm_map_apply_le T hT hd f ht hft

/-- F2 and F3 in one statement, with the witness produced rather than assumed. -/
theorem F2_F3 (f : T.domain) {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : Generated.apply T hT hd t (f : H₀) ∈ T.domain,
      ‖T ⟨Generated.apply T hT hd t (f : H₀), h⟩‖ ≤ ‖T f‖ :=
  Generated.exists_mem_domain_norm_map_apply_le T hT hd f ht

/-- F3 at time zero, using the invariance witness the library produces. -/
theorem F3_zero_time (f : T.domain) :
    ‖T ⟨Generated.apply T hT hd 0 (f : H₀),
        Generated.preserves_form_domain T hT hd f (le_refl (0 : ℝ))⟩‖ ≤ ‖T f‖ :=
  Generated.norm_map_apply_le T hT hd f (le_refl (0 : ℝ)) _

/-! ### Generic auxiliary declarations used above -/

/-- The resolvent contracts the energy on `D(T)`; density is not needed. -/
theorem aux_resolvent_energy (f : T.domain) {s : ℝ} (hs : 0 < s) :
    ‖T (resolventDomain T hT hs (f : H₀))‖ ≤ ‖T f‖ :=
  norm_map_resolventDomain_le T hT hs f

/-- Graph-norm convergence of the resolvent, the analytic core of F1. -/
theorem aux_resolvent_graph_limit (f : T.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
      ‖T (resolventDomain T hT hs (f : H₀)) - T f‖ < ε :=
  exists_delta_norm_map_resolventDomain_sub_map_lt T hT f hε

omit [CompleteSpace H₁] in
include hd in
/-- `V1` on the diagonal: the Dirichlet form of `T†T` is the energy of `T`. -/
theorem aux_dirichlet_form (x : (adjointComp T).domain) :
    ⟪adjointComp T x, (x : H₀)⟫ = ‖T ⟨(x : H₀), x.2.2⟩‖ ^ 2 :=
  inner_adjointComp_self hd x

/-! ### F4: the closed weighted gradient heat semigroup, arbitrary weight -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : KLS.LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- `f ∈ D(T̄)`, `t ≥ 0` implies `P_t f ∈ D(T̄)`, for an arbitrary weight `B`. -/
theorem F4_0 (f : (hν.closedWeightedOperator m B hi).domain) {t : ℝ} (ht : 0 ≤ t) :
    KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f ∈
      (hν.closedWeightedOperator m B hi).domain :=
  KLS.LogConcave.HeatSemigroup.preserves_form_domain m B hν hi f ht

/-- `‖T̄ (P_t f)‖ ≤ ‖T̄ f‖` on the whole form domain, for an arbitrary weight `B`. -/
theorem F4_1 (f : (hν.closedWeightedOperator m B hi).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f ∈
      (hν.closedWeightedOperator m B hi).domain) :
    ‖hν.closedWeightedOperator m B hi
        ⟨KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f, hft⟩‖
      ≤ ‖hν.closedWeightedOperator m B hi f‖ :=
  KLS.LogConcave.HeatSemigroup.norm_closedWeightedOperator_le m B hν hi f ht hft

/-- The concrete statements are available at time zero with the library's own witness. -/
theorem F4_zero_time (f : (hν.closedWeightedOperator m B hi).domain) :
    ‖hν.closedWeightedOperator m B hi
        ⟨KLS.LogConcave.HeatSemigroup.operator m B hν hi (le_refl (0 : ℝ)) f,
          KLS.LogConcave.HeatSemigroup.preserves_form_domain m B hν hi f (le_refl (0 : ℝ))⟩‖
      ≤ ‖hν.closedWeightedOperator m B hi f‖ :=
  KLS.LogConcave.HeatSemigroup.norm_closedWeightedOperator_le m B hν hi f (le_refl (0 : ℝ)) _

-- Still only candidates after this stage: arbitrary-input positive-time membership in the
-- generator domain, and a classical pointwise gradient bound. Neither is declared or proved.
#check fun (S : H₀ →ₗ.[ℝ] H₁) (hS : S.IsClosed) (hsd : Dense (S.domain : Set H₀)) =>
  (∀ (g : H₀) (t : ℝ), 0 < t → Generated.apply S hS hsd t g ∈ S.domain)

end SemigroupFormDomainStabilityAudit

#print axioms FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_self
#print axioms FunctionalInequalities.Analysis.Semigroup.resolventDomain_energy_identity
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_map_resolventDomain_sq_le_of_le
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_map_resolventDomain_sub_sq_le_sub
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_map_resolventDomain_le
#print axioms FunctionalInequalities.Analysis.Semigroup.norm_map_resolventDomain_sub_map_sq_le
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_delta_norm_map_resolventDomain_sub_map_lt
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_mul
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_sq_le_mul_norm
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_le_of_generator
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.inner_adjointComp_apply_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.exists_seq_mem_adjointComp_domain_tendsto_graph
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_domain_norm_map_apply_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.preserves_form_domain
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.norm_map_apply_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.preserves_form_domain
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.norm_closedWeightedOperator_le
#print axioms SemigroupFormDomainStabilityAudit.F0
#print axioms SemigroupFormDomainStabilityAudit.F0_form
#print axioms SemigroupFormDomainStabilityAudit.F1
#print axioms SemigroupFormDomainStabilityAudit.F1_eps
#print axioms SemigroupFormDomainStabilityAudit.F2
#print axioms SemigroupFormDomainStabilityAudit.F2_zero_time
#print axioms SemigroupFormDomainStabilityAudit.F2_zero_vector
#print axioms SemigroupFormDomainStabilityAudit.F3
#print axioms SemigroupFormDomainStabilityAudit.F2_F3
#print axioms SemigroupFormDomainStabilityAudit.F3_zero_time
#print axioms SemigroupFormDomainStabilityAudit.aux_resolvent_energy
#print axioms SemigroupFormDomainStabilityAudit.aux_resolvent_graph_limit
#print axioms SemigroupFormDomainStabilityAudit.aux_dirichlet_form
#print axioms SemigroupFormDomainStabilityAudit.F4_0
#print axioms SemigroupFormDomainStabilityAudit.F4_1
#print axioms SemigroupFormDomainStabilityAudit.F4_zero_time
