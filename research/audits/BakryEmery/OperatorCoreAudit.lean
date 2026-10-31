module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.BakryEmery.GammaTwo

/-! Independent statement audit for the **operator-core criterion** of the log-concave generator.

Every proposition below is restated in full and **proved** from the library. The audit covers:

* the locality of the classical weighted Laplacian, `ℒ f = 0` off `tsupport f`;
* the symmetry of a real a.e. bounded scalar multiplier on `L²`;
* the vanishing theorem: an `L²` class orthogonal to `(A + 1) C_c^∞(V)` whose `C_c^∞`
  localizations all lie in `D(T̄)` is zero, with the sign of the tested equation written
  out and its non-vacuity checked on the zero class;
* the operator-core criterion itself: under that local regularity for every such class,
  `C_c^∞(V)` is an operator core of `A = T̄†T̄`, i.e. the hypothesis `hcore` of the
  heat-flow weak `Γ₂` theorem holds;
* the two statements with the stronger global hypothesis `u ∈ D(T̄)`, and the fact that
  the global hypothesis implies the local one;
* the heat-flow weak `Γ₂` inequality with the local hypothesis in place of `hcore`, for
  arbitrary `L²` data and every positive time.

Deliberately **not** audited here: interior elliptic regularity for `div(e^{-U} ∇ ·)`, i.e. that
a distributional solution of `ℒ u = u` is locally in the form domain.  That is the hypothesis of
`C3_core`–`C5_heat`; it is discharged, together with essential self-adjointness of `ℒ` on
`C_c^∞(V)` and the unconditional heat-flow weak `Γ₂` inequality, in
`research/audits/BakryEmery/InteriorRegularityAudit.lean`.  `Γ(P_t f) ≤ P_t Γ(f)`, the `Γ` time
interpolation and Buser's inequality are outside the scope of this audit. -/

@[expose] public section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff RealInnerProductSpace LinearPMap

namespace BakryEmeryOperatorCoreAudit

/-! ### The classical weighted Laplacian is local -/

section C0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The weighted Laplacian of `f` vanishes at every point outside `tsupport f`, for an arbitrary
potential and with no regularity assumption on `f`. -/
theorem C0_local (U : E → ℝ) {f : E → ℝ} {x : E} (hx : x ∉ tsupport f) :
    weightedLaplacian U f x = 0 :=
  weightedLaplacian_eq_zero_of_notMem_tsupport U hx

/-- The degenerate case: the weighted Laplacian of the zero function vanishes everywhere, which
is `C0_local` with an empty support. -/
theorem C0_zero (U : E → ℝ) (x : E) : weightedLaplacian U (fun _ : E => (0 : ℝ)) x = 0 := by
  refine C0_local U ?_
  simp [tsupport]

end C0

/-! ### A real bounded scalar multiplier is symmetric on `L²` -/

section C1

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : α → ℝ} {M : ℝ}

/-- Multiplication by a real a.e. bounded scalar may be moved across the `L²` inner product. -/
theorem C1_symmetric (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u v : Lp E 2 μ) :
    inner ℝ (L2.bddSmulL hc hM u) v = inner ℝ u (L2.bddSmulL hc hM v) :=
  L2.inner_bddSmulL_left hc hM u v

/-- Taking `v = u` turns the symmetry into the expected quadratic reading; the zero multiplier
gives zero, so the statement is normalized. -/
theorem C1_zero (u v : Lp E 2 μ) :
    inner ℝ (L2.bddSmulL (c := fun _ : α => (0 : ℝ)) (M := 0) aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by simp) u) v = 0 := by
  rw [C1_symmetric]
  have h : (L2.bddSmulL (c := fun _ : α => (0 : ℝ)) (M := 0) aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by simp) v : Lp E 2 μ) = 0 := by
    refine Lp.ext ?_
    filter_upwards [L2.coeFn_bddSmulL (c := fun _ : α => (0 : ℝ)) (M := 0)
      aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ => by simp) v,
      Lp.coeFn_zero (E := E) (p := 2) (μ := μ)] with x h1 h2
    rw [h1, h2]
    simp
  rw [h, inner_zero_right]

end C1

/-! ### The criterion in the tilted model -/

section Criterion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **The vanishing theorem.** For `ν = m.tilted (-U)` with a `C¹` potential and unit weight: an
`L²` class `u` orthogonal to `(A + 1) C_c^∞(V)` — the hypothesis is written with the **sum**
`⟪A [f], u⟫ + ⟪[f], u⟫`, not a difference — all of whose smooth compactly supported localizations
`[χ u]` lie in the form domain `D(T̄)`, is zero. No convexity of `U` and no semigroup input is
used. -/
theorem C2_vanishing (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    (hloc : ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
      (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    u = 0 :=
  hν.eq_zero_of_localRegularity m hi hνU hU u horth hloc

/-- The tested equation of `C2_vanishing` is exactly orthogonality to the range of `A + 1` on
`C_c^∞(V)`. -/
theorem C2_orthogonality (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u : Lp ℝ 2 (ν : Measure V)) (f : V → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫
      = ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)) +
        ((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫ :=
  (inner_add_left _ _ _).symm

/-- Non-vacuity of `C2_vanishing`: the zero class satisfies both hypotheses, and the conclusion
holds for it. The hypotheses are therefore not contradictory. -/
theorem C2_nonvacuous (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) :
    (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), (0 : Lp ℝ 2 (ν : Measure V))⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), (0 : Lp ℝ 2 (ν : Measure V))⟫ = 0) ∧
      ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
        (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc
          (0 : Lp ℝ 2 (ν : Measure V))).toLp _ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  refine ⟨fun f hf hfc => by simp, fun χ hχ hχc => ?_⟩
  have h0 : (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc
      (0 : Lp ℝ 2 (ν : Measure V))).toLp _ = (0 : Lp ℝ 2 (ν : Measure V)) := by
    refine Lp.ext ?_
    filter_upwards [(LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc
        (0 : Lp ℝ 2 (ν : Measure V))).coeFn_toLp,
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (ν : Measure V))] with y h1 h2
    rw [h1, h2]
    simp
  rw [h0]
  exact Submodule.zero_mem _

/-- **The operator-core criterion.** If every `L²` class orthogonal to
`(A + 1) C_c^∞(V)` has all of its smooth compactly supported localizations in `D(T̄)`, then every
`F ∈ D(A)` is a limit of smooth compactly supported classes in the **graph norm of `A`**: both
`[fₙ] → F` and `A [fₙ] → A F` in `L²(ν)`. This is exactly the hypothesis `hcore` of
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`. -/
theorem C3_core (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (hreg : ∀ u : Lp ℝ 2 (ν : Measure V),
      (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
              Lp ℝ 2 (ν : Measure V)), u⟫ +
          ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
            Lp ℝ 2 (ν : Measure V)), u⟫ = 0) →
      ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
        (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(adjointComp (hν.closedWeightedOperator m
            (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩ :
            Lp ℝ 2 (ν : Measure V))
        - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
            Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) :=
  hν.exists_seq_smooth_tendsto_adjointComp_of_localRegularity m hi hνU hU hreg F

/-- **The global hypothesis.** The same two statements with the stronger hypothesis that the
deficiency element lies in `D(T̄)` globally. -/
theorem C4_global_vanishing (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u : Lp ℝ 2 (ν : Measure V))
    (hu : u ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫ = 0) :
    u = 0 :=
  hν.eq_zero_of_mem_closedWeightedOperator_domain m hi hνU hU u hu horth

/-- The global hypothesis implies the local one: membership of `u` in `D(T̄)` gives membership of
every `[χ u]` with `χ ∈ C_c^∞(V)`. This is why `C4_global_vanishing` is a special case of
`C2_vanishing`. -/
theorem C4_global_implies_local (B : V →L[ℝ] V) (u : Lp ℝ 2 (ν : Measure V))
    (hu : u ∈ (hν.closedWeightedOperator m B hi).domain) {χ : V → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
      (hν.closedWeightedOperator m B hi).domain :=
  hν.toLp_mul_mem_closedWeightedOperator_domain m B hi hχ hχc ⟨u, hu⟩

/-- **The heat-flow weak `Γ₂` inequality with the local hypothesis in place of `hcore`.**
For a `C^∞` convex potential, unit weight, an arbitrary datum `g ∈ L²(ν)`, every `t > 0` and
every nonnegative `φ ∈ C_c^∞(V)`, with `F = P_t g`,

`0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν`.

The hypothesis is the local regularity of `C3_core`; it is still a hypothesis. -/
theorem C5_heat (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (hreg :
      ∀ u : Lp ℝ 2 (ν : Measure V),
        (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
            ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
                      ⟨_,
                        hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf
                          hfc⟩ :
                    Lp ℝ 2 (ν : Measure V)),
                  u⟫ +
                ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
                    Lp ℝ 2 (ν : Measure V)),
                  u⟫ =
              0) →
          ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
            (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    0 ≤
      (∫ y,
            weightedLaplacian U φ y *
              WeakGamma.apply
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                  ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
                      g,
                    (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                        (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                  ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
                      g,
                    (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                        (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
                y ∂(ν : Measure V)) /
          2 +
        ∫ y,
          φ y *
            WeakGamma.apply
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                  (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                      (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨_,
                  LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos
                    m (ContinuousLinearMap.id ℝ V) hν hi g ht
                    (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                      (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩)
              y ∂(ν : Measure V) :=
  LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_localRegularity m hν hi hνU hU
    hconv hreg hφ hφc hφ0 g ht

end Criterion

end BakryEmeryOperatorCoreAudit

#print axioms
  FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport
#print axioms FunctionalInequalities.L2.inner_bddSmulL_left
#print axioms FunctionalInequalities.KLS.LogConcave.eq_zero_of_localRegularity
#print axioms FunctionalInequalities.KLS.LogConcave.eq_zero_of_mem_closedWeightedOperator_domain
#print axioms
  FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity
#print axioms
  FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_mem_domain
#print axioms
  FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_localRegularity
#print axioms BakryEmeryOperatorCoreAudit.C0_local
#print axioms BakryEmeryOperatorCoreAudit.C0_zero
#print axioms BakryEmeryOperatorCoreAudit.C1_symmetric
#print axioms BakryEmeryOperatorCoreAudit.C1_zero
#print axioms BakryEmeryOperatorCoreAudit.C2_vanishing
#print axioms BakryEmeryOperatorCoreAudit.C2_orthogonality
#print axioms BakryEmeryOperatorCoreAudit.C2_nonvacuous
#print axioms BakryEmeryOperatorCoreAudit.C3_core
#print axioms BakryEmeryOperatorCoreAudit.C4_global_vanishing
#print axioms BakryEmeryOperatorCoreAudit.C4_global_implies_local
#print axioms BakryEmeryOperatorCoreAudit.C5_heat
