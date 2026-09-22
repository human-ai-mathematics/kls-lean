import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GammaTwo

/-! Independent statement audit for the **interior regularity of deficiency elements** and its
two consequences: the operator-core property of `C_c^∞(V)` for the log-concave generator, and the
heat-flow weak `Γ₂` inequality without any operator-core, approximation or regularity hypothesis.

Every proposition below is restated in full and **proved** from the library. The audit covers:

* the mollification toolkit against a Haar measure: `L²` contraction, `L²` convergence, the
  symmetry (Fubini) identity and the commutation of `∇` and `Δ` with the mollifier (`M0`–`M3`);
* interior regularity: an `L²(ν)` class orthogonal to `(A + 1) C_c^∞(V)` — the equation is
  written with the **sum** `⟪A [f], u⟫ + ⟪[f], u⟫`, i.e. `A + 1` and not `A - 1` — has every
  `C_c^∞` localization in the form domain `D(T̄)` of the **closed** unit-weight gradient, the
  graph closure used throughout the library (`R1`), with the exact class recorded;
* the operator core: every `F ∈ D(A)` is a graph-norm limit of smooth compactly supported
  classes, for every `C¹` potential (`R2`), and its corollary that a deficiency element is zero,
  i.e. the essential self-adjointness statement (`R2'`);
* the heat-flow weak `Γ₂` inequality for arbitrary `g ∈ L²(ν)`, every `t > 0` and every
  nonnegative `φ ∈ C_c^∞(V)`, with only the model hypotheses (`R3`), and the check that the two
  earlier conditional frontends are now consequences (`R3'`).

Deliberately **not** audited, because **not** proved: `Γ(P_t f) ≤ P_t Γ(f)`, the `Γ` time
interpolation with the outer semigroup, the extension of the test class from `C_c^∞` to
`{P_s φ}`, the square and first-order gradient estimates, the general-law passage, the constant
`π`, Buser and KLS. -/
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Energy.WeightedGradient
open FunctionalInequalities.Analysis.Mollification
open scoped ContDiff RealInnerProductSpace LinearPMap Convolution

namespace BakryEmeryInteriorRegularityAudit

/-! ### `M0`–`M3`: mollification against a Haar measure -/

section Mollification

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]

/-- `M0`: the normalised bump is an `L²` contraction on vector-valued functions. -/
theorem M0_contraction (φ : ContDiffBump (0 : V)) {f : V → V} (hf : AEStronglyMeasurable f m) :
    eLpNorm (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m ≤ eLpNorm f 2 m :=
  eLpNorm_convolution_le φ hf

/-- `M1`: mollifications of an `L²` function converge to it in `L²` as the radii tend to zero. -/
theorem M1_convergence {φ : ℕ → ContDiffBump (0 : V)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {f : V → ℝ} (hf : MemLp f 2 m) :
    Tendsto (fun n => eLpNorm ((φ n).normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f - f) 2 m)
      atTop (𝓝 0) :=
  tendsto_eLpNorm_convolution_sub hφ hf

/-- `M2`: the mollifier is symmetric for the `L²` pairing. -/
theorem M2_symmetric (φ : ContDiffBump (0 : V)) {a b : V → V} (ha : Integrable a m)
    (hb : Continuous b) (hbc : HasCompactSupport b) :
    ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ ∂m =
      ∫ y, ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ ∂m :=
  integral_inner_convolution_eq φ ha hb hbc

/-- `M3`: the mollifier commutes with `∇` and `Δ` on smooth compactly supported functions. -/
theorem M3_commute (φ : ContDiffBump (0 : V)) {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (x : V) :
    gradient (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x ∧
      Laplacian.laplacian (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x :=
  ⟨gradient_convolution φ hg hgc x, laplacian_convolution φ hg hgc x⟩

omit [BorelSpace V] [m.IsAddHaarMeasure] in
/-- The mollification of the zero function is zero: the toolkit is normalized. -/
theorem M0_zero (φ : ContDiffBump (0 : V)) :
    φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] (0 : V → ℝ) = 0 :=
  convolution_zero

end Mollification

/-! ### `R1`–`R3`: the tilted model -/

section Regularity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **`R1`, interior regularity.** For `ν = m.tilted (-U)` with a `C¹` potential and unit
weight: if `⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for every `f ∈ C_c^∞(V)` (orthogonality to the range of
`A + 1`, with the **sum**), then for every `χ ∈ C_c^∞(V)` the class of `χ u` in `L²(ν)` lies in
the domain of the closed unit-weight gradient `T̄ = closure (g ↦ ∇g)`. The conclusion is
membership of the exact class `(memLp_mul_of_contDiff_hasCompactSupport hχ hχc u).toLp _`. -/
theorem R1_interior_regularity (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫ = 0)
    {χ : V → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp
        (fun y => χ y * u y) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
  hν.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal m hi hνU hU u horth hχ hχc

/-- `R1` is exactly the hypothesis `hreg` of the criterion theorems: the local regularity holds
for **every** class orthogonal to `(A + 1) C_c^∞(V)`. -/
theorem R1_is_hreg (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) :
    ∀ u : Lp ℝ 2 (ν : Measure V),
      (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
              Lp ℝ 2 (ν : Measure V)), u⟫ +
          ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
            Lp ℝ 2 (ν : Measure V)), u⟫ = 0) →
      ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
        (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain :=
  fun u horth _χ hχ hχc =>
    hν.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal m hi hνU hU u horth hχ hχc

/-- The tested equation of `R1` is orthogonality to the range of `A + 1`: `⟪A [f], u⟫ =
-⟪[f], u⟫`, not `⟪A [f], u⟫ = ⟪[f], u⟫`. -/
theorem R1_sign (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u : Lp ℝ 2 (ν : Measure V)) (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫ = 0 ↔
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), u⟫ =
        -⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫ := by
  constructor <;> intro h <;> linarith

/-- **`R2`, the operator core.** For every `C¹` potential, every `F ∈ D(A)` is the limit of
smooth compactly supported classes in the graph norm of `A`: `[fₙ] → F` and `A [fₙ] → A F` in
`L²(ν)`. No convexity is assumed. -/
theorem R2_core (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩ :
            Lp ℝ 2 (ν : Measure V)) -
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
          Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) :=
  hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU F

/-- **`R2'`, essential self-adjointness in deficiency form.** Every `L²(ν)` class orthogonal to
`(A + 1) C_c^∞(V)` vanishes: `R1` supplies the local regularity needed by the global cutoff
theorem `eq_zero_of_localRegularity`. -/
theorem R2_deficiency_zero (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u : Lp ℝ 2 (ν : Measure V))
    (horth : ∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)), u⟫ +
        ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
          Lp ℝ 2 (ν : Measure V)), u⟫ = 0) :
    u = 0 :=
  hν.eq_zero_of_localRegularity m hi hνU hU u horth
    (fun _χ hχ hχc =>
      hν.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal m hi hνU hU u horth hχ hχc)

/-- `R2` is non-vacuous and consistent with the smooth core: for `F = [f]` with `f ∈ C_c^∞(V)`
the constant sequence is one admissible choice, so the conclusion of `R2` is not empty. -/
theorem R2_nonvacuous (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - ((⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
            Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩ :
            Lp ℝ 2 (ν : Measure V)) -
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ :
          Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) :=
  hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU _

/-- **`R3`, the heat-flow weak `Γ₂` inequality with only the model hypotheses.** For
`ν = m.tilted (-U)` with `U` `C^∞` convex and unit weight, for **every** `g ∈ L²(ν)`, every
`t > 0` and every nonnegative `φ ∈ C_c^∞(V)`, with `F = P_t g`,
`0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν`. No `hcore`, no `hreg`, no
approximation sequence. -/
theorem R3_heat (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) :
    ∀ (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) {φ : V → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (_hφc : HasCompactSupport φ) (_hφ0 : ∀ y, 0 ≤ φ y),
    0 ≤ (∫ y, weightedLaplacian U φ y *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩) y
          ∂(ν : Measure V)) / 2 +
        ∫ y, φ y * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos m
                (ContinuousLinearMap.id ℝ V) hν hi g ht
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩) y
          ∂(ν : Measure V) :=
  fun g _t ht _φ hφ hφc hφ0 =>
    LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg m hν hi hνU hU hconv hφ hφc hφ0 g
      ht

/-- **`R3'`.** The conditional frontend with the local hypothesis is now a consequence of the
unconditional one: its extra hypothesis is not consulted. -/
theorem R3_conditional_consequence (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    0 ≤ (∫ y, weightedLaplacian U φ y *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩) y
          ∂(ν : Measure V)) / 2 +
        ∫ y, φ y * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos m
                (ContinuousLinearMap.id ℝ V) hν hi g ht
                (LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩) y
          ∂(ν : Measure V) :=
  LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_localRegularity m hν hi hνU hU
    hconv (R1_is_hreg m hν hi hνU (hU.of_le (by norm_num))) hφ hφc hφ0 g ht

end Regularity

end BakryEmeryInteriorRegularityAudit

#print axioms FunctionalInequalities.Analysis.Mollification.eLpNorm_convolution_le
#print axioms FunctionalInequalities.Analysis.Mollification.memLp_convolution
#print axioms FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_of_continuous
#print axioms FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub
#print axioms FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq
#print axioms FunctionalInequalities.Analysis.Mollification.gradient_convolution
#print axioms FunctionalInequalities.Analysis.Mollification.laplacian_convolution
#print axioms FunctionalInequalities.KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal
#print axioms FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg
#print axioms BakryEmeryInteriorRegularityAudit.M0_contraction
#print axioms BakryEmeryInteriorRegularityAudit.M1_convergence
#print axioms BakryEmeryInteriorRegularityAudit.M2_symmetric
#print axioms BakryEmeryInteriorRegularityAudit.M3_commute
#print axioms BakryEmeryInteriorRegularityAudit.M0_zero
#print axioms BakryEmeryInteriorRegularityAudit.R1_interior_regularity
#print axioms BakryEmeryInteriorRegularityAudit.R1_is_hreg
#print axioms BakryEmeryInteriorRegularityAudit.R1_sign
#print axioms BakryEmeryInteriorRegularityAudit.R2_core
#print axioms BakryEmeryInteriorRegularityAudit.R2_deficiency_zero
#print axioms BakryEmeryInteriorRegularityAudit.R2_nonvacuous
#print axioms BakryEmeryInteriorRegularityAudit.R3_heat
#print axioms BakryEmeryInteriorRegularityAudit.R3_conditional_consequence
