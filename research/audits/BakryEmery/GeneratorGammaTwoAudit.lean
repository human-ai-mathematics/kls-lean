import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.BakryEmery.GammaTwo
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-! Independent statement audit for the **generator form** of the weak `Γ₂` inequality.

Every proposition below is restated in full and **proved** from the library. The audit covers:

* the bounded-multiplier operators on `L²`, with their representatives and norm bounds;
* the pairing of an `L²` multiplier with a weak `Γ` whose second field is a.e. bounded,
  its integrability, its `L¹` stability and its limit transfer;
* the Leibniz rule for the **closed** weighted gradient against a smooth compactly supported
  multiplier, and the smooth graph core it rests on;
* the identity that removes the second-order field from the tested weak `Γ`,
  `∫ φ Γ(T̄ F, T̄ (A F)) dν = ∫ φ (A F)² dν - ∫ (A F) Γ(T̄ F, T̄ φ) dν`, with the sign of the
  second term checked explicitly;
* the generator form of the weak `Γ₂` inequality on smooth compactly supported data, its
  transfer along **first-order** graph convergence for `A`, the stability of the approximation
  class under graph limits, its non-vacuity on `C_c^∞`, and the resulting two-field statement;
* the heat-flow statement under the single explicit operator-core hypothesis.

Deliberately **not** audited, because it is not proved: that `C_c^∞(V)` is an operator core of
`A = T̄†T̄` (equivalently, essential self-adjointness of `ℒ` on `C_c^∞(V)`), hence also not the
unconditional weak `Γ₂` inequality for `P_t g`. No pointwise gradient bound, no `Γ` time
interpolation and no Buser inequality is audited, because none is proved. -/
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff RealInnerProductSpace LinearPMap

namespace BakryEmeryGeneratorGammaTwoAudit

/-! ### Multiplication of an `L²` class by an a.e. bounded multiplier -/

section G0

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A bounded scalar multiplier preserves `L²`, and the product has the expected
representative. -/
theorem G0_scalar {c : α → ℝ} {M : ℝ} (hc : AEStronglyMeasurable c μ)
    (hM : ∀ᵐ x ∂μ, |c x| ≤ M) (u : Lp H 2 μ) :
    MemLp (fun x => c x • (u x)) 2 μ ∧
      ((L2.bddSmulL hc hM u : Lp H 2 μ) : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  ⟨L2.memLp_bddSmul hc hM u, L2.coeFn_bddSmulL hc hM u⟩

/-- Its operator bound, and the bound on differences that the closedness argument uses. -/
theorem G0_scalar_bound {c : α → ℝ} {M : ℝ} (hc : AEStronglyMeasurable c μ)
    (hM : ∀ᵐ x ∂μ, |c x| ≤ M) (u v : Lp H 2 μ) :
    ‖L2.bddSmulL hc hM u‖ ≤ |M| * ‖u‖ ∧
      ‖L2.bddSmulL hc hM u - L2.bddSmulL hc hM v‖ ≤ |M| * ‖u - v‖ :=
  ⟨L2.norm_bddSmulₗ_le hc hM u, L2.norm_bddSmulL_sub_le hc hM u v⟩

/-- A bounded **vector** multiplier sends a scalar `L²` class to a vector `L²` class, with the
expected representative and the same bound. -/
theorem G0_vector {β : α → H} {M : ℝ} (hβ : AEStronglyMeasurable β μ)
    (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) (u v : Lp ℝ 2 μ) :
    MemLp (fun x => (u x) • β x) 2 μ ∧
      ((L2.bddSmulRightL hβ hM u : Lp H 2 μ) : α → H) =ᵐ[μ] (fun x => (u x) • β x) ∧
      ‖L2.bddSmulRightL hβ hM u - L2.bddSmulRightL hβ hM v‖ ≤ |M| * ‖u - v‖ :=
  ⟨L2.memLp_bddSmulRight hβ hM u, L2.coeFn_bddSmulRightL hβ hM u,
    L2.norm_bddSmulRightL_sub_le hβ hM u v⟩

/-- The zero multiplier gives the zero class: the construction is not vacuous and it is
normalized. -/
theorem G0_zero (u : Lp H 2 μ) :
    ((L2.bddSmulL (c := fun _ : α => (0 : ℝ)) (M := 0) aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ => by simp) u : Lp H 2 μ) : α → H) =ᵐ[μ] 0 := by
  filter_upwards [L2.coeFn_bddSmulL (c := fun _ : α => (0 : ℝ)) (M := 0)
    aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ => by simp) u] with x hx
  rw [hx]
  simp

end G0

/-! ### Pairing an `L²` multiplier against a weak `Γ` with a bounded second field -/

section G1

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- For a scalar class the weak `Γ` with itself is the pointwise square. This is the shape in
which the generator term `∫ φ (A F)²` is read. -/
theorem G1_square (u : Lp ℝ 2 μ) (x : α) : WeakGamma.apply u u x = (u x) ^ 2 :=
  WeakGamma.apply_self_real u x

/-- `a · Γ(u, β)` is integrable as soon as `β` is a.e. bounded. Only `β` is required to be
bounded; `a` and `u` are arbitrary `L²` classes. -/
theorem G1_integrable {β : Lp H 2 μ} {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) (a : Lp ℝ 2 μ)
    (u : Lp H 2 μ) : Integrable (fun x => a x * WeakGamma.apply u β x) μ :=
  WeakGamma.integrable_mul_of_bdd_right hM a u

/-- Its `L¹` stability in the `L²` norms of the multiplier and of the first field. -/
theorem G1_stability {β : Lp H 2 μ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (a a' : Lp ℝ 2 μ) (u u' : Lp H 2 μ) :
    |(∫ x, a x * WeakGamma.apply u β x ∂μ) - ∫ x, a' x * WeakGamma.apply u' β x ∂μ| ≤
      M * (‖a - a'‖ * ‖u‖ + ‖a'‖ * ‖u - u'‖) :=
  WeakGamma.abs_integral_mul_sub_le_of_bdd_right hM0 hM a a' u u'

/-- Consequently the tested integral is continuous along `L²` convergence of the pair. -/
theorem G1_tendsto {β : Lp H 2 μ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    {a : ℕ → Lp ℝ 2 μ} {u : ℕ → Lp H 2 μ} {a₀ : Lp ℝ 2 μ} {u₀ : Lp H 2 μ}
    (ha : Tendsto (fun n => ‖a n - a₀‖) atTop (𝓝 0))
    (hu : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, a n x * WeakGamma.apply (u n) β x ∂μ) atTop
      (𝓝 (∫ x, a₀ x * WeakGamma.apply u₀ β x ∂μ)) :=
  WeakGamma.tendsto_integral_mul_of_bdd_right hM0 hM ha hu

/-- The reflexive case of the stability estimate is the trivial bound: the estimate is not
vacuous and its right-hand side vanishes on the diagonal. -/
theorem G1_stability_refl {β : Lp H 2 μ} {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (a : Lp ℝ 2 μ) (u : Lp H 2 μ) :
    |(∫ x, a x * WeakGamma.apply u β x ∂μ) - ∫ x, a x * WeakGamma.apply u β x ∂μ| ≤
      M * (‖a - a‖ * ‖u‖ + ‖a‖ * ‖u - u‖) :=
  WeakGamma.abs_integral_mul_sub_le_of_bdd_right hM0 hM a a u u

/-- Cauchy–Schwarz for the pointwise norms of two `L²` classes with values in **different**
spaces: this is what makes the mixed scalar/vector pairing legal. -/
theorem G1_mixed_cauchy_schwarz {H' : Type*} [NormedAddCommGroup H'] (u : Lp ℝ 2 μ)
    (v : Lp H' 2 μ) :
    Integrable (fun x => ‖u x‖ * ‖v x‖) μ ∧ ∫ x, ‖u x‖ * ‖v x‖ ∂μ ≤ ‖u‖ * ‖v‖ :=
  ⟨WeakGamma.integrable_norm_mul_norm u v, WeakGamma.integral_norm_mul_norm_le u v⟩

/-- The generic transfer of the three-term generator inequality. The per-index inequality is the
only structural input, and the two convergences are both `L²` convergences of first-order
objects. -/
theorem G1_transfer {ψ φ : α → ℝ} {C₁ C₂ N : ℝ} {β : Lp H 2 μ}
    (hψm : AEStronglyMeasurable ψ μ) (hC₁0 : 0 ≤ C₁) (hψb : ∀ᵐ x ∂μ, |ψ x| ≤ C₁)
    (hφm : AEStronglyMeasurable φ μ) (hC₂0 : 0 ≤ C₂) (hφb : ∀ᵐ x ∂μ, |φ x| ≤ C₂)
    (hN0 : 0 ≤ N) (hNb : ∀ᵐ x ∂μ, ‖β x‖ ≤ N)
    {u : ℕ → Lp H 2 μ} {a : ℕ → Lp ℝ 2 μ} {u₀ : Lp H 2 μ} {a₀ : Lp ℝ 2 μ}
    (hu : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0))
    (ha : Tendsto (fun n => ‖a n - a₀‖) atTop (𝓝 0))
    (hnn : ∀ n, 0 ≤ (∫ x, ψ x * WeakGamma.apply (u n) (u n) x ∂μ) / 2 +
      (∫ x, φ x * ((a n : α → ℝ) x) ^ 2 ∂μ) -
        ∫ x, (a n : α → ℝ) x * WeakGamma.apply (u n) β x ∂μ) :
    0 ≤ (∫ x, ψ x * WeakGamma.apply u₀ u₀ x ∂μ) / 2 +
      (∫ x, φ x * ((a₀ : α → ℝ) x) ^ 2 ∂μ) -
        ∫ x, (a₀ : α → ℝ) x * WeakGamma.apply u₀ β x ∂μ :=
  integral_mul_sq_nonneg_of_tendsto hψm hC₁0 hψb hφm hC₂0 hφb hN0 hNb hu ha hnn

end G1

/-! ### The smooth graph core and the Leibniz rule for the closed weighted gradient -/

section G2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- Smooth compactly supported classes are a graph-norm core of `T̄`: the function **and** its
weighted gradient converge, and nothing of higher order is asserted. -/
theorem G2_core (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ (g : ℕ → V → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n)) (hgc : ∀ n, HasCompactSupport (g n)),
      Tendsto (fun n => (memLp_of_contDiff_hasCompactSupport ν (hg n) (hgc n)).toLp (g n))
          atTop (𝓝 (x : Lp ℝ 2 (ν : Measure V))) ∧
        Tendsto (fun n => (IsTest.of_contDiff_hasCompactSupport ν B (hg n)
            (hgc n)).memLp_apply.toLp (apply B (g n))) atTop
          (𝓝 (hν.closedWeightedOperator m B hi x)) :=
  hν.exists_seq_smooth_tendsto_graph m B hi x

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- A smooth compactly supported multiplier preserves `L²(ν)`. -/
theorem G2_memLp {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (u : Lp ℝ 2 (ν : Measure V)) : MemLp (fun y => φ y * u y) 2 (ν : Measure V) :=
  LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc u

/-- **Leibniz rule for `T̄` against a smooth compactly supported multiplier**, for an arbitrary
form-domain element `x`: the product is again in the form domain and
`T̄ (φ x) = φ (T̄ x) + x (B ∇φ)` almost everywhere. No boundedness or differentiability of `x`
is assumed. -/
theorem G2_leibniz {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (x : (hν.closedWeightedOperator m B hi).domain) :
    ∃ hmem : (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain,
      ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
        =ᵐ[(ν : Measure V)] fun y =>
          φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
            + (x : Lp ℝ 2 (ν : Measure V)) y • apply B φ y :=
  hν.exists_mem_domain_closedWeightedOperator_toLp_mul m B hi hφ hφc x

/-- The domain and value clauses, separately, in the form the applications use. -/
theorem G2_leibniz_parts {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (x : (hν.closedWeightedOperator m B hi).domain)
    (hmem : (LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain) :
    ((LogConcave.memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
        (x : Lp ℝ 2 (ν : Measure V))).toLp _ ∈ (hν.closedWeightedOperator m B hi).domain) ∧
      ((hν.closedWeightedOperator m B hi ⟨_, hmem⟩ : Lp V 2 (ν : Measure V)) : V → V)
        =ᵐ[(ν : Measure V)] fun y =>
          φ y • ((hν.closedWeightedOperator m B hi x : Lp V 2 (ν : Measure V)) : V → V) y
            + (x : Lp ℝ 2 (ν : Measure V)) y • apply B φ y :=
  ⟨hν.toLp_mul_mem_closedWeightedOperator_domain m B hi hφ hφc x,
    hν.coeFn_closedWeightedOperator_toLp_mul m B hi hφ hφc x hmem⟩

end G2

/-! ### Eliminating the second-order field from the tested weak `Γ` -/

section G3

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **The identity.** For `F ∈ D(A)` with `A F ∈ D(T̄)`, an arbitrary weight `B` and a smooth
compactly supported `φ`,
`∫ φ Γ(T̄ F, T̄ (A F)) dν = ∫ φ (A F)² dν - ∫ (A F) Γ(T̄ F, T̄ φ) dν`. -/
theorem G3_identity
    (F : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    (hAF : (adjointComp (hν.closedWeightedOperator m B hi) F : Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m B hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ y, φ y * WeakGamma.apply
        (hν.closedWeightedOperator m B hi ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
        (hν.closedWeightedOperator m B hi ⟨_, hAF⟩) y ∂(ν : Measure V) =
      (∫ y, φ y * ((adjointComp (hν.closedWeightedOperator m B hi) F :
          Lp ℝ 2 (ν : Measure V)) y) ^ 2 ∂(ν : Measure V)) -
        ∫ y, (adjointComp (hν.closedWeightedOperator m B hi) F :
            Lp ℝ 2 (ν : Measure V)) y * WeakGamma.apply
          (hν.closedWeightedOperator m B hi ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
          ((IsTest.of_contDiff_hasCompactSupport ν B hφ hφc).memLp_apply.toLp
            (apply B φ)) y ∂(ν : Measure V) :=
  hν.integral_mul_weakGamma_adjointComp_eq m B hi F hAF hφ hφc

/-- **Sign check**, as an equivalent rearrangement with no subtraction: the `Γ(T̄ F, T̄ φ)` term
is the one that is *subtracted* in `G3_identity`, so here it appears on the same side as the
second-order term. -/
theorem G3_sign
    (F : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    (hAF : (adjointComp (hν.closedWeightedOperator m B hi) F : Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m B hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ y, φ y * WeakGamma.apply
        (hν.closedWeightedOperator m B hi ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
        (hν.closedWeightedOperator m B hi ⟨_, hAF⟩) y ∂(ν : Measure V)) +
      ∫ y, (adjointComp (hν.closedWeightedOperator m B hi) F :
          Lp ℝ 2 (ν : Measure V)) y * WeakGamma.apply
        (hν.closedWeightedOperator m B hi ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
        ((IsTest.of_contDiff_hasCompactSupport ν B hφ hφc).memLp_apply.toLp
          (apply B φ)) y ∂(ν : Measure V) =
      ∫ y, φ y * ((adjointComp (hν.closedWeightedOperator m B hi) F :
        Lp ℝ 2 (ν : Measure V)) y) ^ 2 ∂(ν : Measure V) := by
  have h := hν.integral_mul_weakGamma_adjointComp_eq m B hi F hAF hφ hφc
  linarith [h]

end G3

/-! ### The generator form of the inequality and its heat-flow consequence -/

section G4

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **The generator form of the weak `Γ₂` inequality on smooth compactly supported data**, for a
`C^∞` convex potential, the unit weight and a nonnegative smooth compactly supported test. The
second-order field does not occur. -/
theorem G4_smooth
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ y, 0 ≤ φ y) :
    0 ≤ (∫ y, weightedLaplacian U φ y * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩) y
          ∂(ν : Measure V)) / 2 +
        (∫ y, φ y * ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)) y) ^ 2 ∂(ν : Measure V)) -
        ∫ y, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
              Lp ℝ 2 (ν : Measure V)) y *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
            ((IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hφ
              hφc).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) φ)) y
          ∂(ν : Measure V):=
  hν.integral_mul_sq_adjointComp_toLp_nonneg m hi hνU hU hconv hf hfc hφ hφc hφ0

/-- **Transfer along first-order graph convergence for the generator.** The hypotheses are
`[fₙ] → F` and `A [fₙ] → A F` in `L²(ν)`; convergence of `T̄ fₙ` is derived inside the proof and
is not assumed, and no second-order field appears anywhere. -/
theorem G4_transfer
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) {fn : ℕ → V → ℝ}
    (hfn : ∀ n, ContDiff ℝ ∞ (fn n)) (hfnc : ∀ n, HasCompactSupport (fn n))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (h0 : Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
      - (F : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0))
    (h1 : Tendsto (fun n => ‖(adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn n)
            (hfnc n)⟩ : Lp ℝ 2 (ν : Measure V))
      - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
          Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0)) :
    0 ≤ (∫ y, weightedLaplacian U φ y * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) y ∂(ν : Measure V)) / 2 +
        (∫ y, φ y * ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
          Lp ℝ 2 (ν : Measure V)) y) ^ 2 ∂(ν : Measure V)) -
        ∫ y, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
            Lp ℝ 2 (ν : Measure V)) y *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
            ((IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hφ
              hφc).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) φ)) y
          ∂(ν : Measure V):=
  hν.integral_mul_sq_adjointComp_nonneg_of_tendsto m hi hνU hU hconv hφ hφc hφ0 hfn hfnc F h0 h1

/-- **Non-vacuity.** Every smooth compactly supported class satisfies the hypothesis of
`G4_transfer`, by the constant sequence. -/
theorem G4_nonvacuous
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - ((⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
            (adjointComp (hν.closedWeightedOperator m
              (ContinuousLinearMap.id ℝ V) hi)).domain) :
          Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn n)
              (hfnc n)⟩ : Lp ℝ 2 (ν : Measure V))
        - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
              Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0):=
  hν.exists_seq_smooth_tendsto_adjointComp_toLp m hi hνU hU hf hfc

/-- **The approximation class is closed for the graph norm of `A`.** Together with `G4_nonvacuous`
this identifies it as the domain of the closure of `A` restricted to `C_c^∞(V)`. -/
theorem G4_class_closed
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    {y : ℕ → (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain}
    {z : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain}
    (hy : ∀ k, ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (y k : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn n)
              (hfnc n)⟩ : Lp ℝ 2 (ν : Measure V))
        - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (y k) :
            Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0))
    (h0 : Tendsto (fun k => ‖(y k : Lp ℝ 2 (ν : Measure V))
      - (z : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0))
    (h1 : Tendsto (fun k => ‖(adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (y k) :
          Lp ℝ 2 (ν : Measure V))
      - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z :
          Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0)) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (z : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖(adjointComp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn n)
              (hfnc n)⟩ : Lp ℝ 2 (ν : Measure V))
        - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z :
            Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0):=
  hν.exists_seq_smooth_tendsto_adjointComp_of_tendsto m hi hνU hU hy h0 h1

/-- **The two-field weak `Γ₂` inequality under first-order graph convergence.** The conclusion is
the original two-field statement; only the hypotheses have changed, from two `L²` convergences
of fields (one of them second order) to two `L²` convergences of `fₙ` and `A fₙ`. -/
theorem G4_two_field
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) {fn : ℕ → V → ℝ}
    (hfn : ∀ n, ContDiff ℝ ∞ (fn n)) (hfnc : ∀ n, HasCompactSupport (fn n))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hAF : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
        Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (h0 : Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
      - (F : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0))
    (h1 : Tendsto (fun n => ‖(adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn n)
            (hfnc n)⟩ : Lp ℝ 2 (ν : Measure V))
      - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
          Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0)) :
    0 ≤ (∫ y, weightedLaplacian U φ y * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) y ∂(ν : Measure V)) / 2 +
        ∫ y, φ y * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hAF⟩) y
          ∂(ν : Measure V):=
  hν.integral_mul_weakGamma_adjointComp_nonneg_of_graph_tendsto m hi hνU hU hconv hφ hφc hφ0 hfn hfnc F hAF h0 h1

/-- **Weak `Γ₂` along the actual heat flow under one explicit operator-core hypothesis.** The
hypothesis `hcore` is the statement that `C_c^∞(V)` is an operator core of `A`; it is visible,
it mentions neither `φ` nor `g` nor `t`, and it is **not** proved in this development. -/
theorem G5_heat
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (hcore : ∀ y : (adjointComp (hν.closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hi)).domain,
      ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
        (hfnc : ∀ n, HasCompactSupport (fn n)),
        Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
          - (y : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) ∧
        Tendsto (fun n => ‖(adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
              ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn n)
                (hfnc n)⟩ : Lp ℝ 2 (ν : Measure V))
          - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) y :
              Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0))
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
          ∂(ν : Measure V):=
  LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core m hν hi hνU hU hconv hcore hφ hφc hφ0 g ht

/-- **Consistency of the transfer theorem with the smooth case.** Feeding the constant sequence
of `G4_nonvacuous` into `G4_transfer` reproduces `G4_smooth` exactly, so the transfer theorem is
not vacuous and its hypotheses are satisfiable. -/
theorem G4_transfer_nonvacuous
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ y, 0 ≤ φ y) :
    0 ≤ (∫ y, weightedLaplacian U φ y * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩) y
          ∂(ν : Measure V)) / 2 +
        (∫ y, φ y * ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
            Lp ℝ 2 (ν : Measure V)) y) ^ 2 ∂(ν : Measure V)) -
        ∫ y, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
              Lp ℝ 2 (ν : Measure V)) y *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
            ((IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hφ
              hφc).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) φ)) y
          ∂(ν : Measure V):= by
  obtain ⟨fn, hfn, hfnc, h0, h1⟩ :=
    hν.exists_seq_smooth_tendsto_adjointComp_toLp m hi hνU hU hf hfc
  exact hν.integral_mul_sq_adjointComp_nonneg_of_tendsto m hi hνU hU hconv hφ hφc hφ0 hfn hfnc
    ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ h0 h1

end G4

end BakryEmeryGeneratorGammaTwoAudit

/-! ### Axiom reports: every conclusion above and every library declaration it rests on -/

#print axioms FunctionalInequalities.L2.memLp_bddSmul
#print axioms FunctionalInequalities.L2.bddSmulₗ
#print axioms FunctionalInequalities.L2.coeFn_bddSmulₗ
#print axioms FunctionalInequalities.L2.norm_bddSmulₗ_le
#print axioms FunctionalInequalities.L2.bddSmulL
#print axioms FunctionalInequalities.L2.bddSmulL_apply
#print axioms FunctionalInequalities.L2.coeFn_bddSmulL
#print axioms FunctionalInequalities.L2.norm_bddSmulL_sub_le
#print axioms FunctionalInequalities.L2.memLp_bddSmulRight
#print axioms FunctionalInequalities.L2.bddSmulRightₗ
#print axioms FunctionalInequalities.L2.coeFn_bddSmulRightₗ
#print axioms FunctionalInequalities.L2.norm_bddSmulRightₗ_le
#print axioms FunctionalInequalities.L2.bddSmulRightL
#print axioms FunctionalInequalities.L2.bddSmulRightL_apply
#print axioms FunctionalInequalities.L2.coeFn_bddSmulRightL
#print axioms FunctionalInequalities.L2.norm_bddSmulRightL_sub_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.apply_self_real
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integrable_norm_mul_norm
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integral_norm_mul_norm_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integrable_mul_of_bdd_right
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.abs_integral_mul_sub_le_of_bdd_right
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.tendsto_integral_mul_of_bdd_right
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_mul_sq_nonneg_of_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_graph
#print axioms FunctionalInequalities.KLS.LogConcave.memLp_mul_of_contDiff_hasCompactSupport
#print axioms FunctionalInequalities.KLS.LogConcave.exists_mem_domain_closedWeightedOperator_toLp_mul
#print axioms FunctionalInequalities.KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain
#print axioms FunctionalInequalities.KLS.LogConcave.coeFn_closedWeightedOperator_toLp_mul
#print axioms FunctionalInequalities.KLS.LogConcave.integral_mul_weakGamma_adjointComp_eq
#print axioms FunctionalInequalities.KLS.LogConcave.integral_mul_sq_adjointComp_toLp_nonneg
#print axioms FunctionalInequalities.KLS.LogConcave.integral_mul_sq_adjointComp_nonneg_of_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_toLp
#print axioms FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.integral_mul_weakGamma_adjointComp_nonneg_of_graph_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core
#print axioms BakryEmeryGeneratorGammaTwoAudit.G0_scalar
#print axioms BakryEmeryGeneratorGammaTwoAudit.G0_scalar_bound
#print axioms BakryEmeryGeneratorGammaTwoAudit.G0_vector
#print axioms BakryEmeryGeneratorGammaTwoAudit.G0_zero
#print axioms BakryEmeryGeneratorGammaTwoAudit.G1_square
#print axioms BakryEmeryGeneratorGammaTwoAudit.G1_integrable
#print axioms BakryEmeryGeneratorGammaTwoAudit.G1_stability
#print axioms BakryEmeryGeneratorGammaTwoAudit.G1_tendsto
#print axioms BakryEmeryGeneratorGammaTwoAudit.G1_stability_refl
#print axioms BakryEmeryGeneratorGammaTwoAudit.G1_mixed_cauchy_schwarz
#print axioms BakryEmeryGeneratorGammaTwoAudit.G1_transfer
#print axioms BakryEmeryGeneratorGammaTwoAudit.G2_core
#print axioms BakryEmeryGeneratorGammaTwoAudit.G2_memLp
#print axioms BakryEmeryGeneratorGammaTwoAudit.G2_leibniz
#print axioms BakryEmeryGeneratorGammaTwoAudit.G2_leibniz_parts
#print axioms BakryEmeryGeneratorGammaTwoAudit.G3_identity
#print axioms BakryEmeryGeneratorGammaTwoAudit.G3_sign
#print axioms BakryEmeryGeneratorGammaTwoAudit.G4_smooth
#print axioms BakryEmeryGeneratorGammaTwoAudit.G4_transfer
#print axioms BakryEmeryGeneratorGammaTwoAudit.G4_nonvacuous
#print axioms BakryEmeryGeneratorGammaTwoAudit.G4_class_closed
#print axioms BakryEmeryGeneratorGammaTwoAudit.G4_two_field
#print axioms BakryEmeryGeneratorGammaTwoAudit.G5_heat
#print axioms BakryEmeryGeneratorGammaTwoAudit.G4_transfer_nonvacuous
