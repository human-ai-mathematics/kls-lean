import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.BakryEmery.Gamma

/-! Independent statement audit for the weak `Γ` interface.

Every proposition below is restated in full and **proved** from the library. The audit covers:

* legality of the weak carré du champ `Γ(u, v)(x) = ⟪u x, v x⟫` of two `L²` vector
  fields — measurability, `L¹` (not `L²`) integrability, representative independence, the
  identification of `∫ Γ(u, v)` with the `L²` inner product, legality of testing against a
  bounded function, and the `L¹` stability estimates;
* the Leibniz and chain rules for the weighted gradient and its closure, and the weak
  integration-by-parts identity `∫ Γ(T̄ f, T̄ x) dν = ∫ (A f) x dν` with `A = T̄†T̄`, `ℒ = -A`,
  together with its agreement with the classical `∫ Γ(f, x) dν = ∫ (-ℒ f) x dν` on `C_c^∞`;
* the integrated Bochner inequality `0 ≤ (∫ (ℒφ) Γ(f, f) dμ)/2 - ∫ φ Γ(f, ℒf) dμ` on
  smooth compactly supported tests, in classical and in weak form;
* the transfer of the integrated Bochner inequality along `L²` convergence of the two fields,
  its non-vacuity on smooth data, and the heat-flow statements that are proved outright: the
  integrated `Γ` contraction, the positive-time integrated `Γ` bound for an arbitrary `L²` datum,
  and the weak generator identity applied to `P_t g`.

Deliberately **not** audited, because they are not proved: `Γ(P_t f) ≤ P_t Γ(f)` in any form,
any pointwise gradient bound, the time derivative of `s ↦ P_s Γ(P_{t-s} f)`, and the existence
of the approximating sequences that the transfer theorem `W3_closed_transfer` takes as
hypotheses when the datum is `P_t g`. -/
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff RealInnerProductSpace LinearPMap

namespace BakryEmeryWeakGammaAudit

/-! ### The weak carré du champ of two square-integrable vector fields -/

section W0

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The weak `Γ` is the pointwise inner product of the representatives. -/
theorem W0_def (u v : Lp H 2 μ) (x : α) : WeakGamma.apply u v x = ⟪u x, v x⟫ :=
  WeakGamma.apply_def u v x

/-- It is almost everywhere strongly measurable. -/
theorem W0_measurable (u v : Lp H 2 μ) : AEStronglyMeasurable (WeakGamma.apply u v) μ :=
  WeakGamma.aestronglyMeasurable u v

/-- It is integrable: the pairing of two `L²` fields is `L¹`. No `L²` membership is claimed. -/
theorem W0_integrable (u v : Lp H 2 μ) : Integrable (WeakGamma.apply u v) μ :=
  WeakGamma.integrable u v

/-- Representative independence: any a.e. representatives compute the same weak `Γ`. -/
theorem W0_representative {u v : Lp H 2 μ} {U V : α → H} (hu : (u : α → H) =ᵐ[μ] U)
    (hv : (v : α → H) =ᵐ[μ] V) : WeakGamma.apply u v =ᵐ[μ] fun x => ⟪U x, V x⟫ :=
  WeakGamma.ae_eq_of_ae_eq hu hv

/-- `Γ(u, u) = ‖u‖²` pointwise, and it is nonnegative. -/
theorem W0_self (u : Lp H 2 μ) (x : α) : WeakGamma.apply u u x = ‖u x‖ ^ 2 ∧
    0 ≤ WeakGamma.apply u u x :=
  ⟨WeakGamma.self_eq_norm_sq u x, WeakGamma.self_nonneg u x⟩

/-- Symmetry and the Cauchy–Schwarz bound. -/
theorem W0_symm_and_bound (u v : Lp H 2 μ) (x : α) :
    WeakGamma.apply u v x = WeakGamma.apply v u x ∧ |WeakGamma.apply u v x| ≤ ‖u x‖ * ‖v x‖ :=
  ⟨congrFun (WeakGamma.comm u v) x, WeakGamma.abs_le_mul u v x⟩

/-- `∫ Γ(u, v) dμ` is the `L²` inner product, and `∫ Γ(u, u) dμ` is the energy `‖u‖²`. -/
theorem W0_integral (u v : Lp H 2 μ) :
    (∫ x, WeakGamma.apply u v x ∂μ) = ⟪u, v⟫ ∧ (∫ x, WeakGamma.apply u u x ∂μ) = ‖u‖ ^ 2 :=
  ⟨WeakGamma.integral_eq_inner u v, WeakGamma.integral_self_eq_norm_sq u⟩

/-- Testing against an a.e. bounded function is legal. This is the exact hypothesis under which
`∫ φ Γ(u, v) dμ` is meaningful. -/
theorem W0_tested (u v : Lp H 2 μ) {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, |φ x| ≤ C) : Integrable (fun x => φ x * WeakGamma.apply u v x) μ :=
  WeakGamma.integrable_mul hφ hC u v

/-- `L¹` stability in the `L²` norms of the fields. -/
theorem W0_stability (u u' v v' : Lp H 2 μ) :
    ∫ x, |WeakGamma.apply u v x - WeakGamma.apply u' v' x| ∂μ ≤
      ‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖ :=
  WeakGamma.integral_abs_sub_le u u' v v'

/-- The tested form of the stability estimate. -/
theorem W0_stability_tested {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂μ, |φ x| ≤ C) (u u' v v' : Lp H 2 μ) :
    |(∫ x, φ x * WeakGamma.apply u v x ∂μ) - ∫ x, φ x * WeakGamma.apply u' v' x ∂μ| ≤
      C * (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) :=
  WeakGamma.abs_integral_mul_sub_le hφ hC0 hC u u' v v'

/-- `L²` convergence of both fields transports the tested weak `Γ` integrals. -/
theorem W0_tendsto {φ : α → ℝ} (hφ : AEStronglyMeasurable φ μ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂μ, |φ x| ≤ C) {u v : ℕ → Lp H 2 μ} {u₀ v₀ : Lp H 2 μ}
    (hu : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0))
    (hv : Tendsto (fun n => ‖v n - v₀‖) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, φ x * WeakGamma.apply (u n) (v n) x ∂μ) atTop
      (𝓝 (∫ x, φ x * WeakGamma.apply u₀ v₀ x ∂μ)) :=
  WeakGamma.tendsto_integral_mul hφ hC0 hC hu hv

/-- Boundary case: the zero field. -/
theorem W0_zero (v : Lp H 2 μ) : (∫ x, WeakGamma.apply 0 v x ∂μ) = 0 := by
  rw [WeakGamma.integral_eq_inner, inner_zero_left]

/-- Boundary case: the `L¹` stability estimate is an equality-free bound that is trivially
saturated when both pairs coincide. -/
theorem W0_stability_refl (u v : Lp H 2 μ) :
    ∫ x, |WeakGamma.apply u v x - WeakGamma.apply u v x| ∂μ = 0 := by
  simp

end W0

/-! ### Product and chain rules, and the weak generator interface -/

section W1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} {B : V →L[ℝ] V} {m : Measure V} [m.IsAddHaarMeasure]

omit [SecondCountableTopology V] in
/-- Leibniz rule for the weighted gradient, `ν`-a.e., with no boundedness hypothesis. -/
theorem W1_leibniz_ae (hac : (ν : Measure V) ≪ m) {g₁ g₂ : V → ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) :
    Energy.WeightedGradient.apply B (fun x => g₁ x * g₂ x) =ᵐ[(ν : Measure V)]
      fun x => g₁ x • Energy.WeightedGradient.apply B g₂ x +
        g₂ x • Energy.WeightedGradient.apply B g₁ x :=
  IsTest.apply_mul_ae hac h₁ h₂

/-- The product of two **bounded** tests is a test; boundedness is genuinely used. -/
theorem W1_leibniz_closed (hac : (ν : Measure V) ≪ m) {g₁ g₂ : V → ℝ} {M₁ M₂ : ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) (hb₁ : ∀ x, |g₁ x| ≤ M₁)
    (hb₂ : ∀ x, |g₂ x| ≤ M₂) : IsTest ν B fun x => g₁ x * g₂ x :=
  h₁.mul hac h₂ hb₁ hb₂

omit [SecondCountableTopology V] in
/-- Chain rule for the weighted gradient, `ν`-a.e. -/
theorem W1_chain_ae (hac : (ν : Measure V) ≪ m) {g : V → ℝ} {Φ : ℝ → ℝ}
    (hΦ : Differentiable ℝ Φ) (h : IsTest ν B g) :
    Energy.WeightedGradient.apply B (fun x => Φ (g x)) =ᵐ[(ν : Measure V)]
      fun x => deriv Φ (g x) • Energy.WeightedGradient.apply B g x :=
  IsTest.apply_comp_ae hac hΦ h

/-- A `C¹` map with bounded derivative fixing `0` maps tests to tests. -/
theorem W1_chain_closed (hac : (ν : Measure V) ≪ m) {g : V → ℝ} {Φ : ℝ → ℝ} {K : ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0) (hK : ∀ t, |deriv Φ t| ≤ K) (h : IsTest ν B g) :
    IsTest ν B fun x => Φ (g x) :=
  h.comp hac hΦ hΦ0 hK

/-- The operator value of a product of bounded tests. -/
theorem W1_operator_mul (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {g₁ g₂ : V → ℝ} {M₁ M₂ : ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂) (hb₁ : ∀ x, |g₁ x| ≤ M₁)
    (hb₂ : ∀ x, |g₂ x| ≤ M₂) :
    ((Energy.WeightedGradient.operator ν B hac
        ⟨_, toLp_mem_domain_operator ν B hac (h₁.mul hac h₂ hb₁ hb₂)⟩ : Lp V 2 (ν : Measure V)) :
        V → V) =ᵐ[(ν : Measure V)]
      fun x => g₁ x • Energy.WeightedGradient.apply B g₂ x +
        g₂ x • Energy.WeightedGradient.apply B g₁ x :=
  coeFn_operator_mul hac hfr h₁ h₂ hb₁ hb₂

/-- The Leibniz rule for the **closed** weighted gradient. -/
theorem W1_closed_mul (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {g₁ g₂ : V → ℝ} {M₁ M₂ : ℝ} (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂)
    (hb₁ : ∀ x, |g₁ x| ≤ M₁) (hb₂ : ∀ x, |g₂ x| ≤ M₂) :
    ((hν.closedWeightedOperator m B hi ⟨_,
        hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi
          (h₁.mul (hν.absolutelyContinuous_haar m hi) h₂ hb₁ hb₂)⟩ :
        Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
      fun x => g₁ x • Energy.WeightedGradient.apply B g₂ x +
        g₂ x • Energy.WeightedGradient.apply B g₁ x :=
  KLS.LogConcave.coeFn_closedWeightedOperator_mul m B hν hi h₁ h₂ hb₁ hb₂

/-- The chain rule for the **closed** weighted gradient. -/
theorem W1_closed_comp (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {g : V → ℝ} {Φ : ℝ → ℝ} {K : ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0)
    (hK : ∀ t, |deriv Φ t| ≤ K) (h : IsTest ν B g) :
    ((hν.closedWeightedOperator m B hi ⟨_,
        hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi
          (h.comp (hν.absolutelyContinuous_haar m hi) hΦ hΦ0 hK)⟩ :
        Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
      fun x => deriv Φ (g x) • Energy.WeightedGradient.apply B g x :=
  KLS.LogConcave.coeFn_closedWeightedOperator_comp m B hν hi hΦ hΦ0 hK h

/-- **Weak integration by parts**: `∫ Γ(T̄ f, T̄ x) dν = ∫ (A f) x dν` for `f ∈ D(A)`,
`x ∈ D(T̄)`, with `A = T̄†T̄` and an arbitrary weight `B`. -/
theorem W1_weak_ibp (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    (x : (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply
        (hν.closedWeightedOperator m B hi ⟨(f : Lp ℝ 2 (ν : Measure V)), f.2.2⟩)
        (hν.closedWeightedOperator m B hi x) a ∂(ν : Measure V) =
      ∫ a, (adjointComp (hν.closedWeightedOperator m B hi) f : Lp ℝ 2 (ν : Measure V)) a *
        (x : Lp ℝ 2 (ν : Measure V)) a ∂(ν : Measure V) :=
  KLS.LogConcave.integral_weakGamma_eq_integral_mul_adjointComp m B hν hi f x

/-- The Dirichlet form as an integral of the weak `Γ`. -/
theorem W1_dirichlet (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    (f : (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi f)
        (hν.closedWeightedOperator m B hi f) a ∂(ν : Measure V) =
      ‖hν.closedWeightedOperator m B hi f‖ ^ 2 :=
  KLS.LogConcave.integral_weakGamma_self m B hν hi f

/-- The weak `Γ` of two smooth compactly supported classes is the classical `Γ`. -/
theorem W1_bridge (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {f g : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩)
      =ᵐ[(ν : Measure V)] gamma f g :=
  KLS.LogConcave.weakGamma_toLp m hν hi hf hfc hg hgc

/-- Agreement of the weak and the classical integration by parts on `C_c^∞`, now valid against
every `x ∈ D(T̄)` and not only against classical tests. -/
theorem W1_classical (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ∫ a, WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi x) a ∂(ν : Measure V) =
      ∫ a, -weightedLaplacian U f a * (x : Lp ℝ 2 (ν : Measure V)) a ∂(ν : Measure V) :=
  KLS.LogConcave.integral_weakGamma_toLp_eq m hν hi hνU hU hf hfc x

/-- Graph limits identify the closed gradient of the limit. -/
theorem W1_identification (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    {x : ℕ → Lp ℝ 2 (ν : Measure V)} (hx : ∀ n, x n ∈ (hν.closedWeightedOperator m B hi).domain)
    {a : Lp ℝ 2 (ν : Measure V)} {b : Lp V 2 (ν : Measure V)}
    (hxa : Tendsto x atTop (𝓝 a))
    (hb : Tendsto (fun n => hν.closedWeightedOperator m B hi ⟨x n, hx n⟩) atTop (𝓝 b)) :
    ∃ h : a ∈ (hν.closedWeightedOperator m B hi).domain,
      hν.closedWeightedOperator m B hi ⟨a, h⟩ = b :=
  KLS.LogConcave.exists_closedWeightedOperator_eq_of_tendsto m B hν hi hx hxa hb

end W1

/-! ### The integrated Bochner inequality on smooth compactly supported tests -/

section W2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Symmetry of `ℒ` on compactly supported `C²` functions against the tilted law. -/
theorem W2_symmetry (m : Measure E) [m.IsAddHaarMeasure] {U f g : E → ℝ} (hU : ContDiff ℝ 1 U)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    ∫ x, weightedLaplacian U f x * g x ∂(m.tilted (-U)) =
      ∫ x, f x * weightedLaplacian U g x ∂(m.tilted (-U)) :=
  integral_weightedLaplacian_mul_comm m hU hf hfc hg hgc

/-- **The integrated Bochner inequality**, classical form. -/
theorem W2_classical (m : Measure E) [m.IsAddHaarMeasure] {μ : Measure E} [IsFiniteMeasure μ]
    {U : E → ℝ} (hμ : μ = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {f φ : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    0 ≤ (∫ x, weightedLaplacian U φ x * gamma f f x ∂μ) / 2 -
      ∫ x, φ x * gamma f (weightedLaplacian U f) x ∂μ :=
  integral_mul_gammaTwo_nonneg m hμ hU hconv hf hfc hφ hφc hφ0

/-- **The integrated Bochner inequality**, weak form: the classical gradients are replaced by
`L²` fields representing `∇f` and `∇(Af) = -∇(ℒf)`. -/
theorem W2_weak (m : Measure E) [m.IsAddHaarMeasure] {μ : Measure E} [IsFiniteMeasure μ]
    {U : E → ℝ} (hμ : μ = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {f φ : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {u w : Lp E 2 μ} (hu : (u : E → E) =ᵐ[μ] gradient f)
    (hw : (w : E → E) =ᵐ[μ] fun x => -gradient (weightedLaplacian U f) x) :
    0 ≤ (∫ x, weightedLaplacian U φ x * WeakGamma.apply u u x ∂μ) / 2 +
      ∫ x, φ x * WeakGamma.apply u w x ∂μ :=
  integral_mul_weakGamma_nonneg m hμ hU hconv hf hfc hφ hφc hφ0 hu hw

/-- Boundary case: the zero test function gives the trivial inequality. -/
theorem W2_zero_test (m : Measure E) [m.IsAddHaarMeasure] {μ : Measure E} [IsFiniteMeasure μ]
    {U : E → ℝ} (hμ : μ = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfc : HasCompactSupport f) :
    0 ≤ (∫ x, weightedLaplacian U (fun _ => (0 : ℝ)) x * gamma f f x ∂μ) / 2 -
      ∫ x, (0 : ℝ) * gamma f (weightedLaplacian U f) x ∂μ :=
  integral_mul_gammaTwo_nonneg m hμ hU hconv hf hfc contDiff_const
    (HasCompactSupport.zero) fun _ => le_rfl

/-- **Transfer of the weak inequality along `L²` convergence of the fields.** -/
theorem W3_transfer (m : Measure E) [m.IsAddHaarMeasure] {μ : Measure E} [IsFiniteMeasure μ]
    {U : E → ℝ} (hμ : μ = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {f : ℕ → E → ℝ}
    (hf : ∀ n, ContDiff ℝ 3 (f n)) (hfc : ∀ n, HasCompactSupport (f n))
    {u w : ℕ → Lp E 2 μ} {u₀ w₀ : Lp E 2 μ}
    (hu : ∀ n, ((u n : Lp E 2 μ) : E → E) =ᵐ[μ] gradient (f n))
    (hw : ∀ n, ((w n : Lp E 2 μ) : E → E) =ᵐ[μ]
      fun x => -gradient (weightedLaplacian U (f n)) x)
    (hul : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0))
    (hwl : Tendsto (fun n => ‖w n - w₀‖) atTop (𝓝 0)) :
    0 ≤ (∫ x, weightedLaplacian U φ x * WeakGamma.apply u₀ u₀ x ∂μ) / 2 +
      ∫ x, φ x * WeakGamma.apply u₀ w₀ x ∂μ :=
  integral_mul_weakGamma_nonneg_of_tendsto m hμ hU hconv hφ hφc hφ0 hf hfc hu hw hul hwl

end W2

/-! ### The closed-gradient transfer and the heat-flow statements -/

section W3

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} {B : V →L[ℝ] V} {m : Measure V} [m.IsAddHaarMeasure]

/-- For `f ∈ C_c^∞` and a `C^∞` potential, `A [f]` lies in the form domain and its closed
gradient is `-∇(ℒ f)`; the pair `([f], A [f])` therefore has a weak `Γ`. -/
theorem W3_generator_field (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ h : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
        Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, h⟩ :
          Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
        fun x => -gradient (weightedLaplacian U f) x :=
  ⟨KLS.LogConcave.adjointComp_toLp_mem_closedWeightedOperator_domain m hν hi hνU hU hf hfc,
    KLS.LogConcave.coeFn_closedWeightedOperator_adjointComp_toLp m hν hi hνU hU hf hfc _⟩

/-- **Weak `Γ₂ ≥ 0` for a generator-domain datum**, given `L²` convergence of the two fields of
smooth compactly supported data. The convergence hypotheses are not discharged here. -/
theorem W3_closed_transfer (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : V → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {fn : ℕ → V → ℝ}
    (hfn : ∀ n, ContDiff ℝ 3 (fn n)) (hfnc : ∀ n, HasCompactSupport (fn n))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hAF : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
        Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {u w : ℕ → Lp V 2 (ν : Measure V)}
    (hu : ∀ n, ((u n : Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)] gradient (fn n))
    (hw : ∀ n, ((w n : Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
      fun x => -gradient (weightedLaplacian U (fn n)) x)
    (hul : Tendsto (fun n => ‖u n - hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩‖) atTop (𝓝 0))
    (hwl : Tendsto (fun n => ‖w n - hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, hAF⟩‖) atTop (𝓝 0)) :
    0 ≤ (∫ a, weightedLaplacian U φ a *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) a ∂(ν : Measure V)) / 2 +
        ∫ a, φ a * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hAF⟩) a
          ∂(ν : Measure V) :=
  KLS.LogConcave.integral_mul_weakGamma_adjointComp_nonneg_of_tendsto m hν hi hνU hU hconv hφ hφc
    hφ0 hfn hfnc F hAF hu hw hul hwl

/-- **Non-vacuity of `W3_closed_transfer`**: for a smooth compactly supported datum the
convergence hypotheses hold with the constant sequence, so the weak `Γ₂` inequality is available
for the pair `([f], A [f])` with no approximation at all. -/
theorem W3_nonvacuous (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {U : V → ℝ} (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : V → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ (F : (adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (hAF : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
          Lp ℝ 2 (ν : Measure V)) ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      0 ≤ (∫ a, weightedLaplacian U φ a *
            WeakGamma.apply
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) a ∂(ν : Measure V)) / 2 +
          ∫ a, φ a * WeakGamma.apply
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hAF⟩) a
            ∂(ν : Measure V) := by
  refine ⟨⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩,
    KLS.LogConcave.adjointComp_toLp_mem_closedWeightedOperator_domain m hν hi hνU hU hf hfc, ?_⟩
  refine KLS.LogConcave.integral_mul_weakGamma_adjointComp_nonneg_of_tendsto m hν hi hνU
    (hU.of_le (by decide)) hconv hφ hφc hφ0 (fn := fun _ => f)
    (fun _ => hf.of_le (by decide)) (fun _ => hfc) _ _
    (u := fun _ => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
    (w := fun _ => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, KLS.LogConcave.adjointComp_toLp_mem_closedWeightedOperator_domain m hν hi hνU hU hf hfc⟩)
    (fun _ => hν.coeFn_closedWeightedOperator_toLp_gradient m hi hf hfc)
    (fun _ => KLS.LogConcave.coeFn_closedWeightedOperator_adjointComp_toLp m hν hi hνU hU hf hfc _)
    ?_ ?_ <;> simp

/-- **Integrated `Γ` contraction along the heat flow.** -/
theorem W3_heat_contraction (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty)
    (f : (hν.closedWeightedOperator m B hi).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : KLS.LogConcave.HeatSemigroup.operator m B hν hi ht f ∈
      (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi ⟨_, hft⟩)
        (hν.closedWeightedOperator m B hi ⟨_, hft⟩) a ∂(ν : Measure V) ≤
      ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi f)
        (hν.closedWeightedOperator m B hi f) a ∂(ν : Measure V) :=
  KLS.LogConcave.HeatSemigroup.integral_weakGamma_apply_le m B hν hi f ht hft

/-- **Positive-time integrated `Γ` bound for an arbitrary `L²` datum.** -/
theorem W3_heat_smoothing (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ}
    (ht : 0 < t) :
    ∃ h : KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le g ∈
        (hν.closedWeightedOperator m B hi).domain,
      2 * t * ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi ⟨_, h⟩)
        (hν.closedWeightedOperator m B hi ⟨_, h⟩) a ∂(ν : Measure V) ≤ ‖g‖ ^ 2 :=
  ⟨KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_of_pos m B hν hi g ht,
    KLS.LogConcave.HeatSemigroup.two_mul_integral_weakGamma_apply_le m B hν hi g ht _⟩

/-- **The weak generator identity applies to the heat flow of an arbitrary `L²` datum.** -/
theorem W3_heat_weak_ibp (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ}
    (ht : 0 < t) (x : (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply
        (hν.closedWeightedOperator m B hi
          ⟨KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le g,
            (KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m B hν hi g ht).2⟩)
        (hν.closedWeightedOperator m B hi x) a ∂(ν : Measure V) =
      ∫ a, (adjointComp (hν.closedWeightedOperator m B hi)
          ⟨KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le g,
            KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m B hν hi g ht⟩ :
          Lp ℝ 2 (ν : Measure V)) a * (x : Lp ℝ 2 (ν : Measure V)) a ∂(ν : Measure V) :=
  KLS.LogConcave.HeatSemigroup.integral_weakGamma_apply_eq_integral_mul_adjointComp m B hν hi g
    ht x

/-- **Second-order positive-time regularity**: for an arbitrary `L²` datum and `t > 0`, the
generator image `A (P_t g)` again has a closed weighted gradient, so both fields of the weak
`Γ₂` inequality exist. -/
theorem W3_heat_second_order (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ}
    (ht : 0 < t) :
    ∃ h : KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le g ∈
        (adjointComp (hν.closedWeightedOperator m B hi)).domain,
      (adjointComp (hν.closedWeightedOperator m B hi)
          ⟨KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le g, h⟩ :
          Lp ℝ 2 (ν : Measure V)) ∈ (hν.closedWeightedOperator m B hi).domain :=
  ⟨KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m B hν hi g ht,
    KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos m B hν hi g
      ht _⟩

/-- **Weak `Γ₂ ≥ 0` along the heat flow for an arbitrary `L²` datum.** Both fields exist without
extra hypotheses; the only remaining input is the `L²` approximation of those fields by the
fields of smooth compactly supported data, which is not discharged here. -/
theorem W3_heat_gamma_two (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : V → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) {fn : ℕ → V → ℝ}
    (hfn : ∀ n, ContDiff ℝ 3 (fn n)) (hfnc : ∀ n, HasCompactSupport (fn n))
    (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t)
    {u w : ℕ → Lp V 2 (ν : Measure V)}
    (hu : ∀ n, ((u n : Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)] gradient (fn n))
    (hw : ∀ n, ((w n : Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
      fun x => -gradient (weightedLaplacian U (fn n)) x)
    (hul : Tendsto (fun n => ‖u n -
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
          (KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
            (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩‖) atTop (𝓝 0))
    (hwl : Tendsto (fun n => ‖w n -
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos m
          (ContinuousLinearMap.id ℝ V) hν hi g ht
          (KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
            (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩‖) atTop (𝓝 0)) :
    0 ≤ (∫ a, weightedLaplacian U φ a *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                  (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                  (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩) a ∂(ν : Measure V)) / 2 +
        ∫ a, φ a * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨KLS.LogConcave.HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                  (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos
                m (ContinuousLinearMap.id ℝ V) hν hi g ht
                (KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m
                  (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩) a ∂(ν : Measure V) :=
  KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_tendsto m hν hi hνU hU
    hconv hφ hφc hφ0 hfn hfnc g ht hu hw hul hwl

end W3

end BakryEmeryWeakGammaAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integrable
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.ae_eq_of_ae_eq
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integral_eq_inner
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integral_self_eq_norm_sq
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integrable_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integrable_norm_mul_norm
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integral_norm_mul_norm_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integral_abs_sub_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.abs_integral_mul_sub_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.tendsto_integral_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integral_eq_integral_mul_adjointComp
#print axioms FunctionalInequalities.Analysis.BakryEmery.WeakGamma.integral_self_eq_norm_map_sq
#print axioms FunctionalInequalities.Analysis.BakryEmery.gradient_neg
#print axioms FunctionalInequalities.Analysis.BakryEmery.gradient_comp
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiff_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiff_gamma
#print axioms FunctionalInequalities.Analysis.BakryEmery.continuous_gamma
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gamma_left
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_comm
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_mul_gammaTwo_nonneg
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_mul_weakGamma_nonneg
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_mul_weakGamma_nonneg_of_tendsto
#print axioms FunctionalInequalities.Energy.WeightedGradient.lipschitzWith_mul
#print axioms FunctionalInequalities.Energy.WeightedGradient.IsTest.apply_mul_ae
#print axioms FunctionalInequalities.Energy.WeightedGradient.IsTest.mul
#print axioms FunctionalInequalities.Energy.WeightedGradient.IsTest.apply_comp_ae
#print axioms FunctionalInequalities.Energy.WeightedGradient.IsTest.comp
#print axioms FunctionalInequalities.Energy.WeightedGradient.coeFn_operator_mul
#print axioms FunctionalInequalities.Energy.WeightedGradient.coeFn_operator_comp
#print axioms FunctionalInequalities.KLS.LogConcave.toLp_mem_closedWeightedOperator_domain_of_isTest
#print axioms FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_apply_toLp
#print axioms FunctionalInequalities.KLS.LogConcave.coeFn_closedWeightedOperator_toLp
#print axioms FunctionalInequalities.KLS.LogConcave.coeFn_closedWeightedOperator_toLp_gradient
#print axioms FunctionalInequalities.KLS.LogConcave.weakGamma_toLp
#print axioms FunctionalInequalities.KLS.LogConcave.integral_weakGamma_eq_integral_mul_adjointComp
#print axioms FunctionalInequalities.KLS.LogConcave.integral_weakGamma_self
#print axioms FunctionalInequalities.KLS.LogConcave.exists_closedWeightedOperator_eq_of_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.integral_weakGamma_toLp_eq
#print axioms FunctionalInequalities.KLS.LogConcave.coeFn_closedWeightedOperator_mul
#print axioms FunctionalInequalities.KLS.LogConcave.coeFn_closedWeightedOperator_comp
#print axioms FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_mem_closedWeightedOperator_domain
#print axioms FunctionalInequalities.KLS.LogConcave.coeFn_closedWeightedOperator_adjointComp_toLp
#print axioms FunctionalInequalities.KLS.LogConcave.integral_mul_weakGamma_adjointComp_nonneg_of_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_weakGamma_apply_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.two_mul_integral_weakGamma_apply_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_weakGamma_apply_eq_integral_mul_adjointComp
#print axioms BakryEmeryWeakGammaAudit.W0_def
#print axioms BakryEmeryWeakGammaAudit.W0_measurable
#print axioms BakryEmeryWeakGammaAudit.W0_integrable
#print axioms BakryEmeryWeakGammaAudit.W0_representative
#print axioms BakryEmeryWeakGammaAudit.W0_self
#print axioms BakryEmeryWeakGammaAudit.W0_symm_and_bound
#print axioms BakryEmeryWeakGammaAudit.W0_integral
#print axioms BakryEmeryWeakGammaAudit.W0_tested
#print axioms BakryEmeryWeakGammaAudit.W0_stability
#print axioms BakryEmeryWeakGammaAudit.W0_stability_tested
#print axioms BakryEmeryWeakGammaAudit.W0_tendsto
#print axioms BakryEmeryWeakGammaAudit.W0_zero
#print axioms BakryEmeryWeakGammaAudit.W0_stability_refl
#print axioms BakryEmeryWeakGammaAudit.W1_leibniz_ae
#print axioms BakryEmeryWeakGammaAudit.W1_leibniz_closed
#print axioms BakryEmeryWeakGammaAudit.W1_chain_ae
#print axioms BakryEmeryWeakGammaAudit.W1_chain_closed
#print axioms BakryEmeryWeakGammaAudit.W1_operator_mul
#print axioms BakryEmeryWeakGammaAudit.W1_closed_mul
#print axioms BakryEmeryWeakGammaAudit.W1_closed_comp
#print axioms BakryEmeryWeakGammaAudit.W1_weak_ibp
#print axioms BakryEmeryWeakGammaAudit.W1_dirichlet
#print axioms BakryEmeryWeakGammaAudit.W1_bridge
#print axioms BakryEmeryWeakGammaAudit.W1_classical
#print axioms BakryEmeryWeakGammaAudit.W1_identification
#print axioms BakryEmeryWeakGammaAudit.W2_symmetry
#print axioms BakryEmeryWeakGammaAudit.W2_classical
#print axioms BakryEmeryWeakGammaAudit.W2_weak
#print axioms BakryEmeryWeakGammaAudit.W2_zero_test
#print axioms BakryEmeryWeakGammaAudit.W3_transfer
#print axioms BakryEmeryWeakGammaAudit.W3_generator_field
#print axioms BakryEmeryWeakGammaAudit.W3_closed_transfer
#print axioms BakryEmeryWeakGammaAudit.W3_nonvacuous
#print axioms BakryEmeryWeakGammaAudit.W3_heat_contraction
#print axioms BakryEmeryWeakGammaAudit.W3_heat_smoothing
#print axioms BakryEmeryWeakGammaAudit.W3_heat_weak_ibp
#print axioms BakryEmeryWeakGammaAudit.W3_heat_second_order
#print axioms BakryEmeryWeakGammaAudit.W3_heat_gamma_two
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.mem_domain_adjointComp_apply_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_adjointComp_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_tendsto
