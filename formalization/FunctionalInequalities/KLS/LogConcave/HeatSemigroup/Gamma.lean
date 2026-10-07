import FunctionalInequalities.Analysis.BakryEmery.Bochner.Integrated
import FunctionalInequalities.Energy.WeightedGradient.Leibniz
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator

/-!
# The weak `Γ` of the closed weighted gradient, and its heat-flow interfaces

This module connects three objects that were previously unrelated: the pointwise `Γ`/`Γ₂`
calculus of `Analysis/BakryEmery/`, the weak carré du champ
`Analysis.BakryEmery.WeakGamma.apply` of two `L²` vector fields, and the closed weighted gradient
`T̄ = hν.closedWeightedOperator m B hi` whose generated semigroup is `P_t = exp (-t T̄†T̄)`.
Throughout, `A = T̄†T̄ = adjointComp T̄` is the **nonnegative** generator and `ℒ = -A`.

## Contents

* **Representatives.** `coeFn_closedWeightedOperator_toLp` identifies the representative of
  `T̄ [g]` on a test class with `B ∘ ∇g`, and
  `coeFn_closedWeightedOperator_toLp_gradient` is the smooth compactly supported unit-weight
  case. These are what let the pointwise `Γ` of `Gamma.lean` be read as the weak `Γ` of `T̄`.
* **Weak integration by parts.** `integral_weakGamma_eq_integral_mul_adjointComp`:
  `∫ Γ(T̄ f, T̄ x) dν = ∫ (A f) x dν` for `f ∈ D(A)`, `x ∈ D(T̄)`, arbitrary weight `B`;
  `integral_weakGamma_self`: `∫ Γ(T̄ f, T̄ f) dν = ‖T̄ f‖²`; `integral_weakGamma_toLp_eq`: for
  `f ∈ C_c^∞` and `ν = m.tilted (-U)` this is the classical `∫ Γ(f, x) dν = ∫ (-ℒ f) x dν`, now
  against **every** `x ∈ D(T̄)`. `exists_closedWeightedOperator_eq_of_tendsto` records that
  graph-norm limits identify `T̄` of the limit.
* **Leibniz and chain rules for `T̄`** (`coeFn_closedWeightedOperator_mul`,
  `coeFn_closedWeightedOperator_comp`), on bounded tests and for `C¹` maps with bounded
  derivative fixing `0`; the analytic content is in `Energy/WeightedGradient/Leibniz.lean`.
* **Weak `Γ₂`.** `adjointComp_toLp_mem_closedWeightedOperator_domain` and
  `coeFn_closedWeightedOperator_adjointComp_toLp` compute `T̄ (A [f]) = [-∇(ℒ f)]` for
  `f ∈ C_c^∞` and a `C^∞` potential, and
  `integral_mul_weakGamma_adjointComp_nonneg_of_tendsto` states
  `0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν` for a generator-domain `F` whose
  two fields are `L²` limits of the corresponding fields of smooth compactly supported data.
* **Heat flow.** `HeatSemigroup.integral_weakGamma_apply_le` (integrated `Γ` contraction),
  `HeatSemigroup.two_mul_integral_weakGamma_apply_le` (`2t ∫ Γ(P_t g) dν ≤ ‖g‖²` for an
  arbitrary datum) and
  `HeatSemigroup.integral_weakGamma_apply_eq_integral_mul_adjointComp` (the weak generator
  identity applied to `P_t g`, legitimate because positive-time smoothing puts `P_t g` in
  `D(A)`).

## What this is not

`Γ(T̄ f, T̄ g)` is an `L¹` function; it need not be in `L²`, so the current `L²` semigroup cannot be applied to it in general and no
statement of the form `Γ(P_t f) ≤ P_t Γ(f)` is made, pointwise or otherwise. The integrated
contraction is an inequality between integrals, not a pointwise gradient bound. The convergence
hypotheses of `integral_mul_weakGamma_adjointComp_nonneg_of_tendsto` are **not** proved for
`F = P_t g`: at the time of this module that was the remaining gap, and it is a second-order
approximation property (`∇fₙ → T̄ F` and `∇(A fₙ) → T̄ (A F)` in `L²`) that graph-norm density of
`D(A)` in `D(T̄)` does not supply.

`KLS/LogConcave/HeatSemigroup/GammaTwo.lean` later **removes the second field** from the
inequality, so the second-order approximation is no longer needed: there the same conclusion is
obtained from `[fₙ] → F` and `A [fₙ] → A F` in `L²` alone
(`integral_mul_weakGamma_adjointComp_nonneg_of_graph_tendsto`). The statements of this module
are unchanged and remain correct; they are simply superseded by weaker-hypothesis versions.

No time differentiation of `s ↦ P_s Γ(P_{t-s} f)`, no Bakry–Émery gradient estimate,
no general-law passage and no Buser inequality is claimed.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section Representative

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- The representative of `T̄ [g]` on a test class is the weighted gradient `B ∘ ∇g`. -/
theorem coeFn_closedWeightedOperator_toLp {g : V → ℝ} (h : IsTest ν B g) :
    ((hν.closedWeightedOperator m B hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi h⟩ :
        Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)] Energy.WeightedGradient.apply B g := by
  rw [hν.closedWeightedOperator_apply_toLp m B hi h]
  exact h.memLp_apply.coeFn_toLp

/-- The representative of `T̄ [f]` for the unit weight and a smooth compactly supported `f` is
`∇f`. -/
theorem coeFn_closedWeightedOperator_toLp_gradient {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ :
        Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)] gradient f := by
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc]
  exact (memLp_gradient_of_contDiff_hasCompactSupport hf hfc).coeFn_toLp

/-- **The weak `Γ` of two smooth compactly supported classes is the classical `Γ`.** This is the
compatibility of `WeakGamma.apply` with `Analysis.BakryEmery.gamma`; it holds `ν`-almost
everywhere, which is the strongest form available since `T̄` only determines its values as `L²`
classes. -/
theorem weakGamma_toLp (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {f g : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) :
    WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hg hgc⟩)
      =ᵐ[(ν : Measure V)] gamma f g := by
  filter_upwards [WeakGamma.ae_eq_of_ae_eq
    (hν.coeFn_closedWeightedOperator_toLp_gradient m hi hf hfc)
    (hν.coeFn_closedWeightedOperator_toLp_gradient m hi hg hgc)] with x hx
  rw [hx, gamma_apply]

end Representative

section WeakGenerator

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **Weak integration by parts for the closed weighted gradient.** For `f ∈ D(T̄†T̄)` and every
`x ∈ D(T̄)`, `∫ Γ(T̄ f, T̄ x) dν = ∫ (T̄†T̄ f) x dν`. With `A = T̄†T̄` and `ℒ = -A` this is the weak
form of `∫ Γ(f, x) dν = -∫ (ℒ f) x dν`; it holds for an arbitrary weight `B`. -/
theorem integral_weakGamma_eq_integral_mul_adjointComp
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    (x : (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply
        (hν.closedWeightedOperator m B hi ⟨(f : Lp ℝ 2 (ν : Measure V)), f.2.2⟩)
        (hν.closedWeightedOperator m B hi x) a ∂(ν : Measure V) =
      ∫ a, (adjointComp (hν.closedWeightedOperator m B hi) f : Lp ℝ 2 (ν : Measure V)) a *
        (x : Lp ℝ 2 (ν : Measure V)) a ∂(ν : Measure V) :=
  WeakGamma.integral_eq_integral_mul_adjointComp
    (hν.dense_domain_closedWeightedOperator m B hi) f x

/-- The Dirichlet form as an integral of the weak `Γ`: `∫ Γ(T̄ f, T̄ f) dν = ‖T̄ f‖²`. -/
theorem integral_weakGamma_self (f : (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi f)
        (hν.closedWeightedOperator m B hi f) a ∂(ν : Measure V) =
      ‖hν.closedWeightedOperator m B hi f‖ ^ 2 :=
  WeakGamma.integral_self_eq_norm_sq _

/-- **Identification of a limit field.** If form-domain data converge in `L²` and their closed
gradients converge in `L²`, the limit lies in the form domain and the limit field is its closed
gradient. This is what makes the convergence hypotheses of the weak `Γ₂` transfer checkable:
they are exactly graph-norm convergence for `T̄`. -/
theorem exists_closedWeightedOperator_eq_of_tendsto
    {x : ℕ → Lp ℝ 2 (ν : Measure V)} (hx : ∀ n, x n ∈ (hν.closedWeightedOperator m B hi).domain)
    {a : Lp ℝ 2 (ν : Measure V)} {b : Lp V 2 (ν : Measure V)}
    (hxa : Tendsto x atTop (𝓝 a))
    (hb : Tendsto (fun n => hν.closedWeightedOperator m B hi ⟨x n, hx n⟩) atTop (𝓝 b)) :
    ∃ h : a ∈ (hν.closedWeightedOperator m B hi).domain,
      hν.closedWeightedOperator m B hi ⟨a, h⟩ = b :=
  exists_mem_domain_apply_eq_of_tendsto (hν.closedWeightedOperator_isClosed m B hi) hx hxa hb

end WeakGenerator

section Tilted

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **Compatibility of the weak generator interface with the classical one.** For
`f ∈ C_c^∞(V)`, `ν = m.tilted (-U)` and a `C¹` potential, the weak identity of
`integral_weakGamma_eq_integral_mul_adjointComp` is the classical
`∫ Γ(f, x) dν = ∫ (-ℒ f) x dν`, now valid for every `x ∈ D(T̄)` and not only for classical
test functions. -/
theorem integral_weakGamma_toLp_eq (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (x : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ∫ a, WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi x) a ∂(ν : Measure V) =
      ∫ a, -weightedLaplacian U f a * (x : Lp ℝ 2 (ν : Measure V)) a ∂(ν : Measure V) := by
  have hmem := hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc
  have key := hν.integral_weakGamma_eq_integral_mul_adjointComp m
    (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem⟩ x
  rw [key, hν.adjointComp_toLp_eq m hi hνU hU hf hfc]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU hf hfc).coeFn_toLp] with a ha
  rw [ha]

end Tilted

section Leibniz

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **Leibniz rule for the closed weighted gradient** on bounded tests. -/
theorem coeFn_closedWeightedOperator_mul {g₁ g₂ : V → ℝ} {M₁ M₂ : ℝ}
    (h₁ : IsTest ν B g₁) (h₂ : IsTest ν B g₂)
    (hb₁ : ∀ x, |g₁ x| ≤ M₁) (hb₂ : ∀ x, |g₂ x| ≤ M₂) :
    ((hν.closedWeightedOperator m B hi ⟨_,
        hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi
          (h₁.mul (hν.absolutelyContinuous_haar m hi) h₂ hb₁ hb₂)⟩ :
        Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
      fun x => g₁ x • Energy.WeightedGradient.apply B g₂ x +
        g₂ x • Energy.WeightedGradient.apply B g₁ x :=
  (coeFn_closedWeightedOperator_toLp m B hν hi
      (h₁.mul (hν.absolutelyContinuous_haar m hi) h₂ hb₁ hb₂)).trans
    (IsTest.apply_mul_ae (hν.absolutelyContinuous_haar m hi) h₁ h₂)

/-- **Chain rule for the closed weighted gradient.** -/
theorem coeFn_closedWeightedOperator_comp {g : V → ℝ} {Φ : ℝ → ℝ} {K : ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (hΦ0 : Φ 0 = 0) (hK : ∀ t, |deriv Φ t| ≤ K) (h : IsTest ν B g) :
    ((hν.closedWeightedOperator m B hi ⟨_,
        hν.toLp_mem_closedWeightedOperator_domain_of_isTest m B hi
          (h.comp (hν.absolutelyContinuous_haar m hi) hΦ hΦ0 hK)⟩ :
        Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
      fun x => deriv Φ (g x) • Energy.WeightedGradient.apply B g x :=
  (coeFn_closedWeightedOperator_toLp m B hν hi
      (h.comp (hν.absolutelyContinuous_haar m hi) hΦ hΦ0 hK)).trans
    (IsTest.apply_comp_ae (hν.absolutelyContinuous_haar m hi) (hΦ.differentiable one_ne_zero) h)

end Leibniz

section GammaTwo

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- For `f ∈ C_c^∞` and a `C^∞` potential, `A [f] = [-ℒ f]` again lies in the form domain, so the
weak `Γ` of the pair `([f], A [f])` is defined. -/
theorem adjointComp_toLp_mem_closedWeightedOperator_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
        Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  have hL : ContDiff ℝ ∞ fun x => -weightedLaplacian U f x :=
    (contDiff_weightedLaplacian hU hf (by norm_num) (by decide)).neg
  have hLc : HasCompactSupport fun x => -weightedLaplacian U f x :=
    (hasCompactSupport_weightedLaplacian U hfc).neg
  rw [hν.adjointComp_toLp_eq m hi hνU (hU.of_le (by norm_num)) hf hfc]
  exact hν.toLp_mem_closedWeightedOperator_domain_of_isTest m (ContinuousLinearMap.id ℝ V) hi
    (IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hL hLc)

/-- The representative of `T̄ (A [f])` is `-∇(ℒ f)`, for `f ∈ C_c^∞` and a `C^∞` potential. -/
theorem coeFn_closedWeightedOperator_adjointComp_toLp
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hmem : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
        Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmem⟩ :
        Lp V 2 (ν : Measure V)) : V → V) =ᵐ[(ν : Measure V)]
      fun x => -gradient (weightedLaplacian U f) x := by
  have hL : ContDiff ℝ ∞ fun x => -weightedLaplacian U f x :=
    (contDiff_weightedLaplacian hU hf (by norm_num) (by decide)).neg
  have hLc : HasCompactSupport fun x => -weightedLaplacian U f x :=
    (hasCompactSupport_weightedLaplacian U hfc).neg
  have hte : IsTest ν (ContinuousLinearMap.id ℝ V) fun x => -weightedLaplacian U f x :=
    IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hL hLc
  have hsub : (⟨_, hmem⟩ : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) =
      ⟨hte.memLp.toLp _, hν.toLp_mem_closedWeightedOperator_domain_of_isTest m
        (ContinuousLinearMap.id ℝ V) hi hte⟩ :=
    Subtype.ext (hν.adjointComp_toLp_eq m hi hνU (hU.of_le (by norm_num)) hf hfc)
  rw [hsub]
  refine (coeFn_closedWeightedOperator_toLp m (ContinuousLinearMap.id ℝ V) hν hi hte).trans
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Energy.WeightedGradient.apply_id]
  exact gradient_neg _ x

/-- **Weak `Γ₂ ≥ 0` for the closed weighted gradient of a generator-domain element**, whenever
the two fields `∇fₙ` and `∇(A fₙ) = -∇(ℒ fₙ)` of smooth compactly supported data converge in
`L²` to `T̄ F` and `T̄ (A F)`. This is the specialization of
`Analysis.BakryEmery.integral_mul_weakGamma_nonneg_of_tendsto` to the closed unit-weight
gradient; the two convergence hypotheses are the remaining gap and are **not** proved here for
`F = P_t g`. -/
theorem integral_mul_weakGamma_adjointComp_nonneg_of_tendsto
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
    (hconv : ConvexOn ℝ Set.univ U) {φ : V → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {fn : ℕ → V → ℝ} (hfn : ∀ n, ContDiff ℝ 3 (fn n)) (hfnc : ∀ n, HasCompactSupport (fn n))
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
  integral_mul_weakGamma_nonneg_of_tendsto m hνU hU hconv hφ hφc hφ0 hfn hfnc hu hw hul hwl

end GammaTwo

namespace HeatSemigroup

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **Integrated `Γ` contraction along the heat flow**: for every form-domain datum and every
`t ≥ 0`, `∫ Γ(P_t f) dν ≤ ∫ Γ(f) dν`. This is the `L¹` reading of the energy contraction
`norm_closedWeightedOperator_le`; it is **not** a pointwise statement, and gives no bound on
`Γ(P_t f)(x)` at any point. -/
theorem integral_weakGamma_apply_le (f : (hν.closedWeightedOperator m B hi).domain) {t : ℝ}
    (ht : 0 ≤ t) (hft : HeatSemigroup.operator m B hν hi ht f ∈
      (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi ⟨_, hft⟩)
        (hν.closedWeightedOperator m B hi ⟨_, hft⟩) a ∂(ν : Measure V) ≤
      ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi f)
        (hν.closedWeightedOperator m B hi f) a ∂(ν : Measure V) := by
  rw [WeakGamma.integral_self_eq_norm_sq, WeakGamma.integral_self_eq_norm_sq]
  have h := norm_closedWeightedOperator_le m B hν hi f ht hft
  have h0 : (0 : ℝ) ≤ ‖hν.closedWeightedOperator m B hi ⟨_, hft⟩‖ := norm_nonneg _
  nlinarith [h, h0]

/-- **Integrated `Γ` bound at positive times for an arbitrary `L²` datum**:
`2 t ∫ Γ(P_t g) dν ≤ ‖g‖²`. -/
theorem two_mul_integral_weakGamma_apply_le (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t)
    (hgt : HeatSemigroup.operator m B hν hi ht.le g ∈
      (hν.closedWeightedOperator m B hi).domain) :
    2 * t * ∫ a, WeakGamma.apply (hν.closedWeightedOperator m B hi ⟨_, hgt⟩)
        (hν.closedWeightedOperator m B hi ⟨_, hgt⟩) a ∂(ν : Measure V) ≤ ‖g‖ ^ 2 := by
  rw [WeakGamma.integral_self_eq_norm_sq]
  exact two_mul_norm_closedWeightedOperator_sq_le m B hν hi g ht hgt

/-- **The weak generator identity applies to the heat flow of an arbitrary `L²` datum.** For
every `g ∈ L²(ν)`, every `t > 0` and every `x ∈ D(T̄)`,
`∫ Γ(T̄ (P_t g), T̄ x) dν = ∫ (A (P_t g)) x dν`, because positive-time smoothing puts `P_t g` in
`D(A)`. -/
theorem integral_weakGamma_apply_eq_integral_mul_adjointComp (g : Lp ℝ 2 (ν : Measure V))
    {t : ℝ} (ht : 0 < t) (x : (hν.closedWeightedOperator m B hi).domain) :
    ∫ a, WeakGamma.apply
        (hν.closedWeightedOperator m B hi
          ⟨HeatSemigroup.operator m B hν hi ht.le g,
            (mem_adjointComp_domain_of_pos m B hν hi g ht).2⟩)
        (hν.closedWeightedOperator m B hi x) a ∂(ν : Measure V) =
      ∫ a, (adjointComp (hν.closedWeightedOperator m B hi)
          ⟨HeatSemigroup.operator m B hν hi ht.le g,
            mem_adjointComp_domain_of_pos m B hν hi g ht⟩ :
          Lp ℝ 2 (ν : Measure V)) a * (x : Lp ℝ 2 (ν : Measure V)) a ∂(ν : Measure V) :=
  hν.integral_weakGamma_eq_integral_mul_adjointComp m B hi
    ⟨_, mem_adjointComp_domain_of_pos m B hν hi g ht⟩ x

/-- **Weak `Γ₂ ≥ 0` along the heat flow.** For an *arbitrary* datum `g ∈ L²(ν)` and every
`t > 0`, positive-time smoothing supplies `P_t g ∈ D(A)`
(`mem_adjointComp_domain_of_pos`) and `A (P_t g) ∈ D(T̄)`
(`mem_closedWeightedOperator_domain_adjointComp_of_pos`), so **both** fields `T̄ (P_t g)` and
`T̄ (A (P_t g))` exist with no extra hypothesis. The weak `Γ₂` inequality then holds as soon as
those two fields are `L²` limits of `∇fₙ` and `-∇(ℒ fₙ)` for smooth compactly supported `fₙ`.

That last approximation is a second-order core property, and graph-norm density of `D(A)` in
`D(T̄)` does not supply it. It is **no longer needed**:
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core` in
`KLS/LogConcave/HeatSemigroup/GammaTwo.lean` proves the same conclusion from a first-order graph
condition on the generator. Everything else in the statement is proved. -/
theorem integral_mul_weakGamma_apply_nonneg_of_tendsto
    (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
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
        ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
          (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩‖)
      atTop (𝓝 0))
    (hwl : Tendsto (fun n => ‖w n -
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m
          (ContinuousLinearMap.id ℝ V) hν hi g ht
          (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩‖)
      atTop (𝓝 0)) :
    0 ≤ (∫ a, weightedLaplacian U φ a *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩) a
          ∂(ν : Measure V)) / 2 +
        ∫ a, φ a * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m
                (ContinuousLinearMap.id ℝ V) hν hi g ht
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩) a
          ∂(ν : Measure V) :=
  hν.integral_mul_weakGamma_adjointComp_nonneg_of_tendsto m hi hνU hU hconv hφ hφc hφ0 hfn hfnc
    ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht⟩ _ hu hw hul hwl

end HeatSemigroup

end FunctionalInequalities.KLS.LogConcave
