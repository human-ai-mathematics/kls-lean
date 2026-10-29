import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.BakryEmery.GammaTwo
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov

/-!
# The heat-flow test class `ψ = P_s φ` for the weak `Γ₂` inequality

Heat evolution preserves essential bounds of smooth test data and their generator images.
Both resulting weak-Gamma pairings are integrable for arbitrary `L²` vector fields.
Generator symmetry extends pointwise Bochner to every nonnegative test in `D(A)` when the
**data** remain smooth and compactly supported. In particular the test can be `P_s φ`.

The extension to arbitrary data `F = P_r g` is **not proved**. A separate transfer theorem
retains explicit convergence of both fields `∇fₙ` and `-∇ℒfₙ`; the existing operator core for
`A` does not provide the second convergence. No time interpolation or gradient estimate is
claimed. All statements retain the current full-dimensional log-concave model.

`exists_seq_smooth_tendsto_regularized_fields` constructs two-field approximants of the form
`P_{r/2}[fₙ]` with `fₙ ∈ C_c^∞`. It does not remove the heat evolution from the approximants;
the smooth-data Bochner theorem therefore does not yet apply to them.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section Order

variable {α : Type*} [MeasurableSpace α] {μ : ProbabilityMeasure α}

/-- An a.e. bound `|f| ≤ C` is the `L²`-order bound `|f| ≤ C • 1`. -/
theorem abs_le_const_smul_one_of_ae {f : Lp ℝ 2 (μ : Measure α)} {C : ℝ}
    (hf : ∀ᵐ x ∂(μ : Measure α), |f x| ≤ C) : |f| ≤ C • L2.const μ 1 := by
  rw [← Lp.coeFn_le]
  filter_upwards [hf, Lp.coeFn_abs f, Lp.coeFn_smul C (L2.const μ 1), L2.const_coeFn μ 1]
    with x h1 h2 h3 h4
  rw [h2, h3, Pi.smul_apply, h4, smul_eq_mul, mul_one]
  exact h1

/-- The `L²`-order bound `|f| ≤ C • 1` is the a.e. bound `|f| ≤ C`. -/
theorem ae_abs_le_of_abs_le_const_smul_one {f : Lp ℝ 2 (μ : Measure α)} {C : ℝ}
    (hf : |f| ≤ C • L2.const μ 1) : ∀ᵐ x ∂(μ : Measure α), |f x| ≤ C := by
  have h := (Lp.coeFn_le _ _).mpr hf
  filter_upwards [h, Lp.coeFn_abs f, Lp.coeFn_smul C (L2.const μ 1), L2.const_coeFn μ 1]
    with x h1 h2 h3 h4
  rw [h2, h3, Pi.smul_apply, h4, smul_eq_mul, mul_one] at h1
  exact h1

end Order

section Bounds

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **Positivity of the heat flow, a.e. form**: `0 ≤ f` a.e. gives `0 ≤ P_t f` a.e. -/
theorem ae_nonneg_operator {t : ℝ} (ht : 0 ≤ t) {f : Lp ℝ 2 (ν : Measure V)}
    (hf : ∀ᵐ x ∂(ν : Measure V), 0 ≤ f x) :
    ∀ᵐ x ∂(ν : Measure V), 0 ≤ HeatSemigroup.operator m B hν hi ht f x := by
  have h0 : 0 ≤ f := (Lp.coeFn_nonneg f).mp (by filter_upwards [hf] with x hx; exact hx)
  have h1 := (Lp.coeFn_nonneg _).mpr (HeatSemigroup.positive m B hν hi ht h0)
  filter_upwards [h1] with x hx
  exact hx

/-- **Contraction of essential bounds, a.e. form**: `|f| ≤ C` a.e. gives `|P_t f| ≤ C` a.e. -/
theorem ae_abs_operator_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ C) :
    ∀ᵐ x ∂(ν : Measure V), |HeatSemigroup.operator m B hν hi ht f x| ≤ C :=
  ae_abs_le_of_abs_le_const_smul_one
    (HeatSemigroup.abs_le_const m B hν hi ht f hC (abs_le_const_smul_one_of_ae hf))

end Bounds

/-- Every positive-time heat datum admits two-field approximation by heat evolutions of
smooth compactly supported initial data. The approximating **heat values** are not asserted
to be smooth compactly supported functions, so this is not the higher-order core required
by `integral_weakGamma_nonneg_of_mem_domain_of_tendsto`. -/
theorem exists_seq_smooth_tendsto_regularized_fields
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
          (𝓝 (w r hr g)) := by
  dsimp only
  obtain ⟨f, hf, hfc, hlim, _⟩ := hν.exists_seq_smooth_tendsto_graph m B hi
    ⟨operator m B hν hi (half_pos hr).le g,
      mem_closedWeightedOperator_domain_of_pos m B hν hi g (half_pos hr)⟩
  refine ⟨f, hf, hfc, ?_, ?_⟩
  · have h := Generated.tendsto_map_apply_of_pos _
      (hν.closedWeightedOperator_isClosed m B hi)
      (hν.dense_domain_closedWeightedOperator m B hi) hlim (half_pos hr)
    have heq := Generated.add_time (hν.closedWeightedOperator m B hi)
      (hν.closedWeightedOperator_isClosed m B hi)
      (hν.dense_domain_closedWeightedOperator m B hi) (half_pos hr).le (half_pos hr).le g
    simp only [add_halves] at heq
    simpa only [operator, Generated.operator_apply, ← heq] using h
  · have h := Generated.tendsto_map_adjointComp_apply_of_pos _
      (hν.closedWeightedOperator_isClosed m B hi)
      (hν.dense_domain_closedWeightedOperator m B hi) hlim (half_pos hr)
    have heq := Generated.add_time (hν.closedWeightedOperator m B hi)
      (hν.closedWeightedOperator_isClosed m B hi)
      (hν.dense_domain_closedWeightedOperator m B hi) (half_pos hr).le (half_pos hr).le g
    simp only [add_halves] at heq
    simpa only [operator, Generated.operator_apply, ← heq] using h


section GeneratorBounds

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- A bounded generator image retains its essential bound under heat evolution. -/
theorem ae_abs_adjointComp_operator_le
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂(ν : Measure V), |(adjointComp (hν.closedWeightedOperator m B hi) f) x| ≤ C) :
    ∀ᵐ x ∂(ν : Measure V),
      |(adjointComp (hν.closedWeightedOperator m B hi)
        ⟨operator m B hν hi ht f, preserves_domain m B hν hi f ht⟩) x| ≤ C := by
  rw [generator_comm]
  exact ae_abs_operator_le m B hν hi ht _ hC hf

end GeneratorBounds

section SmoothBounds

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

set_option maxHeartbeats 800000 in
/-- Smooth compactly supported data and their generator images give uniformly bounded heat
orbit tests, including time zero. The constants do not depend on time. -/
theorem exists_bounds_operator_toLp
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (t : ℝ) (ht : 0 ≤ t),
      (∀ᵐ x ∂(ν : Measure V),
        |operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x| ≤ C) ∧
      (∀ᵐ x ∂(ν : Measure V),
        |(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi ht
            ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
            preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
              ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hφ hφc⟩ ht⟩) x| ≤ D) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨D, hD⟩ := (continuous_weightedLaplacian hU (hφ.of_le (by decide))).bounded_above_of_compact_support
    (hasCompactSupport_weightedLaplacian U hφc)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨C, D, hC0, hD0, fun t ht => ⟨?_, ?_⟩⟩
  · apply ae_abs_operator_le m _ hν hi ht _ hC0
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    simpa [hx, Real.norm_eq_abs] using hC x
  · refine ae_abs_adjointComp_operator_le m (ContinuousLinearMap.id ℝ V) hν hi
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hφ hφc⟩ ht hD0 ?_
    rw [hν.adjointComp_toLp_eq m hi hνU hU hφ hφc]
    filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU hφ hφc).coeFn_toLp] with x hx
    simpa [hx, Real.norm_eq_abs] using hD x

/-- Both weak Gamma pairings against a heat-evolved smooth test are genuinely integrable,
for arbitrary square-integrable vector fields. -/
theorem integrable_operator_toLp_weakGamma
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    {s : ℝ} (hs : 0 ≤ s) (u w : Lp V 2 (ν : Measure V)) :
    Integrable (fun x => operator m (ContinuousLinearMap.id ℝ V) hν hi hs
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * WeakGamma.apply u w x)
      (ν : Measure V) ∧
    Integrable (fun x => (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
      ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hs
        ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
        preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hφ hφc⟩ hs⟩) x * WeakGamma.apply u u x)
      (ν : Measure V) := by
  obtain ⟨C, D, _, _, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU hφ hφc
  exact ⟨WeakGamma.integrable_mul (Lp.aestronglyMeasurable _) (hb s hs).1 u w,
    WeakGamma.integrable_mul (Lp.aestronglyMeasurable _) (hb s hs).2 u u⟩


/-- Generator symmetry tests a smooth compactly supported function against any element of
`D(A)`. This does not differentiate a representative of the test class. -/
theorem integral_adjointComp_mul_toLp_eq
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x * q x
      ∂(ν : Measure V)) =
    -(∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * weightedLaplacian U q x ∂(ν : Measure V)) := by
  have heq := adjointComp_isFormalAdjoint
    (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
    ψ ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hq hqc⟩
  rw [hν.adjointComp_toLp_eq m hi hνU hU hq hqc, L2.inner_def, L2.inner_def] at heq
  have hleft : (∫ x, ⟪(adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x,
      ((memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q : Lp ℝ 2 (ν : Measure V)) x⟫
      ∂(ν : Measure V)) =
      ∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x * q x
      ∂(ν : Measure V) := by
    apply integral_congr_ae
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hq hqc).coeFn_toLp] with x hx
    rw [hx, Real.inner_apply]
  rw [hleft] at heq
  rw [heq, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU hq hqc).coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply]
  ring

omit [CompleteSpace V] in
private theorem integrable_mul_compact (ψ : Lp ℝ 2 (ν : Measure V)) {q : V → ℝ}
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    Integrable (fun x => ψ x * q x) (ν : Measure V) := by
  have hqL : MemLp q 2 (ν : Measure V) := hq.memLp_of_hasCompactSupport hqc
  have h := L2.integrable_inner (𝕜 := ℝ) ψ (hqL.toLp q)
  refine h.congr ?_
  filter_upwards [hqL.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply]

set_option maxHeartbeats 800000 in
/-- Pointwise Bochner, integrated against a nonnegative generator-domain class. The data
remain smooth and compactly supported; no smoothness or compact support of the test is assumed. -/
theorem integral_gammaTwo_nonneg_of_mem_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψ : ∀ᵐ x ∂(ν : Measure V), 0 ≤ (ψ : Lp ℝ 2 (ν : Measure V)) x)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      gamma f f x ∂(ν : Measure V)) / 2 -
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * gamma f (weightedLaplacian U f) x
        ∂(ν : Measure V) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have hΓ : ContDiff ℝ ∞ (gamma f f) := contDiff_gamma hf hf (by simp) (by simp)
  have hΓc : HasCompactSupport (gamma f f) := hasCompactSupport_gamma_left f hfc
  have hLf : ContDiff ℝ ∞ (weightedLaplacian U f) :=
    contDiff_weightedLaplacian hU hf (by decide) (by decide)
  have hA := integrable_mul_compact (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V))
    (continuous_weightedLaplacian hU1 (hΓ.of_le (by decide)))
    (hasCompactSupport_weightedLaplacian U hΓc)
  have hB := integrable_mul_compact (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V))
    (continuous_gamma (hf.of_le (by decide)) (hLf.of_le (by decide)))
    (hasCompactSupport_gamma_left (weightedLaplacian U f) hfc)
  have hnonneg : 0 ≤ ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * gammaTwo U f x ∂(ν : Measure V) := by
    apply integral_nonneg_of_ae
    filter_upwards [hψ] with x hx
    exact mul_nonneg hx (gammaTwo_nonneg (hU.of_le (by decide)) hconv (hf.of_le (by decide)) x)
  have hsplit : (∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * gammaTwo U f x ∂(ν : Measure V)) =
      (∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * weightedLaplacian U (gamma f f) x
        ∂(ν : Measure V)) / 2 -
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * gamma f (weightedLaplacian U f) x
        ∂(ν : Measure V) := by
    rw [← integral_div, ← integral_sub (hA.div_const 2) hB]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp only [gammaTwo_apply]; ring
  rw [hsplit] at hnonneg
  have hsym := integral_adjointComp_mul_toLp_eq m hν hi hνU hU1 ψ hΓ hΓc
  linarith

/-- The same domain-test inequality expressed using any representatives of the two smooth
fields. It can be transferred only when both fields converge in `L²`. -/
theorem integral_weakGamma_nonneg_of_mem_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψ : ∀ᵐ x ∂(ν : Measure V), 0 ≤ (ψ : Lp ℝ 2 (ν : Measure V)) x)
    {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {u w : Lp V 2 (ν : Measure V)}
    (hu : (u : V → V) =ᵐ[(ν : Measure V)] gradient f)
    (hw : (w : V → V) =ᵐ[(ν : Measure V)] fun x => -gradient (weightedLaplacian U f) x) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      WeakGamma.apply u u x ∂(ν : Measure V)) / 2 +
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * WeakGamma.apply u w x ∂(ν : Measure V) := by
  have e1 : (fun x => (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      WeakGamma.apply u u x) =ᵐ[(ν : Measure V)] fun x =>
      (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x * gamma f f x := by
    filter_upwards [hu] with x hx
    simp only [WeakGamma.apply_def, hx, gamma_apply]
  have e2 : (fun x => (ψ : Lp ℝ 2 (ν : Measure V)) x * WeakGamma.apply u w x)
      =ᵐ[(ν : Measure V)] fun x => -((ψ : Lp ℝ 2 (ν : Measure V)) x * gamma f (weightedLaplacian U f) x) := by
    filter_upwards [hu, hw] with x hx hy
    simp only [WeakGamma.apply_def, hx, hy, gamma_apply, inner_neg_right, mul_neg]
  rw [integral_congr_ae e1, integral_congr_ae e2, integral_neg, ← sub_eq_add_neg]
  exact integral_gammaTwo_nonneg_of_mem_domain m hν hi hνU hU hconv ψ hψ hf hfc


/-- Extension to limits of both fields, for a bounded nonnegative generator-domain test with
bounded generator image. The two convergences are explicit obligations, not consequences of
operator-core approximation in the graph norm of `A`. -/
theorem integral_weakGamma_nonneg_of_mem_domain_of_tendsto
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψ : ∀ᵐ x ∂(ν : Measure V), 0 ≤ (ψ : Lp ℝ 2 (ν : Measure V)) x)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (hAψb : ∀ᵐ x ∂(ν : Measure V),
      |(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x| ≤ D)
    {f : ℕ → V → ℝ} (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hfc : ∀ n, HasCompactSupport (f n))
    {u w : ℕ → Lp V 2 (ν : Measure V)} {u₀ w₀ : Lp V 2 (ν : Measure V)}
    (hu : ∀ n, (u n : V → V) =ᵐ[(ν : Measure V)] gradient (f n))
    (hw : ∀ n, (w n : V → V) =ᵐ[(ν : Measure V)] fun x => -gradient (weightedLaplacian U (f n)) x)
    (hul : Tendsto (fun n => ‖u n - u₀‖) atTop (𝓝 0))
    (hwl : Tendsto (fun n => ‖w n - w₀‖) atTop (𝓝 0)) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      WeakGamma.apply u₀ u₀ x ∂(ν : Measure V)) / 2 +
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * WeakGamma.apply u₀ w₀ x ∂(ν : Measure V) := by
  have h1 := WeakGamma.tendsto_integral_mul (Lp.aestronglyMeasurable _) hD hAψb hul hul
  have h2 := WeakGamma.tendsto_integral_mul (Lp.aestronglyMeasurable _) hC hψb hul hwl
  exact ge_of_tendsto' ((h1.neg.div_const 2).add h2) fun n =>
    integral_weakGamma_nonneg_of_mem_domain m hν hi hνU hU hconv ψ hψ (hf n) (hfc n) (hu n) (hw n)

/-- The heat-evolved test class is admissible for every smooth compactly supported datum.
This is a test-class extension on smooth data, not yet on arbitrary positive-time heat data. -/
theorem integral_weakGamma_operator_test_nonneg
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {s : ℝ} (hs : 0 ≤ s) {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {u w : Lp V 2 (ν : Measure V)}
    (hu : (u : V → V) =ᵐ[(ν : Measure V)] gradient f)
    (hw : (w : V → V) =ᵐ[(ν : Measure V)] fun x => -gradient (weightedLaplacian U f) x) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
      ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hs
        ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
        preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hφ hφc⟩ hs⟩) x *
        WeakGamma.apply u u x ∂(ν : Measure V)) / 2 +
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi hs
        ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * WeakGamma.apply u w x
          ∂(ν : Measure V) := by
  refine integral_weakGamma_nonneg_of_mem_domain m hν hi hνU hU hconv _ ?_ hf hfc hu hw
  apply ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi hs
  filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
  rw [hx]
  exact hφ0 x

end SmoothBounds

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
