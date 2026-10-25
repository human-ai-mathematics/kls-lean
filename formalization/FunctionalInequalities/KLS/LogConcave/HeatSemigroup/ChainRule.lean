import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.TestClass
import FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Scalar composition on the generator domain

For `A = T†T = -L`, the identity is
`int (A psi) Phi(F) = int Phi'(F) psi (A F) - int psi Phi''(F) Gamma(T F,T F)`.
The scalar function is globally smooth, vanishes at zero, and has bounded value and
first two derivatives. The core approximants need no range bound. The tested statement
needs only an L1 Gamma field. If Gamma is in L2, smooth core pairings and self-adjointness
identify `Phi(F) in D(A)` and the operator-valued chain rule.
-/
noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace LinearPMap
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

omit [CompleteSpace V] in
private theorem integrable_Lp_mul_compact (ψ : Lp ℝ 2 (ν : Measure V)) {q : V → ℝ}
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    Integrable (fun x ↦ ψ x * q x) (ν : Measure V) := by
  have hqL : MemLp q 2 (ν : Measure V) := hq.memLp_of_hasCompactSupport hqc
  refine (L2.integrable_inner (𝕜 := ℝ) ψ (hqL.toLp q)).congr ?_
  filter_upwards [hqL.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

private theorem integral_chain_smooth (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      Φ (q x) ∂(ν : Measure V)) =
    (∫ x, deriv Φ (q x) * ((ψ : Lp ℝ 2 (ν : Measure V)) x * -weightedLaplacian U q x)
      ∂(ν : Measure V)) -
    ∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) (q x)) * gamma q q x
      ∂(ν : Measure V) := by
  have hΦ₁ : ContDiff ℝ ∞ (deriv Φ) := (contDiff_infty_iff_deriv.mp hΦ).2
  have hΦ₂ : ContDiff ℝ ∞ (deriv (deriv Φ)) := (contDiff_infty_iff_deriv.mp hΦ₁).2
  have hs := integral_adjointComp_mul_toLp_eq m hν hi hνU hU ψ (hΦ.comp hq)
    (hqc.comp_left hΦ0)
  have heq : weightedLaplacian U (fun y ↦ Φ (q y)) = fun x ↦
      deriv Φ (q x) * weightedLaplacian U q x + deriv (deriv Φ) (q x) * gamma q q x := by
    funext x
    exact weightedLaplacian_comp U (hq.of_le (by decide))
      (fun y ↦ (hΦ.differentiable (by simp) (q y)).hasDerivAt)
      (hΦ₁.differentiable (by simp) (q x)).hasDerivAt
  have i₁ := integrable_Lp_mul_compact (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V))
    ((hΦ₁.continuous.comp hq.continuous).mul
      (continuous_weightedLaplacian hU (hq.of_le (by decide))))
    ((hasCompactSupport_weightedLaplacian U hqc).mul_left)
  have i₂ := integrable_Lp_mul_compact (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V))
    ((hΦ₂.continuous.comp hq.continuous).mul
      (continuous_gamma (hq.of_le (by decide)) (hq.of_le (by decide))))
    ((hasCompactSupport_gamma_left q hqc).mul_left)
  simp only [Function.comp_def] at hs
  rw [hs, heq]
  have hspl : (fun x ↦ (ψ : Lp ℝ 2 (ν : Measure V)) x *
      (deriv Φ (q x) * weightedLaplacian U q x + deriv (deriv Φ) (q x) * gamma q q x)) =
      (fun x ↦ (ψ : Lp ℝ 2 (ν : Measure V)) x * (deriv Φ (q x) * weightedLaplacian U q x)) +
      (fun x ↦ (ψ : Lp ℝ 2 (ν : Measure V)) x * (deriv (deriv Φ) (q x) * gamma q q x)) := by
    funext x; dsimp; ring
  rw [hspl]
  simp only [Pi.mul_apply, Function.comp_def] at i₁ i₂
  rw [integral_add' i₁ i₂]
  have e₁ : (∫ x, deriv Φ (q x) * ((ψ : Lp ℝ 2 (ν : Measure V)) x * -weightedLaplacian U q x)
      ∂(ν : Measure V)) = -(∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
        (deriv Φ (q x) * weightedLaplacian U q x) ∂(ν : Measure V)) := by
    rw [← integral_neg]; congr 1; funext x; ring
  rw [e₁]
  have e₂ : (∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) (q x)) * gamma q q x
      ∂(ν : Measure V)) = ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
        (deriv (deriv Φ) (q x) * gamma q q x) ∂(ν : Measure V) := by
    congr 1; funext x; ring
  rw [e₂]; ring

/-- All three pairings in the tested chain rule are genuine integrable functions. -/
theorem integrable_chain_pairings {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {M C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ r, |Φ r| ≤ M ∧ |deriv Φ r| ≤ M ∧ |deriv (deriv Φ) r| ≤ M)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    Integrable (fun x ↦ (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      Φ ((g : Lp ℝ 2 (ν : Measure V)) x)) (ν : Measure V) ∧
    Integrable (fun x ↦ deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) *
      WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V))
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x) (ν : Measure V) ∧
    Integrable (fun x ↦ ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x)) *
      WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) (ν : Measure V) := by
  have hΦ₁ : ContDiff ℝ ∞ (deriv Φ) := (contDiff_infty_iff_deriv.mp hΦ).2
  have hΦ₂ : ContDiff ℝ ∞ (deriv (deriv Φ)) := (contDiff_infty_iff_deriv.mp hΦ₁).2
  have hg := Lp.aestronglyMeasurable (g : Lp ℝ 2 (ν : Measure V))
  refine ⟨?_, ?_, ?_⟩
  · exact ((Lp.memLp _).integrable (by norm_num)).mul_bdd
      (hΦ.continuous.comp_aestronglyMeasurable hg)
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using (hbound _).1)
  · exact WeakGamma.integrable_mul (hΦ₁.continuous.comp_aestronglyMeasurable hg)
      (ae_of_all _ fun x ↦ (hbound _).2.1) _ _
  · exact WeakGamma.integrable_mul
      ((Lp.aestronglyMeasurable (ψ : Lp ℝ 2 (ν : Measure V))).mul
        (hΦ₂.continuous.comp_aestronglyMeasurable hg))
      (hψb.mono fun x hx ↦ by
        simp only [Pi.mul_apply, abs_mul]
        exact mul_le_mul hx (hbound _).2.2 (abs_nonneg _) hC) _ _

/-- The tested chain rule for arbitrary generator-domain data. The potential is only C1;
convexity, bounds on core approximants and boundedness of `A psi` are not required. -/
theorem integral_adjointComp_mul_comp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ r, |Φ r| ≤ M ∧ |deriv Φ r| ≤ M ∧ |deriv (deriv Φ) r| ≤ M)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ) x *
      Φ ((g : Lp ℝ 2 (ν : Measure V)) x) ∂(ν : Measure V)) =
    (∫ x, deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) *
      WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V))
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x
      ∂(ν : Measure V)) -
    ∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x)) *
      WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x
      ∂(ν : Measure V) := by
  revert ψ g
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro ψ hψb g
  have hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  obtain ⟨q, hq, hqc, h₁, h₂⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU g
  let a : ℕ → (adjointComp T).domain := fun n ↦
    ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hq n) (hqc n)⟩
  have h₃ : Tendsto (fun n ↦ ‖T ⟨(a n : Lp ℝ 2 (ν : Measure V)), (a n).2.2⟩ -
      T ⟨(g : Lp ℝ 2 (ν : Measure V)), g.2.2⟩‖) atTop (𝓝 0) := by
    have hp : Tendsto (fun n ↦ ‖adjointComp T (a n - g)‖ *
        ‖((a n - g : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) := by
      simpa only [LinearPMap.map_sub, Submodule.coe_sub, mul_zero] using h₂.mul h₁
    have hs : Tendsto (fun n ↦ √(‖adjointComp T (a n - g)‖ *
        ‖((a n - g : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V))‖)) atTop (𝓝 0) := by
      simpa using hp.sqrt
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hs
    have he : T ⟨((a n - g : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V)), (a n - g).2.2⟩ =
        T ⟨(a n : Lp ℝ 2 (ν : Measure V)), (a n).2.2⟩ - T ⟨_, g.2.2⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    have hb := Generated.norm_map_sq_le_mul T hd (a n - g)
    rw [he] at hb
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hb
  have hat : Tendsto (fun n ↦ (a n : Lp ℝ 2 (ν : Measure V))) atTop
      (𝓝 (g : Lp ℝ 2 (ν : Measure V))) := tendsto_iff_norm_sub_tendsto_zero.mpr h₁
  obtain ⟨k, hk, hka⟩ := (tendstoInMeasure_of_tendsto_Lp hat).exists_seq_tendsto_ae
  have hqa : ∀ᵐ x ∂(ν : Measure V), Tendsto (fun n ↦ q (k n) x) atTop
      (𝓝 ((g : Lp ℝ 2 (ν : Measure V)) x)) := by
    have he : ∀ᵐ x ∂(ν : Measure V), ∀ n, (a (k n) : Lp ℝ 2 (ν : Measure V)) x = q (k n) x :=
      ae_all_iff.mpr fun n ↦ (memLp_of_contDiff_hasCompactSupport ν (hq (k n)) (hqc (k n))).coeFn_toLp
    filter_upwards [hka, he] with x hx he
    simpa only [he] using hx
  have hΦ₁ : ContDiff ℝ ∞ (deriv Φ) := (contDiff_infty_iff_deriv.mp hΦ).2
  have hΦ₂ : ContDiff ℝ ∞ (deriv (deriv Φ)) := (contDiff_infty_iff_deriv.mp hΦ₁).2
  have L₁ : Tendsto (fun n ↦ ∫ x, (adjointComp T ψ) x * Φ (q (k n) x) ∂(ν : Measure V))
      atTop (𝓝 (∫ x, (adjointComp T ψ) x * Φ ((g : Lp ℝ 2 (ν : Measure V)) x) ∂(ν : Measure V))) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ |(adjointComp T ψ) x| * M)
      (fun n ↦ (Lp.aestronglyMeasurable _).mul
        (hΦ.continuous.comp (hq (k n)).continuous).aestronglyMeasurable)
      (((Lp.memLp (adjointComp T ψ)).integrable (by norm_num)).abs.mul_const M)
    · intro n; exact ae_of_all _ fun x ↦ by
        simpa only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_def, abs_mul] using
          mul_le_mul_of_nonneg_left (hbound (q (k n) x)).1 (abs_nonneg ((adjointComp T ψ) x))
    · filter_upwards [hqa] with x hx
      exact (hΦ.continuous.continuousAt.tendsto.comp hx).const_mul _
  have L₂ := WeakGamma.tendsto_integral_mul_of_ae
    (fun n ↦ (hΦ₁.continuous.comp (hq (k n)).continuous).aestronglyMeasurable) hM
    (fun n ↦ ae_of_all _ fun x ↦ (hbound (q (k n) x)).2.1)
    (hqa.mono fun x hx ↦ hΦ₁.continuous.continuousAt.tendsto.comp hx)
    (u := fun _ : ℕ ↦ (ψ : Lp ℝ 2 (ν : Measure V))) (u₀ := (ψ : Lp ℝ 2 (ν : Measure V)))
    (by simp) (h₂.comp hk.tendsto_atTop)
  have L₃ := WeakGamma.tendsto_integral_mul_of_ae
    (fun n ↦ (Lp.aestronglyMeasurable (ψ : Lp ℝ 2 (ν : Measure V))).mul
      (hΦ₂.continuous.comp (hq (k n)).continuous).aestronglyMeasurable) (mul_nonneg hC hM)
    (fun n ↦ hψb.mono fun x hx ↦ by
      simp only [Pi.mul_apply, Function.comp_def, abs_mul]; exact mul_le_mul hx (hbound (q (k n) x)).2.2 (abs_nonneg _) hC)
    (hqa.mono fun x hx ↦ (hΦ₂.continuous.continuousAt.tendsto.comp hx).const_mul
      ((ψ : Lp ℝ 2 (ν : Measure V)) x))
    (h₃.comp hk.tendsto_atTop) (h₃.comp hk.tendsto_atTop)
  refine tendsto_nhds_unique L₁ ((L₂.sub L₃).congr fun n ↦ ?_)
  have hAx : adjointComp T (a (k n)) = (memLp_neg_weightedLaplacian (ν := ν) hU
      (hq (k n)) (hqc (k n))).toLp (fun x ↦ -weightedLaplacian U (q (k n)) x) :=
    hν.adjointComp_toLp_eq m hi hνU hU (hq (k n)) (hqc (k n))
  have hTx : T ⟨(a (k n) : Lp ℝ 2 (ν : Measure V)), (a (k n)).2.2⟩ =
      (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq (k n)) (hqc (k n))).toLp
        (gradient (q (k n))) := hν.closedWeightedOperator_toLp_eq m hi (hq (k n)) (hqc (k n))
  rw [hAx, hTx]
  have e₁ : (∫ x, deriv Φ (q (k n) x) * WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V))
      ((memLp_neg_weightedLaplacian (ν := ν) hU (hq (k n)) (hqc (k n))).toLp
        (fun x ↦ -weightedLaplacian U (q (k n)) x)) x ∂(ν : Measure V)) =
      ∫ x, deriv Φ (q (k n) x) * ((ψ : Lp ℝ 2 (ν : Measure V)) x *
        -weightedLaplacian U (q (k n)) x) ∂(ν : Measure V) := by
    apply integral_congr_ae
    filter_upwards [(memLp_neg_weightedLaplacian (ν := ν) hU (hq (k n)) (hqc (k n))).coeFn_toLp] with x hx
    simp only [WeakGamma.apply_def, hx, Real.inner_apply]
  have e₂ : (∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) (q (k n) x)) *
      WeakGamma.apply
        ((memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq (k n)) (hqc (k n))).toLp (gradient (q (k n))))
        ((memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq (k n)) (hqc (k n))).toLp (gradient (q (k n)))) x
        ∂(ν : Measure V)) = ∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) (q (k n) x)) *
          gamma (q (k n)) (q (k n)) x ∂(ν : Measure V) := by
    apply integral_congr_ae
    filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq (k n)) (hqc (k n))).coeFn_toLp] with x hx
    simp only [WeakGamma.apply_def, hx, gamma_apply]
  simp only [Pi.mul_apply, Function.comp_def]
  rw [e₁, e₂]
  exact (integral_chain_smooth m hν hi hνU hU hΦ hΦ0 ψ (hq (k n)) (hqc (k n))).symm

/-- Smooth compact tests identify the actual self-adjoint generator domain and value.
The test core is constructed from the C1 potential; no core hypothesis is added. -/
theorem exists_mem_domain_apply_eq_of_smooth_pairings
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (u v : Lp ℝ 2 (ν : Measure V))
    (h : ∀ (q : V → ℝ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q),
      ⟪v, (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q⟫ =
      ⟪u, adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hq hqc⟩⟫) :
    ∃ hu : u ∈ (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨u, hu⟩ = v := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hs := isSelfAdjoint_adjointComp T (hν.closedWeightedOperator_isClosed m _ hi)
    (hν.dense_domain_closedWeightedOperator m _ hi)
  have he : (adjointComp T)† = adjointComp T := hs
  have hp : ∀ x : (adjointComp T).domain, ⟪v, (x : Lp ℝ 2 (ν : Measure V))⟫ =
      ⟪u, adjointComp T x⟫ := by
    intro x
    obtain ⟨q, hq, hqc, h₁, h₂⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU x
    have l₁ := (tendsto_const_nhds (x := v)).inner (𝕜 := ℝ) (tendsto_iff_norm_sub_tendsto_zero.mpr h₁)
    have l₂ := (tendsto_const_nhds (x := u)).inner (𝕜 := ℝ) (tendsto_iff_norm_sub_tendsto_zero.mpr h₂)
    exact tendsto_nhds_unique l₁ (l₂.congr (fun n ↦ (h (q n) (hq n) (hqc n)).symm))
  have ha := LinearPMap.mem_adjoint_domain_of_exists u ⟨v, hp⟩
  have hv := LinearPMap.adjoint_apply_eq hs.dense_domain ⟨u, ha⟩ hp
  have hg : (u, v) ∈ (adjointComp T)†.graph := by
    rw [← hv]
    exact (adjointComp T)†.mem_graph ⟨u, ha⟩
  rw [he] at hg
  obtain ⟨x, hx, hv⟩ := (adjointComp T).mem_graph_iff.mp hg
  have hx' : (x : Lp ℝ 2 (ν : Measure V)) = u := hx
  refine ⟨hx' ▸ x.2, ?_⟩
  convert hv using 1
  exact congrArg (adjointComp T) (Subtype.ext hx'.symm)

/-- The operator chain rule when the Gamma field is square-integrable. The output
includes the actual domain element and both representative identities. -/
theorem exists_comp_mem_domain (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦ0 : Φ 0 = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r, |Φ r| ≤ M ∧ |deriv Φ r| ≤ M ∧ |deriv (deriv Φ) r| ≤ M)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hΓ : MemLp (WeakGamma.apply
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)) 2 (ν : Measure V)) :
    ∃ u : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      (∀ᵐ x ∂(ν : Measure V), (u : Lp ℝ 2 (ν : Measure V)) x = Φ ((g : Lp ℝ 2 (ν : Measure V)) x)) ∧
      (∀ᵐ x ∂(ν : Measure V),
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) u) x =
        deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) *
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x -
        deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x) * WeakGamma.apply
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, g.2.2⟩) x) := by
  revert g
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro g hΓ
  let G := WeakGamma.apply (T ⟨_, g.2.2⟩) (T ⟨_, g.2.2⟩)
  have hΦ₁ := (contDiff_infty_iff_deriv.mp hΦ).2
  have hΦ₂ := (contDiff_infty_iff_deriv.mp hΦ₁).2
  have hg := Lp.aestronglyMeasurable (g : Lp ℝ 2 (ν : Measure V))
  have hu : MemLp (fun x ↦ Φ ((g : Lp ℝ 2 (ν : Measure V)) x)) 2 (ν : Measure V) :=
    MemLp.of_bound (hΦ.continuous.comp_aestronglyMeasurable hg) M
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using (hbound _).1)
  have hv₁ : MemLp (fun x ↦ deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) * (adjointComp T g) x)
      2 (ν : Measure V) :=
    L2.memLp_bddSmul (hΦ₁.continuous.comp_aestronglyMeasurable hg)
      (ae_of_all _ fun x ↦ (hbound _).2.1) (adjointComp T g)
  have hv₂ : MemLp (fun x ↦ deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x) * G x)
      2 (ν : Measure V) := by
    refine MemLp.ae_eq ?_ (L2.memLp_bddSmul (hΦ₂.continuous.comp_aestronglyMeasurable hg)
      (ae_of_all _ fun x ↦ (hbound _).2.2) (hΓ.toLp G))
    filter_upwards [hΓ.coeFn_toLp] with x hx
    change (hΓ.toLp G : V → ℝ) x = G x at hx
    simp only [smul_eq_mul, hx]
  let u := hu.toLp _
  let v := (hv₁.sub hv₂).toLp _
  obtain ⟨hum, hav⟩ := exists_mem_domain_apply_eq_of_smooth_pairings m hν hi hνU hU u v (by
    intro q hq hqc
    let ψ : (adjointComp T).domain :=
      ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hq hqc⟩
    obtain ⟨C, hC⟩ := hqc.exists_bound_of_continuous hq.continuous
    have hψ : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ |C| := by
      filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hq hqc).coeFn_toLp] with x hx
      simpa only [ψ, hx, Real.norm_eq_abs] using (hC x).trans (le_abs_self C)
    have hc := integral_adjointComp_mul_comp_eq m hν hi hνU hU hΦ hΦ0 hM (abs_nonneg C)
      hbound ψ hψ g
    have hi₁ := (integrable_chain_pairings m hν hi hΦ (abs_nonneg C) hbound ψ hψ g).2.1
    have hi₂ := (integrable_chain_pairings m hν hi hΦ (abs_nonneg C) hbound ψ hψ g).2.2
    rw [L2.inner_def, L2.inner_def]
    have e₁ : (∫ x, ⟪v x, (ψ : Lp ℝ 2 (ν : Measure V)) x⟫ ∂(ν : Measure V)) =
        (∫ x, deriv Φ ((g : Lp ℝ 2 (ν : Measure V)) x) *
          WeakGamma.apply (ψ : Lp ℝ 2 (ν : Measure V)) (adjointComp T g) x ∂(ν : Measure V)) -
        ∫ x, ((ψ : Lp ℝ 2 (ν : Measure V)) x * deriv (deriv Φ) ((g : Lp ℝ 2 (ν : Measure V)) x)) * G x
          ∂(ν : Measure V) := by
      rw [← integral_sub hi₁ hi₂]
      apply integral_congr_ae
      filter_upwards [(hv₁.sub hv₂).coeFn_toLp] with x hx
      simp only [v, hx, Pi.sub_apply, WeakGamma.apply, Real.inner_apply]
      dsimp [G, T, WeakGamma.apply]
      ring
    have e₂ : (∫ x, ⟪u x, (adjointComp T ψ) x⟫ ∂(ν : Measure V)) =
        ∫ x, (adjointComp T ψ) x * Φ ((g : Lp ℝ 2 (ν : Measure V)) x) ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with x hx
      simp only [u, hx, Real.inner_apply, mul_comm]
    exact e₁.trans (hc.symm.trans e₂.symm))
  refine ⟨⟨u, hum⟩, hu.coeFn_toLp, ?_⟩
  rw [hav]
  exact (hv₁.sub hv₂).coeFn_toLp

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
