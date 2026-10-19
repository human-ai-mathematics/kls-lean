import FunctionalInequalities.KLS.BKL.LocalThirdCumulant
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation
import FunctionalInequalities.KLS.LogConcave.Transport
import FunctionalInequalities.KLS.LogConcave.Isotropic
import FunctionalInequalities.Analysis.Operator.InverseSqrt
import FunctionalInequalities.Probability.Transport

/-!
# Reduction of BKL Theorem 4.1 to compactly supported laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19: Theorem 4.1 is proved first for compactly supported
isotropic log-concave laws (`CumulantBoundCompact`), whose localization coefficients are smooth and
bounded. `LetwinCompactBound` is Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for
compactly supported laws: the interface between the Letwin stream and the Theorem 4.1 stream. It gives
the base case `CumulantBoundCompact 2 8` (BKL Lemma 4.2). Both names are hypotheses; neither Letwin's
theorem nor Theorem 4.1 is proved here.
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.Suspension

/-- `CumulantBound d b` restricted to compactly supported laws: `R^ν_{d+1} ≤ b Id` for every compactly
supported isotropic log-concave probability measure in every dimension (BKL arXiv:2610.05474v1, p. 19:
Theorem 4.1 is proved for compactly supported laws first). This names the hypothesis. -/
def CumulantBoundCompact (d : ℕ) (b : ℝ) : Prop :=
  ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
    KLS.Isotropic ν → _root_.FunctionalInequalities.KLS.LogConcave ν →
      IsCompact (ν : Measure (EuclideanSpace ℝ (Fin m))).support →
      ∀ u : EuclideanSpace ℝ (Fin m),
      ∑ J : Fin d → Fin m, cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2

/-- Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for compactly supported isotropic
log-concave laws in positive dimension: the input of BKL Lemma 4.2 used by the localization argument.
This names the hypothesis; it is the interface between the Letwin and the Theorem 4.1 streams. -/
def LetwinCompactBound : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
    _root_.FunctionalInequalities.KLS.LogConcave μ → KLS.Isotropic μ →
      IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support →
      LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n)))

/-- **Base case of the compact induction** (BKL Lemma 4.2 for compactly supported laws): the compact
Letwin bound gives `CumulantBoundCompact 2 8`. -/
theorem cumulantBoundCompact_two_of_letwinCompact (h : LetwinCompactBound) :
    CumulantBoundCompact 2 8 := by
  classical
  intro n μ hiso hLC hcompact u
  cases n with
  | zero =>
    have hs : (∑ J : Fin 2 → Fin 0, cumulant (μ : Measure _) 3
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin 0) ℝ (J k)) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro J _hJ
      exact Fin.elim0 (J 0)
    rw [hs]
    positivity
  | succ n =>
    let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
    have hbound := LogConcave.sum_sq_cumulant_three_le_of_letwin μ hLC hiso
      (h (n + 1) (Nat.succ_pos _) μ hLC hiso hcompact) b u
    have heq : (∑ J : Fin 2 → Fin (n + 1), cumulant (μ : Measure _) 3
        (Fin.cons u fun k => b (J k)) ^ 2) =
        ∑ j, ∑ k, cumulant (μ : Measure _) 3 ![u, b j, b k] ^ 2 := by
      have hreindex := (finTwoArrowEquiv (Fin (n + 1))).symm.sum_comp
        (fun J => cumulant (μ : Measure _) 3 (Fin.cons u fun k => b (J k)) ^ 2)
      calc
        _ = ∑ q : Fin (n + 1) × Fin (n + 1), cumulant (μ : Measure _) 3
            (Fin.cons u fun k => b (((finTwoArrowEquiv (Fin (n + 1))).symm q) k)) ^ 2 :=
          hreindex.symm
        _ = ∑ q : Fin (n + 1) × Fin (n + 1), cumulant (μ : Measure _) 3
            ![u, b q.1, b q.2] ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _hq
          congr 2
          ext i
          fin_cases i <;> rfl
        _ = _ := Fintype.sum_prod_type _
    change (∑ J : Fin 2 → Fin (n + 1), cumulant (μ : Measure _) 3
      (Fin.cons u fun k => b (J k)) ^ 2) ≤ _
    rw [heq]
    exact hbound

/-- A bound for all laws restricts to compactly supported ones. -/
theorem CumulantBound.compact {d : ℕ} {b : ℝ} (h : CumulantBound d b) : CumulantBoundCompact d b := by
  exact fun m ν hiso hLC _ u => h m ν hiso hLC u

end FunctionalInequalities.KLS.LogConcave.Suspension

namespace FunctionalInequalities.KLS.LogConcave.Suspension

section S8CCompactToGeneral

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

/-! Reduction to compactly supported laws (BKL p. 19 and end of Section 6): `cumulantBound_of_compact`. -/

open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis

section OperatorHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A positive square root is at least as close to `1` as its square: `‖S - 1‖ ≤ ‖S² - 1‖`. -/
theorem norm_sub_one_le_of_isPositive_mul_self
    [CompleteSpace E]
    {S Q : E →L[ℝ] E} (hS : S.IsPositive)
    (hQ : S * S = Q) : ‖S - 1‖ ≤ ‖Q - 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set y := (S - 1) x with hy
  have hkey : ‖y‖ ≤ ‖(S + 1) y‖ := by
    have h1 : ‖y‖ * ‖y‖ ≤ ‖(S + 1) y‖ * ‖y‖ := by
      calc
        ‖y‖ * ‖y‖ = ⟪y, y⟫ := (real_inner_self_eq_norm_mul_norm y).symm
        _ ≤ ⟪S y, y⟫ + ⟪y, y⟫ := by
          have := hS.inner_nonneg_left y
          linarith
        _ = ⟪(S + 1) y, y⟫ := by
          rw [add_apply, one_apply_eq_self, inner_add_left]
        _ ≤ ‖(S + 1) y‖ * ‖y‖ := real_inner_le_norm _ _
    rcases (norm_nonneg y).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right h1 h0
  have h2 : (S + 1) y = (Q - 1) x := by
    rw [hy, ← hQ]
    simp only [add_apply, sub_apply,
      one_apply_eq_self, mul_apply_eq_comp, map_sub]
    abel
  calc
    ‖(S - 1) x‖ = ‖y‖ := rfl
    _ ≤ ‖(S + 1) y‖ := hkey
    _ = ‖(Q - 1) x‖ := by rw [h2]
    _ ≤ ‖Q - 1‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _

/-- An operator represented by a bilinear form is bounded by the form's norm. -/
theorem opNorm_le_of_inner_eq
    [CompleteSpace E]
    {A : E →L[ℝ] E}
    {κ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ}
    (h : ∀ u v : E, ⟪A u, v⟫ = κ ![u, v]) : ‖A‖ ≤ ‖κ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  have h1 : ‖A u‖ * ‖A u‖ ≤ (‖κ‖ * ‖u‖) * ‖A u‖ := by
    calc
      ‖A u‖ * ‖A u‖ = ⟪A u, A u⟫ := (real_inner_self_eq_norm_mul_norm _).symm
      _ = κ ![u, A u] := h u (A u)
      _ ≤ ‖κ ![u, A u]‖ := le_abs_self _
      _ ≤ ‖κ‖ * ∏ i, ‖(![u, A u] : Fin 2 → E) i‖ := κ.le_opNorm _
      _ = (‖κ‖ * ‖u‖) * ‖A u‖ := by
        rw [Fin.prod_univ_two]
        simp [mul_assoc]
  rcases (norm_nonneg (A u)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_right h1 h0

/-- An operator with `‖A - 1‖ < 1` is strictly positive, hence a unit, when self-adjoint. -/
theorem inner_self_pos_of_norm_sub_one_lt
    [CompleteSpace E]
    {A : E →L[ℝ] E} (hA : ‖A - 1‖ < 1) {v : E} (hv : v ≠ 0) :
    0 < ⟪A v, v⟫ := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 : ⟪A v, v⟫ = ‖v‖ * ‖v‖ + ⟪(A - 1) v, v⟫ := by
    rw [sub_apply, one_apply_eq_self, inner_sub_left,
      real_inner_self_eq_norm_mul_norm]
    ring
  have h2 : ⟪(A - 1) v, v⟫ ≥ -(‖A - 1‖ * ‖v‖ * ‖v‖) := by
    have := real_inner_le_norm ((A - 1) v) (-v)
    rw [inner_neg_right, norm_neg] at this
    have h3 := ContinuousLinearMap.le_opNorm (A - 1) v
    nlinarith [norm_nonneg ((A - 1) v)]
  rw [h1]
  nlinarith [mul_pos hv' hv', norm_nonneg (A - 1)]

/-- Inverse square roots of operators converging to `1` converge to `1`. -/
theorem tendsto_inverseSqrt_one
    [CompleteSpace E]
    [FiniteDimensional ℝ E] {Sg : ℕ → E →L[ℝ] E}
    (hSg : Tendsto Sg atTop (𝓝 1))
    (hpos : ∀ᶠ R in atTop, (Sg R).IsPositive) (hunit : ∀ᶠ R in atTop, IsUnit (Sg R)) :
    Tendsto (fun R => inverseSqrt (Sg R)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun R => Ring.inverse (Sg R)) atTop (𝓝 1) := by
    have := (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)).tendsto.comp hSg
    simpa [Function.comp_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero] at hinv ⊢
  refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hinv
  filter_upwards [hpos, hunit] with R hp hu
  exact norm_sub_one_le_of_isPositive_mul_self (inverseSqrt_spec _ hp hu).1
    (inverseSqrt_spec _ hp hu).2.2.1

end OperatorHelpers

section MeasureHelpers

variable {E : Type*} [NormedAddCommGroup E]

/-- A ball truncation has exponential moments of every order. -/
theorem integrable_exp_cond_closedBall
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (R : ℕ)
    (hR : ν (Metric.closedBall (0 : E) R) ≠ 0) (t : ℝ) :
    Integrable (fun x => Real.exp (t * ‖x‖)) (ν[|Metric.closedBall (0 : E) R]) := by
  have hres : Integrable (fun x => Real.exp (t * ‖x‖)) (ν.restrict (Metric.closedBall (0 : E) R)) := by
    refine (integrable_const (Real.exp (|t| * R))).mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hx' : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
    calc
      t * ‖x‖ ≤ |t| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg x)
      _ ≤ |t| * R := mul_le_mul_of_nonneg_left hx' (abs_nonneg t)
  exact hres.smul_measure (ENNReal.inv_ne_top.2 hR)

/-- A ball truncation is compactly supported. -/
theorem isCompact_support_cond_closedBall
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) (R : ℕ) :
    IsCompact (ν[|Metric.closedBall (0 : E) R]).support := by
  refine (isCompact_closedBall (0 : E) R).of_isClosed_subset Measure.isClosed_support
    (Measure.support_subset_of_isClosed Metric.isClosed_closedBall ?_)
  rw [mem_ae_iff, cond_apply Metric.isClosed_closedBall.measurableSet]
  simp

/-- **Standardisation of a compactly supported log-concave law** with positive invertible covariance: the
law of `σ (x - a)`, with `σ = Cov^{-1/2}` and `a` the mean, is isotropic, log-concave and compactly
supported. -/
theorem exists_standardized
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ProbabilityMeasure E) (hLC : LogConcave μ)
    (hc : IsCompact (μ : Measure E).support)
    (hpos : (Covariance.operator (μ : Measure E)).IsPositive)
    (hunit : IsUnit (Covariance.operator (μ : Measure E))) :
    ∃ (η : ProbabilityMeasure E) (W : E ≃L[ℝ] E),
      (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (μ : Measure E)) ∧
      KLS.Isotropic η ∧ LogConcave η ∧ IsCompact (η : Measure E).support ∧
      (η : Measure E) = (μ : Measure E).map (fun x => W (x - ∫ y, y ∂(μ : Measure E))) := by
  let A : E →L[ℝ] E := Covariance.operator (μ : Measure E)
  let σ : E →L[ℝ] E := inverseSqrt A
  have hσ : IsUnit σ := by
    change IsUnit (inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
    exact inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
  let W : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hσ.unit
  have hW : (W : E →L[ℝ] E) = σ := by
    change (↑hσ.unit : E →L[ℝ] E) = σ
    exact hσ.unit_spec
  have hWx : ∀ x, W x = σ x := fun x => by rw [← hW]; rfl
  let a : E := ∫ y, y ∂(μ : Measure E)
  let ν' : ProbabilityMeasure E := Probability.translateLaw μ (-a)
  let η : ProbabilityMeasure E := Probability.mapContinuousLinearEquiv ν' W
  have hηcoe : (η : Measure E) = (ν' : Measure E).map W := rfl
  have hmeas : Measurable fun x : E => W (x - a) :=
    (W.continuous.comp (continuous_id.sub continuous_const)).measurable
  have hmap : (η : Measure E) = (μ : Measure E).map (fun x => W (x - a)) := by
    rw [hηcoe, Probability.coe_translateLaw,
      Measure.map_map W.continuous.measurable (measurable_const_add (-a))]
    congr 1
    funext x
    simp [neg_add_eq_sub]
  have hμlp : MemLp id 2 (μ : Measure E) := hLC.memLp_id_two
  have hint : Integrable id (μ : Measure E) := hμlp.integrable (by norm_num)
  have ht : MemLp id 2 (ν' : Measure E) := Probability.memLp_id_two_translateLaw μ (-a) hμlp
  have hηlp : MemLp id 2 (η : Measure E) := by
    rw [hηcoe, memLp_map_measure_iff measurable_id.aestronglyMeasurable W.continuous.aemeasurable]
    simpa [Function.comp_def] using (W : E →L[ℝ] E).comp_memLp' ht
  have hzero : ∫ x, x ∂(ν' : Measure E) = 0 :=
    Probability.integral_id_translateLaw_neg_integral μ hint
  have hmean : ∫ x, x ∂(η : Measure E) = 0 := by
    rw [hηcoe]
    change ∫ x, id x ∂((ν' : Measure E).map W) = 0
    rw [integral_map W.continuous.aemeasurable hηlp.aestronglyMeasurable]
    simp only [id_eq]
    rw [W.integral_comp_comm]
    simpa using congrArg W hzero
  have hself : (σ.adjoint : E →L[ℝ] E) = σ := (inverseSqrt_spec A hpos hunit).2.1.adjoint_eq
  have halg : (σ.comp A).comp σ = 1 := by
    ext x
    simpa [σ, ContinuousLinearMap.comp_apply] using
      congrArg (fun T : E →L[ℝ] E => T x) (inverseSqrt_mul_mul_inverseSqrt A hpos hunit)
  have hiso : KLS.Isotropic η := by
    refine ⟨hηlp, hmean, ?_⟩
    rw [hηcoe, Covariance.operator_map_continuousLinearEquiv, Covariance.operator_translateLaw, hW,
      hself]
    exact halg
  have hLCη : LogConcave η := (hLC.translateLaw (-a)).mapContinuousLinearEquiv W
  have hcη : IsCompact (η : Measure E).support := by
    have hK : IsCompact ((fun x : E => W (x - a)) '' (μ : Measure E).support) :=
      hc.image (W.continuous.comp (continuous_id.sub continuous_const))
    refine hK.of_isClosed_subset Measure.isClosed_support
      (Measure.support_subset_of_isClosed hK.isClosed ?_)
    have hinj : Function.Injective fun x : E => W (x - a) := fun x y hxy =>
      sub_left_injective (W.injective hxy)
    rw [mem_ae_iff, hmap, Measure.map_apply hmeas hK.isClosed.measurableSet.compl,
      Set.preimage_compl, Set.preimage_image_eq _ hinj]
    exact Measure.measure_compl_support
  exact ⟨η, W, hW, hiso, hLCη, hcη, hmap⟩

end MeasureHelpers

/-- **Reduction to compactly supported laws** (BKL arXiv:2610.05474v1, p. 19 and the end of Section 6, "standard
approximation argument"): a cumulant bound for compactly supported isotropic log-concave laws holds for all isotropic
log-concave laws, for every order `d + 1 ≥ 2`. -/
theorem cumulantBound_of_compact {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : CumulantBoundCompact d b) :
    CumulantBound d b := by
  classical
  intro m ν hiso hLC u
  obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff ν).1 hLC).exists_integrable_exp_norm
  let E := EuclideanSpace ℝ (Fin m)
  let νR : ℕ → Measure E := fun R => (ν : Measure E)[|Metric.closedBall (0 : E) R]
  let Sg : ℕ → E →L[ℝ] E := fun R => Covariance.operator (νR R)
  let T : ℕ → E →L[ℝ] E := fun R => inverseSqrt (Sg R)
  have hmass : ∀ᶠ R : ℕ in atTop, (ν : Measure E) (Metric.closedBall (0 : E) R) ≠ 0 :=
    eventually_measure_closedBall_ne_zero_cond (ν : Measure E)
  have hcum2 := tendsto_cumulant_cond_closedBall (ν : Measure E) hr hexp 2
  have hcumd := tendsto_cumulant_cond_closedBall (ν : Measure E) hr hexp (d + 1)
  have hSg : Tendsto Sg atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hcum2
    refine squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) ?_ hcum2
    filter_upwards [hmass] with R hR
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    have hexpR : Integrable (fun x => Real.exp (r * ‖x‖)) (νR R) :=
      (hexp.restrict (s := Metric.closedBall (0 : E) R)).smul_measure (ENNReal.inv_ne_top.2 hR)
    refine opNorm_le_of_inner_eq fun v w => ?_
    simp only [sub_apply]
    rw [cumulant_two_eq_covariance_of_integrable_exp
        ((ν : Measure E)[|Metric.closedBall (0 : E) R]) hr hexpR v w,
      cumulant_two_eq_covariance_of_integrable_exp (ν : Measure E) hr hexp v w,
      hiso.covariance_identity]
    simp [Sg, νR, inner_sub_left]
  have hpos : ∀ R, (Sg R).IsPositive := fun R =>
    (ContinuousLinearMap.isPositive_iff' _).mpr
      ⟨Covariance.operator_isSelfAdjoint _, fun v => by
        rw [Covariance.operator_inner]; exact ProbabilityTheory.covarianceBilin_self_nonneg v⟩
  have hlt : ∀ᶠ R in atTop, ‖Sg R - 1‖ < 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hSg).eventually (gt_mem_nhds one_pos)
  have hunit : ∀ᶠ R in atTop, IsUnit (Sg R) := hlt.mono fun R hR =>
    isUnit_of_inner_self_pos _ fun v hv => inner_self_pos_of_norm_sub_one_lt hR hv
  have hT : Tendsto T atTop (𝓝 1) := tendsto_inverseSqrt_one hSg (Eventually.of_forall hpos) hunit
  have hbound : ∀ᶠ R in atTop, ∑ J : Fin d → Fin m, cumulant (νR R) (d + 1)
      (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 ≤ b * ‖u‖ ^ 2 := by
    filter_upwards [hmass, hunit] with R hR hu
    have : IsProbabilityMeasure (νR R) := cond_isProbabilityMeasure hR
    let μR : ProbabilityMeasure E := ⟨νR R, inferInstance⟩
    have hLCR : LogConcave μR := hLC.cond (convex_closedBall _ _) Metric.isClosed_closedBall hR
    have hcR : IsCompact (μR : Measure E).support := isCompact_support_cond_closedBall (ν : Measure E) R
    obtain ⟨η, W, hW, hiso', hLC', hc', hmap⟩ := exists_standardized μR hLCR hcR (hpos R) hu
    have hb := h m η hiso' hLC' hc' u
    have hexpR : ∀ t : ℝ, Integrable (fun x => Real.exp (t * ‖x‖)) (νR R) :=
      integrable_exp_cond_closedBall (ν : Measure E) R hR
    have hk : 2 ≤ d + 1 := by omega
    have hself : (inverseSqrt (Covariance.operator (μR : Measure E))).adjoint =
        inverseSqrt (Covariance.operator (μR : Measure E)) :=
      (inverseSqrt_spec _ (hpos R) hu).2.1.adjoint_eq
    calc
      ∑ J : Fin d → Fin m, cumulant (νR R) (d + 1)
          (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
          = ∑ J : Fin d → Fin m, cumulant (η : Measure E) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 := by
        refine Finset.sum_congr rfl fun J _ => ?_
        congr 1
        rw [hmap, cumulant_map_affine W _ (μR : Measure E) hexpR hk, hW]
        congr 1
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp only [Fin.cons_zero, hself]; rfl
        · simp only [Fin.cons_succ, hself]; rfl
      _ ≤ b * ‖u‖ ^ 2 := hb
  have hlim : Tendsto (fun R => ∑ J : Fin d → Fin m, cumulant (νR R) (d + 1)
      (Fin.cons (T R u) fun k => T R (EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2) atTop
      (𝓝 (∑ J : Fin d → Fin m, cumulant (ν : Measure E) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2)) := by
    refine tendsto_finsetSum _ fun J _ => ?_
    refine (hcumd.eval ?_).pow 2
    rw [tendsto_pi_nhds]
    have hTv : ∀ v : E, Tendsto (fun R => T R v) atTop (𝓝 v) := fun v => by
      have := ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto 1).comp hT
      simpa [Function.comp_def] using this
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa only [Fin.cons_zero] using hTv u
    · simpa only [Fin.cons_succ] using hTv (EuclideanSpace.basisFun (Fin m) ℝ (J k))
  exact le_of_tendsto hlim hbound

end S8CCompactToGeneral

end FunctionalInequalities.KLS.LogConcave.Suspension
