import FunctionalInequalities.KLS.BKL.Localization.Process
import FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
import FunctionalInequalities.KLS.BKL.Localization.Standardization
import FunctionalInequalities.KLS.BKL.Localization.Energy
import FunctionalInequalities.KLS.BKL.CompactReduction
import FunctionalInequalities.KLS.BKL.CumulantEnvelope

/-!
# The cutoff energy induction: statement and base case

`CutoffEnergyClaim K d`: for every `ε > 0` and `T`, all large cutoffs and all cutoff Eldan processes satisfy
`E_{d+1}(0) + ½∫₀ᵀ E[γ² E_{d+2}(p_t)] dt ≤ b_{d+1} + ε` (the cutoff form of BKL (95)); the base case `d = 1` from Dynkin's
identity for `⟪A u, u⟫` (BKL (78)). Proof bodies: GPT (task S-7a); statements by the S-line sub-controller; placement: Claude.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

private theorem integral_le_of_nonneg_bound
    {α : Type*} [MeasurableSpace α] {M : Measure α} {f g : α → ℝ}
    (hg : Integrable g M)
    (hf : ∀ᵐ x ∂M, 0 ≤ f x)
    (hfg : ∀ᵐ x ∂M, f x ≤ g x) :
    ∫ x, f x ∂M ≤ ∫ x, g x ∂M := by
  by_cases hi : Integrable f M
  · exact integral_mono_ae hi hg hfg
  · rw [integral_undef hi]
    apply integral_nonneg_of_ae
    filter_upwards [hf, hfg] with x hx hxy
    exact hx.trans hxy

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

private theorem cumulantEnergy_one_is_one
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : KLS.Isotropic μ) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) 1 u = 1 := by
  classical
  have hexp :
      Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ((1 : ℝ) * ‖x‖))
        (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_exp_of_compact μ hc (by fun_prop)
  have hsqrt :
      inverseSqrt (Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [compactPosterior_zero] using
      KLS.Isotropic.inverseSqrt_covariance_compactPosterior_zero μ hc hiso
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let e : Fin n ≃ (Fin 1 → Fin n) :=
    { toFun := fun j _ => j
      invFun := fun J => J 0
      left_inv := fun _ => rfl
      right_inv := by
        intro J
        funext i
        fin_cases i
        rfl }
  have hcum (j : Fin n) :
      cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun _ : Fin 1 => b j)) = ⟪u, b j⟫ := by
    have h :=
      cumulant_two_eq_covariance_of_integrable_exp
        (μ : Measure (EuclideanSpace ℝ (Fin n))) (by norm_num) hexp u (b j)
    calc
      cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun _ : Fin 1 => b j)) =
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2 ![u, b j] := by
            congr 1
            funext i
            fin_cases i <;> rfl
      _ = ⟪Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n))) u, b j⟫ := h
      _ = ⟪u, b j⟫ := by
        rw [hiso.covariance_identity]
        rfl
  rw [cumulantEnergy, hsqrt]
  change
    ∑ J : Fin 1 → Fin n,
        cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun k => b (J k))) ^ 2 = 1
  calc
    ∑ J : Fin 1 → Fin n,
        cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
          (Fin.cons u (fun k => b (J k))) ^ 2 =
        ∑ j : Fin n,
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
            (Fin.cons u (fun k => b ((e j) k))) ^ 2 :=
      (e.sum_comp
        (fun J : Fin 1 → Fin n =>
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
            (Fin.cons u (fun k => b (J k))) ^ 2)).symm
    _ = ∑ j : Fin n,
          cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
            (Fin.cons u (fun _ : Fin 1 => b j)) ^ 2 := rfl
    _ = ∑ j : Fin n, ⟪u, b j⟫ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcum]
    _ = ∑ j : Fin n, ⟪u, b j⟫ * ⟪b j, u⟫ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm (b j) u]
      ring
    _ = ⟪u, u⟫ := b.sum_inner_mul_inner u u
    _ = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hu]
      norm_num

section Integrals

variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {γ : Param n → ℝ} {p : ℝ → Ω → Param n}

/-- **Time integrals of bounded functionals along the cutoff Eldan process** are integrable in `ω`: for a continuous
`φ` with `|φ(p_s)| ≤ B` for all `s ≥ 0` almost surely, `ω ↦ ∫₀ᵀ φ(p_s(ω)) ds` is integrable. -/
theorem IsEldanCutoff.integrable_integral_of_ae_bound (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s ω)| ≤ B) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, φ (p s ω)) P := by
  have hpcont := h.continuous
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have h1 :
      Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun ω s => Φ (p s ω)))
    exact hv.measurable_uncurry
  have hpmeas :
      Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
    have h' := Φ.symm.continuous.measurable.comp h1
    change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at h'
    simpa only [Φ.symm_apply_apply] using h'
  have hm :
      Measurable (fun z : Ω × ℝ => φ (p z.2 z.1)) :=
    hφ.measurable.comp hpmeas
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  have hmeas :
      AEStronglyMeasurable (fun z : Ω × ℝ => φ (p z.2 z.1)) (P.prod ν) :=
    hm.aestronglyMeasurable
  have hsm :
      AEStronglyMeasurable (fun ω => ∫ s, φ (p s ω) ∂ν) P :=
    hmeas.integral_prod_right'
  change Integrable (fun ω => ∫ s, φ (p s ω) ∂ν) P
  apply Integrable.of_bound hsm (B * T)
  filter_upwards [hB] with ω hω
  calc
    ‖∫ s, φ (p s ω) ∂ν‖ ≤ ∫ s, ‖φ (p s ω)‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioc (0 : ℝ) T, B := by
      apply setIntegral_mono_on
      · exact ((hφ.comp (hpcont ω)).norm).integrableOn_Ioc
      · exact continuous_const.integrableOn_Ioc
      · exact measurableSet_Ioc
      · intro s hs
        simpa only [Real.norm_eq_abs] using hω s hs.1.le
    _ = B * T := by
      simp [hT]
      ring

/-- **Monotonicity of the iterated integrals** along the cutoff Eldan process: if `0 ≤ φ(p_s) ≤ ψ(p_s)` for all
`s ≥ 0` almost surely and `ψ(p_s)` is almost surely bounded, then `E ∫₀ᵀ φ(p_s) ds ≤ E ∫₀ᵀ ψ(p_s) ds`. -/
theorem IsEldanCutoff.integral_integral_mono (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ ψ : Param n → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |ψ (p s ω)| ≤ B)
    (hle : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → 0 ≤ φ (p s ω) ∧ φ (p s ω) ≤ ψ (p s ω)) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, φ (p s ω) ∂volume ∂P ≤
      ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, ψ (p s ω) ∂volume ∂P := by
  have hψi := h.integrable_integral_of_ae_bound hψ hB hT
  have hφB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s ω)| ≤ B := by
    filter_upwards [hB, hle] with ω hω hωle
    intro s hs
    calc
      |φ (p s ω)| = φ (p s ω) := abs_of_nonneg (hωle s hs).1
      _ ≤ ψ (p s ω) := (hωle s hs).2
      _ ≤ |ψ (p s ω)| := le_abs_self _
      _ ≤ B := hω s hs
  apply integral_mono_ae
    (h.integrable_integral_of_ae_bound hφ hφB hT) hψi
  filter_upwards [hle] with ω hω
  exact setIntegral_mono_on
    (hφ.comp (h.continuous ω)).integrableOn_Ioc
    (hψ.comp (h.continuous ω)).integrableOn_Ioc
    measurableSet_Ioc (fun s hs => (hω s hs.1.le).2)

end Integrals

/-- The cutoff-weighted energy integral `∫₀ᵀ E[γ(p_s)² E_{d+1}(p_s)(u)] ds` (BKL (95)–(97) along the cutoff process). -/
def weightedEnergyIntegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : Param n → ℝ)
    (p : ℝ → Ω → Param n) (d : ℕ) (u : EuclideanSpace ℝ (Fin n)) (T : ℝ) : ℝ :=
  ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 *
    cumulantEnergy (compactPosterior μ hc (p s ω).1 (p s ω).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂volume ∂P

/-- **BKL (95) in cutoff form** at order `m = d + 1 ≥ 2` with envelope `b_m = envelope K m`: for every compactly
supported isotropic log-concave prior, unit vector `u`, tolerance `ε > 0` and horizon `T`, for every large enough cutoff
radius `R` and every ball-cutoff Eldan process on any Brownian setup,
`E_m(0) + ½ ∫₀ᵀ E[γ_R² E_{m+1}(p_s)] ds ≤ b_m + ε`. -/
def CutoffEnergyClaim (K : ℝ) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support),
    KLS.Isotropic μ → KLS.LogConcave μ → ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
    ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 ≤ T → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
        (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ),
        (∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) →
        (∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) →
        ∀ {p : ℝ → Ω → Param n}, IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p →
          cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) d u +
              (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P (ballCutoff R) p (d + 1) u T ≤
            envelope K (d + 1) + ε

/-- **Base case `m = 2`** (BKL p. 25, "the case m = 2 follows from (78)"): under the compact Letwin bound and
`K ≥ 5`, `CutoffEnergyClaim K 1`. -/
theorem cutoffEnergyClaim_one (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 5 ≤ K) :
    CutoffEnergyClaim K 1 := by
  classical
  intro n μ hc hiso hLC u hu ε hε T hT
  refine ⟨0, ?_⟩
  intro R _hR Ω _ P _ W ℱ hW hℱ0 hnull p hp
  let F : Param n → ℝ := fun q => ⟪cov μ hc q u, u⟫
  let G : Param n → ℝ := fun q => ballCutoff R q ^ 2 * F q
  let H : Param n → ℝ := fun q =>
    ballCutoff R q ^ 2 *
      cumulantEnergy
        (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) 2 u
  have hγ : IsCutoff (ballCutoff (V := Param n) R) :=
    isCutoff_ballCutoff R
  have hcov : ContDiff ℝ 2 (cov μ hc) :=
    (contDiff_posteriorCovariance_joint μ hc).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hF : ContDiff ℝ 2 F := by
    have hh : ContDiff ℝ 2 (fun q : Param n => ⟪u, cov μ hc q u⟫) :=
      (innerSL ℝ u).contDiff.comp (hcov.clm_apply contDiff_const)
    simpa only [F, real_inner_comm] using hh
  have hFpos (q : Param n) : 0 ≤ F q :=
    (KLS.Isotropic.compactPosterior_covariance_isPositive
      μ hc hiso q.1 q.2).inner_nonneg_left u
  have hGcont : Continuous G :=
    ((lipschitzWith_ballCutoff R).continuous.pow 2).mul hF.continuous
  have hGpos (q : Param n) : 0 ≤ G q :=
    mul_nonneg (sq_nonneg _) (hFpos q)
  have hHpos (q : Param n) : 0 ≤ H q := by
    dsimp only [H, cumulantEnergy]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  obtain ⟨r, hr⟩ :=
    hc.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  let r' : ℝ := max r 0
  have hr' : 0 ≤ r' := le_max_right _ _
  have hrsupp :
      (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r' := by
    intro x hx
    have hxnorm : ‖x‖ ≤ r := by
      simpa only [mem_closedBall_zero_iff] using hr hx
    simpa only [mem_closedBall_zero_iff] using
      hxnorm.trans (le_max_left r 0)
  have hFbound (q : Param n) : F q ≤ r' ^ 2 := by
    have hnorm : ‖cov μ hc q u‖ ≤ ‖cov μ hc q‖ := by
      simpa only [hu, mul_one] using (cov μ hc q).le_opNorm u
    calc
      F q ≤ ‖cov μ hc q u‖ * ‖u‖ := real_inner_le_norm _ _
      _ = ‖cov μ hc q u‖ := by rw [hu, mul_one]
      _ ≤ ‖cov μ hc q‖ := hnorm
      _ ≤ r' ^ 2 :=
        KLS.opNorm_covariance_compactPosterior_le_sq_radius
          μ hc hr' hrsupp q.1 q.2
  have hGbound (q : Param n) : G q ≤ r' ^ 2 := by
    have hg := ballCutoff_mem_Icc R q
    have hsq : ballCutoff R q ^ 2 ≤ 1 := by
      nlinarith [hg.1, hg.2]
    calc
      G q ≤ 1 * (r' ^ 2) :=
        mul_le_mul hsq (hFbound q) (hFpos q) zero_le_one
      _ = r' ^ 2 := one_mul _
  have hB :
      ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |8 * G (p s ω)| ≤ 8 * r' ^ 2 := by
    filter_upwards [] with ω
    intro s _hs
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (hGpos _))]
    exact mul_le_mul_of_nonneg_left (hGbound _) (by norm_num)
  have hupperInt :
      Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, 8 * G (p s ω)) P :=
    hp.integrable_integral_of_ae_bound
      (continuous_const.mul hGcont) hB hT
  have h8 : LogConcave.Suspension.CumulantBoundCompact 2 8 :=
    LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact hL
  have hq :=
    IsEldanCutoff.ae_Q_posSemidef (μ := μ) (hc := hc) hiso hγ hp
  have hbound :
      ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → H (p s ω) ≤ 8 * G (p s ω) := by
    filter_upwards [hq] with ω hω
    intro s hs
    have hcumul :=
      KLS.compactPosterior_cumulant_bound μ hc hiso hLC
        (d := 2) (b := 8) (p s ω).1 (p s ω).2
        (hω s hs).1 (hω s hs).2 (by norm_num) h8 u
    calc
      H (p s ω) ≤ ballCutoff R (p s ω) ^ 2 * (8 * F (p s ω)) :=
        mul_le_mul_of_nonneg_left hcumul (sq_nonneg _)
      _ = 8 * G (p s ω) := by
        dsimp only [G]
        ring
  have hmono :
      (∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, H (p s ω) ∂volume ∂P) ≤
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, 8 * G (p s ω) ∂volume ∂P := by
    apply integral_le_of_nonneg_bound hupperInt
    · exact Filter.Eventually.of_forall fun ω =>
        integral_nonneg fun s => hHpos (p s ω)
    · filter_upwards [hbound] with ω hω
      apply integral_le_of_nonneg_bound
        (((continuous_const.mul hGcont).comp (hp.continuous ω)).integrableOn_Ioc)
      · exact Filter.Eventually.of_forall fun s => hHpos (p s ω)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hω s hs.1.le
  have hmono' :
      weightedEnergyIntegral μ hc P (ballCutoff R) p 2 u T ≤
        8 * ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, G (p s ω) ∂volume ∂P := by
    change
      (∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, H (p s ω) ∂volume ∂P) ≤ _
    simpa only [integral_const_mul] using hmono
  have hdyn :=
    IsEldanCutoff.dynkin (μ := μ) (hc := hc) hiso hγ hℱ0 hnull hp hF hT
  have hgenq (q : Param n) : generator μ hc F q = -F q :=
    generator_inner_cov μ hc hiso q u u
  have hgen :
      (∫ ω, F (p T ω) ∂P) - F 0 =
        -(∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, G (p s ω) ∂volume ∂P) := by
    simpa only [hgenq, mul_neg, integral_neg] using hdyn.2
  have hinit : F 0 = 1 := by
    change
      ⟪Covariance.operator
        (compactPosterior μ hc 0 0 : Measure (EuclideanSpace ℝ (Fin n))) u, u⟫ = 1
    rw [compactPosterior_zero, hiso.covariance_identity]
    change ⟪u, u⟫ = 1
    rw [real_inner_self_eq_norm_mul_norm, hu]
    norm_num
  have hEF : 0 ≤ ∫ ω, F (p T ω) ∂P :=
    integral_nonneg fun ω => hFpos (p T ω)
  have hupper :
      weightedEnergyIntegral μ hc P (ballCutoff R) p 2 u T ≤ 8 := by
    linarith [hmono', hgen, hinit, hEF]
  have hzero := cumulantEnergy_one_is_one μ hc hiso u hu
  change
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) 1 u +
        (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P (ballCutoff R) p 2 u T ≤
      envelope K 2 + ε
  rw [hzero]
  have henvelope : envelope K 2 = K := by simp [envelope]
  rw [henvelope]
  linarith

end FunctionalInequalities.KLS.BKL.Localization

section S7CClaimToBound

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

/-! From the cutoff energy claim to the compact cumulant bound (task S-7c). -/

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

/-- For an isotropic law the energy at the initial parameter is the standard-basis sum
`Σ_J κ_{d+1}(u, e_J)²` (`σ = Cov⁻¹ᐟ² = Id`). -/
theorem cumulantEnergy_eq_sum_sq_of_isotropic {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hiso : KLS.Isotropic μ) (d : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) d u =
      ∑ J : Fin d → Fin n, cumulant (μ : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 := by
  have hsqrt :
      inverseSqrt (Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hiso.covariance_identity]
    change inverseSqrt (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = 1
    apply inverseSqrt_unique _ _ isUnit_one
    · exact ContinuousLinearMap.isPositive_one
    · simp
  simp only [cumulantEnergy, hsqrt, ContinuousLinearMap.id_apply]

/-- **From the cutoff claim to the cumulant bound** (BKL p. 27, `E_m(0) = ⟨R^μ_m u, u⟩`): `CutoffEnergyClaim K d`
gives `CumulantBoundCompact d (envelope K (d + 1))`. -/
theorem cumulantBoundCompact_of_cutoffEnergyClaim {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (h : CutoffEnergyClaim K d) :
    LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1)) := by
  classical
  unfold LogConcave.Suspension.CumulantBoundCompact
  intro m ν hiso hLC hc u
  by_cases hu0 : u = 0
  · subst u
    have hzero (J : Fin d → Fin m) :
        cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons (0 : EuclideanSpace ℝ (Fin m))
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) = 0 := by
      exact
        (cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)).map_coord_zero 0
          (by simp)
    calc
      ∑ J : Fin d → Fin m,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons (0 : EuclideanSpace ℝ (Fin m))
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro J _
        rw [hzero J]
        norm_num
      _ ≤ envelope K (d + 1) * ‖(0 : EuclideanSpace ℝ (Fin m))‖ ^ 2 :=
        mul_nonneg (envelope_nonneg hK (d + 1)) (sq_nonneg _)
  · let v : EuclideanSpace ℝ (Fin m) := ‖u‖⁻¹ • u
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have hv : ‖v‖ = 1 := by
      calc
        ‖v‖ = ‖(‖u‖ : ℝ)⁻¹‖ * ‖u‖ := norm_smul _ _
        _ = ‖u‖⁻¹ * ‖u‖ := by
          rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
        _ = 1 := inv_mul_cancel₀ hnorm
    have huv : ‖u‖ • v = u := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
    have hunitApprox (ε : ℝ) (hε : 0 < ε) :
        ∑ J : Fin d → Fin m,
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
          ≤ envelope K (d + 1) + ε := by
      obtain ⟨Ω, _, P, _, W, _⟩ :=
        FunctionalInequalities.Probability.Diffusion.exists_brownianSetup m
      let ℱ : Filtration ℝ ‹MeasurableSpace Ω› := usualFiltration W
      have hright : ℱ.IsRightContinuous := by
        dsimp [ℱ]
        infer_instance
      have hW : ∀ k, IsBrownianFiltration (W.W k) ℱ := by
        intro k
        change IsBrownianFiltration (W.W k) (usualFiltration W)
        exact usualFiltration_brownian W k
      have hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t := by
        intro t ht
        change usualFiltration W 0 ≤ usualFiltration W t
        exact usualFiltration_le_of_nonpos W t ht
      have hnull :
          ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s := by
        intro s hs hPs
        change MeasurableSet[usualFiltration W 0] s
        exact usualFiltration_null W s hs hPs
      obtain ⟨R₀, hR₀⟩ := h m ν hc hiso hLC v hv ε hε 0 (by norm_num)
      obtain ⟨p, hp⟩ :=
        @exists_isEldanCutoff m ν hc hiso Ω _ P _ W ℱ hright hW hℱ0 hnull
          (ballCutoff R₀) (isCutoff_ballCutoff R₀)
      have hineq := hR₀ R₀ le_rfl W ℱ hW hℱ0 hnull hp
      have hzeroIntegral :
          weightedEnergyIntegral ν hc P (ballCutoff R₀) p (d + 1) v 0 = 0 := by
        simp [weightedEnergyIntegral]
      rw [hzeroIntegral, mul_zero, add_zero] at hineq
      calc
        ∑ J : Fin d → Fin m,
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
            =
            cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin m))) d v :=
              (cumulantEnergy_eq_sum_sq_of_isotropic ν hiso d v).symm
        _ ≤ envelope K (d + 1) + ε := hineq
    have hunit :
        ∑ J : Fin d → Fin m,
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2
          ≤ envelope K (d + 1) := by
      apply le_of_forall_pos_lt_add
      intro ε hε
      have hhalf := hunitApprox (ε / 2) (by linarith)
      linarith
    have hscale (J : Fin d → Fin m) :
        cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons u
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) =
          ‖u‖ *
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Fin.cons v
                (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) := by
      calc
        cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons u
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) =
            cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
              (Function.update
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0
                (‖u‖ • v)) := by
                  rw [Fin.update_cons_zero, huv]
        _ =
            ‖u‖ •
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Function.update
                  (Fin.cons v
                    (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0 v) :=
              (cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)).map_update_smul
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) 0 ‖u‖ v
        _ =
            ‖u‖ *
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) := by
              rw [Fin.update_cons_zero, smul_eq_mul]
    calc
      ∑ J : Fin d → Fin m,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
            (Fin.cons u
              (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 =
          ∑ J : Fin d → Fin m,
            ‖u‖ ^ 2 *
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 := by
            apply Finset.sum_congr rfl
            intro J _
            rw [hscale, mul_pow]
      _ =
          ‖u‖ ^ 2 *
            ∑ J : Fin d → Fin m,
              cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
                (Fin.cons v
                  (fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k))) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ‖u‖ ^ 2 * envelope K (d + 1) :=
        mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖u‖)
      _ = envelope K (d + 1) * ‖u‖ ^ 2 := mul_comm _ _

/-- The envelope at order `d + 1` is the constant of `conjecture_of_cumulantBound`: `b_{d+1} = (d!)² K^d`. -/
theorem envelope_succ_eq (K : ℝ) (d : ℕ) : envelope K (d + 1) = (d.factorial : ℝ) ^ 2 * K ^ d := by
  unfold envelope
  rw [Nat.add_sub_cancel]
  exact mul_comm _ _

end FunctionalInequalities.KLS.BKL.Localization

end S7CClaimToBound

section S7DTheorem41Compact

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery

/-! The strong induction over the order and Theorem 4.1 for compactly supported laws with `K = 153`, given the induction step and the claim-to-bound passage as hypotheses (task S-7d). -/

namespace FunctionalInequalities.KLS.BKL.Localization

/-- **The cutoff claim at every order** (BKL (95) for all `m ≥ 2`), by induction from the base case and the step. -/
theorem cutoffEnergyClaim_all (hL : LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 153 ≤ K)
    (hstep : ∀ m : ℕ, 3 ≤ m →
      (∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim K (r - 1)) →
      (∀ r : ℕ, 2 ≤ r → r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope K r)) →
      CutoffEnergyClaim K (m - 1))
    (hbound : ∀ d : ℕ, CutoffEnergyClaim K d → LogConcave.Suspension.CumulantBoundCompact d (envelope K (d + 1))) :
    ∀ d : ℕ, 1 ≤ d → CutoffEnergyClaim K d := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro n ih hn
  by_cases h1 : n = 1
  · subst n
    exact cutoffEnergyClaim_one hL (by linarith)
  · have hn2 : 2 ≤ n := by
      omega
    let m : ℕ := n + 1
    have hm : 3 ≤ m := by
      dsimp [m]
      omega
    have hs : CutoffEnergyClaim K (m - 1) := by
      apply hstep m hm
      · intro r hr2 hrm
        exact ih (r - 1) (by omega) (by omega)
      · intro r hr2 hrm
        have hclaim : CutoffEnergyClaim K (r - 1) :=
          ih (r - 1) (by omega) (by omega)
        have hb := hbound (r - 1) hclaim
        rw [Nat.sub_add_cancel (by omega)] at hb
        exact hb
    have hm_sub : m - 1 = n := by
      dsimp [m]
    rw [hm_sub] at hs
    exact hs

/-- **BKL Theorem 4.1 for compactly supported laws** (conditional on the compact Letwin bound): there is a universal
`K ≥ 1` with `R^ν_{d+1} ≤ (d!)² K^d · Id` for every compactly supported isotropic log-concave `ν` and every `d ≥ 2`. -/
theorem theorem41Compact_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound)
    (hstep : ∀ m : ℕ, 3 ≤ m →
      (∀ r : ℕ, 2 ≤ r → r < m → CutoffEnergyClaim 153 (r - 1)) →
      (∀ r : ℕ, 2 ≤ r → r < m → LogConcave.Suspension.CumulantBoundCompact (r - 1) (envelope 153 r)) →
      CutoffEnergyClaim 153 (m - 1))
    (hbound : ∀ d : ℕ, CutoffEnergyClaim 153 d →
      LogConcave.Suspension.CumulantBoundCompact d (envelope 153 (d + 1))) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d : ℕ, 2 ≤ d →
      LogConcave.Suspension.CumulantBoundCompact d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  refine ⟨153, by norm_num, ?_⟩
  intro d hd
  have hclaim : CutoffEnergyClaim 153 d :=
    cutoffEnergyClaim_all hL (by norm_num) hstep hbound d (by omega)
  have hb := hbound d hclaim
  have henvelope : envelope 153 (d + 1) =
      (d.factorial : ℝ) ^ 2 * 153 ^ d := by
    unfold envelope
    rw [Nat.add_sub_cancel d 1]
    exact mul_comm _ _
  rw [henvelope] at hb
  exact hb

end FunctionalInequalities.KLS.BKL.Localization

end S7DTheorem41Compact

section S7B2BoundaryMeanValue

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion

/-! Boundary-term split for the ball cutoff and a mean-value choice of the horizon in `[T₀, 2T₀]` (task S-7b2). -/

namespace FunctionalInequalities.KLS.BKL.Localization

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {n : ℕ} {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ} {p : ℝ → Ω → Param n}

private theorem measurable_path
    {γ : Param n → ℝ}
    (h : IsEldanCutoff μ hc W ℱ hW γ p) (t : ℝ) :
    Measurable (p t) := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun s ω => Φ (p s ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have hm := Φ.symm.continuous.measurable.comp (hv.measurable t)
  change Measurable (fun w => Φ.symm (Φ (p t w))) at hm
  simpa only [Φ.symm_apply_apply] using hm

private theorem measurable_path_uncurry
    {γ : Param n → ℝ}
    (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun s ω => Φ (p s ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have hm :
      Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun w s => Φ (p s w)))
    exact hv.measurable_uncurry
  have hm' := Φ.symm.continuous.measurable.comp hm
  change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at hm'
  simpa only [Φ.symm_apply_apply] using hm'

private theorem cumulantEnergy_nonneg
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ cumulantEnergy ν d u := by
  unfold cumulantEnergy
  exact Finset.sum_nonneg fun J _ => sq_nonneg _

private theorem exists_le_setIntegral_div
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Integrable f (volume.restrict (Set.Ioc T (2 * T)))) :
    ∃ t ∈ Set.Icc T (2 * T),
      f t ≤ (∫ s in Set.Ioc T (2 * T), f s) / T := by
  let S : Set ℝ := Set.Ioc T (2 * T)
  let ν : Measure ℝ := volume.restrict S
  let A : ℝ := (∫ s in S, f s) / T
  by_contra hn
  have hn' : ∀ t ∈ Set.Icc T (2 * T), A < f t := by
    intro t ht
    have hnot : ¬ f t ≤ A := by
      intro hle
      exact hn ⟨t, ht, hle⟩
    exact lt_of_not_ge hnot
  have hnonneg : 0 ≤ᵐ[ν] fun s => f s - A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Set.Icc T (2 * T) := ⟨hs.1.le, hs.2⟩
    exact sub_nonneg.mpr (le_of_lt (hn' s hs'))
  have hfi : Integrable (fun s => f s - A) ν := by
    apply hf.sub
    exact integrable_const A
  have hsupport : S ⊆ Function.support (fun s => f s - A) := by
    intro s hs
    have hs' : s ∈ Set.Icc T (2 * T) := ⟨hs.1.le, hs.2⟩
    exact ne_of_gt (sub_pos.mpr (hn' s hs'))
  have hνS : 0 < ν S := by
    dsimp [ν, S]
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_self, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hpos : 0 < ∫ s, f s - A ∂ν := by
    apply (integral_pos_iff_support_of_nonneg_ae hnonneg hfi).2
    exact lt_of_lt_of_le hνS (measure_mono hsupport)
  have hmeasure : ν.real Set.univ = T := by
    dsimp [ν, S]
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hsub :
      (∫ s in S, f s) - A * T = ∫ s, f s - A ∂ν := by
    rw [integral_sub hf (integrable_const A), integral_const]
    simp only [smul_eq_mul]
    rw [hmeasure]
    ring
  have hzero : (∫ s in S, f s) - A * T = 0 := by
    dsimp [A]
    field_simp [ne_of_gt hT]; ring
  linarith

/-- **Splitting the boundary term** of (93) for the ball cutoff: since `γ_R = 1` on `‖q‖ ≤ R`,
`E E_{d+1}(p_t) ≤ E[γ_R(p_t)² E_{d+1}(p_t)] + C · P(‖p_t‖ > R)` whenever `E_{d+1} ≤ C` on symmetric PSD `Q`. -/
theorem IsEldanCutoff.integral_energy_le_weighted_add (hiso : KLS.Isotropic μ) {R : ℝ}
    (h : IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C)
    (hcont : Continuous fun q : Param n =>
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ w, cumulantEnergy (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P ≤
      (∫ w, ballCutoff R (p t w) ^ 2 *
        cumulantEnergy (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P) +
        C * (P {w | R < ‖p t w‖}).toReal := by
  let E : Param n → ℝ := fun q =>
    cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let A : Set Ω := {w | R < ‖p t w‖}
  have hpt : Measurable (p t) := measurable_path h t
  have hEm : Measurable (fun w => E (p t w)) :=
    hcont.measurable.comp hpt
  have hAm : MeasurableSet A := by
    change MeasurableSet {w | R < ‖p t w‖}
    exact measurableSet_Ioi.preimage hpt.norm
  have hQ := h.ae_Q_posSemidef hiso (isCutoff_ballCutoff R)
  have hEb : ∀ᵐ w ∂P, ‖E (p t w)‖ ≤ C := by
    filter_upwards [hQ] with w hw
    have he := hC (p t w) (hw t ht).1 (hw t ht).2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr
      ⟨(neg_nonpos.mpr hC0).trans (cumulantEnergy_nonneg _ _ _), he⟩
  have hEi : Integrable (fun w => E (p t w)) P := by
    apply Integrable.of_bound hEm.aestronglyMeasurable C
    exact hEb
  have hγm : Measurable (fun w => ballCutoff R (p t w)) :=
    (lipschitzWith_ballCutoff R).continuous.measurable.comp hpt
  have hwm :
      Measurable (fun w => ballCutoff R (p t w) ^ 2 * E (p t w)) :=
    (hγm.pow_const (2 : ℕ)).mul hEm
  have hwi : Integrable (fun w => ballCutoff R (p t w) ^ 2 * E (p t w)) P := by
    apply Integrable.of_bound hwm.aestronglyMeasurable C
    filter_upwards [hEb] with w hw
    have hg := ballCutoff_mem_Icc R (p t w)
    have he : 0 ≤ E (p t w) := cumulantEnergy_nonneg _ _ _
    have heC : E (p t w) ≤ C := (le_abs_self _).trans hw
    have h1 : 0 ≤ 1 - ballCutoff R (p t w) :=
      sub_nonneg.mpr hg.2
    have h2 : 0 ≤ 1 + ballCutoff R (p t w) :=
      add_nonneg zero_le_one hg.1
    have hg2 : ballCutoff R (p t w) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg h1 h2]
    have hle :
        ballCutoff R (p t w) ^ 2 * E (p t w) ≤ E (p t w) := by
      calc
        ballCutoff R (p t w) ^ 2 * E (p t w) ≤ 1 * E (p t w) :=
          mul_le_mul_of_nonneg_right hg2 he
        _ = E (p t w) := one_mul _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) he)]
    exact hle.trans heC
  have hAi0 : Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hAi : Integrable (fun w => C * A.indicator (fun _ : Ω => (1 : ℝ)) w) P :=
    hAi0.const_mul C
  have hpoint :
      ∀ᵐ w ∂P, E (p t w) ≤
        ballCutoff R (p t w) ^ 2 * E (p t w) +
          C * A.indicator (fun _ : Ω => (1 : ℝ)) w := by
    filter_upwards [hEb] with w hwC
    by_cases hwA : w ∈ A
    · have he : 0 ≤ E (p t w) := cumulantEnergy_nonneg _ _ _
      have heC : E (p t w) ≤ C := (le_abs_self _).trans hwC
      have hnonneg :
          0 ≤ ballCutoff R (p t w) ^ 2 * E (p t w) := by
        exact mul_nonneg (sq_nonneg _) he
      have hind :
          A.indicator (fun _ : Ω => (1 : ℝ)) w = 1 := by
        simp [Set.indicator, hwA]
      rw [hind]
      linarith
    · have hwA' : ¬ R < ‖p t w‖ := by
        intro hw'
        exact hwA (by simpa [A] using hw')
      have hR : ‖p t w‖ ≤ R := le_of_not_gt hwA'
      have hγ : ballCutoff R (p t w) = 1 := ballCutoff_eq_one hR
      simp [Set.indicator, hwA, hγ]
  have hind :
      ∫ w, A.indicator (fun _ : Ω => (1 : ℝ)) w ∂P = (P A).toReal := by
    rw [integral_indicator hAm, setIntegral_const]
    simp [Measure.real, smul_eq_mul]
  calc
    ∫ w, E (p t w) ∂P ≤
        ∫ w, ballCutoff R (p t w) ^ 2 * E (p t w) +
          C * A.indicator (fun _ : Ω => (1 : ℝ)) w ∂P :=
      integral_mono_ae hEi (hwi.add hAi) hpoint
    _ = (∫ w, ballCutoff R (p t w) ^ 2 * E (p t w) ∂P) +
          C * (P A).toReal := by
      rw [integral_add hwi hAi, integral_const_mul, hind]

/-- **Mean value in time** (the replacement for "let `T → ∞` along a subsequence", BKL p. 25): for a cutoff
process and a continuous energy bounded on symmetric PSD `Q`, some `t ∈ [T₀, 2T₀]` has
`E[γ(p_t)² E_{d+1}(p_t)] ≤ I_{d+1}(2T₀) / T₀`, where `I_{d+1}(T) = ∫₀ᵀ E[γ² E_{d+1}(p_s)] ds`. -/
theorem IsEldanCutoff.exists_weighted_energy_le (hiso : KLS.Isotropic μ) {γ : Param n → ℝ} (hγ : IsCutoff γ)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C)
    (hcont : Continuous fun q : Param n =>
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
    {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ t ∈ Set.Icc T₀ (2 * T₀),
      (∫ w, γ (p t w) ^ 2 *
        cumulantEnergy (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P) ≤
        weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀ := by
  let E : Param n → ℝ := fun q =>
    cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let F : ℝ → Ω → ℝ := fun s w => γ (p s w) ^ 2 * E (p s w)
  let f : ℝ → ℝ := fun s => ∫ w, F s w ∂P
  have hQ := h.ae_Q_posSemidef hiso hγ
  obtain ⟨Kγ, hγL⟩ := hγ.lipschitz
  have hFcont : Continuous (fun q => γ q ^ 2 * E q) :=
    (hγL.continuous.pow 2).mul hcont
  have hFbound :
      ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |F s w| ≤ C := by
    filter_upwards [hQ] with w hw
    intro s hs
    have he := hC (p s w) (hw s hs).1 (hw s hs).2
    have heC : E (p s w) ≤ C := by
      simpa [E] using he
    have he0 : 0 ≤ E (p s w) := cumulantEnergy_nonneg _ _ _
    have hg := hγ.mem_Icc (p s w)
    have h1 : 0 ≤ 1 - γ (p s w) :=
      sub_nonneg.mpr hg.2
    have h2 : 0 ≤ 1 + γ (p s w) :=
      add_nonneg zero_le_one hg.1
    have hg2 : γ (p s w) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg h1 h2]
    have hle : γ (p s w) ^ 2 * E (p s w) ≤ E (p s w) := by
      calc
        γ (p s w) ^ 2 * E (p s w) ≤ 1 * E (p s w) :=
          mul_le_mul_of_nonneg_right hg2 he0
        _ = E (p s w) := one_mul _
    change |γ (p s w) ^ 2 * E (p s w)| ≤ C
    exact abs_le.mpr
      ⟨(neg_nonpos.mpr hC0).trans (mul_nonneg (sq_nonneg _) he0), hle.trans heC⟩
  have hjoint :
      Measurable (fun z : Ω × ℝ => F z.2 z.1) := by
    change Measurable (fun z : Ω × ℝ => γ (p z.2 z.1) ^ 2 * E (p z.2 z.1))
    exact hFcont.measurable.comp (measurable_path_uncurry h)
  have hprod :
      Integrable (fun z : Ω × ℝ => F z.2 z.1)
        (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀)))) := by
    apply (integrable_prod_iff hjoint.aestronglyMeasurable).2
    constructor
    · filter_upwards [hFbound] with w hw
      apply Integrable.of_bound
        ((hFcont.comp (h.continuous w)).aestronglyMeasurable) C
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simpa only [F, Function.comp_apply, Real.norm_eq_abs] using
        hw s (hT₀.le.trans hs.1.le)
    · have hnormmeas :
          AEStronglyMeasurable
            (fun w => ∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀))) P := by
        simpa only using hjoint.norm.aestronglyMeasurable.integral_prod_right'
      apply Integrable.of_bound hnormmeas (C * (2 * T₀ - T₀))
      filter_upwards [hFbound] with w hw
      have hnonneg :
          0 ≤ ∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀)) :=
        integral_nonneg (fun s => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        (∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀))) ≤
            ∫ s in Set.Ioc T₀ (2 * T₀), C := by
          apply setIntegral_mono_on
          · exact (hFcont.comp (h.continuous w)).norm.integrableOn_Ioc
          · exact continuous_const.integrableOn_Ioc
          · exact measurableSet_Ioc
          · intro s hs
            simpa only [F, Function.comp_apply, Real.norm_eq_abs] using
              hw s (hT₀.le.trans hs.1.le)
        _ = C * (2 * T₀ - T₀) := by
          rw [setIntegral_const]
          simp only [smul_eq_mul]
          have hvol :
              (volume : Measure ℝ).real (Set.Ioc T₀ (2 * T₀)) = T₀ := by
            rw [Measure.real, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith)]
            ring
          rw [hvol]
          ring
  have hfint :
      Integrable f (volume.restrict (Set.Ioc T₀ (2 * T₀))) := by
    change Integrable (fun s => ∫ w, F s w ∂P)
      (volume.restrict (Set.Ioc T₀ (2 * T₀)))
    exact hprod.integral_prod_right
  obtain ⟨t, ht, htf⟩ := exists_le_setIntegral_div hT₀ hfint
  have hprod' :
      Integrable (Function.uncurry (fun w s => F s w))
        (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀)))) := by
    change Integrable (fun z : Ω × ℝ => F z.2 z.1)
      (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀))))
    exact hprod
  have hswap := integral_integral_swap hprod'
  have hfull :
      (∫ s in Set.Ioc T₀ (2 * T₀), f s) =
        ∫ w, ∫ s in Set.Ioc T₀ (2 * T₀), F s w ∂volume ∂P := by
    simpa only [f, Function.uncurry] using hswap.symm
  have hlefti :
      Integrable
        (fun w => ∫ s in Set.Ioc T₀ (2 * T₀), F s w) P :=
    hprod.integral_prod_left
  have hrighti :
      Integrable
        (fun w => ∫ s in Set.Ioc (0 : ℝ) (2 * T₀), F s w) P := by
    simpa only [F] using
      h.integrable_integral_of_ae_bound hFcont hFbound
        (T := 2 * T₀) (by linarith)
  have houter :
      (∫ w, ∫ s in Set.Ioc T₀ (2 * T₀), F s w ∂volume ∂P) ≤
        weightedEnergyIntegral μ hc P γ p d u (2 * T₀) := by
    have hmono :
        ∀ᵐ w ∂P,
          (∫ s in Set.Ioc T₀ (2 * T₀), F s w) ≤
            (∫ s in Set.Ioc (0 : ℝ) (2 * T₀), F s w) := by
      filter_upwards [] with w
      apply setIntegral_mono_set
      · exact (hFcont.comp (h.continuous w)).integrableOn_Ioc
      · exact Filter.Eventually.of_forall (fun s =>
          mul_nonneg (sq_nonneg _) (cumulantEnergy_nonneg _ _ _))
      · exact (Set.Ioc_subset_Ioc_left (by linarith)).eventuallyLE
    have hineq := integral_mono_ae hlefti hrighti hmono
    simpa only [weightedEnergyIntegral, F, E] using hineq
  refine ⟨t, ht, ?_⟩
  calc
    ∫ w, γ (p t w) ^ 2 *
        cumulantEnergy
          (compactPosterior μ hc (p t w).1 (p t w).2 :
            Measure (EuclideanSpace ℝ (Fin n))) d u ∂P =
        f t := by
          rfl
    _ ≤ (∫ s in Set.Ioc T₀ (2 * T₀), f s) / T₀ := htf
    _ ≤ weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀ := by
      rw [hfull]
      exact div_le_div_of_nonneg_right houter hT₀.le

end FunctionalInequalities.KLS.BKL.Localization

end S7B2BoundaryMeanValue
