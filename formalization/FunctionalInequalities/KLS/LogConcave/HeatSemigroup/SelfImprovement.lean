import FunctionalInequalities.L2.PositiveMap
import FunctionalInequalities.Analysis.TestFunctionOrder
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate
import FunctionalInequalities.Analysis.BakryEmery.RegularizedNorm

/-!
# Bakry's `L¹` self-improvement `|T̄P_t f| ≤ P_t |T̄f|`

Let `ν = m.tilted (-U)` be a full-dimensional log-concave probability law with a smooth convex
potential and unit weight, `T̄` the closed gradient, `A = T̄†T̄` and `P_t = exp (-t A)`. With
`N_ε(a) = √(ε + ‖a‖²) - √ε` (`regularizedNorm`) and `U_ε(a) = a/√(ε + ‖a‖²)`:

* `integral_regularizedNorm_smooth_nonneg`: for `q ∈ C_c^∞` and nonnegative `ψ ∈ D(A)`,
  `0 ≤ -∫ (Aψ) N_ε(∇q) + ∫ ψ ⟪U_ε(∇q), ∇(-ℒq)⟫`, from the pointwise inequality
  `ℒ(√(ε + Γ(q)) - √ε) - Γ(q, ℒq)/√(ε + Γ(q)) ≥ 0` (improved Bochner) and generator symmetry;
* `integral_regularizedNorm_nonneg`: the same for every `F ∈ D(A)` with `AF ∈ D(T̄)` and bounded
  `ψ`, `Aψ`, by the two-field smooth core;
* `integral_mul_regularizedNorm_le_of_pos` and `integral_mul_regularizedNorm_le`: monotonicity of
  `r ↦ ∫ (P_{t-r} φ) N_ε(T̄P_r f) dν`, hence `∫ φ N_ε(T̄P_t f) ≤ ∫ (P_t φ) N_ε(T̄f)`;
* `integral_mul_norm_le`: letting `ε → 0`, for every `f ∈ D(T̄)`, `t ≥ 0` and nonnegative
  `φ ∈ C_c^∞`, `∫ φ |T̄P_t f| dν ≤ ∫ (P_t φ) |T̄f| dν`.

This is the tested form of De Ponti–Mondino (28) for `K = 0`. Smooth-test order separation
and semigroup symmetry give `ae_norm_gradient_le`, the a.e. self-improvement on the whole
form domain. Mass preservation then gives `integral_norm_gradient_le`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

omit [CompleteSpace V] in
private theorem integrable_Lp_mul_compact' (ψ : Lp ℝ 2 (ν : Measure V)) {q : V → ℝ}
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    Integrable (fun x => ψ x * q x) (ν : Measure V) := by
  have hqL : MemLp q 2 (ν : Measure V) := hq.memLp_of_hasCompactSupport hqc
  refine (L2.integrable_inner (𝕜 := ℝ) ψ (hqL.toLp q)).congr ?_
  filter_upwards [hqL.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

omit [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
private theorem contDiff_sqrt_gamma {q : V → ℝ} (hq : ContDiff ℝ ∞ q) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun y => √(ε + gamma q q y) - √ε) := by
  have hΓ : ContDiff ℝ ∞ (gamma q q) := contDiff_gamma hq hq (by simp) (by simp)
  refine contDiff_iff_contDiffAt.mpr fun y => ?_
  have hpos : ε + gamma q q y ≠ 0 := by
    have : 0 ≤ gamma q q y := by rw [gamma_self]; positivity
    linarith
  exact ((Real.contDiffAt_sqrt hpos).comp y (contDiffAt_const.add hΓ.contDiffAt)).sub
    contDiffAt_const

/-- **The smooth-data self-improvement inequality.** -/
theorem integral_regularizedNorm_smooth_nonneg (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) {ε : ℝ} (hε : 0 < ε)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hψ : ∀ᵐ x ∂(ν : Measure V), 0 ≤ (ψ : Lp ℝ 2 (ν : Measure V)) x)
    {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
        Lp ℝ 2 (ν : Measure V)) x * (√(ε + gamma q q x) - √ε) ∂(ν : Measure V)) +
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
        (gamma q (fun y => -weightedLaplacian U q y) x / √(ε + gamma q q x)) ∂(ν : Measure V) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have hH := contDiff_sqrt_gamma hq hε
  have hHc : HasCompactSupport (fun y => √(ε + gamma q q y) - √ε) :=
    (hasCompactSupport_gamma_left q hqc).comp_left (g := fun s => √(ε + s) - √ε) (by simp)
  have hsym := integral_adjointComp_mul_toLp_eq m hν hi hνU hU1 ψ hH hHc
  have hLH := continuous_weightedLaplacian hU1 (hH.of_le (by decide))
  have hLHc := hasCompactSupport_weightedLaplacian U hHc
  have hpos : ∀ y, 0 < √(ε + gamma q q y) := fun y => Real.sqrt_pos.mpr (by
    have : 0 ≤ gamma q q y := by rw [gamma_self]; positivity
    linarith)
  have hq3 : ContDiff ℝ 3 q := hq.of_le (by decide)
  have hL : ContDiff ℝ ∞ (weightedLaplacian U q) :=
    contDiff_weightedLaplacian hU hq (by decide) (by decide)
  have hR : Continuous (fun y => gamma q (weightedLaplacian U q) y / √(ε + gamma q q y)) :=
    (continuous_gamma (hq.of_le (by decide)) (hL.of_le (by decide))).div
      (Real.continuous_sqrt.comp (continuous_const.add
        (continuous_gamma (hq.of_le (by decide)) (hq.of_le (by decide))))) fun y => (hpos y).ne'
  have hRc : HasCompactSupport (fun y => gamma q (weightedLaplacian U q) y / √(ε + gamma q q y)) :=
    (hasCompactSupport_gamma_left (weightedLaplacian U q) hqc).mul_right
      (f' := fun y => (√(ε + gamma q q y))⁻¹)
  have i₁ := integrable_Lp_mul_compact' (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V)) hLH hLHc
  have i₂ := integrable_Lp_mul_compact' (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V)) hR hRc
  have hneg : ∀ y, gamma q (fun y => -weightedLaplacian U q y) y = -gamma q (weightedLaplacian U q) y :=
    fun y => by rw [gamma_apply, gamma_apply, gradient_neg, inner_neg_right]
  rw [hsym, neg_neg]
  have e : ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
      (gamma q (fun y => -weightedLaplacian U q y) x / √(ε + gamma q q x)) ∂(ν : Measure V) =
      -∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
        (gamma q (weightedLaplacian U q) x / √(ε + gamma q q x)) ∂(ν : Measure V) := by
    rw [← integral_neg]; congr 1; funext x; rw [hneg]; ring
  rw [e, ← sub_eq_add_neg, ← integral_sub i₁ i₂]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hψ] with x hx
  rw [← mul_sub]
  exact mul_nonneg hx (weightedLaplacian_sqrt_sub_div_nonneg (hU.of_le (by decide)) hconv hq3 hε x)

/-- **The self-improvement inequality on `{F ∈ D(A) : AF ∈ D(T̄)}`.** For a nonnegative bounded
`ψ ∈ D(A)` with bounded `Aψ`:
`0 ≤ -∫ (Aψ) N_ε(T̄F) dν + ∫ ψ ⟪U_ε(T̄F), T̄(AF)⟫ dν`. -/
theorem integral_regularizedNorm_nonneg (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) {ε : ℝ} (hε : 0 < ε)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hψ0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ (ψ : Lp ℝ 2 (ν : Measure V)) x)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (hAψb : ∀ᵐ x ∂(ν : Measure V),
      |(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
        Lp ℝ 2 (ν : Measure V)) x| ≤ D)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hF : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
      Lp ℝ 2 (ν : Measure V)) ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    0 ≤ -(∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
        Lp ℝ 2 (ν : Measure V)) x * regularizedNorm ε
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, F.2.2⟩ :
            Lp V 2 (ν : Measure V)) x) ∂(ν : Measure V)) +
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * ⟪regularizedUnit ε
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, F.2.2⟩ :
            Lp V 2 (ν : Measure V)) x),
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hF⟩ :
            Lp V 2 (ν : Measure V)) x⟫ ∂(ν : Measure V) := by
  obtain ⟨q, hq, hqc, -, c₂, -, c₄⟩ := hν.exists_seq_smooth_tendsto_two_fields hνU hU F hF
  have L₁ := tendsto_integral_mul_regularizedNorm hε
    (tendsto_const_nhds (x := (adjointComp (hν.closedWeightedOperator m
      (ContinuousLinearMap.id ℝ V) hi) ψ : Lp ℝ 2 (ν : Measure V))))
    hD (Eventually.of_forall fun _ => hAψb) hAψb c₂
  have L₂ := tendsto_integral_mul_inner_regularizedUnit hε
    (Lp.aestronglyMeasurable (ψ : Lp ℝ 2 (ν : Measure V))) hC hψb c₂ c₄
  refine ge_of_tendsto (L₁.neg.add L₂) (Eventually.of_forall fun n => ?_)
  have hsm := integral_regularizedNorm_smooth_nonneg m hν hi hνU hU hconv hε ψ hψ0 (hq n) (hqc n)
  have e₁ : ∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
      Lp ℝ 2 (ν : Measure V)) x * regularizedNorm ε
        ((memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n) (hqc n)).toLp
          (gradient (q n)) x) ∂(ν : Measure V) =
      ∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
        Lp ℝ 2 (ν : Measure V)) x * (√(ε + gamma (q n) (q n) x) - √ε) ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n)
      (hqc n)).coeFn_toLp] with x hx
    rw [hx, regularizedNorm_def, gamma_self]
  have e₂ : ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * ⟪regularizedUnit ε
        ((memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n) (hqc n)).toLp
          (gradient (q n)) x),
        (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_weightedLaplacian hU (hq n) (by decide) (by decide)).neg
          (hasCompactSupport_weightedLaplacian U (hqc n)).neg).toLp
            (gradient (fun x => -weightedLaplacian U (q n) x)) x⟫ ∂(ν : Measure V) =
      ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
        (gamma (q n) (fun y => -weightedLaplacian U (q n) y) x / √(ε + gamma (q n) (q n) x))
        ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n)
      (hqc n)).coeFn_toLp, (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν)
          (contDiff_weightedLaplacian hU (hq n) (by decide) (by decide)).neg
          (hasCompactSupport_weightedLaplacian U (hqc n)).neg).coeFn_toLp] with x hx hy
    rw [hx, hy, regularizedUnit_def, real_inner_smul_left, gamma_apply, ← gamma_self,
      inv_mul_eq_div]
  rw [e₁, e₂]
  exact hsm

/-- **Monotonicity of the regularized interpolation, positive-time data.** For arbitrary
`g ∈ L²(ν)`, `0 < a ≤ t`, `ε > 0` and nonnegative `φ ∈ C_c^∞`,
`∫ φ N_ε(T̄P_t g) dν ≤ ∫ (P_{t-a} φ) N_ε(T̄P_a g) dν`. -/
theorem integral_mul_regularizedNorm_le_of_pos
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) {ε : ℝ} (hε : 0 < ε) (g : Lp ℝ 2 (ν : Measure V))
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    ∫ x, φ x * regularizedNorm ε
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
            (ha.trans_le hat)⟩ : Lp V 2 (ν : Measure V)) x) ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi (sub_nonneg.mpr hat)
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * regularizedNorm ε
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ha⟩ :
              Lp V 2 (ν : Measure V)) x) ∂(ν : Measure V) := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  set hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  set hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have ht : 0 < t := ha.trans_le hat
  set Φ : (adjointComp T).domain :=
    ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 hφ hφc⟩ with hΦdef
  obtain ⟨C, D, hC, hD, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  have hAΦ : ∀ᵐ x ∂(ν : Measure V), |(adjointComp T Φ : Lp ℝ 2 (ν : Measure V)) x| ≤ D := by
    have h0 := (hb 0 le_rfl).2
    have e : (⟨operator m (ContinuousLinearMap.id ℝ V) hν hi le_rfl (Φ : Lp ℝ 2 (ν : Measure V)),
        preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ le_rfl⟩ :
        (adjointComp T).domain) = Φ := Subtype.ext (HeatSemigroup.zero m _ hν hi _)
    rwa [e] at h0
  set q : ℝ → Lp ℝ 2 (ν : Measure V) :=
    fun r => Generated.apply T hT hd (t - r) (Φ : Lp ℝ 2 (ν : Measure V)) with hqdef
  set u : ℝ → Lp V 2 (ν : Measure V) := fun r =>
    if h : 0 < r then T ⟨Generated.apply T hT hd r g, Generated.mem_domain_apply_of_pos T hT hd g h⟩
    else 0 with hudef
  have hu : ∀ r (hr : 0 < r), u r = T ⟨Generated.apply T hT hd r g,
      Generated.mem_domain_apply_of_pos T hT hd g hr⟩ := fun r hr => by
    simp only [hudef, dif_pos hr]
  set Ψ : ℝ → ℝ := fun r => ∫ x, q r x * regularizedNorm ε (u r x) ∂(ν : Measure V)
    with hΨdef
  have hqb : ∀ r, r ≤ t → ∀ᵐ x ∂(ν : Measure V), |q r x| ≤ C := fun r hr =>
    (hb (t - r) (sub_nonneg.mpr hr)).1
  set Ψ' : ℝ → ℝ := fun r => if hr : r ∈ Ico a t then
      (∫ x, (adjointComp T ⟨_, preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ
          (sub_nonneg.mpr (le_of_lt hr.2))⟩ : Lp ℝ 2 (ν : Measure V)) x *
          regularizedNorm ε (u r x) ∂(ν : Measure V)) +
        ∫ x, q r x * ⟪regularizedUnit ε (u r x),
          (-T ⟨adjointComp T ⟨Generated.apply T hT hd r g,
            Generated.mem_adjointComp_domain_apply_of_pos T hT hd g (ha.trans_le hr.1)⟩,
            Generated.mem_domain_adjointComp_apply_of_pos T hT hd g
              (ha.trans_le hr.1) _⟩ : Lp V 2 (ν : Measure V)) x⟫ ∂(ν : Measure V) else 0
    with hΨ'def
  have hderiv : ∀ r ∈ Ico a t, HasDerivWithinAt Ψ (Ψ' r) (Ici r) r := by
    intro r hr
    simp only [hΨ'def, dif_pos hr]
    have hr0 : 0 < r := ha.trans_le hr.1
    have htr : 0 < t - r := sub_pos.mpr hr.2
    have hP := Generated.hasDerivWithinAt_apply_Iic T hT hd Φ htr
    have hlin : HasDerivWithinAt (fun r : ℝ => t - r) (-1) (Ici r) r :=
      ((hasDerivAt_id r).const_sub t).hasDerivWithinAt
    have hmaps : MapsTo (fun r : ℝ => t - r) (Ici r) (Iic (t - r)) := fun s hs => by
      simp only [mem_Iic]; linarith [mem_Ici.mp hs]
    have hq' := hP.scomp r hlin hmaps
    simp only [neg_smul, one_smul, neg_neg] at hq'
    have hq : HasDerivWithinAt q _ (Ici r) r := hq'
    have huder := Generated.hasDerivWithinAt_map_apply_Ici T hT hd g hu hr0
    have hslope : ∀ᶠ s in 𝓝[Ici r \ {r}] r, ∀ᵐ x ∂(ν : Measure V), |slope q r s x| ≤ D := by
      rw [Ici_sdiff_left]
      filter_upwards [Ioo_mem_nhdsGT hr.2] with s hs
      have hsr : 0 < s - r := sub_pos.mpr hs.1
      have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2.le
      have hsplit : Generated.apply T hT hd (t - r) (Φ : Lp ℝ 2 (ν : Measure V)) =
          Generated.apply T hT hd (t - s)
            (Generated.apply T hT hd (s - r) (Φ : Lp ℝ 2 (ν : Measure V))) := by
        rw [← Generated.add_time T hT hd hts hsr.le]; congr 1; ring
      have hkey : slope q r s = operator m (ContinuousLinearMap.id ℝ V) hν hi hts
          ((s - r)⁻¹ • ((Φ : Lp ℝ 2 (ν : Measure V)) -
            Generated.apply T hT hd (s - r) (Φ : Lp ℝ 2 (ν : Measure V)))) := by
        rw [slope_def_module, HeatSemigroup.apply, Generated.map_smul T hT hd hts,
          Generated.map_sub T hT hd hts, ← hsplit]
      have hdiff := ae_abs_operator_sub_le m (ContinuousLinearMap.id ℝ V) hν hi Φ hD hAΦ hsr.le
      have hk : ∀ᵐ x ∂(ν : Measure V), |((s - r)⁻¹ • ((Φ : Lp ℝ 2 (ν : Measure V)) -
          Generated.apply T hT hd (s - r) (Φ : Lp ℝ 2 (ν : Measure V))) :
            Lp ℝ 2 (ν : Measure V)) x| ≤ D := by
        filter_upwards [hdiff, Lp.coeFn_smul (s - r)⁻¹ ((Φ : Lp ℝ 2 (ν : Measure V)) -
          Generated.apply T hT hd (s - r) (Φ : Lp ℝ 2 (ν : Measure V))),
          Lp.coeFn_sub (Φ : Lp ℝ 2 (ν : Measure V))
            (Generated.apply T hT hd (s - r) (Φ : Lp ℝ 2 (ν : Measure V)))] with x h1 h2 h3
        rw [h2, Pi.smul_apply, h3, Pi.sub_apply, smul_eq_mul, abs_mul, abs_inv,
          abs_of_pos hsr, abs_sub_comm, inv_mul_le_iff₀ hsr]
        exact h1
      rw [hkey]
      exact ae_abs_operator_le m _ hν hi hts _ hD hk
    have hq'b : ∀ᵐ x ∂(ν : Measure V), |(adjointComp T ⟨_, preserves_domain m
        (ContinuousLinearMap.id ℝ V) hν hi Φ htr.le⟩ : Lp ℝ 2 (ν : Measure V)) x| ≤ D :=
      (hb (t - r) htr.le).2
    have hK : 0 ≤ max C D := le_max_of_le_right hD
    refine hasDerivWithinAt_integral_mul_regularizedNorm hε hq huder hK ?_ ?_ ?_
    · filter_upwards [hqb r hr.2.le] with x hx using hx.trans (le_max_left _ _)
    · filter_upwards [hslope] with s hs
      filter_upwards [hs] with x hx using hx.trans (le_max_right _ _)
    · filter_upwards [hq'b] with x hx using hx.trans (le_max_right _ _)
  have hsign : ∀ r ∈ Ico a t, Ψ' r ≤ 0 := by
    intro r hr
    simp only [hΨ'def, dif_pos hr]
    have hr0 : 0 < r := ha.trans_le hr.1
    have htr : 0 ≤ t - r := sub_nonneg.mpr hr.2.le
    set ψ : (adjointComp T).domain :=
      ⟨_, preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ htr⟩ with hψdef
    have hψ0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ (ψ : Lp ℝ 2 (ν : Measure V)) x := by
      apply ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi htr
      filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
      rw [hx]; exact hφ0 x
    set F : (adjointComp T).domain :=
      ⟨_, Generated.mem_adjointComp_domain_apply_of_pos T hT hd g hr0⟩ with hFdef
    have hF : (adjointComp T F : Lp ℝ 2 (ν : Measure V)) ∈ T.domain :=
      Generated.mem_domain_adjointComp_apply_of_pos T hT hd g hr0 _
    have hmain := integral_regularizedNorm_nonneg m hν hi hνU hU hconv hε ψ hC hD hψ0
      (hb (t - r) htr).1 (hb (t - r) htr).2 F hF
    have hneg : ∫ x, q r x * ⟪regularizedUnit ε (u r x),
        (-T ⟨adjointComp T F, hF⟩ : Lp V 2 (ν : Measure V)) x⟫ ∂(ν : Measure V) =
        -∫ x, q r x * ⟪regularizedUnit ε (u r x),
          (T ⟨adjointComp T F, hF⟩ : Lp V 2 (ν : Measure V)) x⟫ ∂(ν : Measure V) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_neg (T ⟨adjointComp T F, hF⟩ : Lp V 2 (ν : Measure V))] with x hx
      rw [hx, Pi.neg_apply, inner_neg_right, mul_neg]
    rw [hneg, hu r hr0]
    have key : ∀ X Y : ℝ, 0 ≤ -X + Y → X + -Y ≤ 0 := fun X Y h => by linarith
    exact key _ _ hmain
  have hcont : ContinuousOn Ψ (Icc a t) := by
    intro r hr
    have hqc : ContinuousWithinAt q (Icc a t) r := by
      have h1 : ContinuousOn (fun τ => Generated.apply T hT hd τ (Φ : Lp ℝ 2 (ν : Measure V)))
          (Ici 0) := Generated.continuousOn T hT hd _
      have h2 : ContinuousOn (fun r : ℝ => t - r) (Icc a t) :=
        (continuous_const.sub continuous_id).continuousOn
      exact (h1.comp h2 (fun s hs => by simp only [mem_Ici]; linarith [hs.2])) r hr
    have huc : ContinuousWithinAt u (Icc a t) r :=
      ((Generated.continuousOn_map_apply T hT hd g hu).mono
        (fun s hs => (show (0 : ℝ) < s from ha.trans_le hs.1))) r hr
    have hbd : ∀ᶠ s in 𝓝[Icc a t] r, ∀ᵐ x ∂(ν : Measure V), |q s x| ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with s hs using hqb s hs.2
    exact tendsto_integral_mul_regularizedNorm hε hqc hC hbd (hqb r hr.2) huc
  have hmono := image_le_of_deriv_right_le_deriv_boundary (f := Ψ) (f' := Ψ')
    (B := fun _ => Ψ a) (B' := fun _ => 0) hcont hderiv le_rfl
    continuousOn_const (fun r _ => hasDerivWithinAt_const _ _ _) hsign (right_mem_Icc.mpr hat)
  have hΨt : Ψ t = ∫ x, φ x * regularizedNorm ε
      ((T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht⟩ :
        Lp V 2 (ν : Measure V)) x) ∂(ν : Measure V) := by
    simp only [hΨdef, hqdef, sub_self, Generated.zero_time]
    rw [hu t ht]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [hx]
    rfl
  have hΨa : Ψ a = ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi (sub_nonneg.mpr hat)
        ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * regularizedNorm ε
        ((T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ha⟩ :
          Lp V 2 (ν : Measure V)) x) ∂(ν : Measure V) := by
    simp only [hΨdef, hqdef]
    rw [hu a ha]
    rfl
  rw [← hΨt, ← hΨa]
  exact hmono

/-- **The regularized estimate on the form domain.** For `f ∈ D(T̄)`, `t ≥ 0`, `ε > 0` and
nonnegative `φ ∈ C_c^∞`, `∫ φ N_ε(T̄P_t f) dν ≤ ∫ (P_t φ) N_ε(T̄f) dν`. -/
theorem integral_mul_regularizedNorm_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U) {ε : ℝ} (hε : 0 < ε)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, φ x * regularizedNorm ε
        ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
            Lp V 2 (ν : Measure V)) x) ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * regularizedNorm ε
          ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
            Lp V 2 (ν : Measure V)) x) ∂(ν : Measure V) := by
  revert f
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  set hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  set hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro f
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    have e1 : (⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ : T.domain) =
        f := Subtype.ext (HeatSemigroup.zero m _ hν hi _)
    rw [e1]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [HeatSemigroup.zero m _ hν hi, hx]
  obtain ⟨C, D, hC, hD, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  set q : ℝ → Lp ℝ 2 (ν : Measure V) := fun a => Generated.apply T hT hd (t - a)
    ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) with hqdef
  set u : ℝ → Lp V 2 (ν : Measure V) := fun a =>
    if h : 0 ≤ a then T ⟨Generated.apply T hT hd a (f : Lp ℝ 2 (ν : Measure V)),
      Generated.preserves_form_domain T hT hd f h⟩ else 0 with hudef
  have hu : ∀ a (ha : 0 ≤ a), u a = T ⟨Generated.apply T hT hd a (f : Lp ℝ 2 (ν : Measure V)),
      Generated.preserves_form_domain T hT hd f ha⟩ := fun a ha => by
    simp only [hudef, dif_pos ha]
  have hul : Tendsto u (𝓝[>] 0) (𝓝 (T f)) :=
    (Generated.tendsto_map_apply_zero T hT hd f hu).mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hsub : Tendsto (fun a : ℝ => t - a) (𝓝[>] 0) (𝓝[Ici 0] t) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun a : ℝ => t - a) (𝓝 0) (𝓝 (t - 0)) :=
        ((continuous_const.sub continuous_id).tendsto (0 : ℝ))
      rw [sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hpos] with a ha
      simp only [mem_Ici]; linarith [ha.2]
  have hql : Tendsto q (𝓝[>] 0) (𝓝 (Generated.apply T hT hd t
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ))) :=
    ((Generated.continuousOn T hT hd _) t (mem_Ici.mpr ht)).tendsto.comp hsub
  have hqb : ∀ᶠ a in 𝓝[>] 0, ∀ᵐ x ∂(ν : Measure V), |q a x| ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT hpos] with a ha
    exact (hb (t - a) (sub_nonneg.mpr ha.2.le)).1
  have hlim := tendsto_integral_mul_regularizedNorm hε hql hC hqb (hb t ht).1 hul
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hpos] with a ha
  have h := integral_mul_regularizedNorm_le_of_pos m hν hi hνU hU hconv hε
    (f : Lp ℝ 2 (ν : Measure V)) hφ hφc hφ0 ha.1 ha.2.le
  simp only [hqdef, hu a ha.1.le]
  exact h

/-- **Bakry's `L¹` self-improvement, integrated form.** For the closed unit-weight gradient `T̄`
of `ν = m.tilted (-U)` with a smooth convex potential, every `f ∈ D(T̄)`, every `t ≥ 0` and
every nonnegative `φ ∈ C_c^∞(V)`: `∫ φ |T̄P_t f| dν ≤ ∫ (P_t φ) |T̄f| dν`, the tested form of
`|∇P_t f| ≤ P_t |∇f|`. It is the limit `ε → 0⁺` of `integral_mul_regularizedNorm_le`. -/
theorem integral_mul_norm_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, φ x * ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
            Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) ≤
      ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
        ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
          Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  obtain ⟨C, D, -, -, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  obtain ⟨K, hK⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hL := tendsto_integral_mul_regularizedNorm_zero (μ := (ν : Measure V))
    hφ.continuous.aestronglyMeasurable (K := K)
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hK x)
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
  have hR := tendsto_integral_mul_regularizedNorm_zero (μ := (ν : Measure V))
    (Lp.aestronglyMeasurable _) (hb t ht).1
    (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact integral_mul_regularizedNorm_le m hν hi hνU hU hconv hε f hφ hφc hφ0 ht

/-- Bakry's self-improvement as an a.e. inequality. The scalar norm of the initial closed
 gradient is an `L²` function, so the existing scalar heat operator acts on it directly. -/
theorem ae_norm_gradient_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
            Lp V 2 (ν : Measure V)) x‖ ≤
      operator m (ContinuousLinearMap.id ℝ V) hν hi ht
        (((Lp.memLp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f)).norm).toLp
          (fun y => ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
            Lp V 2 (ν : Measure V)) y‖)) x := by
  let u := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f
  let n := (Lp.memLp u).norm.toLp (fun y => ‖u y‖)
  let v := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩
  change ∀ᵐ x ∂(ν : Measure V), ‖v x‖ ≤ operator m _ hν hi ht n x
  apply Analysis.TestFunction.ae_le_of_integral_mul_le
    ((Lp.memLp v).norm.integrable one_le_two) ((Lp.memLp _).integrable one_le_two)
  intro φ hφ hφc hφ0
  let φL := (memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ
  have h := integral_mul_norm_le m hν hi hνU hU hconv f hφ hφc hφ0 ht
  have heq : (∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht φL x * ‖u x‖
      ∂(ν : Measure V)) =
      ∫ x, φ x * operator m (ContinuousLinearMap.id ℝ V) hν hi ht n x ∂(ν : Measure V) := by
    have hs := symmetric m (ContinuousLinearMap.id ℝ V) hν hi ht φL n
    rw [L2.inner_def, L2.inner_def] at hs
    simp only [Real.inner_apply] at hs
    calc
      _ = ∫ x, n x * operator m (ContinuousLinearMap.id ℝ V) hν hi ht φL x ∂(ν : Measure V) := by
        apply integral_congr_ae
        filter_upwards [(Lp.memLp u).norm.coeFn_toLp] with x hx
        dsimp [n]; rw [hx]; ring
      _ = ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht n x * φL x ∂(ν : Measure V) := by simpa only [mul_comm] using hs
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
        dsimp [φL]; rw [hx]; ring
  exact h.trans_eq heq

/-- Weighted Cauchy-Schwarz combined with L1 gradient self-improvement.
The two nonnegative L2 weights can be chosen independently of the heat datum. -/
theorem ae_sq_norm_gradient_le_mul
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (a c : Lp ℝ 2 (ν : Measure V))
    (ha : ∀ᵐ x ∂(ν : Measure V), 0 ≤ a x)
    (hc : ∀ᵐ x ∂(ν : Measure V), 0 ≤ c x)
    (hac : ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤ a x * c x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
            Lp V 2 (ν : Measure V)) x‖ ^ 2 ≤
        operator m (ContinuousLinearMap.id ℝ V) hν hi ht a x *
          operator m (ContinuousLinearMap.id ℝ V) hν hi ht c x := by
  let u := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f
  let n := (Lp.memLp u).norm.toLp (fun x ↦ ‖u x‖)
  have hn : ∀ᵐ x ∂(ν : Measure V), n x ^ 2 ≤ a x * c x := by
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp, hac] with x hx hy
    simpa only [n, hx] using hy
  have hcs := L2.ae_sq_le_mul_of_positive
    (operator m (ContinuousLinearMap.id ℝ V) hν hi ht).toLinearMap
    (fun _ h ↦ positive m (ContinuousLinearMap.id ℝ V) hν hi ht h) a n c ha hc hn
  filter_upwards [ae_norm_gradient_le m hν hi hνU hU hconv f ht, hcs] with x hx hy
  exact (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans hy

/-- The heat flow contracts the integral of the closed-gradient norm on its form domain. -/
theorem integral_norm_gradient_le
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (f : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) ≤
      ∫ x, ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi f :
        Lp V 2 (ν : Measure V)) x‖ ∂(ν : Measure V) := by
  have h := integral_mono_ae ((Lp.memLp _).norm.integrable one_le_two)
    ((Lp.memLp _).integrable one_le_two) (ae_norm_gradient_le m hν hi hνU hU hconv f ht)
  rw [HeatSemigroup.integral m (ContinuousLinearMap.id ℝ V) hν hi ht] at h
  refine h.trans_eq (integral_congr_ae ?_)
  exact (Lp.memLp _).norm.coeFn_toLp

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
