import FunctionalInequalities.Analysis.TestFunctionOrder
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.GradientEstimate

/-!
# The reverse local Poincaré inequality `2t Γ(P_t f) ≤ P_t(f²) - (P_t f)²`

Let `ν = m.tilted (-U)` be a full-dimensional log-concave probability law with a smooth convex
potential and unit weight, `T̄` the closed gradient, `A = T̄†T̄` and `P_t = exp (-t A)`.

* `integral_adjointComp_mul_apply_sub_eq`: the weak carré du champ identity
  `∫ (Aψ) g² dν - 2 ∫ ψ g (Ag) dν = -2 ∫ ψ Γ(T̄g, T̄g) dν` for `g ∈ D(A)` and a bounded
  `ψ ∈ D(A)` with bounded `Aψ`. It is the weak form of `ℒ(g²) = 2 g ℒg + 2 Γ(g)`, proved on
  `C_c^∞` and transferred along the operator core.
* `two_mul_integral_mul_weakGamma_le`: for **arbitrary** `f ∈ L²(ν)`, `t > 0` and nonnegative
  `φ ∈ C_c^∞`,
  `2t ∫ φ Γ(T̄P_t f) dν ≤ ∫ (P_t φ) f² dν - ∫ φ (P_t f)² dν`,
  the integrated reverse local Poincaré (Bakry–Gentil–Ledoux, `K = 0`) inequality.
* `two_mul_integral_mul_weakGamma_le_of_bounded`: if `|f| ≤ M` a.e., then
  `2t ∫ φ Γ(T̄P_t f) dν ≤ M² ∫ φ dν`, the integrated `L^∞ → Lip` regularization
  `|T̄P_t f|² ≤ M²/(2t)`.

The interpolation is `Λ(s) = ∫ (P_s φ)(P_{t-s} f)² dν`. Its right derivative is
`2 ∫ (P_s φ) Γ(T̄P_{t-s} f) dν`, by the product rule and the carré identity. This is at least
`2 ∫ φ Γ(T̄P_t f) dν` by the square gradient estimate `integral_mul_weakGamma_le`. The
general reverse inequality is integrated against `C_c^∞` tests. For bounded data,
`ae_two_mul_weakGamma_le_of_bounded` and `ae_norm_gradient_le_of_bounded` give its a.e.
consequence `|T̄P_t f| ≤ M/√(2t)` via smooth-test order separation.
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
private theorem integrable_Lp_mul_compact (ψ : Lp ℝ 2 (ν : Measure V)) {q : V → ℝ}
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    Integrable (fun x => ψ x * q x) (ν : Measure V) := by
  have hqL : MemLp q 2 (ν : Measure V) := hq.memLp_of_hasCompactSupport hqc
  refine (L2.integrable_inner (𝕜 := ℝ) ψ (hqL.toLp q)).congr ?_
  filter_upwards [hqL.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

/-- The carré identity on smooth compactly supported data. -/
private theorem integral_carre_smooth (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
        Lp ℝ 2 (ν : Measure V)) x * (q x * q x) ∂(ν : Measure V)) -
      2 * ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * (q x * -weightedLaplacian U q x)
        ∂(ν : Measure V) =
      -2 * ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * gamma q q x ∂(ν : Measure V) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have hq2 : ContDiff ℝ ∞ (fun x => q x * q x) := hq.mul hq
  have hq2c : HasCompactSupport (fun x => q x * q x) := hqc.mul_left
  have hsym := integral_adjointComp_mul_toLp_eq m hν hi hνU hU1 ψ hq2 hq2c
  have hL : ContDiff ℝ ∞ (weightedLaplacian U q) :=
    contDiff_weightedLaplacian hU hq (by decide) (by decide)
  have hmul : weightedLaplacian U (fun y => q y * q y) =
      fun x => 2 * (q x * weightedLaplacian U q x) + 2 * gamma q q x := by
    funext x
    rw [weightedLaplacian_mul U (hq.of_le (by decide)) (hq.of_le (by decide)) x]
    ring
  have i₁ : Integrable (fun x => (ψ : Lp ℝ 2 (ν : Measure V)) x *
      (q x * weightedLaplacian U q x)) (ν : Measure V) :=
    integrable_Lp_mul_compact (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V))
      (hq.continuous.mul hL.continuous) (hqc.mul_right)
  have i₂ := integrable_Lp_mul_compact (ν := ν) (ψ : Lp ℝ 2 (ν : Measure V))
    (continuous_gamma (hq.of_le (by decide)) (hq.of_le (by decide)))
    (hasCompactSupport_gamma_left q hqc)
  rw [hsym, hmul]
  have e1 : ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
      (2 * (q x * weightedLaplacian U q x) + 2 * gamma q q x) ∂(ν : Measure V) =
      2 * ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * (q x * weightedLaplacian U q x) ∂(ν : Measure V) +
      2 * ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * gamma q q x ∂(ν : Measure V) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i₁.const_mul 2)
      (i₂.const_mul 2)]
    congr 1; funext x; ring
  have e2 : ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * (q x * -weightedLaplacian U q x)
      ∂(ν : Measure V) =
      -∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x * (q x * weightedLaplacian U q x) ∂(ν : Measure V) := by
    rw [← integral_neg]; congr 1; funext x; ring
  rw [e1, e2]
  ring

/-- **The weak carré du champ identity on `D(A)`.** For `g ∈ D(A)` and `ψ ∈ D(A)` with `ψ` and
`Aψ` a.e. bounded, `∫ (Aψ) g² dν - 2 ∫ ψ g (Ag) dν = -2 ∫ ψ Γ(T̄g, T̄g) dν`. On `C_c^∞` this is
`ℒ(q²) = 2 q ℒq + 2 Γ(q)` tested against `ψ` by generator symmetry; it is transferred along
the operator core, `‖T̄([qₙ] - g)‖² ≤ ‖A([qₙ] - g)‖ ‖[qₙ] - g‖` giving the gradient field. -/
theorem integral_adjointComp_mul_apply_sub_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U)
    (ψ : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hψb : ∀ᵐ x ∂(ν : Measure V), |(ψ : Lp ℝ 2 (ν : Measure V)) x| ≤ C)
    (hAψb : ∀ᵐ x ∂(ν : Measure V),
      |(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
        Lp ℝ 2 (ν : Measure V)) x| ≤ D)
    (g : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    (∫ x, (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ψ :
        Lp ℝ 2 (ν : Measure V)) x *
        WeakGamma.apply (g : Lp ℝ 2 (ν : Measure V)) (g : Lp ℝ 2 (ν : Measure V)) x
        ∂(ν : Measure V)) -
      2 * ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
        WeakGamma.apply (g : Lp ℝ 2 (ν : Measure V))
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) g) x
        ∂(ν : Measure V) =
      -2 * ∫ x, (ψ : Lp ℝ 2 (ν : Measure V)) x *
        WeakGamma.apply (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(g : Lp ℝ 2 (ν : Measure V)), g.2.2⟩)
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(g : Lp ℝ 2 (ν : Measure V)), g.2.2⟩) x ∂(ν : Measure V) := by
  revert ψ g
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  intro ψ hψb hAψb g
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  obtain ⟨q, hq, hqc, h₁, h₂⟩ := hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU1 g
  set x : ℕ → (adjointComp T).domain :=
    fun n => ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU1 (hq n) (hqc n)⟩ with hxdef
  have h₃ : Tendsto (fun n => ‖T ⟨(x n : Lp ℝ 2 (ν : Measure V)), (x n).2.2⟩ -
      T ⟨(g : Lp ℝ 2 (ν : Measure V)), g.2.2⟩‖) atTop (𝓝 0) := by
    have hprod : Tendsto (fun n => ‖adjointComp T (x n - g)‖ *
        ‖((x n - g : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) := by
      have := h₂.mul h₁
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [LinearPMap.map_sub, Submodule.coe_sub]
    have hsq : Tendsto (fun n => √(‖adjointComp T (x n - g)‖ *
        ‖((x n - g : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V))‖)) atTop (𝓝 0) := by
      simpa using hprod.sqrt
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsq
    have hle := Generated.norm_map_sq_le_mul T hd (x n - g)
    have e : T ⟨((x n - g : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V)), (x n - g).2.2⟩ =
        T ⟨(x n : Lp ℝ 2 (ν : Measure V)), (x n).2.2⟩ -
          T ⟨(g : Lp ℝ 2 (ν : Measure V)), g.2.2⟩ := by
      rw [← LinearPMap.map_sub]; rfl
    rw [e] at hle
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hle
  have L₁ := WeakGamma.tendsto_integral_mul (Lp.aestronglyMeasurable _) hD hAψb h₁ h₁
  have L₂ := WeakGamma.tendsto_integral_mul (Lp.aestronglyMeasurable _) hC hψb h₁ h₂
  have L₃ := WeakGamma.tendsto_integral_mul (Lp.aestronglyMeasurable _) hC hψb h₃ h₃
  refine tendsto_nhds_unique (L₁.sub (L₂.const_mul 2)) ((L₃.const_mul (-2)).congr fun n => ?_)
  -- the identity for each smooth approximant
  have hAx : adjointComp T (x n) = (memLp_neg_weightedLaplacian (ν := ν) hU1 (hq n)
      (hqc n)).toLp (fun y => -weightedLaplacian U (q n) y) :=
    hν.adjointComp_toLp_eq m hi hνU hU1 (hq n) (hqc n)
  have hTx : T ⟨(x n : Lp ℝ 2 (ν : Measure V)), (x n).2.2⟩ =
      (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n) (hqc n)).toLp
        (gradient (q n)) :=
    hν.closedWeightedOperator_toLp_eq m hi (hq n) (hqc n)
  have hsm := integral_carre_smooth m hν hi hνU hU ψ (hq n) (hqc n)
  have e₁ : ∫ y, (adjointComp T ψ : Lp ℝ 2 (ν : Measure V)) y *
      WeakGamma.apply (x n : Lp ℝ 2 (ν : Measure V)) (x n : Lp ℝ 2 (ν : Measure V)) y
        ∂(ν : Measure V) =
      ∫ y, (adjointComp T ψ : Lp ℝ 2 (ν : Measure V)) y * (q n y * q n y) ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν (hq n) (hqc n)).coeFn_toLp] with y hy
    rw [WeakGamma.apply_def, hy, Real.inner_apply]
  have e₂ : ∫ y, (ψ : Lp ℝ 2 (ν : Measure V)) y *
      WeakGamma.apply (x n : Lp ℝ 2 (ν : Measure V)) (adjointComp T (x n)) y ∂(ν : Measure V) =
      ∫ y, (ψ : Lp ℝ 2 (ν : Measure V)) y * (q n y * -weightedLaplacian U (q n) y)
        ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    rw [hAx]
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν (hq n) (hqc n)).coeFn_toLp,
      (memLp_neg_weightedLaplacian (ν := ν) hU1 (hq n) (hqc n)).coeFn_toLp] with y hy hy'
    rw [WeakGamma.apply_def, hy, hy', Real.inner_apply]
  have e₃ : ∫ y, (ψ : Lp ℝ 2 (ν : Measure V)) y *
      WeakGamma.apply (T ⟨(x n : Lp ℝ 2 (ν : Measure V)), (x n).2.2⟩)
        (T ⟨(x n : Lp ℝ 2 (ν : Measure V)), (x n).2.2⟩) y ∂(ν : Measure V) =
      ∫ y, (ψ : Lp ℝ 2 (ν : Measure V)) y * gamma (q n) (q n) y ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    rw [hTx]
    filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n)
      (hqc n)).coeFn_toLp] with y hy
    rw [WeakGamma.apply_def, hy, gamma_apply]
  simp only [hxdef] at e₁ e₂ e₃ ⊢
  rw [e₁, e₂, e₃] at *
  linarith

/-- **The reverse local Poincaré inequality, integrated form.** For `ν = m.tilted (-U)` with a
smooth convex potential and unit weight, **arbitrary** `f ∈ L²(ν)`, `t > 0` and nonnegative
`φ ∈ C_c^∞(V)`: `2t ∫ φ Γ(T̄P_t f) dν ≤ ∫ (P_t φ) f² dν - ∫ φ (P_t f)² dν`. -/
theorem two_mul_integral_mul_weakGamma_le (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 < t) :
    2 * t * ∫ x, φ x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤
      (∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * (f x) ^ 2 ∂(ν : Measure V)) -
        ∫ x, φ x * (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2
          ∂(ν : Measure V) := by
  set T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi with hTdef
  set hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  set hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
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
    fun s => Generated.apply T hT hd s (Φ : Lp ℝ 2 (ν : Measure V)) with hqdef
  set g : ℝ → Lp ℝ 2 (ν : Measure V) := fun s => Generated.apply T hT hd (t - s) f with hgdef
  set Λ : ℝ → ℝ := fun s => ∫ x, q s x * WeakGamma.apply (g s) (g s) x ∂(ν : Measure V)
    with hΛdef
  set c := ∫ x, φ x * WeakGamma.apply
      (T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
      (T ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
      ∂(ν : Measure V) with hcdef
  have hqb : ∀ s, 0 ≤ s → ∀ᵐ x ∂(ν : Measure V), |q s x| ≤ C := fun s hs => (hb s hs).1
  set Λ' : ℝ → ℝ := fun s => if hs : s ∈ Ico 0 t then
      (∫ x, (-adjointComp T ⟨_, preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ hs.1⟩ :
          Lp ℝ 2 (ν : Measure V)) x * WeakGamma.apply (g s) (g s) x ∂(ν : Measure V)) +
        2 * ∫ x, q s x * WeakGamma.apply (g s)
          (adjointComp T ⟨g s, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f
            (sub_pos.mpr hs.2)⟩) x ∂(ν : Measure V) else 0 with hΛ'def
  have hderiv : ∀ s ∈ Ico 0 t, HasDerivWithinAt Λ (Λ' s) (Ici s) s := by
    intro s hs
    simp only [hΛ'def, dif_pos hs]
    have hts : 0 < t - s := sub_pos.mpr hs.2
    have hq := Generated.hasDerivWithinAt_apply_Ici T hT hd Φ hs.1
    have hg' := HasDerivAt.scomp s (Generated.hasDerivAt_apply_of_pos T hT hd f hts)
      ((hasDerivAt_id' s).const_sub t)
    simp only [neg_smul, one_smul, neg_neg] at hg'
    have hg : HasDerivWithinAt g _ (Ici s) s := hg'.hasDerivWithinAt
    have hslope : ∀ᶠ s' in 𝓝[Ici s \ {s}] s, ∀ᵐ x ∂(ν : Measure V), |slope q s s' x| ≤ D := by
      rw [Ici_sdiff_left]
      filter_upwards [self_mem_nhdsWithin] with s' hs'
      have hss : 0 < s' - s := sub_pos.mpr hs'
      have hsplit : Generated.apply T hT hd s' (Φ : Lp ℝ 2 (ν : Measure V)) =
          Generated.apply T hT hd s
            (Generated.apply T hT hd (s' - s) (Φ : Lp ℝ 2 (ν : Measure V))) := by
        rw [← Generated.add_time T hT hd hs.1 hss.le]; congr 1; ring
      have hkey : slope q s s' = operator m (ContinuousLinearMap.id ℝ V) hν hi hs.1
          ((s' - s)⁻¹ • (Generated.apply T hT hd (s' - s) (Φ : Lp ℝ 2 (ν : Measure V)) -
            (Φ : Lp ℝ 2 (ν : Measure V)))) := by
        rw [slope_def_module, HeatSemigroup.apply, Generated.map_smul T hT hd hs.1,
          Generated.map_sub T hT hd hs.1, ← hsplit]
      have hdiff := ae_abs_operator_sub_le m (ContinuousLinearMap.id ℝ V) hν hi Φ hD hAΦ hss.le
      have hk : ∀ᵐ x ∂(ν : Measure V), |((s' - s)⁻¹ •
          (Generated.apply T hT hd (s' - s) (Φ : Lp ℝ 2 (ν : Measure V)) -
            (Φ : Lp ℝ 2 (ν : Measure V))) : Lp ℝ 2 (ν : Measure V)) x| ≤ D := by
        filter_upwards [hdiff, Lp.coeFn_smul (s' - s)⁻¹
          (Generated.apply T hT hd (s' - s) (Φ : Lp ℝ 2 (ν : Measure V)) -
            (Φ : Lp ℝ 2 (ν : Measure V))),
          Lp.coeFn_sub (Generated.apply T hT hd (s' - s) (Φ : Lp ℝ 2 (ν : Measure V)))
            (Φ : Lp ℝ 2 (ν : Measure V))] with x h1 h2 h3
        rw [h2, Pi.smul_apply, h3, Pi.sub_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hss,
          inv_mul_le_iff₀ hss]
        exact h1
      rw [hkey]
      exact ae_abs_operator_le m _ hν hi hs.1 _ hD hk
    have hK : 0 ≤ max C D := le_max_of_le_right hD
    refine WeakGamma.hasDerivWithinAt_integral_mul_apply_self hq hg hK ?_ ?_ ?_
    · filter_upwards [hqb s hs.1] with x hx using hx.trans (le_max_left _ _)
    · filter_upwards [hslope] with s' hs'
      filter_upwards [hs'] with x hx using hx.trans (le_max_right _ _)
    · filter_upwards [(hb s hs.1).2, Lp.coeFn_neg (adjointComp T ⟨_, preserves_domain m
        (ContinuousLinearMap.id ℝ V) hν hi Φ hs.1⟩ : Lp ℝ 2 (ν : Measure V))] with x hx hx'
      rw [hx', Pi.neg_apply, abs_neg]
      exact hx.trans (le_max_right _ _)
  -- the right derivative dominates `2c`
  have hsign : ∀ s ∈ Ico 0 t, 2 * c ≤ Λ' s := by
    intro s hs
    simp only [hΛ'def, dif_pos hs]
    have hts : 0 < t - s := sub_pos.mpr hs.2
    set ψ : (adjointComp T).domain :=
      ⟨_, preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi Φ hs.1⟩ with hψdef
    set G : (adjointComp T).domain :=
      ⟨g s, Generated.mem_adjointComp_domain_apply_of_pos T hT hd f hts⟩ with hGdef
    have hcarre := integral_adjointComp_mul_apply_sub_eq m hν hi hνU hU ψ hC hD
      (hb s hs.1).1 (hb s hs.1).2 G
    have hneg : ∫ x, (-adjointComp T ψ : Lp ℝ 2 (ν : Measure V)) x *
        WeakGamma.apply (g s) (g s) x ∂(ν : Measure V) =
        -∫ x, (adjointComp T ψ : Lp ℝ 2 (ν : Measure V)) x *
          WeakGamma.apply (g s) (g s) x ∂(ν : Measure V) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_neg (adjointComp T ψ : Lp ℝ 2 (ν : Measure V))] with x hx
      rw [hx, Pi.neg_apply, neg_mul]
    have hGT : (g s) ∈ T.domain := Generated.mem_domain_apply_of_pos T hT hd f hts
    have hsq := integral_mul_weakGamma_le m hν hi hνU hU hconv ⟨g s, hGT⟩ hφ hφc hφ0 hs.1
    have e : (⟨_, preserves_form_domain m (ContinuousLinearMap.id ℝ V) hν hi ⟨g s, hGT⟩ hs.1⟩ :
        T.domain) = ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V)
          hν hi f ht⟩ := by
      apply Subtype.ext
      simp only [hgdef, HeatSemigroup.apply]
      rw [← Generated.add_time T hT hd hs.1 hts.le]
      congr 1; ring
    rw [e] at hsq
    have key : ∀ X Y Z W : ℝ, X - 2 * Y = -2 * Z → W ≤ Z → 2 * W ≤ -X + 2 * Y :=
      fun X Y Z W h1 h2 => by linarith
    rw [hneg]
    exact key _ _ _ _ hcarre hsq
  -- continuity of `Λ` on `[0, t]`
  have hcont : ContinuousOn Λ (Icc 0 t) := by
    intro s hs
    have hqc : ContinuousWithinAt q (Icc 0 t) s :=
      ((Generated.continuousOn T hT hd _).mono Icc_subset_Ici_self) s hs
    have hgc : ContinuousWithinAt g (Icc 0 t) s := by
      have h1 : ContinuousOn (fun τ => Generated.apply T hT hd τ f) (Ici 0) :=
        Generated.continuousOn T hT hd _
      have h2 : ContinuousOn (fun s : ℝ => t - s) (Icc 0 t) :=
        (continuous_const.sub continuous_id).continuousOn
      exact (h1.comp h2 (fun s hs => by simp only [mem_Ici]; linarith [hs.2])) s hs
    have hbd : ∀ᶠ s' in 𝓝[Icc 0 t] s, ∀ᵐ x ∂(ν : Measure V), |q s' x| ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with s' hs' using hqb s' hs'.1
    exact WeakGamma.tendsto_integral_mul_of_tendsto_multiplier hqc hC hbd (hqb s hs.1) hgc hgc
  -- comparison with the affine function `Λ 0 + 2 c s`
  have hmono := image_le_of_deriv_right_le_deriv_boundary (f := fun s => Λ 0 + 2 * c * s)
    (f' := fun _ => 2 * c) (B := Λ) (B' := Λ')
    ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn)
    (fun s _ => by
      simpa using ((hasDerivAt_id s).const_mul (2 * c)).const_add (Λ 0) |>.hasDerivWithinAt)
    (by simp) hcont hderiv hsign (right_mem_Icc.mpr ht.le)
  -- endpoints
  have hΛ0 : Λ 0 = ∫ x, φ x * (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2
      ∂(ν : Measure V) := by
    simp only [hΛdef, hqdef, hgdef, sub_zero, Generated.zero_time]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [WeakGamma.apply_self_real, hx]
    rfl
  have hΛt : Λ t = ∫ x, operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
      ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x * (f x) ^ 2 ∂(ν : Measure V) := by
    simp only [hΛdef, hqdef, hgdef, sub_self, Generated.zero_time, WeakGamma.apply_self_real]
    rfl
  rw [← hΛ0, ← hΛt]
  linarith


/-- **`L^∞ → Lip` regularization, integrated form.** If `|f| ≤ M` a.e., then for every `t > 0`
and nonnegative `φ ∈ C_c^∞(V)`, `2t ∫ φ Γ(T̄P_t f) dν ≤ M² ∫ φ dν`. This is the tested form of
`|T̄P_t f|² ≤ M²/(2t)`. -/
theorem two_mul_integral_mul_weakGamma_le_of_bounded (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    {t : ℝ} (ht : 0 < t) :
    2 * t * ∫ x, φ x * WeakGamma.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
        ∂(ν : Measure V) ≤ M ^ 2 * ∫ x, φ x ∂(ν : Measure V) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have hmain := two_mul_integral_mul_weakGamma_le m hν hi hνU hU hconv f hφ hφc hφ0 ht
  set φL := (memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ with hφLdef
  set ψ := operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le φL with hψdef
  obtain ⟨C, D, hC, -, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  have hψ0 : ∀ᵐ x ∂(ν : Measure V), 0 ≤ ψ x := by
    apply ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [hx]; exact hφ0 x
  have hf2 : Integrable (fun x => (f x) ^ 2) (ν : Measure V) := (Lp.memLp f).integrable_sq
  have hPf2 : Integrable (fun x => (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2)
      (ν : Measure V) := (Lp.memLp _).integrable_sq
  have hφb : ∃ K, ∀ x, |φ x| ≤ K := by
    obtain ⟨K, hK⟩ := hφ.continuous.bounded_above_of_compact_support hφc
    exact ⟨K, fun x => by simpa [Real.norm_eq_abs] using hK x⟩
  obtain ⟨K, hK⟩ := hφb
  have i₁ : Integrable (fun x => ψ x * (f x) ^ 2) (ν : Measure V) :=
    hf2.bdd_mul (Lp.aestronglyMeasurable ψ) (by
      filter_upwards [(hb t ht.le).1] with x hx; rwa [Real.norm_eq_abs])
  have i₂ : Integrable (fun x => φ x * (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2)
      (ν : Measure V) :=
    hPf2.bdd_mul hφ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hK x)
  have hnn : 0 ≤ ∫ x, φ x * (operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le f x) ^ 2
      ∂(ν : Measure V) :=
    integral_nonneg fun x => mul_nonneg (hφ0 x) (sq_nonneg _)
  have hle : ∫ x, ψ x * (f x) ^ 2 ∂(ν : Measure V) ≤ ∫ x, M ^ 2 * ψ x ∂(ν : Measure V) := by
    refine integral_mono_ae i₁ ((Lp.memLp ψ).integrable one_le_two |>.const_mul _) ?_
    filter_upwards [hψ0, hf] with x hx hfx
    have : (f x) ^ 2 ≤ M ^ 2 := by
      have := sq_abs (f x) ▸ pow_le_pow_left₀ (abs_nonneg _) hfx 2; exact this
    nlinarith
  have hmass : ∫ x, M ^ 2 * ψ x ∂(ν : Measure V) = M ^ 2 * ∫ x, φ x ∂(ν : Measure V) := by
    rw [integral_const_mul, hψdef, HeatSemigroup.integral m _ hν hi ht.le]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [hx]
  linarith

/-- The a.e. bounded-data reverse estimate, obtained from all nonnegative smooth tests. -/
theorem ae_two_mul_weakGamma_le_of_bounded (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(ν : Measure V), 2 * t * WeakGamma.apply
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩) x
      ≤ M ^ 2 := by
  apply Analysis.TestFunction.ae_le_of_integral_mul_le
    ((WeakGamma.integrable _ _).const_mul (2 * t)) (integrable_const _)
  intro φ hφ hφc hφ0
  have h := two_mul_integral_mul_weakGamma_le_of_bounded m hν hi hνU hU hconv f hf
    hφ hφc hφ0 ht
  simp_rw [mul_left_comm (φ _) (2 * t)]
  rw [integral_const_mul, integral_mul_const]
  nlinarith [h]

/-- Positive-time `L∞` to gradient regularization, with the sharp reverse-estimate factor. -/
theorem ae_norm_gradient_le_of_bounded (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂(ν : Measure V),
      ‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
          Lp V 2 (ν : Measure V)) x‖ ≤ M / Real.sqrt (2 * t) := by
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hf.exists
    exact (abs_nonneg _).trans hx
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * t by positivity)
  filter_upwards [ae_two_mul_weakGamma_le_of_bounded m hν hi hνU hU hconv f hf ht] with x hx
  rw [WeakGamma.apply, real_inner_self_eq_norm_sq] at hx
  apply (le_div_iff₀ hs).mpr
  have hn := norm_nonneg ((hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
      Lp V 2 (ν : Measure V)) x)
  have hmul : (‖(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
    ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩ :
      Lp V 2 (ν : Measure V)) x‖ * Real.sqrt (2 * t)) ^ 2 ≤ M ^ 2 := by
    rw [mul_pow, hsq]
    nlinarith [hx]
  nlinarith [mul_nonneg hn hs.le]

/-- For bounded heat data at positive time, the Gamma field is in L2, so it may
be used as an input to the L2 semigroup. This uses the proved gradient bound. -/
theorem memLp_weakGamma_of_bounded (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (f : Lp ℝ 2 (ν : Measure V))
    {M : ℝ} (hf : ∀ᵐ x ∂(ν : Measure V), |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    MemLp (WeakGamma.apply
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi f ht⟩))
      2 (ν : Measure V) := by
  refine MemLp.of_bound (WeakGamma.aestronglyMeasurable _ _) ((M / Real.sqrt (2 * t)) ^ 2) ?_
  filter_upwards [ae_norm_gradient_le_of_bounded m hν hi hνU hU hconv f hf ht] with x hx
  simp only [WeakGamma.apply, real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hx 2

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
