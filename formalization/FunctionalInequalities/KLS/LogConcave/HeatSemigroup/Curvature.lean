import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare
import FunctionalInequalities.Analysis.BakryEmery.Curvature
import FunctionalInequalities.Analysis.Semigroup.Generated.Curvature

/-!
# The heat semigroup of a strongly log-concave law: curvature and the Poincaré bound

Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (2014), Corollary 4.8.2:
if `dμ = e^{-U} dm` is a probability measure with `∇∇U ≥ ρ Id`, `ρ > 0`, then `μ` satisfies the
Poincaré inequality `P(1/ρ)`. The book's proof (Propositions 4.8.1 and 4.8.3) combines the
integrated curvature bound `ρ ∫ Γ(f) dμ ≤ ∫ (ℒf)² dμ` with the heat flow and ergodicity.

For the heat semigroup model of `HeatSemigroup/` (`ν = m.tilted (-U)`, closed unit gradient `T̄`,
`A = T̄†T̄`), this file proves:
* the curvature bound `ρ ‖T̄ y‖² ≤ ‖A y‖²` on `C_c^∞` and then on all of `D(A)`, through the
  operator core `exists_seq_smooth_tendsto_adjointComp`;
* the finite-time Poincaré bound `Var(u) - Var(P_t u) ≤ (1 - e^{-2ρt}) / ρ · ‖T̄ u‖²` on `D(T̄)`;
* Corollary 4.8.2 **under an explicit ergodicity hypothesis** `Var(P_t u) → 0`, as the bound
  `C_P(ν) ≤ 1/ρ` on the literature Poincaré constant.

Ergodicity (equivalently, `T̄ h = 0` forces `h` to be constant) is not proved here, so
Corollary 4.8.2 itself remains open.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)

omit [FiniteDimensional ℝ V] in
/-- The squared `L²(ν)` norm of the class of `∇f` is `∫ ‖∇f‖² dν`. -/
theorem norm_toLp_gradient_sq {f : V → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ‖(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)‖ ^ 2 =
      ∫ x, gamma f f x ∂(ν : Measure V) := by
  let hG := memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc
  change ‖hG.toLp (gradient f)‖ ^ 2 = ∫ x, gamma f f x ∂(ν : Measure V)
  calc
    ‖hG.toLp (gradient f)‖ ^ 2 =
        ⟪hG.toLp (gradient f), hG.toLp (gradient f)⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq]
    _ = ∫ x, ⟪gradient f x, gradient f x⟫_ℝ ∂(ν : Measure V) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hG] with x hx
      rw [hx]
    _ = ∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [real_inner_self_eq_norm_sq]
    _ = ∫ x, gamma f f x ∂(ν : Measure V) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [gamma_self]

include hνU hU in
/-- The curvature bound on smooth compactly supported classes: if `∇∇U ≥ ρ`, then
`ρ ‖T̄ [f]‖² ≤ ‖A [f]‖²`. -/
theorem mul_norm_closedWeightedOperator_toLp_sq_le {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {f : V → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ hf hfc⟩‖ ^ 2 := by
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc,
    hν.adjointComp_toLp_eq m hi hνU hU.of_succ hf hfc]

  have hneg :
      ‖(memLp_neg_weightedLaplacian (ν := ν) hU.of_succ hf hfc).toLp
          (fun x => -weightedLaplacian U f x)‖ ^ 2 =
        ∫ x, weightedLaplacian U f x ^ 2 ∂(ν : Measure V) := by
    let hL := memLp_neg_weightedLaplacian (ν := ν) hU.of_succ hf hfc
    change ‖hL.toLp (fun x => -weightedLaplacian U f x)‖ ^ 2 =
      ∫ x, weightedLaplacian U f x ^ 2 ∂(ν : Measure V)
    calc
      ‖hL.toLp (fun x => -weightedLaplacian U f x)‖ ^ 2 =
          ⟪hL.toLp (fun x => -weightedLaplacian U f x),
            hL.toLp (fun x => -weightedLaplacian U f x)⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      _ = ∫ x, ⟪-weightedLaplacian U f x,
            -weightedLaplacian U f x⟫_ℝ ∂(ν : Measure V) := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hL] with x hx
        rw [hx]
      _ = ∫ x, weightedLaplacian U f x ^ 2 ∂(ν : Measure V) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [real_inner_self_eq_norm_sq, norm_neg, Real.norm_eq_abs,
          sq_abs]

  rw [norm_toLp_gradient_sq (ν := ν) hf hfc, hneg, hνU]
  exact Analysis.BakryEmery.mul_integral_gamma_le m hU
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hfc hH

include hνU hU in
/-- The curvature bound on the whole operator domain: if `∇∇U ≥ ρ`, then `ρ ‖T̄ y‖² ≤ ‖A y‖²`
for every `y ∈ D(A)`. -/
theorem mul_norm_closedWeightedOperator_sq_le {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨F, F.2.2⟩‖ ^ 2 ≤
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

  have hinner
      (x : (adjointComp T).domain) :
      ‖T ⟨x, x.2.2⟩‖ ^ 2 = ⟪adjointComp T x, x⟫_ℝ := by
    symm
    exact inner_adjointComp_self_eq m (ContinuousLinearMap.id ℝ V) hν hi x

  obtain ⟨fn, hfn, hfnc, h1, h2⟩ :=
    hν.exists_seq_smooth_tendsto_adjointComp m hi hνU hU.of_succ F

  let Fn : ℕ → (adjointComp T).domain := fun n =>
    ⟨(Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport (ν := ν) (hfn n)
        (hfnc n)).toLp (fn n),
      hν.toLp_mem_adjointComp_domain m hi hνU hU.of_succ
        (hfn n) (hfnc n)⟩

  have hle : ∀ n,
      ρ * ⟪adjointComp T (Fn n), Fn n⟫_ℝ ≤
        ‖adjointComp T (Fn n)‖ ^ 2 := by
    intro n
    rw [← hinner (Fn n)]
    exact
      mul_norm_closedWeightedOperator_toLp_sq_le m hν hi hνU hU hH
        (hfn n) (hfnc n)

  have hFn :
      Tendsto
        (fun n =>
          ((Fn n : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V)))
        atTop
        (𝓝 ((F : (adjointComp T).domain) : Lp ℝ 2 (ν : Measure V))) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [Fn, T] using h1

  have hAF :
      Tendsto
        (fun n => adjointComp T (Fn n))
        atTop
        (𝓝 (adjointComp T F)) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [Fn, T] using h2

  have hleft :
      Tendsto
        (fun n =>
          ρ * ⟪adjointComp T (Fn n),
            ((Fn n : (adjointComp T).domain) :
              Lp ℝ 2 (ν : Measure V))⟫_ℝ)
        atTop
        (𝓝
          (ρ * ⟪adjointComp T F,
            ((F : (adjointComp T).domain) :
              Lp ℝ 2 (ν : Measure V))⟫_ℝ)) := by
    simpa using
      (tendsto_const_nhds.mul (hAF.inner hFn))

  have hright :
      Tendsto
        (fun n => ‖adjointComp T (Fn n)‖ ^ 2)
        atTop
        (𝓝 (‖adjointComp T F‖ ^ 2)) := by
    simpa using hAF.norm.pow 2

  have hlim :
      ρ * ⟪adjointComp T F,
        ((F : (adjointComp T).domain) :
          Lp ℝ 2 (ν : Measure V))⟫_ℝ ≤
        ‖adjointComp T F‖ ^ 2 :=
    le_of_tendsto_of_tendsto' hleft hright hle

  change
    ρ * ‖T ⟨F, F.2.2⟩‖ ^ 2 ≤
      ‖adjointComp T F‖ ^ 2

  calc
    ρ * ‖T ⟨F, F.2.2⟩‖ ^ 2 =
        ρ * ⟪adjointComp T F,
          ((F : (adjointComp T).domain) :
            Lp ℝ 2 (ν : Measure V))⟫_ℝ := by
      rw [hinner F]
    _ ≤ ‖adjointComp T F‖ ^ 2 := hlim

/-- Centering stays in the domain of the closed gradient: `center u ∈ D(T̄)` for `u ∈ D(T̄)`. -/
theorem center_mem_closedWeightedOperator_domain
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    L2.center ν (u : Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  have hconst :
      L2.const ν (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) ∈ T.domain := by
    have hone :
        L2.const ν 1 ∈ T.domain :=
      one_mem_domain_closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hν hi
    have hsmul :
        L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) • L2.const ν 1 ∈ T.domain :=
      T.domain.smul_mem
        (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) hone
    rw [← mul_one (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))),
      L2.const_smul]
    exact hsmul
  have hsub :
      (u : Lp ℝ 2 (ν : Measure V)) -
          L2.const ν (L2.mean ν (u : Lp ℝ 2 (ν : Measure V))) ∈ T.domain :=
    T.domain.sub_mem u.2 hconst
  simpa [T, L2.center] using hsub

/-- Centering does not change the closed gradient: `T̄ (center u) = T̄ u`. -/
theorem closedWeightedOperator_center
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
          center_mem_closedWeightedOperator_domain m hν hi u⟩ =
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let c := L2.mean ν (u : Lp ℝ 2 (ν : Measure V))
  let o : T.domain :=
    ⟨L2.const ν 1,
      one_mem_domain_closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hν hi⟩

  have hu :
      (⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
          center_mem_closedWeightedOperator_domain m hν hi u⟩ : T.domain) =
        u - c • o := by
    apply Subtype.ext
    change
      L2.center ν (u : Lp ℝ 2 (ν : Measure V)) =
        (u : Lp ℝ 2 (ν : Measure V)) -
          c • (L2.const ν 1)
    simp only [L2.center]
    congr 1
    rw [← L2.const_smul, mul_one]

  have ho : T o = 0 := by
    change
      hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨L2.const ν 1,
            one_mem_domain_closedWeightedOperator m
              (ContinuousLinearMap.id ℝ V) hν hi⟩ = 0
    exact hν.closedWeightedOperator_one_eq_zero m
      (ContinuousLinearMap.id ℝ V) hi

  have hmain :
      T
          ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
            center_mem_closedWeightedOperator_domain m hν hi u⟩ =
        T u := by
    have h := congrArg (fun x : T.domain => T x) hu
    calc
      T
          ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
            center_mem_closedWeightedOperator_domain m hν hi u⟩ =
          T (u - c • o) := h
      _ = T u - T (c • o) := by
        exact T.toFun.map_sub u (c • o)
      _ = T u - c • T o := by
        congr 1
        exact T.toFun.map_smul c o
      _ = T u := by
        rw [ho, smul_zero, sub_zero]

  exact hmain

include hνU hU in
/-- The finite-time Poincaré bound: if `∇∇U ≥ ρ > 0`, then for `u ∈ D(T̄)` and `t ≥ 0`,
`Var(u) - Var(P_t u) ≤ (1 - e^{-2ρt}) / ρ · ‖T̄ u‖²`. -/
theorem norm_center_sq_sub_le {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖L2.center ν
          (HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht u)‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

  let c : T.domain :=
    ⟨L2.center ν (u : Lp ℝ 2 (ν : Measure V)),
      center_mem_closedWeightedOperator_domain m hν hi u⟩

  have hcurv :
      ∀ y : (adjointComp T).domain,
        ρ * ‖T ⟨y, y.2.2⟩‖ ^ 2 ≤ ‖adjointComp T y‖ ^ 2 := by
    intro y
    exact mul_norm_closedWeightedOperator_sq_le m hν hi hνU hU hH y

  have hkey :=
    Generated.norm_sq_sub_norm_apply_sq_le T hT hd hρ hcurv c ht

  have hcenter :
      L2.center ν
          (HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
            (u : Lp ℝ 2 (ν : Measure V))) =
        HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht
          (L2.center ν (u : Lp ℝ 2 (ν : Measure V))) := by
    exact HeatSemigroup.center_operator m (ContinuousLinearMap.id ℝ V) hν hi ht
      (u : Lp ℝ 2 (ν : Measure V))

  rw [hcenter]

  change
    ‖(c : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
        ‖Generated.apply T hT hd t c‖ ^ 2 ≤
      (1 - Real.exp (-2 * ρ * t)) / ρ *
        ‖T u‖ ^ 2

  have hTc :
      T c = T u := by
    simpa [c, T] using
      (closedWeightedOperator_center m hν hi u)

  rw [hTc] at hkey
  exact hkey

/-- A form-domain gap `Var(u) ≤ C ‖T̄ u‖²` bounds the literature Poincaré constant by `C`
(the converse of `closedWeightedOperator_id_gap_of_literature_le`). -/
theorem literatureConstant_le_of_gap (C : NNReal)
    (hgap : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
        (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) := by
  rw [← hν.closedWeightedOperator_id_constant_eq_literature m hi,
    ← Poincare.L2Energy.holds_iff_constant_le,
    Poincare.L2Energy.holds_iff]

  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  intro f

  have hfT : f.1 ∈ T.domain := by
    by_contra h
    have htop :
        Energy.PreEnergy.normSqEnergy T f.1 = ⊤ :=
      Energy.PreEnergy.normSqEnergy_of_notMem T h
    exact f.2 htop

  let u : T.domain := ⟨f.1, hfT⟩

  have hvalue :
      Energy.PreEnergy.normSqEnergy T f.1 =
        ((‖T u‖₊ ^ 2 : NNReal) : ENNReal) := by
    simpa [u] using
      (Energy.PreEnergy.normSqEnergy_of_mem T u)

  have hfinite :
      (Energy.PreEnergy.normSqEnergy T).finiteValue f =
        ‖T u‖₊ ^ 2 := by
    apply ENNReal.coe_injective
    calc
      ((Energy.PreEnergy.normSqEnergy T).finiteValue f : ENNReal) =
          (Energy.PreEnergy.normSqEnergy T).toFun f :=
        Energy.Functional.coe_finiteValue
          (Energy.PreEnergy.normSqEnergy T) f
      _ = Energy.PreEnergy.normSqEnergy T f.1 := rfl
      _ = ((‖T u‖₊ ^ 2 : NNReal) : ENNReal) := hvalue

  have hgap' :
      ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖₊ ^ 2 ≤
        C * ‖T u‖₊ ^ 2 := by
    exact_mod_cast hgap u

  change
    L2.variance ν (f : Lp ℝ 2 (ν : Measure V)) ≤
      C * (Energy.PreEnergy.normSqEnergy T).finiteValue f

  rw [L2.variance, hfinite]
  simpa [u, T] using hgap'

include hνU hU in
/-- Bakry–Gentil–Ledoux (2014), Corollary 4.8.2, **under an ergodicity hypothesis**: if
`∇∇U ≥ ρ > 0` and `Var(P_t u) → 0` as `t → ∞` for every `u ∈ D(T̄)`, then the literature Poincaré
constant satisfies `C_P(ν) ≤ 1/ρ`. -/
theorem literatureConstant_le_inv_of_tendsto {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (herg : ∀ u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
      Tendsto (fun t : ℝ => ‖L2.center ν (Generated.apply
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        (hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi)
        (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) t u)‖)
        atTop (𝓝 0)) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ := by
  let C : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  let T := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
  let hT := hν.closedWeightedOperator_isClosed m (ContinuousLinearMap.id ℝ V) hi
  let hd := hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

  have hgap :
      ∀ u : T.domain,
        ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
          (C : ℝ) * ‖T u‖ ^ 2 := by
    intro u

    let a : ℝ := ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2
    let b : ℕ → ℝ := fun n =>
      ‖L2.center ν (Generated.apply T hT hd (n : ℝ) u)‖ ^ 2
    let d : ℝ := ‖T u‖ ^ 2

    have hpointwise : ∀ n : ℕ, a ≤ b n + ρ⁻¹ * d := by
      intro n
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hmain :=
        norm_center_sq_sub_le m hν hi hνU hU hρ hH u hn
      change
        ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 -
            ‖L2.center ν (Generated.apply T hT hd (n : ℝ) u)‖ ^ 2 ≤
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ * ‖T u‖ ^ 2 at hmain

      have hnum :
          1 - Real.exp (-2 * ρ * (n : ℝ)) ≤ (1 : ℝ) := by
        linarith [Real.exp_nonneg (-2 * ρ * (n : ℝ))]

      have hcoef :
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ ≤ ρ⁻¹ := by
        calc
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ ≤ 1 / ρ :=
            div_le_div_of_nonneg_right hnum hρ.le
          _ = ρ⁻¹ := by rw [one_div]

      have hmul :
          (1 - Real.exp (-2 * ρ * (n : ℝ))) / ρ * ‖T u‖ ^ 2 ≤
            ρ⁻¹ * ‖T u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

      dsimp [a, b, d]
      linarith

    have hb :
        Tendsto (fun n : ℕ => b n) atTop (𝓝 0) := by
      have hnat :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop
      have h := (herg u).comp hnat
      have h' :
          Tendsto
            (fun n : ℕ =>
              ‖L2.center ν (Generated.apply T hT hd (n : ℝ) u)‖ ^ 2)
            atTop (𝓝 (0 : ℝ)) := by
        simpa [T, hT, hd] using h.pow 2
      simpa [b] using h'

    have hsum :
        Tendsto (fun n : ℕ => b n + ρ⁻¹ * d)
          atTop (𝓝 (ρ⁻¹ * d)) := by
      simpa using hb.add tendsto_const_nhds

    have ha : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) :=
      tendsto_const_nhds

    have hlim : a ≤ ρ⁻¹ * d :=
      le_of_tendsto_of_tendsto' ha hsum hpointwise

    have hC : (C : ℝ) = ρ⁻¹ := by
      rfl

    dsimp [a, d] at hlim ⊢
    rw [hC]
    exact hlim

  have hconst :
      Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) :=
    literatureConstant_le_of_gap m hν hi C hgap

  calc
    Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) := hconst
    _ = ENNReal.ofReal ρ⁻¹ := by
      rw [ENNReal.ofReal_eq_coe_nnreal]
      rfl

end FunctionalInequalities.KLS.LogConcave
