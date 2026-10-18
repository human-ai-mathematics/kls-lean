import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Gamma
import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity

/-!
# The generator form of the weak `Γ₂` inequality

`HeatSemigroup/Gamma.lean` states the weak `Γ₂` inequality in the **two-field** form

`0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν`,

whose transfer to a general `F` needs `L²` convergence of `∇fₙ` **and** of `-∇(ℒ fₙ)`. The
second convergence is a second-order property of the approximating sequence, and it is the
obstruction that motivates the formulation below.

This module removes the second field from the inequality altogether. For `F ∈ D(A)` with
`A F ∈ D(T̄)` and `φ ∈ C_c^∞(V)`, the Leibniz rule of
`KLS/LogConcave/WeightedGradient/Multiplier.lean` applied to the product `φ (A F)` together with
the weak integration by parts of `Gamma.lean` gives the exact identity

`∫ φ Γ(T̄ F, T̄ (A F)) dν = ∫ φ (A F)² dν - ∫ (A F) Γ(T̄ F, T̄ φ) dν`

(`integral_mul_weakGamma_adjointComp_eq`). Both terms on the right involve `T̄ F` and `A F`
only: the field `T̄ (A F)` has disappeared. Consequently the weak `Γ₂` inequality in the form

`0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ (A F)² dν - ∫ (A F) Γ(T̄ F, T̄ φ) dν`

transfers along **first-order** graph convergence for the generator: `fₙ → F` and `A fₙ → A F`
in `L²` suffice, and `T̄ fₙ → T̄ F` is then automatic through `‖T̄ y‖² = ⟪A y, y⟫`. No convergence
of any second-order field is required.

## What is proved and what is assumed

`integral_mul_weakGamma_adjointComp_eq` and the transfer theorem
`integral_mul_sq_adjointComp_nonneg_of_tendsto` are unconditional. The hypothesis of the
transfer theorem is that `F` is a graph limit of smooth compactly supported classes **for the
generator** `A`, that is, `F` lies in the domain of the closure of `A` restricted to
`C_c^∞(V)`; this is visible in the statement as two explicit `L²` convergences of `fₙ` and
`A fₙ`, and it holds for every `f ∈ C_c^∞(V)` itself
(`exists_seq_smooth_tendsto_adjointComp_toLp`, the constant sequence). The class of admissible
`F` is moreover closed for the graph norm of `A`
(`exists_seq_smooth_tendsto_adjointComp_of_tendsto`), so it is exactly the domain of the closure
of `A` restricted to `C_c^∞(V)`; it is not claimed to be all of `D(A)`.

That `P_t g` has this property for an arbitrary `g ∈ L²(ν)` is exactly the assertion that
`C_c^∞(V)` is an **operator core** of `A`, equivalently that `ℒ` is essentially self-adjoint on
`C_c^∞(V)` for the log-concave weight; it is a property of the model, independent of `φ`, `t`
and `g`. It is stated as the explicit hypothesis `hcore` of
`HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core`, and it is **proved** for every `C¹`
potential in `HeatSemigroup/InteriorRegularity.lean`
(`KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp`). Everything else in that
theorem — `P_t g ∈ D(A)`, `A (P_t g) ∈ D(T̄)`, all integrabilities and the identity relating the
generator form to the two-field form — is proved in this module.

`HeatSemigroup/OperatorCore.lean` splits `hcore` into its two classical halves and proves the
global one: `integral_mul_weakGamma_apply_nonneg_of_localRegularity` below is the same heat-flow
conclusion with `hcore` replaced by the **local** statement that every `L²` class orthogonal to
`(A + 1) C_c^∞(V)` has all of its `C_c^∞` localizations in `D(T̄)`.
`HeatSemigroup/InteriorRegularity.lean` proves that local statement for every `C¹` potential, so
`hcore` is a theorem (`KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp`), and
`integral_mul_weakGamma_apply_nonneg` below is the heat-flow weak `Γ₂` inequality **without**
any operator-core, approximation or regularity hypothesis, for a `C^∞` convex potential, arbitrary
`g ∈ L²(ν)`, every `t > 0` and every nonnegative `φ ∈ C_c^∞(V)`. The two conditional frontends
are kept unchanged.

Neither `Γ(P_t f) ≤ P_t Γ(f)`, nor the `Γ` time interpolation, nor Buser's inequality follows
from anything in this module.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section Identity

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- **The second field can be eliminated from the tested weak `Γ`.** For `F ∈ D(A)` with
`A F ∈ D(T̄)` and a smooth compactly supported `φ`,

`∫ φ Γ(T̄ F, T̄ (A F)) dν = ∫ φ (A F)² dν - ∫ (A F) Γ(T̄ F, T̄ φ) dν`.

The proof pairs `T̄ F` against `T̄ (φ (A F))`: the Leibniz rule
`coeFn_closedWeightedOperator_toLp_mul` splits that field into `φ (T̄ (A F))` and
`(A F) (B ∇φ)`, and weak integration by parts evaluates the pairing as `∫ (A F) (φ (A F)) dν`.
Every term is integrable: `φ` and `B ∇φ` are bounded with compact support, and `A F`, `T̄ F`,
`T̄ (A F)` are in `L²`. -/
theorem integral_mul_weakGamma_adjointComp_eq
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
            (apply B φ)) y ∂(ν : Measure V) := by
  classical
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (mod_cast le_top)
  have hβcont : Continuous (apply B φ) :=
    B.continuous.comp (Analysis.BakryEmery.continuous_gradient hφ1)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨N, hN⟩ := hβcont.bounded_above_of_compact_support (hasCompactSupport_apply B hφc)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hMb : ∀ᵐ y ∂(ν : Measure V), |φ y| ≤ M :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hM y
  have hNb : ∀ᵐ y ∂(ν : Measure V),
      ‖((IsTest.of_contDiff_hasCompactSupport ν B hφ hφc).memLp_apply.toLp
        (apply B φ) : Lp V 2 (ν : Measure V)) y‖ ≤ N := by
    filter_upwards [(IsTest.of_contDiff_hasCompactSupport ν B hφ hφc).memLp_apply.coeFn_toLp]
      with y hy
    rw [hy]
    exact hN y
  set u := hν.closedWeightedOperator m B hi ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩ with hu
  set a := (adjointComp (hν.closedWeightedOperator m B hi) F : Lp ℝ 2 (ν : Measure V)) with ha
  set w := hν.closedWeightedOperator m B hi ⟨a, hAF⟩ with hw
  set β := (IsTest.of_contDiff_hasCompactSupport ν B hφ hφc).memLp_apply.toLp (apply B φ) with hβ
  have hmul := hν.toLp_mul_mem_closedWeightedOperator_domain m B hi hφ hφc ⟨a, hAF⟩
  have hval := hν.coeFn_closedWeightedOperator_toLp_mul m B hi hφ hφc ⟨a, hAF⟩ hmul
  have hibp := hν.integral_weakGamma_eq_integral_mul_adjointComp m B hi F ⟨_, hmul⟩
  -- the right-hand side of the integration by parts
  have hrhs : ∫ y, a y * ((memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
      ((⟨a, hAF⟩ : (hν.closedWeightedOperator m B hi).domain) :
        Lp ℝ 2 (ν : Measure V))).toLp _ : Lp ℝ 2 (ν : Measure V)) y ∂(ν : Measure V)
      = ∫ y, φ y * (a y) ^ 2 ∂(ν : Measure V) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hφ hφc
      ((⟨a, hAF⟩ : (hν.closedWeightedOperator m B hi).domain) :
        Lp ℝ 2 (ν : Measure V))).coeFn_toLp] with y hy
    rw [hy]
    ring
  -- the left-hand side splits by the Leibniz rule
  have hsplit : (fun y => WeakGamma.apply u
        (hν.closedWeightedOperator m B hi ⟨_, hmul⟩) y)
      =ᵐ[(ν : Measure V)] fun y => φ y * WeakGamma.apply u w y + a y * WeakGamma.apply u β y := by
    filter_upwards [hval, (IsTest.of_contDiff_hasCompactSupport ν B hφ
      hφc).memLp_apply.coeFn_toLp] with y hy1 hy2
    simp only [WeakGamma.apply_def, hw, hβ, hy1, hy2, inner_add_right, real_inner_smul_right]
  rw [integral_congr_ae hsplit, integral_add (WeakGamma.integrable_mul
      hφ.continuous.aestronglyMeasurable hMb u w)
    (WeakGamma.integrable_mul_of_bdd_right hNb a u)] at hibp
  rw [hrhs] at hibp
  linarith [hibp]

end Identity

section Tilted

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **The generator form of the weak `Γ₂` inequality on smooth compactly supported data.** For
`ν = m.tilted (-U)` with a `C^∞` convex potential, a smooth compactly supported `f` and a smooth
compactly supported `φ ≥ 0`,

`0 ≤ (∫ (ℒφ) Γ(T̄ f, T̄ f) dν)/2 + ∫ φ (A f)² dν - ∫ (A f) Γ(T̄ f, T̄ φ) dν`.

This is `Analysis.BakryEmery.integral_mul_weakGamma_nonneg` with the second field eliminated by
`integral_mul_weakGamma_adjointComp_eq`; no new analytic input is used, and the two statements
are equivalent for smooth compactly supported data. -/
theorem integral_mul_sq_adjointComp_toLp_nonneg
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
          ∂(ν : Measure V) := by
  have hAF := hν.adjointComp_toLp_mem_closedWeightedOperator_domain m hi hνU hU hf hfc
  have hid := hν.integral_mul_weakGamma_adjointComp_eq m (ContinuousLinearMap.id ℝ V) hi
    ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ hAF hφ hφc
  have hbase := integral_mul_weakGamma_nonneg (μ := (ν : Measure V)) m hνU
    (hU.of_le (by decide)) hconv (hf.of_le (by decide)) hfc
    (hφ.of_le (by decide)) hφc hφ0
    (u := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
      ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩)
    (w := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hAF⟩)
    (hν.coeFn_closedWeightedOperator_toLp_gradient m hi hf hfc)
    (hν.coeFn_closedWeightedOperator_adjointComp_toLp m hi hνU hU hf hfc hAF)
  rw [hid] at hbase
  linarith [hbase]

/-- **Transfer of the generator form of the weak `Γ₂` inequality along graph convergence for the
generator.** If `fₙ ∈ C_c^∞(V)` satisfies `[fₙ] → F` and `A [fₙ] → A F` in `L²(ν)`, then the
inequality holds at `F`. Only these two convergences are hypotheses: `T̄ fₙ → T̄ F` is **derived**
from them through `‖T̄ y‖² = ⟪A y, y⟫`, and no convergence of a second-order field is required or
available.

The hypothesis says exactly that `F` lies in the domain of the closure of `A` restricted to
`C_c^∞(V)`; it holds for every smooth compactly supported class by the constant sequence, and it
is **not** proved here for `P_t g`. -/
theorem integral_mul_sq_adjointComp_nonneg_of_tendsto
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
          ∂(ν : Measure V) := by
  classical
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  have hU2 : ContDiff ℝ 2 U := hU.of_le (by decide)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by decide)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by decide)
  obtain ⟨C₁, hC₁⟩ := (continuous_weightedLaplacian hU1 hφ2).bounded_above_of_compact_support
    (hasCompactSupport_weightedLaplacian U hφc)
  obtain ⟨C₂, hC₂⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hβcont : Continuous (apply (ContinuousLinearMap.id ℝ V) φ) :=
    (ContinuousLinearMap.id ℝ V).continuous.comp (Analysis.BakryEmery.continuous_gradient hφ1)
  obtain ⟨N, hN⟩ := hβcont.bounded_above_of_compact_support
    (hasCompactSupport_apply (ContinuousLinearMap.id ℝ V) hφc)
  have hC₁' : ∀ᵐ y ∂(ν : Measure V), |weightedLaplacian U φ y| ≤ C₁ :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hC₁ y
  have hC₂' : ∀ᵐ y ∂(ν : Measure V), |φ y| ≤ C₂ :=
    Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hC₂ y
  have hNb : ∀ᵐ y ∂(ν : Measure V),
      ‖((IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hφ
        hφc).memLp_apply.toLp (apply (ContinuousLinearMap.id ℝ V) φ) :
          Lp V 2 (ν : Measure V)) y‖ ≤ N := by
    filter_upwards [(IsTest.of_contDiff_hasCompactSupport ν (ContinuousLinearMap.id ℝ V) hφ
      hφc).memLp_apply.coeFn_toLp] with y hy
    rw [hy]
    exact hN y
  have hmemT : ∀ n, (memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := fun n =>
    hν.toLp_mem_closedWeightedOperator_domain m hi (hfn n) (hfnc n)
  have hmemA : ∀ n, (memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n) ∈
      (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain :=
    fun n => hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn n) (hfnc n)
  -- the first-order convergence is derived, not assumed
  have hsq : ∀ n, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmemT n⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩‖ ^ 2
      ≤ ‖(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hmemA n⟩ : Lp ℝ 2 (ν : Measure V)) -
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
            Lp ℝ 2 (ν : Measure V))‖ *
        ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n) -
          (F : Lp ℝ 2 (ν : Measure V))‖ := by
    intro n
    have hdval : (((⟨_, hmemA n⟩ : (adjointComp (hν.closedWeightedOperator m
          (ContinuousLinearMap.id ℝ V) hi)).domain) - F :
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
          Lp ℝ 2 (ν : Measure V))
        = (memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n) -
          (F : Lp ℝ 2 (ν : Measure V)) := rfl
    have hAd := apply_sub_of_eq_sub (S := adjointComp
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) (hmemA n) F.2
      ((⟨_, hmemA n⟩ : (adjointComp (hν.closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hi)).domain) - F).2 hdval
    have hTd := apply_sub_of_eq_sub
      (S := hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (hmemT n) F.2.2
      (((⟨_, hmemA n⟩ : (adjointComp (hν.closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hi)).domain) - F)).2.2 hdval
    have hform := inner_adjointComp_self
      (hν.dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
      ((⟨_, hmemA n⟩ : (adjointComp (hν.closedWeightedOperator m
        (ContinuousLinearMap.id ℝ V) hi)).domain) - F)
    rw [hAd, hTd, hdval] at hform
    rw [← hform]
    exact real_inner_le_norm _ _
  have hprod : Tendsto (fun n =>
      ‖(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hmemA n⟩ : Lp ℝ 2 (ν : Measure V)) -
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F :
          Lp ℝ 2 (ν : Measure V))‖ *
      ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n) -
        (F : Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) := by
    simpa using h1.mul h0
  have hu : Tendsto (fun n =>
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hmemT n⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩‖) atTop (𝓝 0) := by
    have hsq0 := squeeze_zero (fun n => sq_nonneg _) hsq hprod
    have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq0
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hroot
    exact hroot
  refine integral_mul_sq_nonneg_of_tendsto
    (continuous_weightedLaplacian hU1 hφ2).aestronglyMeasurable
    (le_trans (norm_nonneg _) (hC₁ 0)) hC₁' hφ.continuous.aestronglyMeasurable
    (le_trans (norm_nonneg _) (hC₂ 0)) hC₂' (le_trans (norm_nonneg _) (hN 0)) hNb hu h1
    fun n => ?_
  exact hν.integral_mul_sq_adjointComp_toLp_nonneg m hi hνU hU hconv (hfn n) (hfnc n) hφ hφc hφ0

/-- **Every smooth compactly supported class is in the approximation class**, by the constant
sequence. This is what makes the hypothesis of
`integral_mul_sq_adjointComp_nonneg_of_tendsto` non-vacuous. -/
theorem exists_seq_smooth_tendsto_adjointComp_toLp
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
              Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) := by
  refine ⟨fun _ => f, fun _ => hf, fun _ => hfc, ?_, ?_⟩ <;> simp

/-- **The approximation class is stable under graph limits for the generator.** If every `y k`
is a graph limit of smooth compactly supported classes for `A`, and `y k → z` with
`A (y k) → A z`, then `z` is such a graph limit too. Together with the fact that every smooth
compactly supported class is trivially one (constant sequence), this identifies the hypothesis
of `integral_mul_sq_adjointComp_nonneg_of_tendsto` as membership in the domain of the **closure
of `A` restricted to `C_c^∞(V)`** — a closed operator extending the classical `-ℒ`, and the
largest class on which the present argument delivers the inequality. It is not claimed that this
class is all of `D(A)`. -/
theorem exists_seq_smooth_tendsto_adjointComp_of_tendsto
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
            Lp ℝ 2 (ν : Measure V))‖) atTop (𝓝 0) := by
  classical
  choose fn hfn hfnc hP using hy
  have hchoose : ∀ k : ℕ, ∃ n : ℕ,
      ‖(memLp_of_contDiff_hasCompactSupport ν (hfn k n) (hfnc k n)).toLp (fn k n)
          - (y k : Lp ℝ 2 (ν : Measure V))‖ < 1 / (k + 1) ∧
        ‖(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn k n)
              (hfnc k n)⟩ : Lp ℝ 2 (ν : Measure V))
          - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (y k) :
              Lp ℝ 2 (ν : Measure V))‖ < 1 / (k + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    exact ((((hP k).1).eventually_lt_const hpos).and
      (((hP k).2).eventually_lt_const hpos)).exists
  choose n hn₀ hn₁ using hchoose
  refine ⟨fun k => fn k (n k), fun k => hfn k (n k), fun k => hfnc k (n k), ?_, ?_⟩
  · have hbound : ∀ k : ℕ,
        ‖(memLp_of_contDiff_hasCompactSupport ν (hfn k (n k)) (hfnc k (n k))).toLp (fn k (n k))
          - (z : Lp ℝ 2 (ν : Measure V))‖
        ≤ 1 / (k + 1) + ‖(y k : Lp ℝ 2 (ν : Measure V)) - (z : Lp ℝ 2 (ν : Measure V))‖ := by
      intro k
      calc ‖(memLp_of_contDiff_hasCompactSupport ν (hfn k (n k))
              (hfnc k (n k))).toLp (fn k (n k)) - (z : Lp ℝ 2 (ν : Measure V))‖
          ≤ ‖(memLp_of_contDiff_hasCompactSupport ν (hfn k (n k))
                (hfnc k (n k))).toLp (fn k (n k)) - (y k : Lp ℝ 2 (ν : Measure V))‖
            + ‖(y k : Lp ℝ 2 (ν : Measure V)) - (z : Lp ℝ 2 (ν : Measure V))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1 / (k + 1) + ‖(y k : Lp ℝ 2 (ν : Measure V)) - (z : Lp ℝ 2 (ν : Measure V))‖ := by
            gcongr
            exact (hn₀ k).le
    refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).add h0
  · have hbound : ∀ k : ℕ,
        ‖(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) (hfn k (n k))
              (hfnc k (n k))⟩ : Lp ℝ 2 (ν : Measure V))
          - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z :
              Lp ℝ 2 (ν : Measure V))‖
        ≤ 1 / (k + 1) +
          ‖(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (y k) :
              Lp ℝ 2 (ν : Measure V))
            - (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) z :
                Lp ℝ 2 (ν : Measure V))‖ := by
      intro k
      refine le_trans (norm_sub_le_norm_sub_add_norm_sub _
        ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) (y k) :
          Lp ℝ 2 (ν : Measure V))) _) ?_
      gcongr
      exact (hn₁ k).le
    refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).add h1

/-- **The two-field weak `Γ₂` inequality under first-order graph convergence for the generator.**

This is the statement `integral_mul_weakGamma_adjointComp_nonneg_of_tendsto` of
`HeatSemigroup/Gamma.lean` with its two hypotheses replaced by one: instead of `L²` convergence
of `∇fₙ` **and** of `-∇(ℒ fₙ)` to the two fields of `F`, it asks only that `fₙ → F` and
`A fₙ → A F` in `L²`. The second-order field `T̄ (A F)` still appears in the conclusion — it
exists because of the hypothesis `hAF` — but no approximation of it is required, because
`integral_mul_weakGamma_adjointComp_eq` rewrites its contribution in terms of `A F` alone. -/
theorem integral_mul_weakGamma_adjointComp_nonneg_of_graph_tendsto
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
          ∂(ν : Measure V) := by
  have hgen := hν.integral_mul_sq_adjointComp_nonneg_of_tendsto m hi hνU hU hconv hφ hφc hφ0
    hfn hfnc F h0 h1
  rw [hν.integral_mul_weakGamma_adjointComp_eq m (ContinuousLinearMap.id ℝ V) hi F hAF hφ hφc]
  linarith [hgen]

end Tilted

namespace HeatSemigroup

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **Weak `Γ₂` along the actual heat flow, under one operator-core hypothesis.**

For an arbitrary datum `g ∈ L²(ν)` and every `t > 0`, positive-time smoothing puts `P_t g` in
`D(A)` and `A (P_t g)` in `D(T̄)`, so both fields of the inequality exist unconditionally. The
only remaining input is `hcore`: every element of `D(A)` is a graph limit of smooth compactly
supported classes **for `A`**. That is the statement that `C_c^∞(V)` is an operator core of
`A = T̄†T̄`, equivalently that `ℒ = Δ - ⟪∇U, ∇·⟫` is essentially self-adjoint on `C_c^∞(V)` in
`L²(ν)`.

`hcore` is a property of the model alone: it does not mention `φ`, `g` or `t`, it involves no
second-order field, and it is a *first-order* graph condition for the generator. It is proved for
every `C¹` potential in `HeatSemigroup/InteriorRegularity.lean`
(`KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp`); this conditional form is kept as the
statement that isolates it. -/
theorem integral_mul_weakGamma_apply_nonneg_of_core
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
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩) y
          ∂(ν : Measure V)) / 2 +
        ∫ y, φ y * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m
                (ContinuousLinearMap.id ℝ V) hν hi g ht
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩) y
          ∂(ν : Measure V) := by
  obtain ⟨fn, hfn, hfnc, h0, h1⟩ := hcore
    ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht⟩
  exact hν.integral_mul_weakGamma_adjointComp_nonneg_of_graph_tendsto m hi hνU hU hconv hφ hφc
    hφ0 hfn hfnc ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht⟩
    (mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
      ht (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)) h0 h1

/-- **Weak `Γ₂` along the actual heat flow, under a purely local regularity hypothesis.**

Same conclusion as `integral_mul_weakGamma_apply_nonneg_of_core`, with the global operator-core
hypothesis replaced by the local one supplied to
`KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity`: every `u ∈ L²(ν)`
orthogonal to `(A + 1) C_c^∞(V)` has all of its localizations `[χ u]`, `χ ∈ C_c^∞(V)`, in the
form domain `D(T̄)`. The global cutoff argument that turns this into an operator core is proved
in `HeatSemigroup/OperatorCore.lean`.

The hypothesis is **not weaker** than `hcore`: if `hcore` holds there is no nonzero class
orthogonal to `(A + 1) C_c^∞(V)`, so the hypothesis holds vacuously, and the criterion proves the
converse, so the two are logically equivalent. The hypothesis names the classical ingredient,
interior elliptic regularity for `div(e^{-U} ∇ ·)`, which is proved for every `C¹` potential in
`HeatSemigroup/InteriorRegularity.lean`
(`KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`); the unconditional
statement is `integral_mul_weakGamma_apply_nonneg` below. -/
theorem integral_mul_weakGamma_apply_nonneg_of_localRegularity
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    (hreg : ∀ u : Lp ℝ 2 (ν : Measure V),
      (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by norm_num)) hf hfc⟩ :
              Lp ℝ 2 (ν : Measure V)), u⟫ +
          ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f :
            Lp ℝ 2 (ν : Measure V)), u⟫ = 0) →
      ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
        (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    0 ≤ (∫ y, weightedLaplacian U φ y *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩) y
          ∂(ν : Measure V)) / 2 +
        ∫ y, φ y * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m
                (ContinuousLinearMap.id ℝ V) hν hi g ht
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩) y
          ∂(ν : Measure V) :=
  integral_mul_weakGamma_apply_nonneg_of_core m hν hi hνU hU hconv
    (fun y => hν.exists_seq_smooth_tendsto_adjointComp_of_localRegularity m hi hνU
      (hU.of_le (by norm_num)) hreg y) hφ hφc hφ0 g ht

/-- **Weak `Γ₂` along the heat flow, with no operator-core, approximation or regularity
hypothesis.**

For `ν = m.tilted (-U)` with a `C^∞` convex potential `U` and unit weight, for **every**
`g ∈ L²(ν)`, every `t > 0` and every nonnegative `φ ∈ C_c^∞(V)`, with `F = P_t g`,

`0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν`.

This is `integral_mul_weakGamma_apply_nonneg_of_core` with `hcore` supplied by the operator-core
theorem `KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp`, itself a consequence of the
interior regularity of deficiency elements proved in `HeatSemigroup/InteriorRegularity.lean`. The
remaining hypotheses are those of the model: the tilted form of the law, smoothness and convexity
of the potential, and the unit weight. -/
theorem integral_mul_weakGamma_apply_nonneg
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (hconv : ConvexOn ℝ Set.univ U)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (g : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    0 ≤ (∫ y, weightedLaplacian U φ y *
          WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩) y
          ∂(ν : Measure V)) / 2 +
        ∫ y, φ y * WeakGamma.apply
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨HeatSemigroup.operator m (ContinuousLinearMap.id ℝ V) hν hi ht.le g,
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht).2⟩)
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
              ⟨_, mem_closedWeightedOperator_domain_adjointComp_of_pos m
                (ContinuousLinearMap.id ℝ V) hν hi g ht
                (mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g ht)⟩) y
          ∂(ν : Measure V) :=
  integral_mul_weakGamma_apply_nonneg_of_core m hν hi hνU hU hconv
    (fun y => hν.exists_seq_smooth_tendsto_adjointComp m hi hνU (hU.of_le (by norm_num)) y)
    hφ hφc hφ0 g ht

end HeatSemigroup

end FunctionalInequalities.KLS.LogConcave
