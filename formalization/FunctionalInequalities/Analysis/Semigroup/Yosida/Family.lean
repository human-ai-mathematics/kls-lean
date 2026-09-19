import FunctionalInequalities.Analysis.Semigroup.Resolvent.Limit
import FunctionalInequalities.Analysis.Semigroup.VonNeumann
import FunctionalInequalities.Analysis.Semigroup.Yosida.Approximation
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Yosida family `L_s = s⁻¹ (1 - J_s)`

Part A (`Y0`–`Y5`) of the Yosida-limit route recorded in
`research/decisions/2026-09-19-yosida-limit-route.md` and restated in
`research/audits/YosidaLimitRouteStatements.lean`, for a closed operator `T : H₀ →ₗ.[ℝ] H₁`
between real Hilbert spaces.  `J_s = resolventCLM T hT hs` is the resolvent of
`Analysis/Semigroup/Resolvent/Basic.lean` and `L_s = yosida T hT hs = s⁻¹ • (1 - J_s)` is the
Yosida approximation of `Analysis/Semigroup/Yosida/Approximation.lean`.

What is proved here:

* `Y0` = `not_forall_exists_tendsto_exp_neg_smul`: **the abstract `S6` of
  `research/audits/SemigroupGenerationRouteStatements.lean` is false.**  Nonnegativity and
  commutation of a family `L : ℝ → (ℝ →L[ℝ] ℝ)` do not force `exp (-t • L s) f` to converge as
  `s ↓ 0`.  The counterexample is `counterFamily s = counterCoeff s • 1` with `counterCoeff` the
  indicator of `counterSet = {1/(n+1) | n : ℕ}`: along `1/(n+1)` the value at `t = f = 1` is
  `Real.exp (-1)`, along `2/(2n+3)` it is `1`.  The route file
  `SemigroupGenerationRouteStatements.lean` is left byte-unchanged; this module records the
  correction instead.
* `Y1` = `yosida_nonneg`: `0 ≤ ⟪L_s f, f⟫`;
* `Y2` = `yosida_symm`: `⟪L_s f, g⟫ = ⟪f, L_s g⟫`;
* `Y3` = `yosida_comp_comm`: `L_s L_r = L_r L_s`;
* `Y4` = `yosida_apply_eq_resolventCLM_adjointComp`: `L_s f = J_s (T†T f)` for `f ∈ D(T†T)`;
* `Y5` = `exists_delta_norm_yosida_sub_adjointComp_lt`: `L_s f → T†T f` as `s ↓ 0`, for
  `f ∈ D(T†T)`, in the `ε`–`δ` form the route uses (`yosida` carries the proof `0 < s` as an
  argument).

## Route hypotheses

No route hypothesis of `Y0`–`Y5` is dropped, so — unlike the precedent of `S2`, `S3`, `S5`, `V1`
and `V2`, where a strengthened statement is paired with a verbatim wrapper — **no wrapper is
needed here** and the module statements are already the route statements up to the names of the
binders.  In particular the density hypothesis `Dense (T.domain : Set H₀)` of `Y4` is genuinely
used: `Y4` is `V5` (`sub_resolvent_eq_smul`) divided by `s`, and `V5` identifies a value of
Mathlib's `LinearPMap.adjoint`, which carries a junk value on a non-dense domain.  `CompleteSpace
H₀` and `CompleteSpace H₁` are needed for `resolventCLM`, hence for `yosida`, to exist at all, and
`T.IsClosed` likewise.

## Deliberately out of scope

Part B of the route is **not** proved here: `Y6` (the mean-value bound
`‖exp (-t • A) f - exp (-t • B) f‖ ≤ t ‖A f - B f‖` for commuting nonnegative bounded operators),
`Y7` (the corrected abstract `S6`, with a Cauchy hypothesis on a dense set) and `Y8` (`S6` for the
Yosida approximation itself) are owned by other sessions and composed by the integrator.  Nothing
here proves `S7` (the semigroup and strong-continuity laws of the limit) or `S8` (the generator is
`T†T`).

Nothing here is the Markov property, Bakry–Émery `Γ`-calculus, a small-time heat estimate, a
localization step, or any step of Buser's inequality;
`thm:logconcave-cheeger-poincare-comparison` gains no progress marker.  This is general real
Hilbert space material: no measure, no log-concavity and no KLS quantity.
-/

noncomputable section

open Filter Topology InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

/-! ## `Y0` — the abstract `S6` is false

The original `S6` asked, for an abstract family `L : ℝ → H₀ →L[ℝ] H₀` assumed only nonnegative and
commuting, that `exp (-t • L s) f` converge as `s ↓ 0`.  Already on `H₀ = ℝ` this fails.  -/

section Counterexample

/-- The reals of the form `1/(n+1)`, `n : ℕ`; a sequence accumulating at `0⁺`. -/
def counterSet : Set ℝ := {s : ℝ | ∃ n : ℕ, s = 1 / (n + 1)}

/-- The coefficient of the counterexample to the abstract `S6`: the indicator of `counterSet`,
i.e. `1` on `{1/(n+1) | n : ℕ}` and `0` elsewhere. -/
def counterCoeff : ℝ → ℝ := counterSet.indicator fun _ => 1

/-- The counterexample coefficient is nonnegative. -/
theorem counterCoeff_nonneg (s : ℝ) : 0 ≤ counterCoeff s :=
  Set.indicator_apply_nonneg fun _ => zero_le_one

/-- On `counterSet` the coefficient is `1`. -/
theorem counterCoeff_of_mem {s : ℝ} (hs : s ∈ counterSet) : counterCoeff s = 1 :=
  Set.indicator_of_mem hs _

/-- Off `counterSet` the coefficient is `0`. -/
theorem counterCoeff_of_notMem {s : ℝ} (hs : s ∉ counterSet) : counterCoeff s = 0 :=
  Set.indicator_of_notMem hs _

/-- The counterexample family: `L s = counterCoeff s • 1` on `ℝ`. -/
def counterFamily (s : ℝ) : ℝ →L[ℝ] ℝ := counterCoeff s • (1 : ℝ →L[ℝ] ℝ)

/-- The counterexample family is nonnegative, as the abstract `S6` demands. -/
theorem counterFamily_nonneg (s : ℝ) (_hs : 0 < s) (f : ℝ) : 0 ≤ ⟪counterFamily s f, f⟫ := by
  have hval : counterFamily s f = counterCoeff s * f := by simp [counterFamily]
  rw [Real.inner_apply, hval, mul_assoc]
  exact mul_nonneg (counterCoeff_nonneg s) (mul_self_nonneg f)

/-- The counterexample family commutes, as the abstract `S6` demands: scalar multiples of the
identity always do. -/
theorem counterFamily_comm (s r : ℝ) (_hs : 0 < s) (_hr : 0 < r) :
    (counterFamily s).comp (counterFamily r) = (counterFamily r).comp (counterFamily s) := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [ContinuousLinearMap.comp_apply, counterFamily, smul_apply, one_apply_eq_self,
    smul_eq_mul]
  ring

/-- In the algebra `ℝ →L[ℝ] ℝ` the exponential of a scalar multiple of the identity is the scalar
multiple of the identity by the real exponential: `exp (a • 1) x = Real.exp a * x`. -/
theorem exp_smul_one_apply (a x : ℝ) :
    NormedSpace.exp (a • (1 : ℝ →L[ℝ] ℝ)) x = Real.exp a * x := by
  have halg : a • (1 : ℝ →L[ℝ] ℝ) = algebraMap ℝ (ℝ →L[ℝ] ℝ) a :=
    (Algebra.algebraMap_eq_smul_one a).symm
  have hmap : NormedSpace.exp (algebraMap ℝ (ℝ →L[ℝ] ℝ) a)
      = algebraMap ℝ (ℝ →L[ℝ] ℝ) (NormedSpace.exp a) :=
    (NormedSpace.map_exp (algebraMap ℝ (ℝ →L[ℝ] ℝ))
      (continuous_algebraMap ℝ (ℝ →L[ℝ] ℝ)) a).symm
  rw [halg, hmap, ← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
  simp

/-- The value of the counterexample at time `t = 1`: `exp (-1 • L s) x = exp (-c s) x`. -/
theorem counterFamily_exp_apply (s x : ℝ) :
    NormedSpace.exp (-(1 : ℝ) • counterFamily s) x = Real.exp (-counterCoeff s) * x := by
  have hsmul : -(1 : ℝ) • counterFamily s = (-counterCoeff s) • (1 : ℝ →L[ℝ] ℝ) := by
    simp [counterFamily, smul_smul]
  rw [hsmul, exp_smul_one_apply]

/-- The sequence `1/(n+1)` tends to `0` from the right. -/
theorem tendsto_one_div_nhdsGT_zero :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  filter_upwards with n
  simp only [Set.mem_Ioi]
  positivity

/-- The sequence `2/(2n+3)` tends to `0` from the right. -/
theorem tendsto_two_div_nhdsGT_zero :
    Tendsto (fun n : ℕ => 2 / (2 * (n : ℝ) + 3)) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · filter_upwards with n
    simp only [Set.mem_Ioi]
    positivity

/-- `1/(n+1)` lies in `counterSet`, so the coefficient there is `1`. -/
theorem counterCoeff_one_div (n : ℕ) : counterCoeff (1 / ((n : ℝ) + 1)) = 1 :=
  counterCoeff_of_mem ⟨n, rfl⟩

/-- `2/(2n+3)` does not lie in `counterSet` — `2/(2n+3) = 1/(m+1)` would force `2m+2 = 2n+3` —
so the coefficient there is `0`. -/
theorem counterCoeff_two_div (n : ℕ) : counterCoeff (2 / (2 * (n : ℝ) + 3)) = 0 := by
  refine counterCoeff_of_notMem ?_
  rintro ⟨m, hm⟩
  rw [div_eq_div_iff (by positivity) (by positivity)] at hm
  have hcast : ((2 * m + 2 : ℕ) : ℝ) = ((2 * n + 3 : ℕ) : ℝ) := by push_cast; linarith
  have := Nat.cast_injective (R := ℝ) hcast
  omega

/-- `Y0`: **the abstract `S6` is false**.  A family of nonnegative, pairwise commuting bounded
operators on `ℝ` need not have `exp (-t • L s) f` convergent as `s ↓ 0`.  Witness:
`counterFamily`, at `f = 1` and `t = 1`, whose values along `1/(n+1)` and along `2/(2n+3)` are the
distinct constants `Real.exp (-1)` and `1`. -/
theorem not_forall_exists_tendsto_exp_neg_smul :
    ¬ (∀ (L : ℝ → ℝ →L[ℝ] ℝ),
      (∀ s : ℝ, 0 < s → ∀ f, 0 ≤ ⟪L s f, f⟫) →
      (∀ s r : ℝ, 0 < s → 0 < r → (L s).comp (L r) = (L r).comp (L s)) →
      (∀ f : ℝ, ∀ t : ℝ, 0 ≤ t →
        ∃ g : ℝ, Tendsto (fun s : ℝ => NormedSpace.exp (-t • L s) f) (𝓝[>] 0) (𝓝 g))) := by
  intro hS6
  obtain ⟨g, hg⟩ := hS6 counterFamily counterFamily_nonneg counterFamily_comm 1 1 zero_le_one
  -- Along `1/(n+1)` the family is the identity, and the value is `Real.exp (-1)`.
  have hA : Tendsto (fun _ : ℕ => Real.exp (-1)) atTop (𝓝 g) := by
    have hcomp := hg.comp tendsto_one_div_nhdsGT_zero
    refine hcomp.congr fun n => ?_
    simp only [Function.comp_apply, counterFamily_exp_apply, counterCoeff_one_div n, mul_one]
  -- Along `2/(2n+3)` the family vanishes, and the value is `1`.
  have hB : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 g) := by
    have hcomp := hg.comp tendsto_two_div_nhdsGT_zero
    refine hcomp.congr fun n => ?_
    simp only [Function.comp_apply, counterFamily_exp_apply, counterCoeff_two_div n, neg_zero,
      Real.exp_zero, mul_one]
  have hgA : g = Real.exp (-1) := tendsto_nhds_unique hA tendsto_const_nhds
  have hgB : g = 1 := tendsto_nhds_unique hB tendsto_const_nhds
  have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  rw [hgA] at hgB
  exact absurd hgB hlt.ne

end Counterexample

/-! ## `Y1`–`Y5` — the Yosida approximation of `T†T` -/

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- `Y1`: the Yosida approximation is a nonnegative operator.  Indeed
`⟪L_s f, f⟫ = s⁻¹ (⟪f, f⟫ - ⟪J_s f, f⟫)` and `⟪J_s f, f⟫ ≤ ‖J_s f‖ ‖f‖ ≤ ‖f‖ ^ 2 = ⟪f, f⟫` because
`J_s` is a contraction. -/
theorem yosida_nonneg (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
    0 ≤ ⟪yosida T hT hs f, f⟫ := by
  have hle : ⟪resolventCLM T hT hs f, f⟫ ≤ ⟪f, f⟫ := by
    calc ⟪resolventCLM T hT hs f, f⟫ ≤ ‖resolventCLM T hT hs f‖ * ‖f‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * ‖f‖ := by
          gcongr
          exact norm_resolventCLM_le T hT hs f
      _ = ⟪f, f⟫ := (real_inner_self_eq_norm_mul_norm f).symm
  rw [yosida_apply, real_inner_smul_left, inner_sub_left]
  exact mul_nonneg (inv_nonneg.mpr hs.le) (by linarith)

/-- `Y2`: the Yosida approximation is symmetric, because `J_s` is. -/
theorem yosida_symm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f g : H₀) :
    ⟪yosida T hT hs f, g⟫ = ⟪f, yosida T hT hs g⟫ := by
  rw [yosida_apply, yosida_apply, real_inner_smul_left, real_inner_smul_right, inner_sub_left,
    inner_sub_right, resolventCLM_symm]

/-- `Y3`: the Yosida family commutes, `L_s L_r = L_r L_s`.  Both sides expand to
`s⁻¹ r⁻¹ (1 - J_s - J_r + J_s J_r)`, and `J_s J_r = J_r J_s` is `R3`
(`resolventCLM_comp_comm`). -/
theorem yosida_comp_comm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) :
    (yosida T hT hs).comp (yosida T hT hr) = (yosida T hT hr).comp (yosida T hT hs) := by
  ext f
  have hcomm := ContinuousLinearMap.ext_iff.mp (resolventCLM_comp_comm T hT hs hr) f
  simp only [ContinuousLinearMap.comp_apply] at hcomm
  simp only [ContinuousLinearMap.comp_apply, yosida_apply, map_smul, map_sub, hcomm]
  module

/-- `Y4`: on `D(T†T)` the Yosida approximation is `L_s = J_s T†T`.  This is `V5`
(`sub_resolvent_eq_smul`) divided by `s`. -/
theorem yosida_apply_eq_resolventCLM_adjointComp (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) {s : ℝ} (hs : 0 < s) (f : (adjointComp T).domain) :
    yosida T hT hs f = resolventCLM T hT hs (adjointComp T f) := by
  rw [yosida_apply, sub_resolvent_eq_smul T hT hd hs f, smul_smul, inv_mul_cancel₀ hs.ne',
    one_smul]

/-- `Y5`: on `D(T†T)` the Yosida approximation converges strongly to `T†T` as `s ↓ 0`.  By `Y4`
the difference is `J_s (T†T f) - T†T f`, which `R2`
(`exists_delta_norm_resolventCLM_sub_lt`) makes small. -/
theorem exists_delta_norm_yosida_sub_adjointComp_lt (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : (adjointComp T).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
      ‖yosida T hT hs f - adjointComp T f‖ < ε := by
  obtain ⟨δ, hδ, hlt⟩ :=
    exists_delta_norm_resolventCLM_sub_lt T hT hd (adjointComp T f) hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsδ
  rw [yosida_apply_eq_resolventCLM_adjointComp T hT hd hs f]
  exact hlt hs hsδ

end FunctionalInequalities.Analysis.Semigroup
