module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.Order.Group.Indicator

/-! # A nonconvergent family of commuting nonnegative exponentials
Nonnegativity and pairwise commutation alone do not ensure a strong limit.
This counterexample is independent of the Yosida construction. -/

@[expose] public section

noncomputable section

open Filter Topology InnerProductSpace
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

section Counterexample

/-- The reals of the form `1/(n+1)`, `n : ℕ`; a sequence accumulating at `0⁺`. -/
def counterSet : Set ℝ := {s : ℝ | ∃ n : ℕ, s = 1 / (n + 1)}

/--
The coefficient of the counterexample to the abstract adjoint-product identification: the indicator
of `counterSet`,
i.e. `1` on `{1/(n+1) | n : ℕ}` and `0` elsewhere. -/
def counterCoeff : ℝ → ℝ :=
  counterSet.indicator fun _ => 1

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

/--
The counterexample family is nonnegative, as the abstract adjoint-product identification demands. -/
theorem counterFamily_nonneg (s : ℝ) (_hs : 0 < s) (f : ℝ) : 0 ≤ ⟪counterFamily s f, f⟫ := by
  have hval : counterFamily s f = counterCoeff s * f := by simp [counterFamily]
  rw [Real.inner_apply, hval, mul_assoc]
  exact mul_nonneg (counterCoeff_nonneg s) (mul_self_nonneg f)

/--
The counterexample family commutes, as the abstract adjoint-product identification demands: scalar
multiples of the
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

/--
**The abstract adjoint-product identification is false.**  A family of nonnegative, pairwise
commuting bounded
operators on `ℝ` need not have `exp (-t • L s) f` convergent as `s ↓ 0`.  Witness:
`counterFamily`, at `f = 1` and `t = 1`, whose values along `1/(n+1)` and along `2/(2n+3)` are the
distinct constants `Real.exp (-1)` and `1`. -/
theorem not_forall_exists_tendsto_exp_neg_smul :
    ¬(∀ (L : ℝ → ℝ →L[ℝ] ℝ),
        (∀ s : ℝ, 0 < s → ∀ f, 0 ≤ ⟪L s f, f⟫) →
          (∀ s r : ℝ, 0 < s → 0 < r → (L s).comp (L r) = (L r).comp (L s)) →
            (∀ f : ℝ,
              ∀ t : ℝ,
                0 ≤ t →
                  ∃ g : ℝ,
                    Tendsto (fun s : ℝ => NormedSpace.exp (-t • L s) f) (𝓝[>] 0) (𝓝 g))) := by
  intro hS6
  obtain ⟨g, hg⟩ :=
    hS6 counterFamily counterFamily_nonneg counterFamily_comm 1 1
      zero_le_one
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

end FunctionalInequalities.Analysis.Semigroup
