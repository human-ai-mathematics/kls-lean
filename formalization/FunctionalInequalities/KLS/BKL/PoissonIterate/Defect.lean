import FunctionalInequalities.KLS.BKL.PoissonIterate.Domain
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Hessian
import FunctionalInequalities.Analysis.BakryEmery.TensorEnergy

/-!
# The defects of the BKL iterates: (47), Lemma 3.4, Corollary 3.5 and Lemma 3.2

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 3, pp. 11–13, for the iterates
`iter T̄ f k` of `PoissonIterate/Basic.lean` (the source's `h_{k+1}`) in the heat model
`ν = m.tilted (-U)`, with `U` of temperate growth and all exponential moments, `T̄` the closed
unit-weight gradient, `A = T̄†T̄ = -ℒ` and `C_P(ν) ≤ C`. The defect is
`χ = defect h = ‖∇²h - α ∇h'‖²` for `h' = step h = α (-L)⁻¹ ∇₀h`, `α = scale h`.

## What is proved

For `f ∈ D(A)` and every `k`:

* `normSq_gradField_gradField_iter`: the Pythagorean identity (47),
  `‖∇²h_{k+1}‖² = ‖L h_{k+2}‖² + χ_{k+1}`;
* `normSq_genField_iter_succ_add_defect_le`: **Lemma 3.4**, if `∇²U ≥ a` (any real `a`) then
  `‖L h_{k+2}‖² + χ_{k+1} + a ‖∇h_{k+1}‖² ≤ ‖L h_{k+1}‖²`;
* `tendsto_energy_iter_zero`: **Corollary 3.5**, if `a > 0` then `‖∇h_{k+1}‖² → 0`;
* `sum_defect_iter_le`: if `a ≥ 0` then `Σ_{k<N} χ_{k+1} ≤ ‖L f‖²`;
* `exists_symm_normSq_grad0_iter_succ_sub_le`: **Lemma 3.2** with `λ = 1/C`, a field `S` with
  `k + 2` indices, symmetric under the swap of its first two index positions, with
  `‖∇₀h_{k+2} - S‖² ≤ C χ_{k+1}`.

Each is first proved for one step from an arbitrary field `h` with components in `D(A)`
(`normSq_gradField_gradField_step`, `normSq_genField_step_add_defect_le`,
`exists_symm_normSq_grad0_step_sub_le`). Along the way: weak first derivatives of `D(A)` lie in
`D(T̄)` (`partialDeriv_mem_domain`) and the weak Hessian is symmetric (`partialDeriv_comm`,
`gradField_gradField_comp_swap`), both from `HeatSemigroup/Generator/Hessian.lean`; `α ≥ 0`
(`scale_nonneg`); `⟪u - ∫u, u⟫ = ‖u - ∫u‖²` and `‖u - ∫u‖ ≤ ‖u‖`.

## The argument

Write `u_J = ∂_{J₀} h_{J'}` (the components of `∇h`, in `D(T̄)`) and `w_J = h'_J ∈ D(A)`.
Parseval in the fixed orthonormal basis gives
`Σ_j ‖∂_j u_J - α ∂_j w_J‖² = ‖∇u_J‖² - 2α ⟪A w_J, u_J⟫ + α² ‖∇w_J‖²`, using
`⟪∇u, ∇w⟫ = ⟪A w, u⟫` (`inner_adjointComp`). By (30), `A w_J = α ∇₀h_J = α (u_J - ∫u_J)`, so
the cross terms sum to `α² ‖∇₀h‖²`; with (33) `‖∇h'‖² = ‖∇₀h‖²` and (46)
`‖L h'‖² = α² ‖∇h'‖²` this is (47). Lemma 3.4 is (47) plus the curvature form of (16),
`Σ_j ‖∇∂_j h_I‖² + a ‖∇h_I‖² ≤ ‖A h_I‖²`, summed over `I`; Corollary 3.5 and the summed
defects are its telescoping (`telescope_energy`, `summable_and_tendsto_zero_of_energy`). For
Lemma 3.2 take `S = α⁻¹ (∇²h - ∫∇²h)` (so `S = 0` if `α = 0`, when `h' = 0`): it is symmetric
by the Hessian symmetry, `∇₀h' - S` is the centering of `∇h' - α⁻¹∇²h = -α⁻¹(∇²h - α∇h')`, and
centering is a contraction, so `‖∇₀h' - S‖² ≤ α⁻² χ ≤ C χ` by (32).

## What this is not

These are statements about `L²` classes in the operator domain, not about the source's class
`𝒜`; the weak Hessian is taken in the fixed standard orthonormal basis. Lemma 3.3,
Lemmas 3.8–3.9 and Theorem 3.1 are not proved here.
-/

noncomputable section

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

section General

/-- Splitting off the first index position: `Σ_{J'} F J' = Σ_J Σ_j F (j, J)`. -/
private theorem sum_cons {n k : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin (k + 1) → Fin n) → M) :
    ∑ J, F J = ∑ J, ∑ j, F (Fin.cons j J) := by
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

variable {α : Type*} [MeasurableSpace α] {ν : ProbabilityMeasure α}

/-- Pairing with the centered part: `⟪u - ∫u, u⟫ = ‖u - ∫u‖²`. -/
theorem inner_center_self (u : Lp ℝ 2 (ν : Measure α)) :
    ⟪L2.center ν u, u⟫ = ‖L2.center ν u‖ ^ 2 := by
  have hc : ⟪L2.const ν (L2.mean ν u), u⟫ = L2.mean ν u * L2.mean ν u := by
    rw [← mul_one (L2.mean ν u), L2.const_smul, real_inner_smul_left, real_inner_comm, mul_one]
    rfl
  rw [← real_inner_self_eq_norm_sq, L2.inner_center_center, L2.center, inner_sub_left, hc]

/-- Centering does not increase the `L²` norm: `‖u - ∫u‖² ≤ ‖u‖²`. -/
theorem norm_center_sq_le (u : Lp ℝ 2 (ν : Measure α)) :
    ‖L2.center ν u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_center_center]
  nlinarith [sq_nonneg (L2.mean ν u)]

/-- Centering is linear: `center (x - c y) = center x - c center y`. -/
private theorem center_sub_smul (x y : Lp ℝ 2 (ν : Measure α)) (c : ℝ) :
    L2.center ν (x - c • y) = L2.center ν x - c • L2.center ν y := by
  rw [sub_eq_add_neg, ← neg_smul, L2.center_add, L2.center_smul, neg_smul, ← sub_eq_add_neg]

end General

section Scale

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : ProbabilityMeasure V}
  (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))

/-- The normalizing coefficient `α` is nonnegative. -/
theorem scale_nonneg {k : ℕ} (h : Field ν k) : 0 ≤ scale T h := by
  unfold scale
  split_ifs
  exacts [le_rfl, Real.sqrt_nonneg _]

end Scale

section HeatModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- A weak partial derivative on `D(T̄)` in terms of `T̄`. -/
private theorem partialDeriv_eq {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (T̄).domain)
    (j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ j u = (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (T̄ ⟨u, hu⟩) := by
  rw [partialDeriv, weakGrad_of_mem _ hu]

include hνU hUt hexp in
/-- **Weak first derivatives of `D(A)` lie in `D(T̄)`**: for `u ∈ D(A)`, `∂_j u ∈ D(T̄)`. -/
theorem partialDeriv_mem_domain {u : Lp ℝ 2 (ν : Measure V)}
    (hu : u ∈ (adjointComp T̄).domain) (j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ j u ∈ (T̄).domain := by
  rw [partialDeriv_eq m hν hi hu.2]
  exact compLp_innerSL_mem_closedWeightedOperator_domain m hν hi hνU hUt hexp ⟨u, hu⟩ j

include hνU hUt hexp in
/-- **Symmetry of the weak Hessian**: for `u ∈ D(A)`, `∂_i ∂_j u = ∂_j ∂_i u`. -/
theorem partialDeriv_comm {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain)
    (i j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ i (partialDeriv T̄ j u) = partialDeriv T̄ j (partialDeriv T̄ i u) := by
  have hD : ∀ l, (innerSL ℝ (stdOrthonormalBasis ℝ V l)).compLp (T̄ ⟨u, hu.2⟩) ∈ (T̄).domain :=
    compLp_innerSL_mem_closedWeightedOperator_domain m hν hi hνU hUt hexp ⟨u, hu⟩
  have hc : (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp (T̄ ⟨_, hD j⟩) =
      (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (T̄ ⟨_, hD i⟩) :=
    compLp_innerSL_closedWeightedOperator_comm m hν hi hνU hUt hexp ⟨u, hu⟩ hD j i
  rw [partialDeriv_eq m hν hi hu.2 j, partialDeriv_eq m hν hi hu.2 i,
    partialDeriv_eq m hν hi (hD j), partialDeriv_eq m hν hi (hD i)]
  exact hc

/-- The norm expansion behind (47) for one component: for `u ∈ D(T̄)` and `w ∈ D(A)`,
`Σ_j ‖∂_j u - α ∂_j w‖² = ‖∇u‖² - 2α ⟪A w, u⟫ + α² ‖∇w‖²`. -/
private theorem sum_norm_sq_partialDeriv_sub_smul {u w : Lp ℝ 2 (ν : Measure V)}
    (hu : u ∈ (T̄).domain) (hw : w ∈ (adjointComp T̄).domain) (α : ℝ) :
    ∑ j, ‖partialDeriv T̄ j u - α • partialDeriv T̄ j w‖ ^ 2 =
      ‖weakGrad T̄ u‖ ^ 2 - 2 * α * ⟪gen T̄ w, u⟫ + α ^ 2 * ‖weakGrad T̄ w‖ ^ 2 := by
  have hlin : ∀ j, partialDeriv T̄ j u - α • partialDeriv T̄ j w =
      (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (weakGrad T̄ u - α • weakGrad T̄ w) := by
    intro j
    have h1 := ((innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLpₗ 2 (ν : Measure V)).map_sub
      (weakGrad T̄ u) (α • weakGrad T̄ w)
    have h2 := ((innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLpₗ 2 (ν : Measure V)).map_smul
      α (weakGrad T̄ w)
    simp only [ContinuousLinearMap.compLpₗ_apply] at h1 h2
    rw [h1, h2]
    rfl
  have hinner : ⟪gen T̄ w, u⟫ = ⟪weakGrad T̄ u, weakGrad T̄ w⟫ := by
    rw [gen_of_mem _ hw, inner_adjointComp
      (dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hν hi) ⟨w, hw⟩ hu,
      weakGrad_of_mem _ hu, weakGrad_of_mem _ hw.2, real_inner_comm]
  simp_rw [hlin]
  rw [L2.sum_norm_sq_compLp_innerSL (stdOrthonormalBasis ℝ V), norm_sub_sq_real, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right, hinner]
  ring

include hνU hUt hexp hC in
/-- **BKL (47) for one step.** For a field `h` with components in `D(A)`, `h' = α (-L)⁻¹ ∇₀h` and
`α = scale h`: `‖∇²h‖² = ‖L h'‖² + ‖∇²h - α ∇h'‖²`. -/
theorem normSq_gradField_gradField_step {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
    normSq (gradField T̄ (gradField T̄ h)) = normSq (genField T̄ (step T̄ h)) + defect T̄ h := by
  have hU : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  set α := scale T̄ h
  have hu : ∀ J, gradField T̄ h J ∈ (T̄).domain := fun J =>
    partialDeriv_mem_domain m hν hi hνU hUt hexp (hh _) _
  have hw : ∀ J, step T̄ h J ∈ (adjointComp T̄).domain := step_mem_domain m hν hi hνU hU hC h
  have hgen : ∀ J, gen T̄ (step T̄ h J) = α • grad0 T̄ h J := fun J =>
    congrFun (genField_step m hν hi hνU hU hC h) J
  have hdef : defect T̄ h = ∑ J, (‖weakGrad T̄ (gradField T̄ h J)‖ ^ 2 -
      2 * α * ⟪gen T̄ (step T̄ h J), gradField T̄ h J⟫ +
        α ^ 2 * ‖weakGrad T̄ (step T̄ h J)‖ ^ 2) := by
    rw [defect, normSq, sum_cons]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← sum_norm_sq_partialDeriv_sub_smul m hν hi (hu J) (hw J)]
    rfl
  have hH : normSq (gradField T̄ (gradField T̄ h)) =
      ∑ J, ‖weakGrad T̄ (gradField T̄ h J)‖ ^ 2 :=
    energy_eq_sum _ _
  have hE : ∑ J, ‖weakGrad T̄ (step T̄ h J)‖ ^ 2 = normSq (grad0 T̄ h) := by
    rw [← energy_eq_sum, energy_step m hν hi hνU hU hC]
  have hP : ∑ J, ⟪gen T̄ (step T̄ h J), gradField T̄ h J⟫ = α * normSq (grad0 T̄ h) := by
    rw [normSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hgen, real_inner_smul_left, grad0, inner_center_self]
  rw [normSq_genField_step m hν hi hνU hU hC, energy_step m hν hi hνU hU hC, hdef,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hP, hE,
    ← hH]
  ring

include hνU hUt hexp in
/-- The curvature form of BKL (16) on `D(A)` in terms of the total operators:
`Σ_j ‖∇∂_j u‖² + a ‖∇u‖² ≤ ‖L u‖²` for `u ∈ D(A)` when `∇²U ≥ a`. -/
private theorem sum_norm_sq_weakGrad_partialDeriv_add_le {a : ℝ}
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain) :
    ∑ j, ‖weakGrad T̄ (partialDeriv T̄ j u)‖ ^ 2 + a * ‖weakGrad T̄ u‖ ^ 2 ≤ ‖gen T̄ u‖ ^ 2 := by
  have hD : ∀ l, (innerSL ℝ (stdOrthonormalBasis ℝ V l)).compLp (T̄ ⟨u, hu.2⟩) ∈ (T̄).domain :=
    compLp_innerSL_mem_closedWeightedOperator_domain m hν hi hνU hUt hexp ⟨u, hu⟩
  have h := sum_norm_sq_closedWeightedOperator_add_le m hν hi hνU hUt hexp ha ⟨u, hu⟩ hD
  have e : ∀ j, weakGrad T̄ (partialDeriv T̄ j u) = T̄ ⟨_, hD j⟩ := fun j => by
    rw [partialDeriv_eq m hν hi hu.2, weakGrad_of_mem _ (hD j)]
  simp only [e]
  rw [weakGrad_of_mem _ hu.2, gen_of_mem _ hu]
  exact h

include hνU hUt hexp hC in
/-- **BKL Lemma 3.4 for one step.** For a field `h` with components in `D(A)`, `∇²U ≥ a` and
`h' = α (-L)⁻¹ ∇₀h`: `‖L h'‖² + χ + a ‖∇h‖² ≤ ‖L h‖²`, with `χ = ‖∇²h - α ∇h'‖²`. -/
theorem normSq_genField_step_add_defect_le {a : ℝ}
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
    normSq (genField T̄ (step T̄ h)) + defect T̄ h + a * energy T̄ h ≤ normSq (genField T̄ h) := by
  rw [← normSq_gradField_gradField_step m hν hi hνU hUt hexp hC h hh]
  have hH : normSq (gradField T̄ (gradField T̄ h)) =
      ∑ I, ∑ j, ‖weakGrad T̄ (partialDeriv T̄ j (h I))‖ ^ 2 := by
    rw [show normSq (gradField T̄ (gradField T̄ h)) = energy T̄ (gradField T̄ h) from rfl,
      energy_eq_sum, sum_cons]
    rfl
  rw [hH, energy_eq_sum, normSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun I _ =>
    sum_norm_sq_weakGrad_partialDeriv_add_le m hν hi hνU hUt hexp ha (hh I)

include hνU hUt hexp in
/-- The weak Hessian of a field with components in `D(A)` is symmetric in its first two index
positions: `∂_{J₀} ∂_{J₁} h_I = ∂_{J₁} ∂_{J₀} h_I`. -/
theorem gradField_gradField_comp_swap {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain)
    (J : Fin (k + 2) → Fin (Module.finrank ℝ V)) :
    gradField T̄ (gradField T̄ h) (J ∘ Equiv.swap 0 1) = gradField T̄ (gradField T̄ h) J := by
  have ht : Fin.tail (Fin.tail (J ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail J) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)]
    intro h1
    rw [← Fin.succ_zero_eq_one] at h1
    exact Fin.succ_ne_zero _ (Fin.succ_injective _ h1)
  simp only [gradField]
  rw [ht]
  simp only [Fin.tail, Function.comp_apply, Equiv.swap_apply_left, Fin.succ_zero_eq_one,
    Equiv.swap_apply_right]
  exact partialDeriv_comm m hν hi hνU hUt hexp (hh _) _ _

/-- Centering componentwise is a contraction of `normSq`: for `α = scale h`,
`‖∇₀h' - α⁻¹ center ∇²h‖² ≤ ‖∇h' - α⁻¹ ∇²h‖²`. -/
private theorem normSq_grad0_step_sub_le {k : ℕ} (h : Field ν k) :
    normSq (grad0 T̄ (step T̄ h) -
        fun J => (scale T̄ h)⁻¹ • L2.center ν (gradField T̄ (gradField T̄ h) J)) ≤
      normSq (gradField T̄ (step T̄ h) - (scale T̄ h)⁻¹ • gradField T̄ (gradField T̄ h)) := by
  unfold normSq
  refine Finset.sum_le_sum fun J _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, grad0]
  rw [← center_sub_smul]
  exact norm_center_sq_le _

include hνU hUt hexp hC in
/-- **BKL Lemma 3.2 for one step**, with `λ = 1/C`. For a field `h` with components in `D(A)`,
`h' = α (-L)⁻¹ ∇₀h` is within `C χ` of a field symmetric in its first two index positions:
`S = α⁻¹ (∇²h - ∫∇²h)` (and `S = 0` when `α = 0`) satisfies `‖∇₀h' - S‖² ≤ C χ`. -/
theorem exists_symm_normSq_grad0_step_sub_le (hCpos : 0 < C) {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
    ∃ S : Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      normSq (grad0 T̄ (step T̄ h) - S) ≤ (C : ℝ) * defect T̄ h := by
  have hU : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun J => (scale T̄ h)⁻¹ • L2.center ν (gradField T̄ (gradField T̄ h) J),
    fun J => ?_, (normSq_grad0_step_sub_le m hν hi h).trans ?_⟩
  · simp only [gradField_gradField_comp_swap m hν hi hνU hUt hexp h hh J]
  have hdef : 0 ≤ defect T̄ h := normSq_nonneg _
  rcases (scale_nonneg (T̄) h).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_smul, sub_zero,
      show normSq (gradField T̄ (step T̄ h)) = energy T̄ (step T̄ h) from rfl, step, energy_smul,
      ← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg C.2 hdef
  · have e : gradField T̄ (step T̄ h) - (scale T̄ h)⁻¹ • gradField T̄ (gradField T̄ h) =
        (-(scale T̄ h)⁻¹) •
          (gradField T̄ (gradField T̄ h) - scale T̄ h • gradField T̄ (step T̄ h)) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hpos.ne', neg_smul, neg_smul, one_smul]
      abel
    have hinv : (scale T̄ h ^ 2)⁻¹ ≤ (C : ℝ) :=
      inv_le_of_inv_le₀ (NNReal.coe_pos.mpr hCpos)
        (inv_le_scale_sq_step m hν hi hνU hU hC hCpos h hpos)
    rw [e, normSq_smul, neg_sq, inv_pow]
    exact mul_le_mul_of_nonneg_right hinv hdef

/-! ### The iterates -/

include hνU hUt hexp hC in
/-- **BKL (47).** For `f ∈ D(A)`: `‖∇²h_{k+1}‖² = ‖L h_{k+2}‖² + χ_{k+1}`. -/
theorem normSq_gradField_gradField_iter {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) :
    normSq (gradField T̄ (gradField T̄ (iter T̄ f k))) =
      normSq (genField T̄ (iter T̄ f (k + 1))) + defect T̄ (iter T̄ f k) :=
  normSq_gradField_gradField_step m hν hi hνU hUt hexp hC _
    (iter_mem_adjointComp_domain m hν hi hνU (hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)) hC hf k)

include hνU hUt hexp hC in
/-- **BKL Lemma 3.4.** For `f ∈ D(A)` and `∇²U ≥ a`:
`‖L h_{k+2}‖² + χ_{k+1} + a ‖∇h_{k+1}‖² ≤ ‖L h_{k+1}‖²`. -/
theorem normSq_genField_iter_succ_add_defect_le {a : ℝ}
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) :
    normSq (genField T̄ (iter T̄ f (k + 1))) + defect T̄ (iter T̄ f k) +
        a * energy T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f k)) :=
  normSq_genField_step_add_defect_le m hν hi hνU hUt hexp hC ha _
    (iter_mem_adjointComp_domain m hν hi hνU (hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)) hC hf k)

include hνU hUt hexp hC in
/-- **BKL Corollary 3.5.** For `f ∈ D(A)` and `∇²U ≥ a > 0`, the energies `‖∇h_{k+1}‖²` are
summable and tend to `0`. -/
theorem tendsto_energy_iter_zero {a : ℝ} (ha₀ : 0 < a)
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) :
    Tendsto (fun k => energy T̄ (iter T̄ f k)) atTop (𝓝 0) :=
  (Analysis.BakryEmery.summable_and_tendsto_zero_of_energy
    (L := fun k => normSq (genField T̄ (iter T̄ f k))) (χ := fun k => defect T̄ (iter T̄ f k))
    (v := fun k => energy T̄ (iter T̄ f k)) ha₀ (fun _ => normSq_nonneg _)
    (fun _ => normSq_nonneg _) (fun _ => energy_nonneg _ _)
    (normSq_genField_iter_succ_add_defect_le m hν hi hνU hUt hexp hC ha hf)).2.2

include hνU hUt hexp hC in
/-- **The summed defects.** For `f ∈ D(A)` and `∇²U ≥ a ≥ 0`:
`Σ_{k<N} χ_{k+1} ≤ ‖L f‖²`. -/
theorem sum_defect_iter_le {a : ℝ} (ha₀ : 0 ≤ a)
    (ha : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) (N : ℕ) :
    ∑ k ∈ Finset.range N, defect T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f 0)) := by
  have h := Analysis.BakryEmery.telescope_energy
    (L := fun k => normSq (genField T̄ (iter T̄ f k))) (χ := fun k => defect T̄ (iter T̄ f k))
    (v := fun k => energy T̄ (iter T̄ f k))
    (normSq_genField_iter_succ_add_defect_le m hν hi hνU hUt hexp hC ha hf) N
  have hv : 0 ≤ a * ∑ k ∈ Finset.range N, energy T̄ (iter T̄ f k) :=
    mul_nonneg ha₀ (Finset.sum_nonneg fun _ _ => energy_nonneg _ _)
  linarith [normSq_nonneg (genField T̄ (iter T̄ f N))]

include hνU hUt hexp hC in
/-- **BKL Lemma 3.2**, with `λ = 1/C`. For `f ∈ D(A)`, `∇₀h_{k+2}` is within `C χ_{k+1}` of a
field symmetric in its first two index positions. -/
theorem exists_symm_normSq_grad0_iter_succ_sub_le (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) :
    ∃ S : Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      normSq (grad0 T̄ (iter T̄ f (k + 1)) - S) ≤ (C : ℝ) * defect T̄ (iter T̄ f k) :=
  exists_symm_normSq_grad0_step_sub_le m hν hi hνU hUt hexp hC hCpos _
    (iter_mem_adjointComp_domain m hν hi hνU (hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)) hC hf k)

end HeatModel

end FunctionalInequalities.KLS.LogConcave.PoissonIterate
