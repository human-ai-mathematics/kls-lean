import FunctionalInequalities.KLS.BKL.PoissonIterate.Basic

/-!
# The BKL iterates lie in `D(A)`: domain, (30), (33), (46), (35)–(36) and (32)

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 3, (30)–(36), for the iterates
`iter T̄ f k` of `PoissonIterate/Basic.lean` in the heat model `ν = m.tilted (-U)`, `U ∈ C²`,
with `T̄` the closed unit-weight gradient, `A = T̄†T̄ = -ℒ` and `C_P(ν) ≤ C`.

## What is proved

For a centered `f ∈ D(A)` and every `k` (`iter T̄ f k` is the source's `h_{k+1}`):

* `iter_mem_domain_and_mean_eq_zero`: every component of `h_{k+1}` lies in `D(A)` and is
  centered;
* `genField_iter_succ`: the Poisson relation (30), `-L h_{k+2} = α_{k+2} ∇₀ h_{k+1}`;
* `energy_iter_succ`: the normalization (33), `‖∇h_{k+2}‖² = ‖∇₀h_{k+1}‖²`;
* `normSq_genField_iter_succ`: (46), `‖L h_{k+2}‖² = α_{k+2}² ‖∇h_{k+2}‖²`;
* `energy_sub_energy_iter_succ`: the energy drop (35), `v_{k+1} - v_{k+2} = p_{k+1}`;
* `inv_le_scale_sq`: (32), `α_{k+2}² ≥ 1/C` when `α_{k+2} > 0`;
* `energy_iter_zero_eq`: the telescoped identity (36).

Except for the domain statement at `k = 0`, these hold for one step `h ↦ step T̄ h` from an
arbitrary field `h` (`step_mem_domain`, `genField_step`, `energy_step`, ...), since `∇₀h` is
always centered. Along the way: `weakGrad`, `gen` agree with `T̄`, `A` on their domains and are
homogeneous; `centeredInv T̄ g` is the centered solution of `A u = g` for centered `g`
(`centeredInv_spec`, `gen_centeredInv`), unique (`centeredInv_eq_of_gen_eq`) and hence linear on
centered inputs; `‖∇(-L)⁻¹g‖² ≤ C ‖g‖²` (BKL (20)); `∇(center u) = ∇u`; Parseval
`Σ_j ‖∂_j u‖² = ‖∇u‖²`; and the algebra of `normSq`.

## The argument

The centered inverse returns the unique centered preimage from
`existsUnique_centered_adjointComp_eq` (Lemma 2.1); `∇₀h` has centered components by definition,
so one step lands in `D(A)` with centered components and `A (α (-L)⁻¹∇₀h) = α ∇₀h`. With
`w = (-L)⁻¹ ∇₀h`, `‖∇(α w)‖² = α² ‖∇w‖²`; if `‖∇w‖ = 0`, the Poincaré gap forces the centered
`w_J` to vanish and hence `∇₀h = A w = 0`, while otherwise `α² = ‖∇₀h‖² / ‖∇w‖²` by (31). This
gives (33) in both cases, and (46) follows from (30). (35) is `‖x‖² - ‖x - ∫x‖² = (∫x)²` per
component, (36) its telescoping, and (32) is `‖∇w_J‖² = ⟪∇₀h_J, w_J⟫ ≤ C ‖∇₀h_J‖²` (BKL (20),
`centered_adjointComp_bounds`) summed over `J`.

## What this is not

These are statements about `L²` classes in the operator domain, not about the source's class `𝒜`
of smooth functions of polynomial growth; Lemmas 3.2–3.4, Corollary 3.5 and Theorem 3.1 are not
proved here.
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave.PoissonIterate

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

  {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))

/-- The total gradient agrees with `T` on its domain. -/
theorem weakGrad_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ T.domain) :
    weakGrad T u = T ⟨u, hu⟩ :=
  dif_pos hu

/-- The total generator agrees with `T†T` on its domain. -/
theorem gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu

/-- The total gradient of `0` is `0`. -/
@[simp]
theorem weakGrad_zero : weakGrad T 0 = 0 := by
  rw [weakGrad_of_mem T T.domain.zero_mem]
  exact LinearPMap.map_zero T

/-- The total generator of `0` is `0`. -/
@[simp]
theorem gen_zero : gen T 0 = 0 := by
  rw [gen_of_mem T (adjointComp T).domain.zero_mem]
  exact LinearPMap.map_zero (adjointComp T)

/-- The total gradient is homogeneous, on and off the domain of `T`. -/
theorem weakGrad_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) :
    weakGrad T (c • u) = c • weakGrad T u := by
  by_cases hu : u ∈ T.domain
  · rw [weakGrad_of_mem T (T.domain.smul_mem c hu), weakGrad_of_mem T hu]
    exact LinearPMap.map_smul T c ⟨u, hu⟩
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hcu : c • u ∉ T.domain := fun h => hu (by
        simpa [smul_smul, hc] using T.domain.smul_mem c⁻¹ h)
      simp [weakGrad, hu, hcu]

/-- The total generator is homogeneous on the domain of `T†T`. -/
theorem gen_smul (c : ℝ) {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T (c • u) = c • gen T u := by
  rw [gen_of_mem T ((adjointComp T).domain.smul_mem c hu), gen_of_mem T hu]
  exact LinearPMap.map_smul (adjointComp T) c ⟨u, hu⟩

/-- The total generator is additive on the domain of `T†T`. -/
theorem gen_add {u v : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain)
    (hv : v ∈ (adjointComp T).domain) : gen T (u + v) = gen T u + gen T v := by
  rw [gen_of_mem T ((adjointComp T).domain.add_mem hu hv), gen_of_mem T hu, gen_of_mem T hv]
  exact LinearPMap.map_add (adjointComp T) ⟨u, hu⟩ ⟨v, hv⟩

/-- The centered inverse is always centered (it is `0` when no centered preimage exists). -/
theorem mean_centeredInv (g : Lp ℝ 2 (ν : Measure V)) : L2.mean ν (centeredInv T g) = 0 := by
  unfold centeredInv
  split_ifs with h
  · exact h.choose_spec.1
  · exact L2.mean_zero ν

/-- If a centered preimage of `g` under `T†T` exists, the centered inverse is one. -/
theorem centeredInv_spec_of_exists {g : Lp ℝ 2 (ν : Measure V)}
    (h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g) :
    ∃ hu : centeredInv T g ∈ (adjointComp T).domain, adjointComp T ⟨_, hu⟩ = g := by
  have hc : centeredInv T g = (h.choose : Lp ℝ 2 (ν : Measure V)) := by
    unfold centeredInv
    rw [dif_pos h]
  rw [hc]
  exact ⟨h.choose.2, h.choose_spec.2⟩

/-- `normSq` is quadratic: `‖c u‖² = c² ‖u‖²`. -/
theorem normSq_smul {k : ℕ} (c : ℝ) (u : Field ν k) : normSq (c • u) = c ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- `normSq u = 0` exactly when every component vanishes. -/
theorem normSq_eq_zero_iff {k : ℕ} (u : Field ν k) : normSq u = 0 ↔ ∀ I, u I = 0 := by
  unfold normSq
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  simp

variable [FiniteDimensional ℝ V]

/-- Parseval for the weak partial derivatives: `Σ_j ‖∂_j u‖² = ‖∇u‖²`. -/
theorem sum_norm_sq_partialDeriv (u : Lp ℝ 2 (ν : Measure V)) :
    ∑ j, ‖partialDeriv T j u‖ ^ 2 = ‖weakGrad T u‖ ^ 2 :=
  L2.sum_norm_sq_compLp_innerSL (stdOrthonormalBasis ℝ V) (weakGrad T u)

/-- The energy of a field is the sum of the squared gradient norms of its components. -/
theorem energy_eq_sum {k : ℕ} (u : Field ν k) :
    energy T u = ∑ I, ‖weakGrad T (u I)‖ ^ 2 := by
  unfold energy normSq gradField
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin (Module.finrank ℝ V)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  exact sum_norm_sq_partialDeriv T (u I)

/-- The energy is nonnegative. -/
theorem energy_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ energy T u :=
  normSq_nonneg _

/-- The energy is quadratic: `‖∇(c u)‖² = c² ‖∇u‖²`. -/
theorem energy_smul {k : ℕ} (c : ℝ) (u : Field ν k) : energy T (c • u) = c ^ 2 * energy T u := by
  rw [energy_eq_sum, energy_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, weakGrad_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

omit [FiniteDimensional ℝ V] in
/-- Centering the components removes the squared means: `‖u‖² - ‖u - ∫u‖² = Σ_J (∫u_J)²`. -/
theorem normSq_sub_normSq_center {k : ℕ} (u : Field ν k) :
    normSq u - normSq (fun J => L2.center ν (u J)) = ∑ J, L2.mean ν (u J) ^ 2 := by
  unfold normSq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  have h := L2.inner_center_center ν (u J) (u J)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [h]
  ring

/-- The energy drop of BKL (35) in the form `‖∇h‖² - ‖∇₀h‖² = |∫∇h|²`. -/
theorem energy_sub_normSq_grad0 {k : ℕ} (h : Field ν k) :
    energy T h - normSq (grad0 T h) = meanGradSq T h :=
  normSq_sub_normSq_center (gradField T h)

/-- The components of `∇₀h` are centered. -/
@[simp]
theorem mean_grad0 {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    L2.mean ν (grad0 T h J) = 0 :=
  L2.mean_center ν _

/-- The components of one step `α (-L)⁻¹ ∇₀ h` are centered. -/
theorem mean_step {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    L2.mean ν (step T h J) = 0 := by
  rw [step, Pi.smul_apply, L2.mean_smul, invField, mean_centeredInv, mul_zero]

/-- The iterates satisfy the recursion (30) definitionally. -/
theorem iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    iter T f (k + 1) = step T (iter T f k) :=
  rfl

/-- The iterate `h₁` is `f`. -/
theorem iter_zero (f : Lp ℝ 2 (ν : Measure V)) (I : Fin 0 → Fin (Module.finrank ℝ V)) :
    iter T f 0 I = f :=
  rfl

/-- **The iterates are centered.** Every component of `h_{k+1} = iter T f k` is centered, for
centered `f`. -/
theorem mean_iter {f : Lp ℝ 2 (ν : Measure V)}
    (hf : L2.mean ν f = 0) (k : ℕ) (I : Fin k → Fin (Module.finrank ℝ V)) :
    L2.mean ν (iter T f k I) = 0 := by
  cases k with
  | zero => exact hf
  | succ k => exact mean_step T _ I

end General

section HeatModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-- Centering does not change the total gradient of the heat model: constants lie in `D(T̄)`
and have zero gradient. -/
theorem weakGrad_center (u : Lp ℝ 2 (ν : Measure V)) :
    weakGrad T̄ (L2.center ν u) = weakGrad T̄ u := by
  by_cases hu : u ∈ (T̄).domain
  · rw [weakGrad_of_mem _ hu,
      weakGrad_of_mem _ (center_mem_closedWeightedOperator_domain m hν hi ⟨u, hu⟩)]
    exact closedWeightedOperator_center m hν hi ⟨u, hu⟩
  · have hconst : L2.const ν (L2.mean ν u) ∈ (T̄).domain := by
      have h1 := (T̄).domain.smul_mem (L2.mean ν u)
        (one_mem_domain_closedWeightedOperator (ν := ν) m (ContinuousLinearMap.id ℝ V) hν hi)
      simpa [← L2.const_smul] using h1
    have hc : L2.center ν u ∉ (T̄).domain := fun h => hu (by
      simpa [L2.center] using (T̄).domain.add_mem h hconst)
    simp [weakGrad, hu, hc]

include hC in
/-- The Poincaré gap for a centered `u ∈ D(T̄)`: `‖u‖² ≤ C ‖∇u‖²`. -/
theorem norm_sq_le_weakGrad {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (T̄).domain)
    (hmean : L2.mean ν u = 0) : ‖u‖ ^ 2 ≤ (C : ℝ) * ‖weakGrad T̄ u‖ ^ 2 := by
  have h := hν.closedWeightedOperator_id_gap_of_literature_le m hi C hC ⟨u, hu⟩
  have hcenter : L2.center ν u = u := by simp [L2.center, hmean]
  rw [weakGrad_of_mem _ hu]
  simpa [hcenter] using h

include hνU hU hC in
/-- **BKL Lemma 2.1 for the total centered inverse.** For centered `g`, `centeredInv T̄ g` lies in
`D(A)` and solves `A u = g`. -/
theorem centeredInv_spec {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    ∃ hu : centeredInv T̄ g ∈ (adjointComp T̄).domain, adjointComp T̄ ⟨_, hu⟩ = g :=
  centeredInv_spec_of_exists _
    (existsUnique_centered_adjointComp_eq m hν hi hνU hU hC g hg).exists

include hνU hU hC in
/-- For centered `g`, `(-L)⁻¹ g ∈ D(A)`. -/
theorem centeredInv_mem_domain {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    centeredInv T̄ g ∈ (adjointComp T̄).domain :=
  (centeredInv_spec m hν hi hνU hU hC hg).1

include hνU hU hC in
/-- For centered `g`, `-L (-L)⁻¹ g = g`. -/
theorem gen_centeredInv {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    gen T̄ (centeredInv T̄ g) = g := by
  obtain ⟨hu, hAu⟩ := centeredInv_spec m hν hi hνU hU hC hg
  rw [gen_of_mem _ hu, hAu]

include hνU hU hC in
/-- Uniqueness: a centered `u ∈ D(A)` with `A u = g` is the centered inverse of `g`. -/
theorem centeredInv_eq_of_gen_eq {g u : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0)
    (hu : u ∈ (adjointComp T̄).domain) (hmean : L2.mean ν u = 0) (hgen : gen T̄ u = g) :
    centeredInv T̄ g = u := by
  obtain ⟨hv, hAv⟩ := centeredInv_spec m hν hi hνU hU hC hg
  have huniq := (existsUnique_centered_adjointComp_eq m hν hi hνU hU hC g hg).unique
    (y₁ := ⟨_, hv⟩) (y₂ := ⟨u, hu⟩) ⟨mean_centeredInv (T̄) g, hAv⟩
    ⟨hmean, by rw [← gen_of_mem _ hu, hgen]⟩
  exact congrArg Subtype.val huniq

include hνU hU hC in
/-- The centered inverse is homogeneous on centered inputs. -/
theorem centeredInv_smul (c : ℝ) {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    centeredInv T̄ (c • g) = c • centeredInv T̄ g := by
  have hmem := centeredInv_mem_domain m hν hi hνU hU hC hg
  refine centeredInv_eq_of_gen_eq m hν hi hνU hU hC (by rw [L2.mean_smul, hg, mul_zero])
    ((adjointComp T̄).domain.smul_mem c hmem) (by rw [L2.mean_smul, mean_centeredInv, mul_zero])
    ?_
  rw [gen_smul _ c hmem, gen_centeredInv m hν hi hνU hU hC hg]

include hνU hU hC in
/-- The centered inverse is additive on centered inputs. -/
theorem centeredInv_add {g₁ g₂ : Lp ℝ 2 (ν : Measure V)} (hg₁ : L2.mean ν g₁ = 0)
    (hg₂ : L2.mean ν g₂ = 0) :
    centeredInv T̄ (g₁ + g₂) = centeredInv T̄ g₁ + centeredInv T̄ g₂ := by
  have h₁ := centeredInv_mem_domain m hν hi hνU hU hC hg₁
  have h₂ := centeredInv_mem_domain m hν hi hνU hU hC hg₂
  refine centeredInv_eq_of_gen_eq m hν hi hνU hU hC (by rw [L2.mean_add, hg₁, hg₂, add_zero])
    ((adjointComp T̄).domain.add_mem h₁ h₂)
    (by rw [L2.mean_add, mean_centeredInv, mean_centeredInv, add_zero]) ?_
  rw [gen_add _ h₁ h₂, gen_centeredInv m hν hi hνU hU hC hg₁,
    gen_centeredInv m hν hi hνU hU hC hg₂]

include hνU hU hC in
/-- **BKL (20)** for the total centered inverse: for centered `g`,
`‖∇(-L)⁻¹g‖² = ⟪g, (-L)⁻¹g⟫ ≤ C ‖g‖²`. -/
theorem norm_weakGrad_centeredInv_sq_le {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    ‖weakGrad T̄ (centeredInv T̄ g)‖ ^ 2 = ⟪g, centeredInv T̄ g⟫ ∧
      ⟪g, centeredInv T̄ g⟫ ≤ (C : ℝ) * ‖g‖ ^ 2 := by
  obtain ⟨hu, hAu⟩ := centeredInv_spec m hν hi hνU hU hC hg
  obtain ⟨-, h₂, h₃, -⟩ :=
    centered_adjointComp_bounds m hν hi hνU hU hC ⟨_, hu⟩ (mean_centeredInv (T̄) g)
  rw [hAu] at h₂ h₃
  rw [weakGrad_of_mem _ hu.2]
  exact ⟨h₂, h₃⟩

/-! ### One step `h ↦ α (-L)⁻¹ ∇₀ h` -/

include hνU hU hC in
/-- The components of one step lie in `D(A)`. -/
theorem step_mem_domain {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    step T̄ h J ∈ (adjointComp T̄).domain :=
  (adjointComp T̄).domain.smul_mem _
    (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J))

include hνU hU hC in
/-- **BKL (30)** for one step: `-L (α (-L)⁻¹ ∇₀h) = α ∇₀h`. -/
theorem genField_step {k : ℕ} (h : Field ν k) :
    genField T̄ (step T̄ h) = scale T̄ h • grad0 T̄ h := by
  funext J
  rw [genField, step, Pi.smul_apply, Pi.smul_apply, invField,
    gen_smul _ _ (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)),
    gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J)]

include hνU hU hC in
/-- If `∇(-L)⁻¹∇₀h = 0` then `∇₀h = 0`: the centered `w_J` with `∇w_J = 0` vanish by the Poincaré
gap, so `∇₀h_J = A w_J = 0`. -/
private theorem normSq_grad0_eq_zero_of_energy_eq_zero {k : ℕ} (h : Field ν k)
    (h0 : energy T̄ (invField T̄ (grad0 T̄ h)) = 0) : normSq (grad0 T̄ h) = 0 := by
  rw [normSq_eq_zero_iff]
  intro J
  have hJ : ‖weakGrad T̄ (invField T̄ (grad0 T̄ h) J)‖ ^ 2 = 0 := by
    rw [energy_eq_sum, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h0
    exact h0 J (Finset.mem_univ J)
  have hmem := centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)
  have hgap := norm_sq_le_weakGrad m hν hi hC hmem.2 (mean_centeredInv (T̄) _)
  rw [invField] at hJ
  rw [hJ, mul_zero] at hgap
  have hw : centeredInv T̄ (grad0 T̄ h J) = 0 := by
    have hn := norm_nonneg (centeredInv T̄ (grad0 T̄ h J))
    have : ‖centeredInv T̄ (grad0 T̄ h J)‖ = 0 := by nlinarith
    exact norm_eq_zero.mp this
  rw [← gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J), hw, gen_zero]

include hνU hU hC in
/-- **BKL (33)** for one step: `‖∇(α (-L)⁻¹∇₀h)‖² = ‖∇₀h‖²`, also when `∇₀h = 0`. -/
theorem energy_step {k : ℕ} (h : Field ν k) :
    energy T̄ (step T̄ h) = normSq (grad0 T̄ h) := by
  rw [step, energy_smul]
  by_cases h0 : energy T̄ (invField T̄ (grad0 T̄ h)) = 0
  · rw [h0, mul_zero, normSq_grad0_eq_zero_of_energy_eq_zero m hν hi hνU hU hC h h0]
  · have hs : scale T̄ h = Real.sqrt (normSq (grad0 T̄ h) /
        energy T̄ (invField T̄ (grad0 T̄ h))) := if_neg h0
    rw [hs, Real.sq_sqrt (div_nonneg (normSq_nonneg _) (energy_nonneg _ _)),
      div_mul_cancel₀ _ h0]

include hνU hU hC in
/-- **BKL (46)** for one step: `‖L h'‖² = α² ‖∇h'‖²` for `h' = α (-L)⁻¹∇₀h`. -/
theorem normSq_genField_step {k : ℕ} (h : Field ν k) :
    normSq (genField T̄ (step T̄ h)) = scale T̄ h ^ 2 * energy T̄ (step T̄ h) := by
  rw [genField_step m hν hi hνU hU hC, normSq_smul, energy_step m hν hi hνU hU hC]

include hνU hU hC in
/-- **BKL (35)** for one step: `‖∇h‖² - ‖∇h'‖² = |∫∇h|²`. -/
theorem energy_sub_energy_step {k : ℕ} (h : Field ν k) :
    energy T̄ h - energy T̄ (step T̄ h) = meanGradSq T̄ h := by
  rw [energy_step m hν hi hνU hU hC, energy_sub_normSq_grad0]

include hνU hU hC in
/-- **BKL (32)** for one step: if `α > 0` then `α² ≥ 1/C`. -/
theorem inv_le_scale_sq_step (hCpos : 0 < C) {k : ℕ} (h : Field ν k) (hs : 0 < scale T̄ h) :
    (C : ℝ)⁻¹ ≤ scale T̄ h ^ 2 := by
  set E := energy T̄ (invField T̄ (grad0 T̄ h)) with hE
  have h0 : E ≠ 0 := by
    intro h0
    have : scale T̄ h = 0 := if_pos h0
    exact hs.ne' this
  have hEpos : 0 < E := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
  have hsq : scale T̄ h ^ 2 = normSq (grad0 T̄ h) / E := by
    have : scale T̄ h = Real.sqrt (normSq (grad0 T̄ h) / E) := if_neg h0
    rw [this, Real.sq_sqrt (div_nonneg (normSq_nonneg _) hEpos.le)]
  have hbound : E ≤ (C : ℝ) * normSq (grad0 T̄ h) := by
    rw [hE, energy_eq_sum, normSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun J _ => ?_
    obtain ⟨h₁, h₂⟩ := norm_weakGrad_centeredInv_sq_le m hν hi hνU hU hC (mean_grad0 (T̄) h J)
    exact h₁.trans_le h₂
  have hC' : (0 : ℝ) < C := hCpos
  rw [hsq, inv_le_iff_one_le_mul₀ hC', div_mul_eq_mul_div, le_div_iff₀ hEpos, one_mul,
    mul_comm]
  exact hbound

/-! ### The iterates -/

include hνU hU hC in
/-- **The iterates lie in `D(A)`.** Every component of `h_{k+1} = iter T̄ f k` lies in `D(A)`, for
`f ∈ D(A)`. -/
theorem iter_mem_adjointComp_domain {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) (I : Fin k → Fin (Module.finrank ℝ V)) :
    iter T̄ f k I ∈ (adjointComp T̄).domain := by
  cases k with
  | zero => exact hf
  | succ k => exact step_mem_domain m hν hi hνU hU hC _ I

include hνU hU hC in
/-- **BKL Section 3, iterates in `D(A)`.** For a centered `f ∈ D(A)`, every component of every
iterate lies in `D(A)` and is centered. -/
theorem iter_mem_domain_and_mean_eq_zero {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∈ (adjointComp T̄).domain) (hfm : L2.mean ν f = 0) (k : ℕ)
    (I : Fin k → Fin (Module.finrank ℝ V)) :
    iter T̄ f k I ∈ (adjointComp T̄).domain ∧ L2.mean ν (iter T̄ f k I) = 0 :=
  ⟨iter_mem_adjointComp_domain m hν hi hνU hU hC hf k I, mean_iter _ hfm k I⟩

include hνU hU hC in
/-- **BKL (30).** `-L h_{k+2} = α_{k+2} ∇₀ h_{k+1}`. -/
theorem genField_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    genField T̄ (iter T̄ f (k + 1)) = scale T̄ (iter T̄ f k) • grad0 T̄ (iter T̄ f k) :=
  genField_step m hν hi hνU hU hC _

include hνU hU hC in
/-- **BKL (33).** `‖∇h_{k+2}‖² = ‖∇₀h_{k+1}‖²`. -/
theorem energy_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    energy T̄ (iter T̄ f (k + 1)) = normSq (grad0 T̄ (iter T̄ f k)) :=
  energy_step m hν hi hνU hU hC _

include hνU hU hC in
/-- **BKL (46).** `‖L h_{k+2}‖² = α_{k+2}² ‖∇h_{k+2}‖²`. -/
theorem normSq_genField_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    normSq (genField T̄ (iter T̄ f (k + 1))) =
      scale T̄ (iter T̄ f k) ^ 2 * energy T̄ (iter T̄ f (k + 1)) :=
  normSq_genField_step m hν hi hνU hU hC _

include hνU hU hC in
/-- **BKL (35).** `v_{k+1} - v_{k+2} = p_{k+1}`. -/
theorem energy_sub_energy_iter_succ (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ) :
    energy T̄ (iter T̄ f k) - energy T̄ (iter T̄ f (k + 1)) = meanGradSq T̄ (iter T̄ f k) :=
  energy_sub_energy_step m hν hi hνU hU hC _

include hνU hU hC in
/-- **BKL (32).** If `α_{k+2} > 0` then `α_{k+2}² ≥ 1/C`. -/
theorem inv_le_scale_sq (hCpos : 0 < C) (f : Lp ℝ 2 (ν : Measure V)) (k : ℕ)
    (hs : 0 < scale T̄ (iter T̄ f k)) : (C : ℝ)⁻¹ ≤ scale T̄ (iter T̄ f k) ^ 2 :=
  inv_le_scale_sq_step m hν hi hνU hU hC hCpos _ hs

include hνU hU hC in
/-- **BKL (36).** `v₁ = v_{N+1} + Σ_{k<N} p_{k+1}`. -/
theorem energy_iter_zero_eq (f : Lp ℝ 2 (ν : Measure V)) (N : ℕ) :
    energy T̄ (iter T̄ f 0) =
      energy T̄ (iter T̄ f N) + ∑ k ∈ Finset.range N, meanGradSq T̄ (iter T̄ f k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ,
      ← energy_sub_energy_iter_succ m hν hi hνU hU hC f N]
    ring

end HeatModel

end FunctionalInequalities.KLS.LogConcave.PoissonIterate
