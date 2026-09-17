import FunctionalInequalities.Analysis.WhitneyBump
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The smooth partition carried by a Whitney ball cover

The denominator is the locally finite sum of the scaled bumps. It is at least one on the
complement, since the radius-five balls cover it. Dividing by it gives smooth nonnegative
weights with sum one, supported in the radius-eight balls. Local finiteness is asserted on
the complement only, where derivatives will be taken.
-/

noncomputable section

open Set Metric Function Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis.WhitneyCover

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The index restriction is in the center variable, not in the evaluation variable. -/
def bumpFamily (S C : Set V) (z y : V) : ℝ := by
  classical
  exact if z ∈ C then bump z (radius S z) y else 0

def bumpSum (S C : Set V) (y : V) : ℝ := ∑ᶠ z, bumpFamily S C z y

/-- The normalized weight. Its smoothness is claimed only off `S`. -/
def weight (S C : Set V) (z y : V) : ℝ := bumpFamily S C z y / bumpSum S C y

theorem contDiff_bumpFamily (S C : Set V) (z : V) : ContDiff ℝ ∞ (bumpFamily S C z) := by
  classical
  unfold bumpFamily
  split_ifs
  · exact contDiff_bump z (radius S z)
  · exact contDiff_const

theorem bumpFamily_nonneg (S C : Set V) (z y : V) : 0 ≤ bumpFamily S C z y := by
  classical
  by_cases hz : z ∈ C <;> simp [bumpFamily, hz, bump_nonneg]

theorem bumpFamily_le_one (S C : Set V) (z y : V) : bumpFamily S C z y ≤ 1 := by
  classical
  by_cases hz : z ∈ C <;> simp [bumpFamily, hz, bump_le_one]

theorem bumpSum_eq_sum {S C : Set V} {t : Finset V} {y : V}
    (h : ∀ z ∉ t, bumpFamily S C z y = 0) :
    bumpSum S C y = ∑ z ∈ t, bumpFamily S C z y := by
  apply finsum_eq_finsetSum_of_support_subset
  intro z hz
  by_contra hzt
  exact hz (h z hzt)

/-- A deliberately non-sharp normalization estimate when the numerator lies in `[0,1]`
and the denominator is at least one. -/
theorem norm_fderiv_div_le {b B : V → ℝ} {y : V}
    (hb : DifferentiableAt ℝ b y) (hB : DifferentiableAt ℝ B y)
    (hb0 : 0 ≤ b y) (hb1 : b y ≤ 1) (hB1 : 1 ≤ B y) :
    ‖fderiv ℝ (fun x => b x / B x) y‖ ≤ ‖fderiv ℝ b y‖ + ‖fderiv ℝ B y‖ := by
  have hB0 : 0 < B y := zero_lt_one.trans_le hB1
  have hi := (hasDerivAt_inv hB0.ne').comp_hasFDerivAt y hB.hasFDerivAt
  have hiBound : ‖(-(B y ^ 2)⁻¹) • fderiv ℝ B y‖ ≤ ‖fderiv ℝ B y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (inv_nonneg.2 (sq_nonneg _))]
    have hsq : 1 ≤ B y ^ 2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (inv_le_one_of_one_le₀ hsq) (norm_nonneg (fderiv ℝ B y))
  have hprod := hb.hasFDerivAt.fun_mul hi
  simp only [Function.comp_def] at hprod
  simp only [div_eq_mul_inv]
  rw [hprod.fderiv]
  have hnorm := norm_add_le (b y • (-(B y ^ 2)⁻¹ • fderiv ℝ B y))
    ((B y)⁻¹ • fderiv ℝ b y)
  have h1 : ‖b y • (-(B y ^ 2)⁻¹ • fderiv ℝ B y)‖ ≤ ‖fderiv ℝ B y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0]
    simpa only [one_mul] using mul_le_mul hb1 hiBound (norm_nonneg _) zero_le_one
  have h2 : ‖(B y)⁻¹ • fderiv ℝ b y‖ ≤ ‖fderiv ℝ b y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hB0)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (inv_le_one_of_one_le₀ hB1) (norm_nonneg (fderiv ℝ b y))
  exact hnorm.trans (by linarith)

section Cover

variable [FiniteDimensional ℝ V] {S C : Set V}

/-- A single finite set of centers controls every summand on an entire neighborhood. This
permits differentiating finite sums; pointwise finiteness alone would not justify that step. -/
theorem exists_local_finset (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z))) {y : V} (hy : y ∉ S) :
    ∃ t : Finset V, (∀ z ∈ t, z ∈ C) ∧ t.card ≤ 81 ^ Module.finrank ℝ V ∧
      (∀ z ∈ t, radius S y / 2 ≤ radius S z ∧ radius S z ≤ 2 * radius S y ∧
        dist z y ≤ 20 * radius S y) ∧
      ∀ w ∈ ball y (radius S y), ∀ z ∉ t, bumpFamily S C z w = 0 := by
  classical
  have hpos : ∀ z ∈ C, 0 < radius S z := fun z hz => radius_pos S hS hne (hC hz)
  have hfin := finite_inter hpos hdisj (radius_pos S hS hne hy)
  refine ⟨hfin.toFinset, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hfin.mem_toFinset.1 hz).1
  · exact card_inter_le hpos hdisj (radius_pos S hS hne hy) _
      (fun z hz => hfin.mem_toFinset.1 hz)
  · intro z hz
    exact radius_comparable_of_inter S (hfin.mem_toFinset.1 hz).2
  · intro w hw z hz
    by_cases hzC : z ∈ C
    · simp only [bumpFamily, if_pos hzC]
      apply bump_eq_zero (hpos z hzC)
      by_contra h
      apply hz
      exact hfin.mem_toFinset.2 ⟨hzC, ⟨w, le_of_lt (not_le.1 h), hw⟩⟩
    · simp [bumpFamily, hzC]

theorem contDiffAt_bumpSum (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z))) {y : V} (hy : y ∉ S) :
    ContDiffAt ℝ ∞ (bumpSum S C) y := by
  obtain ⟨t, -, -, -, ht⟩ := exists_local_finset hS hne hC hdisj hy
  apply (ContDiff.sum (fun z (_ : z ∈ t) => contDiff_bumpFamily S C z)).contDiffAt.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds y (radius_pos S hS hne hy)] with w hw
  exact bumpSum_eq_sum (ht w hw)

theorem one_le_bumpSum (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    (hcover : Sᶜ = ⋃ z ∈ C, ball z (5 * radius S z)) {y : V} (hy : y ∉ S) :
    1 ≤ bumpSum S C y := by
  classical
  obtain ⟨t, -, -, -, ht⟩ := exists_local_finset hS hne hC hdisj hy
  have hym : y ∈ ball y (radius S y) := mem_ball_self (radius_pos S hS hne hy)
  have hz := hy
  change y ∈ Sᶜ at hz
  rw [hcover] at hz
  obtain ⟨z, hzC, hyz⟩ := mem_iUnion₂.1 hz
  have hb : bumpFamily S C z y = 1 := by
    simp only [bumpFamily, if_pos hzC]
    exact bump_eq_one (radius_pos S hS hne (hC hzC)) (le_of_lt hyz)
  have hzt : z ∈ t := by
    by_contra h
    have := ht y hym z h
    linarith
  rw [bumpSum_eq_sum (ht y hym), ← hb]
  exact Finset.single_le_sum (fun i _ => bumpFamily_nonneg S C i y) hzt

theorem contDiffOn_weight (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    (hcover : Sᶜ = ⋃ z ∈ C, ball z (5 * radius S z)) (z : V) :
    ContDiffOn ℝ ∞ (weight S C z) Sᶜ := by
  intro y hy
  exact ((contDiff_bumpFamily S C z).contDiffAt.div
    (contDiffAt_bumpSum hS hne hC hdisj hy)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_bumpSum hS hne hC hdisj hcover hy)))).contDiffWithinAt

theorem weight_nonneg (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    (hcover : Sᶜ = ⋃ z ∈ C, ball z (5 * radius S z)) (z : V) {y : V} (hy : y ∉ S) :
    0 ≤ weight S C z y :=
  div_nonneg (bumpFamily_nonneg S C z y)
    (zero_le_one.trans (one_le_bumpSum hS hne hC hdisj hcover hy))

theorem sum_weight_eq_one (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    (hcover : Sᶜ = ⋃ z ∈ C, ball z (5 * radius S z)) {y : V} (hy : y ∉ S) :
    ∑ᶠ z, weight S C z y = 1 := by
  classical
  obtain ⟨t, -, -, -, ht⟩ := exists_local_finset hS hne hC hdisj hy
  have hym : y ∈ ball y (radius S y) := mem_ball_self (radius_pos S hS hne hy)
  have hsupport : support (fun z => weight S C z y) ⊆ (t : Set V) := by
    intro z hz
    by_contra hzt
    exact hz (by simp [weight, ht y hym z hzt])
  rw [finsum_eq_finsetSum_of_support_subset _ hsupport]
  simp only [weight, ← Finset.sum_div, ← bumpSum_eq_sum (ht y hym)]
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_bumpSum hS hne hC hdisj hcover hy)))

omit [FiniteDimensional ℝ V] in
theorem tsupport_weight_subset (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    {z : V} (hz : z ∈ C) : tsupport (weight S C z) ⊆ closedBall z (8 * radius S z) := by
  classical
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  by_contra hyb
  have hb := bump_eq_zero (radius_pos S hS hne (hC hz)) (le_of_lt (not_le.1 hyb))
  exact hy (by simp [weight, bumpFamily, hz, hb])

/-- Every normalized weight has the same scale-invariant derivative bound, uniformly in
the center and the evaluation point. Local finiteness is used before differentiating the sum. -/
theorem exists_weight_derivative_bound (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    (hcover : Sᶜ = ⋃ z ∈ C, ball z (5 * radius S z)) :
    ∃ K : ℝ, 0 < K ∧ ∀ y ∉ S, ∀ z : V,
      ‖fderiv ℝ (weight S C z) y‖ ≤ K / radius S y := by
  classical
  obtain ⟨M, hM, hMb⟩ := exists_derivative_bound (V := V)
  let N : ℝ := (81 ^ Module.finrank ℝ V : ℕ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨2 * M * (N + 1), by positivity, fun y hy z => ?_⟩
  have hry := radius_pos S hS hne hy
  obtain ⟨t, htC, htN, htrad, ht⟩ := exists_local_finset hS hne hC hdisj hy
  have htN' : (t.card : ℝ) ≤ N := by dsimp [N]; exact_mod_cast htN
  have hdb : ∀ i ∈ t, ‖fderiv ℝ (bumpFamily S C i) y‖ ≤ 2 * M / radius S y := by
    intro i hi
    have hri := radius_pos S hS hne (hC (htC i hi))
    have heq : bumpFamily S C i = bump i (radius S i) := by
      funext w; simp [bumpFamily, htC i hi]
    rw [heq]
    apply (hMb i _ hri y).trans
    rw [div_le_div_iff₀ hri hry]
    nlinarith [(htrad i hi).1]
  have hsum := HasFDerivAt.fun_sum (u := t)
    (fun i (_ : i ∈ t) => ((contDiff_bumpFamily S C i).differentiable (by simp) y).hasFDerivAt)
  have hlocal : bumpSum S C =ᶠ[𝓝 y] fun w => ∑ i ∈ t, bumpFamily S C i w := by
    filter_upwards [ball_mem_nhds y hry] with w hw
    exact bumpSum_eq_sum (ht w hw)
  have hD := hsum.congr_of_eventuallyEq hlocal
  have hDB : ‖fderiv ℝ (bumpSum S C) y‖ ≤ N * (2 * M / radius S y) := by
    rw [hD.fderiv]
    calc
      _ ≤ ∑ i ∈ t, ‖fderiv ℝ (bumpFamily S C i) y‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ t, 2 * M / radius S y := Finset.sum_le_sum hdb
      _ = (t.card : ℝ) * (2 * M / radius S y) := by simp
      _ ≤ N * (2 * M / radius S y) := mul_le_mul_of_nonneg_right htN' (by positivity)
  by_cases hzt : z ∈ t
  · have h := norm_fderiv_div_le
      ((contDiff_bumpFamily S C z).differentiable (by simp) y) hD.differentiableAt
      (bumpFamily_nonneg S C z y) (bumpFamily_le_one S C z y)
      (one_le_bumpSum hS hne hC hdisj hcover hy)
    change ‖fderiv ℝ (fun w => bumpFamily S C z w / bumpSum S C w) y‖ ≤ _
    apply h.trans
    have heq : 2 * M / radius S y + N * (2 * M / radius S y) =
        2 * M * (N + 1) / radius S y := by ring
    rw [← heq]
    exact add_le_add (hdb z hzt) hDB
  · have heq : weight S C z =ᶠ[𝓝 y] (fun _ => 0) := by
      filter_upwards [ball_mem_nhds y hry] with w hw
      simp [weight, ht w hw z hzt]
    rw [((hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq heq).fderiv, norm_zero]
    positivity

end Cover

end FunctionalInequalities.Analysis.WhitneyCover
