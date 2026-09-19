import FunctionalInequalities.Analysis.Sard.TaylorRemainder
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Planar quadratic covering and null images

A bounded planar set on which a function oscillates at most quadratically in the mutual
distance has a Lebesgue null image. Neither the set nor its image is assumed measurable,
and the function is unconstrained away from the set. The grid count `O(r⁻²)` and the
image length `O(ε r²)` only balance in dimension two, so the argument is planar by nature.

Feeding the uniform quadratic remainder into this covering makes the set of second-order
flat points of a `C²` function on a planar compact set have null image. This is one layer
of Sard's theorem only: nonflat points, higher dimensions and the general statement are
untouched here.
-/

noncomputable section

open Set MeasureTheory

namespace FunctionalInequalities.Analysis

/-- Two reals in a common half-open grid cell of width `r` are less than `r` apart. -/
private lemma abs_sub_lt_of_floor_div_eq {a b r : ℝ} (hr : 0 < r)
    (h : ⌊a / r⌋ = ⌊b / r⌋) : |a - b| < r := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rwa [← sub_div, abs_div, abs_of_pos hr, div_lt_one hr] at h1

/-- A bounded subset of the line on which `f` has a quadratic modulus of continuity with a
**fixed** constant has Lebesgue null image. No measurability of the set or of its image is
required, and `f` is arbitrary off the set. In dimension one the cell count `O(r⁻¹)` already
beats the image length `O(r²)`, so no `ε`-refinement of the constant is needed; the planar
statement below does need one. -/
theorem volume_image_eq_zero_of_quadratic_bound {A : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hA : Bornology.IsBounded A)
    (hC : ∀ x ∈ A, ∀ y ∈ A, |f y - f x| ≤ C * |y - x| ^ 2) :
    (volume : Measure ℝ) (f '' A) = 0 := by
  classical
  obtain ⟨R, hR, hAR⟩ := hA.exists_pos_norm_le
  set D : ℝ := max C 0 with hDdef
  have hD : 0 ≤ D := le_max_right _ _
  have hCD : ∀ x ∈ A, ∀ y ∈ A, |f y - f x| ≤ D * |y - x| ^ 2 := fun x hx y hy =>
    (hC x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have key : ∀ r : ℝ, 0 < r → r ≤ 1 →
      (volume : Measure ℝ) (f '' A) ≤ ENNReal.ofReal (2 * D * (2 * R + 3) * r) := by
    intro r hr _
    set M : ℤ := ⌈R / r⌉ with hMdef
    have hM0 : (0 : ℤ) ≤ M := Int.ceil_nonneg (div_pos hR hr).le
    set S : Finset ℤ := Finset.Icc (-M) M with hSdef
    have hchoice : ∀ c : ℤ, ∃ z : ℝ, (∃ x, x ∈ A ∧ ⌊x / r⌋ = c) → z ∈ A ∧ ⌊z / r⌋ = c := by
      intro c
      by_cases h : ∃ x, x ∈ A ∧ ⌊x / r⌋ = c
      · obtain ⟨x, hx⟩ := h
        exact ⟨x, fun _ => hx⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose g hg using hchoice
    set I : ℤ → Set ℝ := fun c => Icc (f (g c) - D * r ^ 2) (f (g c) + D * r ^ 2) with hIdef
    have hIvol : ∀ c, (volume : Measure ℝ) (I c) ≤ ENNReal.ofReal (2 * D * r ^ 2) := by
      intro c
      rw [hIdef, Real.volume_Icc]
      exact le_of_eq (by ring_nf)
    have hcover : f '' A ⊆ ⋃ c ∈ S, I c := by
      rintro _ ⟨y, hy, rfl⟩
      have habs : |y| ≤ R := by simpa [Real.norm_eq_abs] using hAR y hy
      have hmemS : ⌊y / r⌋ ∈ S := by
        have hub : ⌊y / r⌋ ≤ M :=
          (Int.floor_le_floor (div_le_div_of_nonneg_right (abs_le.mp habs).2 hr.le)).trans
            (Int.floor_le_ceil (R / r))
        have hlb : -M ≤ ⌊y / r⌋ := by
          have := Int.floor_le_floor
            (div_le_div_of_nonneg_right (abs_le.mp habs).1 hr.le)
          rwa [neg_div, Int.floor_neg] at this
        exact Finset.mem_Icc.mpr ⟨hlb, hub⟩
      obtain ⟨hgA, hgq⟩ := hg ⌊y / r⌋ ⟨y, hy, rfl⟩
      have hclose : |y - g ⌊y / r⌋| < r := abs_sub_lt_of_floor_div_eq hr hgq.symm
      have hsq : |y - g ⌊y / r⌋| ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hclose.le 2
      have hle : |f y - f (g ⌊y / r⌋)| ≤ D * r ^ 2 :=
        (hCD (g ⌊y / r⌋) hgA y hy).trans (mul_le_mul_of_nonneg_left hsq hD)
      obtain ⟨hl, hu⟩ := abs_le.mp hle
      exact mem_biUnion hmemS ⟨by linarith, by linarith⟩
    have hcard : (S.card : ℝ) = 2 * (M : ℝ) + 1 := by
      have hN : ((Finset.Icc (-M) M).card : ℤ) = 2 * M + 1 := by
        rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
        omega
      rw [hSdef]
      exact_mod_cast hN
    have hMr : (M : ℝ) * r < R + r := by
      have h1 : (M : ℝ) < R / r + 1 := Int.ceil_lt_add_one _
      have := mul_lt_mul_of_pos_right h1 hr
      rwa [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hr)] at this
    have hMR : (2 * (M : ℝ) + 1) * r ≤ 2 * R + 3 := by
      have hexp : (2 * (M : ℝ) + 1) * r = 2 * ((M : ℝ) * r) + r := by ring
      rw [hexp]; linarith
    have hreal : (S.card : ℝ) * (2 * D * r ^ 2) ≤ 2 * D * (2 * R + 3) * r := by
      calc (S.card : ℝ) * (2 * D * r ^ 2)
          = (2 * D * r) * ((2 * (M : ℝ) + 1) * r) := by rw [hcard]; ring
        _ ≤ (2 * D * r) * (2 * R + 3) :=
              mul_le_mul_of_nonneg_left hMR (by positivity)
        _ = 2 * D * (2 * R + 3) * r := by ring
    calc (volume : Measure ℝ) (f '' A)
        ≤ (volume : Measure ℝ) (⋃ c ∈ S, I c) := measure_mono hcover
      _ ≤ ∑ c ∈ S, (volume : Measure ℝ) (I c) := measure_biUnion_finset_le _ _
      _ ≤ S.card • ENNReal.ofReal (2 * D * r ^ 2) :=
            Finset.sum_le_card_nsmul _ _ _ (fun c _ => hIvol c)
      _ = ENNReal.ofReal ((S.card : ℝ) * (2 * D * r ^ 2)) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast S.card,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
      _ ≤ ENNReal.ofReal (2 * D * (2 * R + 3) * r) := ENNReal.ofReal_le_ofReal hreal
  refine le_antisymm ?_ zero_le
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hE : (0 : ℝ) < 2 * D * (2 * R + 3) + 1 := by positivity
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  set r : ℝ := min 1 ((η : ℝ) / (2 * D * (2 * R + 3) + 1)) with hrdef
  have hr : 0 < r := lt_min one_pos (div_pos hηR hE)
  have hbound : 2 * D * (2 * R + 3) * r ≤ (η : ℝ) := by
    have hle : r ≤ (η : ℝ) / (2 * D * (2 * R + 3) + 1) := min_le_right _ _
    have hnn : (0 : ℝ) ≤ 2 * D * (2 * R + 3) := by positivity
    calc 2 * D * (2 * R + 3) * r ≤ (2 * D * (2 * R + 3) + 1) * r := by nlinarith
      _ ≤ (2 * D * (2 * R + 3) + 1) * ((η : ℝ) / (2 * D * (2 * R + 3) + 1)) :=
            mul_le_mul_of_nonneg_left hle hE.le
      _ = (η : ℝ) := by field_simp
  refine (key r hr (min_le_left _ _)).trans ?_
  rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hbound

/-- A bounded subset of `Fin n → ℝ` on which `f` has a uniform `o(‖y-x‖ⁿ)` modulus has
Lebesgue null image. No measurability of the set or of its image is required, and `f` is
arbitrary off the set. The exponent must match the dimension: the grid has `O(r⁻ⁿ)` cells and
each image interval has length `O(ε rⁿ)`, and only then is the product free of `r`. -/
theorem volume_image_eq_zero_of_oscillation_pow {n : ℕ} {A : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hA : Bornology.IsBounded A)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ n) :
    (volume : Measure ℝ) (f '' A) = 0 := by
  classical
  obtain ⟨R, hR, hAR⟩ := hA.exists_pos_norm_le
  have key : ∀ ε : ℝ, 0 < ε →
      (volume : Measure ℝ) (f '' A) ≤ ENNReal.ofReal (2 * (2 * R + 3) ^ n * ε) := by
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hosc ε hε
    set r : ℝ := min δ 1 with hrdef
    have hr : 0 < r := lt_min hδ one_pos
    have hrδ : r ≤ δ := min_le_left _ _
    have hr1 : r ≤ 1 := min_le_right _ _
    set q : (Fin n → ℝ) → (Fin n → ℤ) := fun x i => ⌊x i / r⌋ with hqdef
    set M : ℤ := ⌈R / r⌉ with hMdef
    have hM0 : (0 : ℤ) ≤ M := Int.ceil_nonneg (div_pos hR hr).le
    set S : Finset (Fin n → ℤ) := Fintype.piFinset fun _ : Fin n => Finset.Icc (-M) M with hSdef
    have hchoice : ∀ c : Fin n → ℤ, ∃ z : Fin n → ℝ,
        (∃ x, x ∈ A ∧ q x = c) → z ∈ A ∧ q z = c := by
      intro c
      by_cases h : ∃ x, x ∈ A ∧ q x = c
      · obtain ⟨x, hx⟩ := h
        exact ⟨x, fun _ => hx⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose g hg using hchoice
    set I : (Fin n → ℤ) → Set ℝ :=
      fun c => Icc (f (g c) - ε * r ^ n) (f (g c) + ε * r ^ n) with hIdef
    have hIvol : ∀ c, (volume : Measure ℝ) (I c) ≤ ENNReal.ofReal (2 * ε * r ^ n) := by
      intro c
      rw [hIdef, Real.volume_Icc]
      exact le_of_eq (by ring_nf)
    have hcover : f '' A ⊆ ⋃ c ∈ S, I c := by
      rintro _ ⟨y, hy, rfl⟩
      have hnorm : ‖y‖ ≤ R := hAR y hy
      have hcoord : ∀ i : Fin n, |y i| ≤ R :=
        fun i => (Real.norm_eq_abs (y i) ▸ norm_le_pi_norm y i).trans hnorm
      have hmemS : q y ∈ S := by
        rw [hSdef, Fintype.mem_piFinset]
        intro i
        have hub : ⌊y i / r⌋ ≤ M :=
          (Int.floor_le_floor (div_le_div_of_nonneg_right (abs_le.mp (hcoord i)).2 hr.le)).trans
            (Int.floor_le_ceil (R / r))
        have hlb : -M ≤ ⌊y i / r⌋ := by
          have := Int.floor_le_floor
            (div_le_div_of_nonneg_right (abs_le.mp (hcoord i)).1 hr.le)
          rwa [neg_div, Int.floor_neg] at this
        exact Finset.mem_Icc.mpr ⟨hlb, hub⟩
      obtain ⟨hgA, hgq⟩ := hg (q y) ⟨y, hy, rfl⟩
      have hclose : ‖y - g (q y)‖ < r := by
        rw [pi_norm_lt_iff hr]
        intro i
        have hi : ⌊y i / r⌋ = ⌊g (q y) i / r⌋ := (congrFun hgq i).symm
        simpa [Real.norm_eq_abs] using abs_sub_lt_of_floor_div_eq hr hi
      have hosc' := hd (g (q y)) hgA y hy (hclose.trans_le hrδ)
      have hsq : ‖y - g (q y)‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) hclose.le n
      have hle : |f y - f (g (q y))| ≤ ε * r ^ n :=
        hosc'.trans (mul_le_mul_of_nonneg_left hsq hε.le)
      obtain ⟨hl, hu⟩ := abs_le.mp hle
      exact mem_biUnion hmemS ⟨by linarith, by linarith⟩
    have hcard : (S.card : ℝ) = (2 * (M : ℝ) + 1) ^ n := by
      have hNR : ((Finset.Icc (-M) M).card : ℝ) = 2 * (M : ℝ) + 1 := by
        have hN : ((Finset.Icc (-M) M).card : ℤ) = 2 * M + 1 := by
          rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
          omega
        exact_mod_cast hN
      rw [hSdef, Fintype.card_piFinset, Nat.cast_prod, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hNR]
    have hMr : (M : ℝ) * r < R + r := by
      have h1 : (M : ℝ) < R / r + 1 := Int.ceil_lt_add_one _
      have := mul_lt_mul_of_pos_right h1 hr
      rwa [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hr)] at this
    have hMR : (2 * (M : ℝ) + 1) * r ≤ 2 * R + 3 := by
      have hexp : (2 * (M : ℝ) + 1) * r = 2 * ((M : ℝ) * r) + r := by ring
      rw [hexp]; linarith
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM0
    have hnn : 0 ≤ (2 * (M : ℝ) + 1) * r := mul_nonneg (by linarith) hr.le
    have hreal : (S.card : ℝ) * (2 * ε * r ^ n) ≤ 2 * (2 * R + 3) ^ n * ε := by
      have hsq : ((2 * (M : ℝ) + 1) * r) ^ n ≤ (2 * R + 3) ^ n :=
        pow_le_pow_left₀ hnn hMR n
      calc (S.card : ℝ) * (2 * ε * r ^ n)
          = 2 * ε * ((2 * (M : ℝ) + 1) * r) ^ n := by rw [hcard, mul_pow]; ring
        _ ≤ 2 * ε * (2 * R + 3) ^ n := mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 2 * (2 * R + 3) ^ n * ε := by ring
    calc (volume : Measure ℝ) (f '' A)
        ≤ (volume : Measure ℝ) (⋃ c ∈ S, I c) := measure_mono hcover
      _ ≤ ∑ c ∈ S, (volume : Measure ℝ) (I c) := measure_biUnion_finset_le _ _
      _ ≤ S.card • ENNReal.ofReal (2 * ε * r ^ n) :=
            Finset.sum_le_card_nsmul _ _ _ (fun c _ => hIvol c)
      _ = ENNReal.ofReal ((S.card : ℝ) * (2 * ε * r ^ n)) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast S.card,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
      _ ≤ ENNReal.ofReal (2 * (2 * R + 3) ^ n * ε) := ENNReal.ofReal_le_ofReal hreal
  refine le_antisymm ?_ zero_le
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  have hC : (0 : ℝ) < 2 * (2 * R + 3) ^ n := by positivity
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have hkey := key ((η : ℝ) / (2 * (2 * R + 3) ^ n)) (div_pos hηR hC)
  rw [mul_div_cancel₀ _ (ne_of_gt hC)] at hkey
  simpa [ENNReal.ofReal_coe_nnreal] using hkey

/-- A bounded planar set whose image oscillates quadratically in the mutual distance has
Lebesgue null image. No measurability of the set or of its image is required, and `f` is
arbitrary off the set. -/
theorem volume_image_eq_zero_of_quadratic_oscillation
    {A : Set (Fin 2 → ℝ)} {f : (Fin 2 → ℝ) → ℝ} (hA : Bornology.IsBounded A)
    (hosc : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ 2) :
    (volume : Measure ℝ) (f '' A) = 0 :=
  volume_image_eq_zero_of_oscillation_pow hA hosc

/-- The second-order flat points of a `C²` function on a planar compact set have null
image. Flatness is imposed pointwise on the subset, not on all of `K`, and the subset is
not assumed measurable. -/
theorem volume_image_flat_eq_zero {u : (Fin 2 → ℝ) → ℝ} {K : Set (Fin 2 → ℝ)}
    (hu : ContDiff ℝ 2 u) (hK : IsCompact K) :
    (volume : Measure ℝ)
      (u '' {x ∈ K | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0}) = 0 := by
  refine volume_image_eq_zero_of_quadratic_oscillation
    (hK.isBounded.subset fun x hx => hx.1) ?_
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := exists_uniform_quadratic_remainder hu hK ε hε
  exact ⟨δ, hδ, fun x hx y _ hxy => h x hx.1 hx.2.1 hx.2.2 y hxy⟩

/-- The second-order flat points of a `C²` function on the whole plane have null image.
Countable exhaustion of the compact statement; no boundedness or measurability hypothesis
survives. -/
theorem volume_image_flat_univ_eq_zero {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ)
      (u '' {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0}) = 0 := by
  have hcover : {x : Fin 2 → ℝ | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0}
      = ⋃ n : ℕ, {x ∈ Metric.closedBall (0 : Fin 2 → ℝ) n |
          fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, Metric.mem_closedBall]
    refine ⟨fun hx => ?_, fun ⟨_, _, hx⟩ => hx⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (dist x 0)
    exact ⟨n, hn, hx⟩
  rw [hcover, image_iUnion]
  exact measure_iUnion_null fun n =>
    volume_image_flat_eq_zero hu (isCompact_closedBall _ _)

/-- The fully flat points of a `C^n` function on a compact subset of `Fin n → ℝ` have null
image: every derivative of order `1` to `n` vanishes there. Flatness is imposed pointwise on
the subset, not on all of `K`, and the subset is not assumed measurable. -/
theorem volume_image_flat_pow_eq_zero {n : ℕ} {u : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}
    (hu : ContDiff ℝ (n : ℕ) u) (hK : IsCompact K) :
    (volume : Measure ℝ)
      (u '' {x ∈ K | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0}) = 0 := by
  refine volume_image_eq_zero_of_oscillation_pow (hK.isBounded.subset fun x hx => hx.1) ?_
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := exists_uniform_pow_remainder hu hK ε hε
  exact ⟨δ, hδ, fun x hx y _ hxy => h x hx.1 hx.2 y hxy⟩

/-- The fully flat points of a `C^n` function on all of `Fin n → ℝ` have null image.
Countable exhaustion of the compact statement; no compactness, boundedness or measurability
hypothesis survives. This is the top layer of Sard's theorem in dimension `n`, not Sard. -/
theorem volume_image_flat_pow_univ_eq_zero {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ (n : ℕ) u) :
    (volume : Measure ℝ)
      (u '' {x | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0}) = 0 := by
  have hcover : {x : Fin n → ℝ | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0}
      = ⋃ m : ℕ, {x ∈ Metric.closedBall (0 : Fin n → ℝ) m |
          ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, Metric.mem_closedBall]
    refine ⟨fun hx => ?_, fun ⟨_, _, hx⟩ => hx⟩
    obtain ⟨m, hm⟩ := exists_nat_ge (dist x 0)
    exact ⟨m, hm, hx⟩
  rw [hcover, image_iUnion]
  exact measure_iUnion_null fun m =>
    volume_image_flat_pow_eq_zero hu (isCompact_closedBall _ _)

end FunctionalInequalities.Analysis
