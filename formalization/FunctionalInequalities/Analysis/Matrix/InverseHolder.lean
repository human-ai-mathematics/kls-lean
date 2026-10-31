module

public import FunctionalInequalities.Analysis.MeasureAverage
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Hölder moduli of matrix inverses and averaged inverses

The entrywise modulus `|A⁻¹ᵢⱼ − B⁻¹ᵢⱼ| ≤ n² L² d` of the inverse, Hölder entries of `P⁻¹` for a
Hölder field `P` with bounded
inverse entries, and Hölder entries of the averaged inverse `x ↦ ∫₀¹ ((1 − t) P x + t Q x)⁻¹ dt`. On
a compact space, continuous
positive definite fields admit a uniform inverse cap, so the averaged inverse of Hölder positive
definite fields is Hölder
(the coefficients of Gilbarg–Trudinger (2001), Lemma 17.16). The cap and every integrability
statement are derived.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

section InverseEntries

open scoped BigOperators NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
**Entrywise modulus of the inverse.** For invertible `A`, `B` whose inverse entries are bounded by
`L ≥ 0` and whose
entrywise difference is bounded by `d ≥ 0`, `|A⁻¹ᵢⱼ − B⁻¹ᵢⱼ| ≤ n² L² d` with `n = card ι`, from
`A⁻¹ − B⁻¹ = A⁻¹ (B − A) B⁻¹`. -/
theorem abs_inv_sub_inv_entry_le {A B : Matrix ι ι ℝ} {L d : ℝ} (hA : IsUnit A) (hB : IsUnit B)
    (hL : 0 ≤ L) (hd : 0 ≤ d) (ha : ∀ i j, |A⁻¹ i j| ≤ L) (hb : ∀ i j, |B⁻¹ i j| ≤ L)
    (hab : ∀ i j, |A i j - B i j| ≤ d) (i j : ι) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (Fintype.card ι : ℝ) ^ 2 * L ^ 2 * d := by
  classical
  have hi : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := Matrix.inv_sub_inv ⟨fun _ => hB, fun _ => hA⟩
  calc
    |A⁻¹ i j - B⁻¹ i j| = |∑ k : ι, ∑ l : ι, A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      change |(A⁻¹ - B⁻¹) i j| = _
      rw [hi]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
    _ ≤ ∑ k : ι, ∑ l : ι, |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      exact
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k : ι, ∑ _l : ι, L * d * L := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_mul, abs_sub_comm (B l k) (A l k)]
      exact
        mul_le_mul (mul_le_mul (ha i l) (hab l k) (abs_nonneg _) hL) (hb k j) (abs_nonneg _)
          (mul_nonneg hL hd)
    _ = _ := by simp; ring

/-- A map with `dist (f x) (f y) ≤ C · dist x y ^ r` is `(C, r)`-Hölder. -/
private theorem holderWith_of_dist_bound {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (f : X → Y) (C r : ℝ≥0)
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) : HolderWith C r f := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg]
  calc
    _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) := ENNReal.ofReal_le_ofReal (h x y)
    _ = _ := by rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/--
If a field `P` of invertible matrices has `(C, r)`-Hölder entries and inverse entries bounded by
`L`, every entry of
`P⁻¹` is `(n² L² C, r)`-Hölder; the constant is fixed before the entries and the points. -/
theorem holderWith_inverse_entries {X : Type*} [PseudoMetricSpace X] (P : X → Matrix ι ι ℝ)
    (C r L : ℝ≥0) (hP : ∀ x, IsUnit (P x)) (hb : ∀ x i j, |(P x)⁻¹ i j| ≤ L)
    (hc : ∀ i j, HolderWith C r (fun x => P x i j)) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r (fun x => (P x)⁻¹ i j) := by
  apply holderWith_of_dist_bound
  intro x y
  have h :=
    abs_inv_sub_inv_entry_le (hP x) (hP y) L.coe_nonneg
      (mul_nonneg C.coe_nonneg (Real.rpow_nonneg dist_nonneg _)) (hb x) (hb y)
      (fun a b => by simpa only [Real.dist_eq] using (hc a b).dist_le x y) i j
  simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, mul_assoc] using
    h

end InverseEntries

section AveragedInverse

open Set MeasureTheory
open scoped NNReal ENNReal

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

omit [Fintype ι] [DecidableEq ι] in
/--
For `t ∈ [0, 1]`, the entries of `(1 − t) P + t Q` are `(C, r)`-Hölder when those of `P` and `Q`
are. -/
theorem holderWith_convex_matrix_entries (P Q : X → Matrix ι ι ℝ) (C r : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j)) {t : ℝ} (ht : t ∈ Icc 0 1) (i j : ι) :
    HolderWith C r (fun x => ((1 - t) • P x + t • Q x) i j) := by
  have h := ((hP i j).smul (1 - t)).add ((hQ i j).smul t)
  have heq : C * ‖1 - t‖₊ + C * ‖t‖₊ = C := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    ring
  rw [heq] at h
  convert h using 1
  rfl

/--
**Hölder averaged inverse.** If `P` and `Q` have `(C, r)`-Hölder entries and every `(1 − t) P x + t
Q x`, `t ∈ [0, 1]`,
is invertible with inverse entries bounded by `L`, then `x ↦ ∫₀¹ ((1 − t) P x + t Q x)⁻¹ᵢⱼ dt` is
`(n² L² C, r)`-Hölder.
Interval integrability is derived from continuity of the inverse. -/
theorem holderWith_averaged_inverse_entries (P Q : X → Matrix ι ι ℝ) (C r L : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j))
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, IsUnit ((1 - t) • P x + t • Q x))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x i j, |((1 - t) • P x + t • Q x)⁻¹ i j| ≤ L) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
      (fun x => ∫ t in (0 : ℝ)..1, ((1 - t) • P x + t • Q x)⁻¹ i j) := by
  have hint (x : X) :
    IntervalIntegrable (fun t : ℝ => ((1 - t) • P x + t • Q x)⁻¹ i j) volume 0 1 := by
    have hc : ContinuousOn (fun t : ℝ => ((1 - t) • P x + t • Q x)⁻¹ i j) (Icc 0 1) := by
      intro t ht
      have hn : (((1 - t) • P x + t • Q x).det) ≠ 0 :=
        ((Matrix.isUnit_iff_isUnit_det ((1 - t) • P x + t • Q x)).mp (hu t ht x)).ne_zero
      have hm : ContinuousAt (fun s : ℝ => ((1 - s) • P x + s • Q x)⁻¹) t :=
        (continuousAt_matrix_inv ((1 - t) • P x + t • Q x)
              (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hn)).comp
          (f := fun s : ℝ => (1 - s) • P x + s • Q x) (by fun_prop)
      exact
        (((continuous_apply j).comp (continuous_apply i)).continuousAt.comp (f := fun s : ℝ =>
            ((1 - s) • P x + s • Q x)⁻¹) hm).continuousWithinAt
    exact hc.intervalIntegrable_of_Icc (by norm_num)
  apply holderWith_unit_interval_mean _ _ _ hint
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simp only [uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  exact
    holderWith_inverse_entries (fun x => (1 - t) • P x + t • Q x) C r L (hu t ht') (hb t ht')
      (holderWith_convex_matrix_entries P Q C r hP hQ ht') i j

end AveragedInverse

section CompactPositiveFields

open Set MeasureTheory
open scoped NNReal Matrix.Norms.Elementwise ComplexOrder

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X] [CompactSpace X]

omit [Fintype ι] [DecidableEq ι] in
/--
Convex combinations `(1 − t) A + t B`, `t ∈ [0, 1]`, of positive definite matrices are positive
definite. -/
private theorem posDef_convex_segment {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : t ∈ Icc 0 1) : ((1 - t) • A + t • B).PosDef := by
  by_cases h0 : t = 0
  · simpa only [h0, sub_zero, one_smul, zero_smul, add_zero] using hA
  by_cases h1 : t = 1
  · simpa only [h1, sub_self, zero_smul, one_smul, zero_add] using hB
  exact
    (hA.smul (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))).add
      (hB.smul (lt_of_le_of_ne ht.1 (Ne.symm h0)))

/--
On a compact space, continuous positive definite fields `P` and `Q` admit one bound `L > 0` on every
entry of
`((1 − t) P x + t Q x)⁻¹`, `t ∈ [0, 1]`; it is derived from continuity of the inverse on the compact
`X × [0, 1]`. -/
theorem exists_uniform_inverse_entry_bound_on_compact (P Q : X → Matrix ι ι ℝ)
    (hP : Continuous P) (hQ : Continuous Q) (hPP : ∀ x, (P x).PosDef)
    (hQP : ∀ x, (Q x).PosDef) :
    ∃ L : ℝ≥0, 0 < L ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ x i j, |((1 - t) • P x + t • Q x)⁻¹ i j| ≤ L := by
  let F : X × Icc (0 : ℝ) 1 → Matrix ι ι ℝ := fun z =>
    (1 - (z.2 : ℝ)) • P z.1 + (z.2 : ℝ) • Q z.1
  have hc : Continuous F := by fun_prop
  have hi : Continuous (fun z => (F z)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    apply
      (continuousAt_matrix_inv (F z)
            (by
              simpa only [Ring.inverse_eq_inv'] using
                continuousAt_inv₀
                  (posDef_convex_segment (hPP z.1) (hQP z.1) z.2.property).det_pos.ne')).comp
        (f := F) hc.continuousAt
  obtain ⟨R, hR⟩ := (isCompact_range hi).isBounded.exists_norm_le
  let L : ℝ≥0 := ⟨max R 0 + 1, by positivity⟩
  refine ⟨L, by change (0 : ℝ) < max R 0 + 1; positivity, ?_⟩
  intro t ht x i j
  have hh := hR ((F (x, ⟨t, ht⟩))⁻¹) ⟨(x, ⟨t, ht⟩), rfl⟩
  have he := Matrix.norm_entry_le_entrywise_sup_norm ((F (x, ⟨t, ht⟩))⁻¹) (i := i) (j := j)
  change |((F (x, ⟨t, ht⟩))⁻¹) i j| ≤ (L : ℝ)
  rw [← Real.norm_eq_abs]
  exact he.trans (hh.trans (by change R ≤ max R 0 + 1; linarith [le_max_left R 0]))

/--
**Averaged inverse of compact positive definite fields** (coefficients of Gilbarg–Trudinger (2001),
Lemma 17.16). If `P`
and `Q` are positive definite with `(C, r)`-Hölder entries, `r > 0`, on a compact space, there is `L
> 0` such that every
`x ↦ ∫₀¹ ((1 − t) P x + t Q x)⁻¹ᵢⱼ dt` is `(n² L² C, r)`-Hölder. Continuity of the fields and the
uniform inverse cap are
derived. -/
theorem exists_holder_averaged_inverse_entries_of_posDef (P Q : X → Matrix ι ι ℝ) (C r : ℝ≥0)
    (hr : 0 < r) (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j)) (hPP : ∀ x, (P x).PosDef)
    (hQP : ∀ x, (Q x).PosDef) :
    ∃ L : ℝ≥0,
      0 < L ∧
        ∀ i j,
          HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r
            (fun x => ∫ t in (0 : ℝ)..1, ((1 - t) • P x + t • Q x)⁻¹ i j) := by
  have hPc : Continuous P :=
    continuous_pi fun i => continuous_pi fun j => (hP i j).continuous hr
  have hQc : Continuous Q :=
    continuous_pi fun i => continuous_pi fun j => (hQ i j).continuous hr
  obtain ⟨L, hL, hb⟩ := exists_uniform_inverse_entry_bound_on_compact P Q hPc hQc hPP hQP
  refine ⟨L, hL, fun i j => holderWith_averaged_inverse_entries P Q C r L hP hQ ?_ hb i j⟩
  intro t ht x
  exact (posDef_convex_segment (hPP x) (hQP x) ht).isUnit

end CompactPositiveFields

end FunctionalInequalities.Analysis
