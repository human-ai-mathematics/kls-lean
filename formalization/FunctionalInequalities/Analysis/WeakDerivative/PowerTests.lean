import FunctionalInequalities.Analysis.WeakDerivative.ChainRule

/-! # Nonnegative power tests localized by smooth cutoffs

Supporting weak calculus for Letwin arXiv:2607.24164v1 and the
local elliptic estimates of Gilbarg--Trudinger (2001). Each declaration
retains its own support, integrability and dimensional hypotheses.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff

section BoundedRpowCutoffTests

open MeasureTheory Set
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-! Shifted real powers of a bounded, a.e. nonnegative weak `H¹_loc` function under a compactly supported `C¹` cutoff:
the energy variables of a Moser-type iteration (Letwin arXiv:2607.24164v1 Lemma 2.2; GT (8.48)–(8.49)). -/

open Filter in
/-- **Linear cutoff energy variable, local nonnegativity.** For bounded `w` with coordinate weak derivatives `a k` in
`L²_loc`, nonnegative only a.e. on `tsupport χ` (`χ` of class `C¹` with compact support), `δ > 0` and every real `q`,
`χ (δ + max w 0)^q` is bounded, compactly supported in `tsupport χ` and nonnegative when `χ` is, with the exact weak
derivatives `∂χ · s^q + χ q s^(q-1) a k` (`s = δ + max w 0`), compactly supported in `tsupport χ` and globally `L²`.
The compact smooth power profile and the bounded noncompact chain rule are applied to `w` itself; the identification
with `max w 0` is used only on `tsupport χ`. Every dimension, zero included. -/
theorem local_rpow_cutoff_weak_data {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)), 0 ≤ w x)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  intro η dη
  classical
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  obtain ⟨Φ, D, hΦ, -, hLip, -, he⟩ := exists_smooth_compact_rpow_shift_extension hδ hC q
  have hc := hasWeakDerivAlong_comp_of_bounded hw hbound hweak ha2
    (hΦ.of_le (by exact_mod_cast le_top)) hLip
  obtain ⟨B, hB, hb⟩ := hc.2.1
  let P := fun x => δ ^ q + Φ (w x)
  let dP := fun (k : Fin n) x => deriv Φ (w x) * a k x
  have hp (k : Fin n) : HasWeakDerivAlong P (dP k) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    simpa only [P, dP, one_mul] using (hc.2.2 k).1.const_add_mul (δ ^ q) 1
  have hpb (x : EuclideanSpace ℝ (Fin n)) : ‖P x‖ ≤ ‖δ ^ q‖ + B :=
    (norm_add_le _ _).trans (add_le_add_right (hb x) _)
  have hpm : AEStronglyMeasurable P (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aestronglyMeasurable_const.add hc.1.aestronglyMeasurable
  have hptop (S : Set (EuclideanSpace ℝ (Fin n))) (_hS : IsCompact S) :
      MemLp P (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    memLp_top_of_bound hpm.restrict _ (ae_of_all _ hpb)
  have hmain (k : Fin n) := (hp k).compact_mul_data (fun S _ => (hc.2.2 k).2 S ‹_›) hptop hχ hχc
  have hzero (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport χ) : χ x = 0 ∧ fderiv ℝ χ x = 0 := by
    exact ⟨image_eq_zero_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx⟩
  have hn := (ae_restrict_iff' (isClosed_tsupport χ).measurableSet).mp hnonneg
  have heP : (fun x => χ x * P x) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] η := by
    filter_upwards [hn] with x hx
    by_cases hxs : x ∈ tsupport χ
    · have h0 := hx hxs
      have hCw : w x ≤ C := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)
      simp only [P, η, max_eq_left h0, (he (w x) ⟨h0, hCw⟩).1]
      ring
    · simp only [η, (hzero x hxs).1, zero_mul]
  have hedP (k : Fin n) :
      (fun x => χ x * dP k x + fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * P x)
        =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] dη k := by
    filter_upwards [hn] with x hx
    by_cases hxs : x ∈ tsupport χ
    · have h0 := hx hxs
      have hCw : w x ≤ C := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)
      simp only [P, dP, dη, max_eq_left h0, (he (w x) ⟨h0, hCw⟩).1, (he (w x) ⟨h0, hCw⟩).2]
      ring
    · simp only [dη, (hzero x hxs).1, (hzero x hxs).2, _root_.zero_apply, zero_mul, add_zero]
  have hsupp : Function.support η ⊆ tsupport χ := by
    intro x hx
    exact by_contradiction fun h => hx (by simp only [η, (hzero x h).1, zero_mul])
  have hdsupp (k : Fin n) : Function.support (dη k) ⊆ tsupport χ := by
    intro x hx
    exact by_contradiction fun h => hx (by simp only [dη, (hzero x h).1, (hzero x h).2, _root_.zero_apply]; ring)
  obtain ⟨Bp, hBp⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) C)).exists_bound_of_continuousOn
    (f := fun t : ℝ => (δ + t) ^ q)
    (ContinuousOn.rpow_const (f := fun t : ℝ => δ + t) (by fun_prop)
      fun t ht => Or.inl (show δ + t ≠ 0 from ne_of_gt (by linarith [ht.1])))
  have hmax0 (x) : 0 ≤ max (w x) 0 := le_max_right _ _
  have hmaxC (x) : max (w x) 0 ≤ C := max_le
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound x)) hC
  have hpbound (x) : ‖(δ + max (w x) 0) ^ q‖ ≤ Bp := hBp _ ⟨hmax0 x,hmaxC x⟩
  obtain ⟨Cχ, hCχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hBp0 : 0 ≤ Bp := (norm_nonneg _).trans (hpbound 0)
  have hCχ0 : 0 ≤ Cχ := (norm_nonneg _).trans (hCχ 0)
  have hηb (x) : ‖η x‖ ≤ Cχ * Bp := by
    exact (norm_mul _ _).le.trans (mul_le_mul (hCχ x) (hpbound x) (norm_nonneg _) hCχ0)
  have hηm : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hχ.continuous.aestronglyMeasurable.mul hpm).congr heP
  have hloc : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply locallyIntegrable_iff.mpr
    intro S hS
    have : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
      isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (memLp_top_of_bound hηm.restrict _ (ae_of_all _ hηb)).integrable le_top
  refine ⟨hloc,hχc.mono' hsupp,hsupp,⟨Cχ*Bp,by positivity,hηb⟩,
    fun hχ0 x => mul_nonneg (hχ0 x) (Real.rpow_nonneg (by linarith [hmax0 x]) _),fun k => ?_⟩
  exact ⟨(hmain k).1.congr_ae heP (hedP k), hχc.mono' (hdsupp k), hdsupp k,
    MemLp.ae_eq (hedP k) (hmain k).2.2.2⟩

/-- **Linear cutoff energy variable.** For bounded `w ≥ 0` a.e. with coordinate weak derivatives `a k` in `L²_loc`, a
`C¹` compactly supported `χ`, `δ > 0` and every real `q`, the function `χ (δ + max w 0)^q` is bounded, compactly
supported in `tsupport χ` and nonnegative when `χ` is, with the exact coordinate weak derivatives
`∂χ · s^q + χ q s^(q-1) a k` (`s = δ + max w 0`), compactly supported in `tsupport χ` and globally `L²`. Every
dimension, zero included. -/
theorem bounded_rpow_cutoff_weak_data {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ ((∀ x, 0 ≤ χ x) → ∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact local_rpow_cutoff_weak_data hw hbound hweak ha2 hχ hχc (ae_restrict_of_ae hnonneg) hδ q

open Filter in
/-- **Square cutoff test, local nonnegativity.** The pointwise nonnegative test `χ² (δ + max w 0)^q` with derivative
`2 χ ∂χ s^q + χ² q s^(q-1) a k`, from `local_rpow_cutoff_weak_data` at `χ²`; nonnegativity of `w` is needed only a.e.
on `tsupport χ`. -/
theorem local_rpow_cutoff_weak_test {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hnonneg : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)), 0 ≤ w x)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x ^ 2 * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x ^ 2 * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ (∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  intro η dη
  have hsqc : HasCompactSupport (fun x => χ x ^ 2) := hχc.mono' fun x hx => subset_tsupport χ (fun h => hx (by
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]))
  have hts : tsupport (fun x => χ x ^ 2) ⊆ tsupport χ := closure_mono fun x hx => fun h => hx (by
    simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
  -- local nonnegativity on the smaller support of the square cutoff
  have hnonneg' : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport (fun x => χ x ^ 2))),
      0 ≤ w x := ae_restrict_of_ae_restrict_of_subset hts hnonneg
  obtain ⟨hl, hc, hs, hb, hpos, hd⟩ := local_rpow_cutoff_weak_data hw hbound hweak ha2
    (χ := fun x => χ x ^ 2) (hχ.pow 2) hsqc hnonneg' hδ q
  have hdsq (k : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => χ y ^ 2) x (EuclideanSpace.basisFun (Fin n) ℝ k) =
        2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    rw [((hχ.differentiable one_ne_zero x).hasFDerivAt.pow 2).fderiv]
    simp only [_root_.smul_apply, smul_eq_mul]
    ring
  have hdη (k : Fin n) : (fun x => fderiv ℝ (fun y => χ y ^ 2) x (EuclideanSpace.basisFun (Fin n) ℝ k) *
      (δ + max (w x) 0) ^ q + χ x ^ 2 * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x) = dη k := by
    funext x; rw [hdsq k x]
  -- pointwise nonnegativity of `χ² (δ + max w 0)^q` (not an a.e. statement)
  refine ⟨hl, hc, hs.trans hts, hb, hpos fun x => sq_nonneg _, fun k => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hd k
  rw [← hdη k]
  exact ⟨h1, h2, h3.trans hts, h4⟩

/-- **Square cutoff test.** The nonnegative test `χ² (δ + max w 0)^q` with derivative `2 χ ∂χ s^q + χ² q s^(q-1) a k`;
the linear cutoff energy variable at the cutoff `χ²`. -/
theorem bounded_rpow_cutoff_weak_test {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C δ : ℝ}
    (hw : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖w x‖ ≤ C)
    (hweak : ∀ k : Fin n, HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k))
    (ha2 : ∀ k : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hnonneg : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ w x)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hδ : 0 < δ) (q : ℝ) :
    let η := fun x => χ x ^ 2 * (δ + max (w x) 0) ^ q
    let dη := fun (k : Fin n) x =>
      2 * χ x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ k) * (δ + max (w x) 0) ^ q +
      χ x ^ 2 * (q * (δ + max (w x) 0) ^ (q - 1)) * a k x
    LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      HasCompactSupport η ∧ Function.support η ⊆ tsupport χ ∧
      (∃ Cη : ℝ, 0 ≤ Cη ∧ ∀ x, ‖η x‖ ≤ Cη) ∧ (∀ x, 0 ≤ η x) ∧
      ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ tsupport χ ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact local_rpow_cutoff_weak_test hw hbound hweak ha2 hχ hχc (ae_restrict_of_ae hnonneg) hδ q

end FunctionalInequalities.Analysis

end BoundedRpowCutoffTests
