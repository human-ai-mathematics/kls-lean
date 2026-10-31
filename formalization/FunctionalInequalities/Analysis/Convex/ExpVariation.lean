module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Variation of `e^{-G}` for a convex function `G` on an interval

Let `G` be convex on an open set `J ⊆ ℝ` and write `D(s) = G'₊(s)` for its right derivative. On a
compact interval `[a, b] ⊆ J` the function `e^{-G}` is the integral of its right derivative
`−D e^{−G}` (`integral_rightDeriv_mul_exp_neg`). Since `D` is nondecreasing, `e^{-G}` increases up
to a minimum point of `G` and decreases afterwards, so its variation on `[a, b]` is at most twice
its maximum (`integral_abs_rightDeriv_mul_exp_neg_le`), and at least
`2e^{-G(m)} − e^{-G(a)} − e^{-G(b)}` for every `m ∈ [a, b]`
(`two_mul_exp_neg_sub_le_integral_abs`).

These are the one-dimensional estimates behind Cordero-Erausquin–Klartag, *Moment measures*
(arXiv:1304.0630v1), Lemma 4 (`∫ |∂ᵢρ| ≤ 2 ∫ sup_t ρ(y, t) dy` for a log-concave `ρ`) and the
vanishing boundary term of Lemma 9 for a continuous log-concave function on a line.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory intervalIntegral

namespace FunctionalInequalities.Analysis

variable {G : ℝ → ℝ} {J : Set ℝ}

/-- **Fundamental theorem of calculus for `e^{-G}`** with the right derivative of a convex `G`:
`∫_a^b G'₊ e^{−G} = e^{−G(a)} − e^{−G(b)}` for `[a, b]` inside the open set where `G` is convex. -/
theorem integral_rightDeriv_mul_exp_neg (hJ : IsOpen J) (hG : ConvexOn ℝ J G) {a b : ℝ}
    (hab : a ≤ b) (hsub : Icc a b ⊆ J) :
    ∫ s in a..b, derivWithin G (Ioi s) s * Real.exp (-G s) =
      Real.exp (-G a) - Real.exp (-G b) := by
  have hcontJ : ContinuousOn G J := hG.continuousOn hJ
  have hcont : ContinuousOn (fun s => -Real.exp (-G s)) (Icc a b) :=
    ((hcontJ.mono hsub).neg.rexp).neg
  have hmono : MonotoneOn (fun s => derivWithin G (Ioi s) s) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (hG.monotoneOn_rightDeriv).mono (by rw [hJ.interior_eq]; exact hsub)
  have hint : IntervalIntegrable (fun s => derivWithin G (Ioi s) s * Real.exp (-G s)) volume a b :=
    hmono.intervalIntegrable.mul_continuousOn (by
      rw [uIcc_of_le hab]; exact (hcontJ.mono hsub).neg.rexp)
  have h := integral_eq_sub_of_hasDeriv_right_of_le hab hcont (f' := fun s =>
      derivWithin G (Ioi s) s * Real.exp (-G s)) (fun s hs => by
    have hsJ : s ∈ interior J := by
      rw [hJ.interior_eq]; exact hsub (Ioo_subset_Icc_self hs)
    have hd := (hG.hasDerivWithinAt_rightDeriv_of_mem_interior hsJ).neg.exp.neg
    convert hd using 1
    simp only [Pi.neg_apply]; ring) hint
  rw [h]
  ring

/-- **Upper bound for the variation**: on `[a, b] ⊆ J`, `∫_a^b |G'₊| e^{−G} ≤ 2S` whenever
`e^{−G} ≤ S` on `[a, b]`. -/
theorem integral_abs_rightDeriv_mul_exp_neg_le (hJ : IsOpen J) (hG : ConvexOn ℝ J G) {a b : ℝ}
    (hab : a ≤ b) (hsub : Icc a b ⊆ J) {S : ℝ}
    (hS : ∀ s ∈ Icc a b, Real.exp (-G s) ≤ S) :
    ∫ s in a..b, |derivWithin G (Ioi s) s| * Real.exp (-G s) ≤ 2 * S := by
  have hcontJ : ContinuousOn G J := hG.continuousOn hJ
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) (hcontJ.mono hsub)
  have hint : ∀ {u v : ℝ}, u ≤ v → Icc u v ⊆ Icc a b →
      IntervalIntegrable (fun s => |derivWithin G (Ioi s) s| * Real.exp (-G s)) volume u v := by
    intro u v huv hsub'
    have hmono : MonotoneOn (fun s => derivWithin G (Ioi s) s) (uIcc u v) := by
      rw [uIcc_of_le huv]
      exact (hG.monotoneOn_rightDeriv).mono (by rw [hJ.interior_eq]; exact hsub'.trans hsub)
    exact hmono.intervalIntegrable.abs.mul_continuousOn (by
      rw [uIcc_of_le huv]; exact (hcontJ.mono (hsub'.trans hsub)).neg.rexp)
  have hJs : ∀ s ∈ Icc a b, s ∈ interior J := fun s hs => by rw [hJ.interior_eq]; exact hsub hs
  -- the right derivative is nonpositive before `m` and nonnegative from `m` on
  have hneg : ∀ s ∈ Ico a m, derivWithin G (Ioi s) s ≤ 0 := by
    intro s hs
    have h := hG.rightDeriv_le_slope_of_mem_interior (hJs s ⟨hs.1, hs.2.le.trans hm.2⟩)
      (hsub hm) hs.2
    have hsl : slope G s m ≤ 0 := by
      rw [slope_def_field]
      have := isMinOn_iff.mp hmin s ⟨hs.1, hs.2.le.trans hm.2⟩
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hs.2])
    linarith
  have hpos_m : m < b → 0 ≤ derivWithin G (Ioi m) m := by
    intro hmb
    have hd := hG.hasDerivWithinAt_rightDeriv_of_mem_interior (hJs m hm)
    refine ge_of_tendsto ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hd) ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_lt_nhds hmb] with t htb (hmt : m < t)
    rw [slope_def_field]
    have := isMinOn_iff.mp hmin t ⟨hm.1.trans hmt.le, htb.le⟩
    exact div_nonneg (by linarith) (by linarith)
  have hpos : ∀ s ∈ Ico m b, 0 ≤ derivWithin G (Ioi s) s := by
    intro s hs
    have hmb : m < b := lt_of_le_of_lt hs.1 hs.2
    exact (hpos_m hmb).trans ((hG.monotoneOn_rightDeriv) (hJs m hm)
      (hJs s ⟨hm.1.trans hs.1, hs.2.le⟩) hs.1)
  -- split at `m` and integrate the signed derivative on each piece
  have hleft : ∫ s in a..m, |derivWithin G (Ioi s) s| * Real.exp (-G s) =
      Real.exp (-G m) - Real.exp (-G a) := by
    have hcongr : ∫ s in a..m, |derivWithin G (Ioi s) s| * Real.exp (-G s) =
        ∫ s in a..m, -(derivWithin G (Ioi s) s * Real.exp (-G s)) := by
      refine integral_congr_ae ?_
      filter_upwards [(countable_singleton m).ae_notMem volume] with s hsm hs
      rw [uIoc_of_le hm.1] at hs
      rw [abs_of_nonpos (hneg s ⟨hs.1.le, lt_of_le_of_ne hs.2 hsm⟩)]
      ring
    rw [hcongr, intervalIntegral.integral_neg,
      integral_rightDeriv_mul_exp_neg hJ hG hm.1 ((Icc_subset_Icc_right hm.2).trans hsub)]
    ring
  have hright : ∫ s in m..b, |derivWithin G (Ioi s) s| * Real.exp (-G s) =
      Real.exp (-G m) - Real.exp (-G b) := by
    have hcongr : ∫ s in m..b, |derivWithin G (Ioi s) s| * Real.exp (-G s) =
        ∫ s in m..b, derivWithin G (Ioi s) s * Real.exp (-G s) := by
      refine integral_congr_ae ?_
      filter_upwards [(countable_singleton b).ae_notMem volume] with s hsb hs
      rw [uIoc_of_le hm.2] at hs
      rw [abs_of_nonneg (hpos s ⟨hs.1.le, lt_of_le_of_ne hs.2 hsb⟩)]
    rw [hcongr, integral_rightDeriv_mul_exp_neg hJ hG hm.2 ((Icc_subset_Icc_left hm.1).trans hsub)]
  rw [← integral_add_adjacent_intervals (hint hm.1 (Icc_subset_Icc_right hm.2))
    (hint hm.2 (Icc_subset_Icc_left hm.1)), hleft, hright]
  have h1 := hS m hm
  have h2 := Real.exp_pos (-G a)
  have h3 := Real.exp_pos (-G b)
  linarith

/-- **Lower bound for the variation**: for `a ≤ m ≤ b` with `[a, b] ⊆ J`,
`2e^{−G(m)} − e^{−G(a)} − e^{−G(b)} ≤ ∫_a^b |G'₊| e^{−G}`. -/
theorem two_mul_exp_neg_sub_le_integral_abs (hJ : IsOpen J) (hG : ConvexOn ℝ J G)
    {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b) (hsub : Icc a b ⊆ J) :
    2 * Real.exp (-G m) - Real.exp (-G a) - Real.exp (-G b) ≤
      ∫ s in a..b, |derivWithin G (Ioi s) s| * Real.exp (-G s) := by
  have hcontJ : ContinuousOn G J := hG.continuousOn hJ
  have hint : ∀ {u v : ℝ}, u ≤ v → Icc u v ⊆ J →
      IntervalIntegrable (fun s => derivWithin G (Ioi s) s * Real.exp (-G s)) volume u v := by
    intro u v huv hsub'
    have hmono : MonotoneOn (fun s => derivWithin G (Ioi s) s) (uIcc u v) := by
      rw [uIcc_of_le huv]
      exact (hG.monotoneOn_rightDeriv).mono (by rw [hJ.interior_eq]; exact hsub')
    exact hmono.intervalIntegrable.mul_continuousOn (by
      rw [uIcc_of_le huv]; exact (hcontJ.mono hsub').neg.rexp)
  have hsa : Icc a m ⊆ J := (Icc_subset_Icc_right hmb).trans hsub
  have hsb : Icc m b ⊆ J := (Icc_subset_Icc_left ham).trans hsub
  have habs : ∀ s, |derivWithin G (Ioi s) s| * Real.exp (-G s) =
      |derivWithin G (Ioi s) s * Real.exp (-G s)| := fun s => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simp_rw [habs]
  rw [← integral_add_adjacent_intervals (hint ham hsa).abs (hint hmb hsb).abs]
  have h1 := abs_integral_le_integral_abs (μ := volume) ham
    (f := fun s => derivWithin G (Ioi s) s * Real.exp (-G s))
  have h2 := abs_integral_le_integral_abs (μ := volume) hmb
    (f := fun s => derivWithin G (Ioi s) s * Real.exp (-G s))
  rw [integral_rightDeriv_mul_exp_neg hJ hG ham hsa] at h1
  rw [integral_rightDeriv_mul_exp_neg hJ hG hmb hsb] at h2
  have h3 := neg_abs_le (Real.exp (-G a) - Real.exp (-G m))
  have h4 := le_abs_self (Real.exp (-G m) - Real.exp (-G b))
  linarith

end FunctionalInequalities.Analysis
