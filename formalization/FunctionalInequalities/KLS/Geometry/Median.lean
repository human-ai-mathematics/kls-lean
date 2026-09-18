import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Medians of a measurable real function

Hole-free auxiliary layer for the Cheeger inequality route: every measurable real function on a
probability space has a **median**, a level `m` with `μ{g > m} ≤ 1/2` and `μ{g < m} ≤ 1/2`.

The proof is the classical one.  The set `S = {t | 1/2 ≤ μ{g ≤ t}}` is nonempty (the sets
`{g ≤ n}` increase to the whole space, so their masses increase to `1`) and bounded below (the
sets `{g ≤ -n}` decrease to the empty set, so some one of them has mass `< 1/2`), and
`m = sInf S` works: `{g ≤ m}` is the intersection of the sets `{g ≤ m + 1/(n+1)}`, each of mass
at least `1/2`, which bounds `μ{g > m} = 1 - μ{g ≤ m}` by `1/2`, while `{g < m}` is the union of
the sets `{g ≤ m - 1/(n+1)}`, each of mass less than `1/2` because `m` is a lower bound of `S`.

No topology, no density, no continuity and no finite dimension are involved: the ambient space is
an arbitrary measurable space carrying a probability measure.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FunctionalInequalities.KLS.Isoperimetry

variable {α : Type*} [MeasurableSpace α]

/-- Every measurable real function on a probability space has a median: a level `m` whose strict
superlevel set and strict sublevel set both carry mass at most `1/2`.  No continuity, no density
and no nonatomicity of the law are assumed, and the median is in general not unique. -/
theorem exists_median (μ : Measure α) [IsProbabilityMeasure μ] {g : α → ℝ} (hg : Measurable g) :
    ∃ m : ℝ, μ {x | m < g x} ≤ 1 / 2 ∧ μ {x | g x < m} ≤ 1 / 2 := by
  classical
  have hmeas : ∀ t : ℝ, MeasurableSet {x | g x ≤ t} := fun t =>
    measurableSet_le hg measurable_const
  have hmono : ∀ {s t : ℝ}, s ≤ t → μ {x | g x ≤ s} ≤ μ {x | g x ≤ t} := fun {s t} hst =>
    measure_mono fun x hx => le_trans hx hst
  have hhalf : (1 : ℝ≥0∞) / 2 < 1 := ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
  have hhalfpos : (0 : ℝ≥0∞) < 1 / 2 := ENNReal.half_pos one_ne_zero
  set S : Set ℝ := {t : ℝ | 1 / 2 ≤ μ {x | g x ≤ t}} with hSdef
  -- `S` is nonempty: the sets `{g ≤ n}` increase to the whole space.
  have hSne : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hlt : ∀ n : ℕ, μ {x | g x ≤ (n : ℝ)} ≤ 1 / 2 := by
      intro n
      have hn : (n : ℝ) ∉ S := by rw [hcon]; exact Set.notMem_empty _
      rw [hSdef] at hn
      exact (not_le.mp hn).le
    have hmn : Monotone fun n : ℕ => {x | g x ≤ (n : ℝ)} := by
      intro a b hab x hx
      have hx' : g x ≤ (a : ℝ) := hx
      exact le_trans hx' (by exact_mod_cast hab)
    have hsup := hmn.measure_iUnion (μ := μ)
    have huniv : (⋃ n : ℕ, {x | g x ≤ (n : ℝ)}) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge (g x)
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    rw [huniv, measure_univ] at hsup
    exact absurd (lt_of_lt_of_le hhalf (hsup.le.trans (iSup_le hlt))) (lt_irrefl _)
  -- `S` is bounded below: the sets `{g ≤ -n}` decrease to the empty set.
  have hSbdd : BddBelow S := by
    have hanti : Antitone fun n : ℕ => {x | g x ≤ -(n : ℝ)} := by
      intro a b hab x hx
      have hx' : g x ≤ -(b : ℝ) := hx
      refine le_trans hx' (neg_le_neg ?_)
      exact_mod_cast hab
    have hinf := hanti.measure_iInter (μ := μ) (fun n => (hmeas _).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {x | g x ≤ -(n : ℝ)}) = (∅ : Set α) := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨m, hm⟩ := exists_nat_gt (-(g x))
      have hxm : g x ≤ -(m : ℝ) := Set.mem_iInter.mp hx m
      linarith
    rw [hempty, measure_empty] at hinf
    have hex : ∃ n : ℕ, μ {x | g x ≤ -(n : ℝ)} < 1 / 2 := by
      by_contra hcon
      rw [not_exists] at hcon
      have h2 : (1 : ℝ≥0∞) / 2 ≤ 0 := by
        rw [hinf]
        exact le_iInf fun n => not_lt.mp (hcon n)
      exact absurd (lt_of_lt_of_le hhalfpos h2) (lt_irrefl _)
    obtain ⟨N, hN⟩ := hex
    refine ⟨-(N : ℝ), fun t ht => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (lt_of_le_of_lt (le_trans ht (hmono hlt.le)) hN) (lt_irrefl _)
  refine ⟨sInf S, ?_, ?_⟩
  · -- `μ{g ≤ sInf S} ≥ 1/2` by continuity from above along `sInf S + 1/(n+1)`.
    set m : ℝ := sInf S with hmdef
    have hstep : ∀ n : ℕ, (1 : ℝ≥0∞) / 2 ≤ μ {x | g x ≤ m + 1 / ((n : ℝ) + 1)} := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨t, htS, hts⟩ := exists_lt_of_csInf_lt hSne (by linarith : m < m + 1 / ((n : ℝ) + 1))
      exact le_trans htS (hmono hts.le)
    have hanti : Antitone fun n : ℕ => {x | g x ≤ m + 1 / ((n : ℝ) + 1)} := by
      intro a b hab x hx
      have hx' : g x ≤ m + 1 / ((b : ℝ) + 1) := hx
      have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith
      have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have := one_div_le_one_div_of_le hpos hab'
      show g x ≤ m + 1 / ((a : ℝ) + 1)
      linarith
    have hinf := hanti.measure_iInter (μ := μ) (fun n => (hmeas _).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
    have hinter : (⋂ n : ℕ, {x | g x ≤ m + 1 / ((n : ℝ) + 1)}) = {x | g x ≤ m} := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => Set.mem_iInter.mpr fun n => ?_)
      · show g x ≤ m
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        have hxn : g x ≤ m + 1 / ((n : ℝ) + 1) := Set.mem_iInter.mp hx n
        linarith
      · have hx' : g x ≤ m := hx
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        show g x ≤ m + 1 / ((n : ℝ) + 1)
        linarith
    rw [hinter] at hinf
    have hge : (1 : ℝ≥0∞) / 2 ≤ μ {x | g x ≤ m} := by
      rw [hinf]
      exact le_iInf hstep
    have hcompl : {x | m < g x} = {x | g x ≤ m}ᶜ := by
      ext x
      exact (lt_iff_not_ge (α := ℝ)).trans Iff.rfl
    rw [hcompl, measure_compl (hmeas m) (measure_ne_top _ _), measure_univ]
    refine tsub_le_iff_right.mpr ?_
    calc (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
      _ ≤ 1 / 2 + μ {x | g x ≤ m} := by gcongr
  · -- `{g < sInf S}` is the union of the sets `{g ≤ sInf S - 1/(n+1)}`, all of mass `< 1/2`.
    set m : ℝ := sInf S with hmdef
    have hstep : ∀ n : ℕ, μ {x | g x ≤ m - 1 / ((n : ℝ) + 1)} ≤ 1 / 2 := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hnot : m - 1 / ((n : ℝ) + 1) ∉ S := fun hmem =>
        absurd (csInf_le hSbdd hmem) (by rw [← hmdef]; linarith)
      rw [hSdef] at hnot
      exact (not_le.mp hnot).le
    have hmn : Monotone fun n : ℕ => {x | g x ≤ m - 1 / ((n : ℝ) + 1)} := by
      intro a b hab x hx
      have hx' : g x ≤ m - 1 / ((a : ℝ) + 1) := hx
      have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
        linarith
      have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have := one_div_le_one_div_of_le hpos hab'
      show g x ≤ m - 1 / ((b : ℝ) + 1)
      linarith
    have hsup := hmn.measure_iUnion (μ := μ)
    have hunion : (⋃ n : ℕ, {x | g x ≤ m - 1 / ((n : ℝ) + 1)}) = {x | g x < m} := by
      refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
        have hn' : g x ≤ m - 1 / ((n : ℝ) + 1) := hn
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        show g x < m
        linarith
      · have hx' : g x < m := hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < m - g x)
        refine Set.mem_iUnion.mpr ⟨n, ?_⟩
        show g x ≤ m - 1 / ((n : ℝ) + 1)
        linarith
    rw [hunion] at hsup
    rw [hsup]
    exact iSup_le hstep

end FunctionalInequalities.KLS.Isoperimetry
