import FunctionalInequalities.Analysis.Cutoff.Profile

/-!
# Audit: real-parameter monotone exhaustion of Letwin Lemma A.4

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17), `χ_R = η(W/R) ↑ 1` for real `R ≥ 1` with
`W ≥ 1`. Actual clients of `monotoneOn_and_tendsto_smoothTransition_two_sub_div`, every premise
derived here: the restriction to `[1, ∞)` used by the real-parameter producer; the genuinely
nonconstant family `a = 3` (`η(3/1) = 0`, `η(3/3) = 1`, monotone on `[1, ∞)`, limit `1`); the
negative case `a = −2` (constant `1`, consistent with the limit); and agreement with the
natural-index exhaustion `η(a/(n+1))` along `R = n + 1`.
-/

open Filter
open FunctionalInequalities.Analysis
open scoped ContDiff

namespace A4RealExhaustionClient

/-- The producer's form: monotone on `[1, ∞)` (restricted from `(0, ∞)`) with limit `1`, for every real `a`. -/
theorem monotoneOn_Ici_one (a : ℝ) :
    MonotoneOn (fun R : ℝ => Real.smoothTransition (2 - a / R)) (Set.Ici 1) ∧
      Tendsto (fun R : ℝ => Real.smoothTransition (2 - a / R)) atTop (nhds 1) :=
  ⟨(monotoneOn_and_tendsto_smoothTransition_two_sub_div a).1.mono fun _ hR =>
      Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos hR),
    (monotoneOn_and_tendsto_smoothTransition_two_sub_div a).2⟩

/-- A genuinely nonconstant real family: `η(3/1) = 0`, `η(3/3) = 1`, monotone on `[1, ∞)`, limit `1`. -/
theorem nonconstant_three :
    Real.smoothTransition (2 - 3 / 1) = 0 ∧ Real.smoothTransition (2 - 3 / 3) = 1 ∧
      MonotoneOn (fun R : ℝ => Real.smoothTransition (2 - 3 / R)) (Set.Ici 1) ∧
      Tendsto (fun R : ℝ => Real.smoothTransition (2 - 3 / R)) atTop (nhds 1) := by
  refine ⟨Real.smoothTransition.zero_of_nonpos (by norm_num), Real.smoothTransition.one_of_one_le (by norm_num),
    (monotoneOn_Ici_one 3).1, (monotoneOn_Ici_one 3).2⟩

/-- The negative case `a = −2`: every value is `1` (independent check), consistent with the limit. -/
theorem negative_constant (R : ℝ) (hR : 0 < R) :
    Real.smoothTransition (2 - (-2) / R) = 1 ∧
      Tendsto (fun R : ℝ => Real.smoothTransition (2 - (-2) / R)) atTop (nhds 1) := by
  refine ⟨Real.smoothTransition.one_of_one_le ?_, (monotoneOn_and_tendsto_smoothTransition_two_sub_div (-2)).2⟩
  have : 0 < 2 / R := div_pos two_pos hR
  rw [neg_div]
  linarith

/-- Agreement with the natural-index exhaustion along `R = n + 1`: both give monotone sequences
tending to `1`. -/
theorem natural_agreement (a : ℝ) :
    Monotone (fun n : ℕ => Real.smoothTransition (2 - a / ((n : ℝ) + 1))) ∧
      Tendsto (fun n : ℕ => Real.smoothTransition (2 - a / ((n : ℝ) + 1))) atTop (nhds 1) := by
  have h1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := n.cast_nonneg (α := ℝ)
    linarith
  refine ⟨fun m n hmn => (monotoneOn_Ici_one a).1 (h1 m) (h1 n) (add_le_add_left (Nat.cast_le.mpr hmn) 1),
    (monotoneOn_Ici_one a).2.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)⟩

/-- Cross-check with the natural-index exhaustion (an independent derivation): identical
conclusions. -/
theorem natural_crosscheck (a : ℝ) :
    Monotone (fun n : ℕ => Real.smoothTransition (2 - a / ((n : ℝ) + 1))) ∧
      Tendsto (fun n : ℕ => Real.smoothTransition (2 - a / ((n : ℝ) + 1))) atTop (nhds 1) :=
  monotone_and_tendsto_smoothTransition_two_sub_div_succ a

end A4RealExhaustionClient

#print axioms monotoneOn_and_tendsto_smoothTransition_two_sub_div
#print axioms A4RealExhaustionClient.monotoneOn_Ici_one
#print axioms A4RealExhaustionClient.nonconstant_three
#print axioms A4RealExhaustionClient.negative_constant
#print axioms A4RealExhaustionClient.natural_agreement
#print axioms A4RealExhaustionClient.natural_crosscheck
