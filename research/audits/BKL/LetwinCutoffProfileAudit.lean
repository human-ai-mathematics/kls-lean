module

public import FunctionalInequalities.Analysis.Cutoff.Profile
public import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: scalar cutoff profile of Letwin Lemma A.4

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17). Actual clients of the three scalar
results, every premise derived here: the profile is not constant (`η 0 = 1`, `η 3 = 0`); the
majorant `w` of `|η″|` is interval-integrable on `[0, 3]` and vanishes at `4`; the exhaustion
`η(5/(n+1))` starts at `0` for `n = 0`, is monotone and tends to `1`, so it is not constant
either.
-/

@[expose] public section

open Filter
open FunctionalInequalities.Analysis

namespace A4CutoffProfileClient

/-- The profile is not constant: `η 0 = 1` and `η 3 = 0`. -/
theorem profile_values :
    Real.smoothTransition (2 - 0) = 1 ∧ Real.smoothTransition (2 - 3) = 0 :=
  ⟨smoothTransition_two_sub_cutoff.2.2.2.1 0 (by norm_num),
    smoothTransition_two_sub_cutoff.2.2.2.2.1 3 (by norm_num)⟩

/--
The majorant is interval-integrable on `[0, 3]` (its integral is the constant of the defect bound)
and vanishes at `4`. -/
theorem majorant_integrable_and_vanishing :
    ∃ w : ℝ → ℝ,
      (∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t) ∧
        IntervalIntegrable w MeasureTheory.volume 0 3 ∧ w 4 = 0 ∧ 0 ≤ ∫ t in (0 : ℝ)..3, w t := by
  obtain ⟨w, hw, -, hw0, hws, hmaj⟩ := exists_majorant_abs_deriv_deriv_smoothTransition_two_sub
  exact
    ⟨w, hmaj, hw.continuous.intervalIntegrable 0 3, hws 4 (Or.inr (by norm_num)),
      intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hw0 t)⟩

/-- The exhaustion at `a = 5` starts at `0`, is monotone and tends to `1`. -/
theorem exhaustion_five :
    Real.smoothTransition (2 - 5 / (((0 : ℕ) : ℝ) + 1)) = 0 ∧
      Monotone (fun n : ℕ => Real.smoothTransition (2 - 5 / ((n : ℝ) + 1))) ∧
      Tendsto (fun n : ℕ => Real.smoothTransition (2 - 5 / ((n : ℝ) + 1))) atTop (nhds 1) :=
  ⟨smoothTransition_two_sub_cutoff.2.2.2.2.1 _ (by norm_num),
    (monotone_and_tendsto_smoothTransition_two_sub_div_succ 5).1,
    (monotone_and_tendsto_smoothTransition_two_sub_div_succ 5).2⟩

end A4CutoffProfileClient

#print axioms smoothTransition_two_sub_cutoff
#print axioms exists_majorant_abs_deriv_deriv_smoothTransition_two_sub
#print axioms monotone_and_tendsto_smoothTransition_two_sub_div_succ
#print axioms A4CutoffProfileClient.profile_values
#print axioms A4CutoffProfileClient.majorant_integrable_and_vanishing
#print axioms A4CutoffProfileClient.exhaustion_five
