module

public import FunctionalInequalities.Analysis.Cutoff.Profile
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A Lipschitz bound for the radial cutoff

`exists_lipschitz_radial_cutoff_cap`: one constant `B > 0` such that `s ↦ smoothTransition (2 - s)`
is
`B`-Lipschitz and, in every dimension and for every `eps > 0`, the radial cutoff
`y ↦ 1 - smoothTransition (2 - ‖y‖ / eps)` is `B / eps`-Lipschitz. Used for the truncation errors in
the Newtonian estimates of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Classics 2001 (ISBN 3-540-41160-7), Lemmas 4.1–4.2.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-- A positive dimension-independent Lipschitz cap for the actual smooth
profile and its radial complement. The cap is derived from the profile's derivative bound,
not assumed. -/
theorem exists_lipschitz_radial_cutoff_cap :
    ∃ B : ℝ,
      0 < B ∧
        LipschitzWith (Real.toNNReal B) (fun s : ℝ => Real.smoothTransition (2 - s)) ∧
          ∀ (n : ℕ) (eps : ℝ),
            0 < eps →
              LipschitzWith (Real.toNNReal (B / eps))
                (fun y : EuclideanSpace ℝ (Fin n) =>
                  1 - Real.smoothTransition (2 - ‖y‖ / eps)) := by
  obtain ⟨hp, _, _, _, _, _, _, _, ⟨B₀, hB₀, hbound⟩⟩ :=
    FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff
  let B := B₀ + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let rho : ℝ → ℝ := fun s => Real.smoothTransition (2 - s)
  have hlip : LipschitzWith (Real.toNNReal B) rho := by
    apply lipschitzWith_of_nnnorm_deriv_le (hp.differentiable (by simp))
    intro t
    apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal B hB.le] using
      (hbound t).1.trans (show B₀ ≤ B by dsimp [B]; linarith)
  refine ⟨B, hB, hlip, ?_⟩
  intro n eps heps
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [Real.coe_toNNReal (B / eps) (div_nonneg hB.le heps.le)]
  calc
    dist (1 - rho (‖a‖ / eps)) (1 - rho (‖b‖ / eps)) = |rho (‖a‖ / eps) - rho (‖b‖ / eps)| := by
      rw [Real.dist_eq]
      have he :
        (1 - rho (‖a‖ / eps)) - (1 - rho (‖b‖ / eps)) = -(rho (‖a‖ / eps) - rho (‖b‖ / eps)) := by
        ring
      rw [he, abs_neg]
    _ ≤ B * |(‖a‖ - ‖b‖) / eps| := by
      simpa only [Real.dist_eq, ← sub_div, Real.coe_toNNReal B hB.le] using
        hlip.dist_le_mul (‖a‖ / eps) (‖b‖ / eps)
    _ = (B / eps) * |‖a‖ - ‖b‖| := by rw [abs_div, abs_of_pos heps]; ring
    _ ≤ (B / eps) * ‖a - b‖ :=
      mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le a b) (div_nonneg hB.le heps.le)
    _ = (B / eps) * dist a b := by rw [dist_eq_norm]

end FunctionalInequalities.Analysis
