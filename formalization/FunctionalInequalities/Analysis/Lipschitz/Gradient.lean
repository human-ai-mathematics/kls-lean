import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set Metric
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Produce the global Lipschitz exponent from the actual bounded total gradient. -/
theorem exists_lipschitzWith_neg_add_comp_gradient {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ LF : NNReal, LipschitzWith LF (fun x => -u x + V (gradient u x)) := by
  have hgrad_bound (x : EuclideanSpace ℝ (Fin n)) :
      ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hL)
  obtain ⟨C, hC⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ))
      hV.locallyLipschitz.locallyLipschitzOn
  have hmaps : MapsTo (gradient u) univ
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)) := by
    intro x _
    simpa only [mem_closedBall, dist_zero_right] using hgrad_bound x
  have hcomp : LipschitzWith (C * G) (V ∘ gradient u) :=
    lipschitzOnWith_univ.mp (hC.comp hG.lipschitzOnWith hmaps)
  exact ⟨L + C * G, hL.neg.add hcomp⟩

end FunctionalInequalities.Analysis
