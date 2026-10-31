module

public import FunctionalInequalities.Analysis.Convex.EssentialContinuity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace LetwinEssentialContinuityAudit
open FunctionalInequalities.Analysis

/-- The zero potential on a Euclidean space is a convex potential. -/
theorem zero_convexPotential (n : ℕ) :
    ConvexPotential (fun _ : EuclideanSpace ℝ (Fin n) => (0 : EReal)) := by
  refine ⟨fun _ => EReal.zero_ne_bot, ?_⟩
  have hset : {p : EuclideanSpace ℝ (Fin n) × ℝ | (0 : EReal) ≤ (p.2 : EReal)} =
      (LinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ⁻¹' Ici 0 := by
    ext p
    change (0 : EReal) ≤ (p.2 : EReal) ↔ 0 ≤ p.2
    exact EReal.coe_nonneg
  rw [hset]
  exact (convex_Ici 0).linear_preimage _

/-- Concrete client: the (finite) zero potential is essentially continuous. -/
theorem zero_essentiallyContinuous (n : ℕ) :
    EssentiallyContinuous (fun _ : EuclideanSpace ℝ (Fin n) => (0 : EReal)) :=
  (zero_convexPotential n).essentiallyContinuous_of_ne_top fun _ => EReal.zero_ne_top

/-- Concrete client: the closed half-line `[0, ∞)` has a frontier of positive `H⁰` measure. -/
theorem half_line_frontier_pos :
    0 < μH[(Module.finrank ℝ ℝ : ℝ) - 1] (frontier (Ici (0 : ℝ))) :=
  hausdorffMeasure_frontier_pos (convex_Ici 0) isClosed_Ici
    (by rw [interior_Ici]; exact ⟨1, mem_Ioi.mpr one_pos⟩) (fun h => by
      have h' : (-1 : ℝ) ∈ Ici (0 : ℝ) := h ▸ mem_univ _
      exact absurd (mem_Ici.mp h') (by norm_num))

/-- Client of the bounded-support step of CEK Theorem 2: an essentially continuous convex potential
on `ℝⁿ` whose nonzero moment measure is supported in a ball is a continuous finite function. -/
theorem continuous_of_bounded_moment_measure {n : ℕ}
    {ψ : EuclideanSpace ℝ (Fin n) → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      fun x => EReal.exp (-ψ x)).map (gradient fun x => (ψ x).toReal) = μ)
    (hμ0 : μ ≠ 0) {R : ℝ≥0} (hsupp : μ (closedBall 0 R)ᶜ = 0) :
    Continuous ψ := by
  obtain ⟨hfin, hlip⟩ := hψ.ne_top_of_map_gradient hess hμ hμ0 hsupp
  have heq : (fun x => ((ψ x).toReal : EReal)) = ψ :=
    funext fun x => EReal.coe_toReal (hfin x) (hψ.1 x)
  rw [← heq]
  exact continuous_coe_real_ereal.comp hlip.continuous

end LetwinEssentialContinuityAudit

#print axioms LetwinEssentialContinuityAudit.zero_convexPotential
#print axioms LetwinEssentialContinuityAudit.zero_essentiallyContinuous
#print axioms LetwinEssentialContinuityAudit.half_line_frontier_pos
#print axioms LetwinEssentialContinuityAudit.continuous_of_bounded_moment_measure
#print axioms FunctionalInequalities.Analysis.ConvexPotential.convex_domain
#print axioms FunctionalInequalities.Analysis.ConvexPotential.convexOn_toReal
#print axioms FunctionalInequalities.Analysis.not_continuousAt_of_mem_domain_diff_interior
#print axioms FunctionalInequalities.Analysis.ConvexPotential.setOf_not_continuousAt
#print axioms FunctionalInequalities.Analysis.ConvexPotential.essentiallyContinuous_iff
#print axioms FunctionalInequalities.Analysis.ConvexPotential.essentiallyContinuous_of_ne_top
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_frontier_pos
#print axioms FunctionalInequalities.Analysis.ConvexPotential.isClosed_domain_of_lipschitzOnWith
#print axioms FunctionalInequalities.Analysis.ConvexPotential.ne_top_of_lipschitzOnWith
#print axioms FunctionalInequalities.Analysis.lipschitzOnWith_of_ae_norm_gradient_le
#print axioms FunctionalInequalities.Analysis.ConvexPotential.ne_top_of_map_gradient
