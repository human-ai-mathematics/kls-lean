import FunctionalInequalities.Analysis.Convex.AffineMaximum
import FunctionalInequalities.Probability.MomentMeasure.Basic

/-! Audit clients for the extended-real Legendre transform and finite affine maxima
(`Analysis/Convex/Legendre.lean`, `Analysis/Convex/AffineMaximum.lean`; Cordero-Erausquin–Klartag, arXiv:1304.0630v1,
(61) and the proof of Proposition 12). Client blocks are verbatim from the root-compiled lane A clients
(`lane-a/Clients.lean` c3964edf…, `lane-a/round2-convexification/ConvexificationClients.lean` a733721b…), re-pointed from
the scratch namespace `KLSConstruction.MomentMap` to the owning namespaces: a nonconstant affine primal negative on half
the line, the infinite-value density boundary, a nonconvex discontinuous two-point primal and the empty effective domain. -/

noncomputable section

section LaneAClients

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.MomentMeasure
open scoped ENNReal

namespace CEKLegendreClients

/-- Truncation/convexification properties required by CEK Proposition 12 hold
for the affine potential `x`, even though it is negative on half the line. -/
theorem affine_truncation_client (dx : Measure ℝ) :
    let f : ℝ → EReal := fun x => (x : EReal)
    let g := lowerTruncate f 2
    ProperPotential g ∧ ProperPotential (legendre g) ∧
      legendre g 0 ≤ (2 : EReal) ∧
      (∀ y, legendre (legendre (legendre g)) y = legendre g y) ∧
      mass dx (legendre f) ≤ mass dx (legendre g) := by
  dsimp only
  have hf : ∃ x : ℝ, (x : EReal) ≠ ⊤ := ⟨0, EReal.coe_ne_top 0⟩
  have hg := lowerTruncate_proper (fun x : ℝ => (x : EReal)) 2 hf
  have hdual := legendre_lowerTruncate_proper (fun x : ℝ => (x : EReal)) 2 hf
  refine ⟨hg, hdual, ?_, triconjugate_eq _ hg hdual, ?_⟩
  · exact legendre_zero_le_of_lower_bound _ 2 (fun x => le_max_right _ _)
  · exact mass_legendre_mono dx (fun x => le_max_left _ _)

/-- Infinite potential has zero density; finite values retain the real exponential.
This guards against using `toReal` to define the extended density. -/
theorem density_boundary_client (r : ℝ) :
    density (fun _ : ℝ => (⊤ : EReal)) 0 = 0 ∧
      density (fun _ : ℝ => (r : EReal)) 0 = ENNReal.ofReal (Real.exp (-r)) := by
  simp [density, ← EReal.coe_neg]

end CEKLegendreClients

end LaneAClients

section ConvexificationClients

open FunctionalInequalities.Analysis

namespace CEKConvexificationClients

/-- Nonconvex input with finite values only at the two endpoints. -/
def twoPoint (x : ℝ) : EReal := if x = 0 ∨ x = 1 then 0 else ⊤

/-- Convexification fills the gap between endpoints and preserves the exact dual,
although the original potential has neither convexity nor continuity. -/
theorem twoPoint_convexification :
    let c := legendre (legendre twoPoint)
    ¬ ConvexPotential twoPoint ∧ ConvexPotential c ∧ LowerSemicontinuous c ∧
      c (1 / 2 : ℝ) = 0 ∧ (∀ y, legendre c y = legendre twoPoint y) := by
  dsimp only
  have hfinite : ∃ x, twoPoint x ≠ ⊤ := ⟨0, by simp [twoPoint]⟩
  have htrunc : lowerTruncate twoPoint 0 = twoPoint := by
    funext x
    by_cases hx : x = 0 ∨ x = 1 <;> simp [lowerTruncate, twoPoint, hx]
  have h := lowerTruncate_convexification twoPoint 0 hfinite
  dsimp only at h
  rw [htrunc] at h
  obtain ⟨hc, hls, _, hbound, hdual⟩ := h
  have hz : legendre (legendre twoPoint) 0 = 0 := by
    apply le_antisymm
    · simpa [twoPoint] using (hbound 0).2
    · simpa using (hbound 0).1
  have ho : legendre (legendre twoPoint) 1 = 0 := by
    apply le_antisymm
    · simpa [twoPoint] using (hbound 1).2
    · simpa using (hbound 1).1
  have hp : ((0, 0) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | legendre (legendre twoPoint) p.1 ≤ (p.2 : EReal)} := by
    simp [hz]
  have hq : ((1, 0) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | legendre (legendre twoPoint) p.1 ≤ (p.2 : EReal)} := by
    simp [ho]
  have hm := hc.2 hp hq
    (show 0 ≤ (1 / 2 : ℝ) from by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) from by norm_num) (by norm_num)
  have hmid : legendre (legendre twoPoint) (1 / 2 : ℝ) ≤ 0 := by
    simpa using hm
  refine ⟨?_, hc, hls, le_antisymm hmid ?_, hdual⟩
  · intro hf
    have hp₀ : ((0, 0) : ℝ × ℝ) ∈ {p : ℝ × ℝ | twoPoint p.1 ≤ (p.2 : EReal)} := by
      simp [twoPoint]
    have hq₀ : ((1, 0) : ℝ × ℝ) ∈ {p : ℝ × ℝ | twoPoint p.1 ≤ (p.2 : EReal)} := by
      simp [twoPoint]
    have hbad := hf.2 hp₀ hq₀
      (show 0 ≤ (1 / 2 : ℝ) from by norm_num)
      (show 0 ≤ (1 / 2 : ℝ) from by norm_num) (by norm_num)
    norm_num [twoPoint] at hbad
  · simpa using (hbound (1 / 2 : ℝ)).1

/-- With no effective-domain witness the conjugate is `-∞`, so its epigraph is
still convex and it is lsc, but it cannot satisfy `ConvexPotential`'s no-bottom part. -/
theorem allTop_boundary :
    LowerSemicontinuous (legendre (fun _ : ℝ => (⊤ : EReal))) ∧
      Convex ℝ {p : ℝ × ℝ | legendre (fun _ : ℝ => (⊤ : EReal)) p.1 ≤ (p.2 : EReal)} ∧
      ¬ ConvexPotential (legendre (fun _ : ℝ => (⊤ : EReal))) := by
  refine ⟨lowerSemicontinuous_legendre _, convex_epigraph_legendre _, ?_⟩
  intro h
  have hne := h.1 0
  exact hne (by simp [legendre])

end CEKConvexificationClients

end ConvexificationClients

#print axioms CEKLegendreClients.affine_truncation_client
#print axioms CEKLegendreClients.density_boundary_client
#print axioms CEKConvexificationClients.twoPoint_convexification
#print axioms CEKConvexificationClients.allTop_boundary
#print axioms FunctionalInequalities.Analysis.legendre_antitone
#print axioms FunctionalInequalities.Analysis.legendre_ne_bot
#print axioms FunctionalInequalities.Analysis.fenchel_le
#print axioms FunctionalInequalities.Analysis.biconjugate_le
#print axioms FunctionalInequalities.Analysis.legendre_zero_le_of_lower_bound
#print axioms FunctionalInequalities.Analysis.triconjugate_eq
#print axioms FunctionalInequalities.Analysis.lowerTruncate_proper
#print axioms FunctionalInequalities.Analysis.legendre_lowerTruncate_proper
#print axioms FunctionalInequalities.Analysis.continuous_legendre_summand
#print axioms FunctionalInequalities.Analysis.lowerSemicontinuous_legendre
#print axioms FunctionalInequalities.Analysis.convex_epigraph_legendre
#print axioms FunctionalInequalities.Analysis.legendre_ne_bot_iff
#print axioms FunctionalInequalities.Analysis.convexPotential_legendre
#print axioms FunctionalInequalities.Analysis.lower_bound_biconjugate
#print axioms FunctionalInequalities.Analysis.lowerTruncate_convexification
#print axioms FunctionalInequalities.Analysis.legendre_eq_interior_sup
#print axioms FunctionalInequalities.Analysis.continuous_affineMaximum
#print axioms FunctionalInequalities.Analysis.exists_finite_hull_neighborhood
#print axioms FunctionalInequalities.Analysis.affineMaximum_coercive
#print axioms FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre
#print axioms FunctionalInequalities.Analysis.affineMaximum_le_legendre
