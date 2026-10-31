module

public import FunctionalInequalities.Analysis.Convex.Subgradient.Existence

/-!
# Supporting inequalities and convex gluing across a ball

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations.
-/

@[expose] public section

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis
open Set Metric Filter
open scoped Topology

section PiecewiseMaximum
open Classical

section Pure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A support of the raising branch at an active interior point supports the
locally raised function on the WHOLE domain, including outside the ball. -/
theorem subgradient_le_piecewise_max_ball {Ω : Set E} {u q : E → ℝ} {c x p : E} {r : ℝ}
    (hu : ConvexOn ℝ Ω u) (hball : closedBall c r ⊆ Ω) (hboundary : ∀ z ∈ sphere c r, q z ≤ u z)
    (hx : x ∈ ball c r) (hxu : u x ≤ q x) (hp : ∀ y ∈ closedBall c r, q x + ⟪p, y - x⟫ ≤ q y) :
    ∀ y ∈ Ω, q x + ⟪p, y - x⟫ ≤ if y ∈ ball c r then max (u y) (q y) else u y := by
  intro y hy
  by_cases hyb : y ∈ ball c r
  · rw [ite_eq_left hyb]
    exact (hp y (ball_subset_closedBall hyb)).trans (le_max_right _ _)
  rw [ite_eq_right hyb]
  have h0 : dist x c < r := hx
  have h1 : r ≤ dist y c := le_of_not_gt hyb
  have hc : ContinuousOn (fun t : ℝ => dist (AffineMap.lineMap x y t) c) (Icc 0 1) := by
    fun_prop
  have hbetween :
    r ∈
      Icc ((fun t : ℝ => dist (AffineMap.lineMap x y t) c) 0)
        ((fun t : ℝ => dist (AffineMap.lineMap x y t) c) 1) := by
    simpa using And.intro h0.le h1
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc zero_le_one hc hbetween
  have htpos : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro h
    subst t
    simp only [AffineMap.lineMap_apply_zero] at he
    exact (ne_of_lt h0) he
  let z := AffineMap.lineMap x y t
  have hzs : z ∈ sphere c r := he
  have hzu := hboundary z hzs
  have hqs := hp z (sphere_subset_closedBall hzs)
  have hxuΩ : x ∈ Ω := hball (ball_subset_closedBall hx)
  have hzconv := hu.2 hxuΩ hy (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  have hzm : z - x = t • (y - x) := by
    dsimp [z]
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_right]
  rw [hzm, inner_smul_right] at hqs
  have hzv : u z ≤ (1 - t) * u x + t * u y := by
    simpa only [z, AffineMap.lineMap_apply_module, smul_eq_mul] using hzconv
  have hm := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hxu)
  have hprod : t * (q x + ⟪p, y - x⟫ - u y) ≤ 0 := by nlinarith
  by_contra hn
  have hpos := mul_pos htpos (sub_pos.mpr (lt_of_not_ge hn))
  linarith only [hprod, hpos]

/-- Actual C0 gluing uses only equality at the boundary of the ball. -/
theorem continuousOn_piecewise_max_ball
    {Ω : Set E} {u q : E → ℝ} {c : E} {r : ℝ}
    (hr : 0 < r) (huc : ContinuousOn u (closure Ω))
    (hqc : ContinuousOn q (closure Ω))
    (hboundary : ∀ z ∈ sphere c r, q z ≤ u z) :
    ContinuousOn (fun y => if y ∈ ball c r then max (u y) (q y) else u y)
      (closure Ω) := by
  apply ContinuousOn.if
  · intro z hz
    exact max_eq_left (hboundary z (by
      have hzf : z ∈ frontier (ball c r) := hz.2
      rw [frontier_ball c (ne_of_gt hr)] at hzf
      exact hzf))
  · exact (huc.sup hqc).mono inter_subset_left
  · exact huc.mono inter_subset_left

end Pure

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Convexity on the WHOLE closure is GENERATED from actual C0 supports of q
inside the ball. The unknown u needs no differentiability or support input. -/
theorem convexOn_closure_piecewise_max_ball {Ω : Set E} {u q : E → ℝ} {c : E} {r : ℝ}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ (closure Ω) u) (hq : ConvexOn ℝ Ω q)
    (hqc : ContinuousOn q Ω) (hball : closedBall c r ⊆ Ω)
    (hboundary : ∀ z ∈ sphere c r, q z ≤ u z) :
    ConvexOn ℝ (closure Ω) (fun y => if y ∈ ball c r then max (u y) (q y) else u y) := by
  let w : E → ℝ := fun y => if y ∈ ball c r then max (u y) (q y) else u y
  have hwu (y : E) : u y ≤ w y := by
    by_cases hy : y ∈ ball c r
    · dsimp only [w]; rw [ite_eq_left hy]; exact le_max_left _ _
    · dsimp only [w]; rw [ite_eq_right hy]
  refine ⟨hu.1, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ closure Ω := hu.1 hx hy ha hb hab
  have hsimple (he : w z = u z) : w z ≤ a * w x + b * w y := by
    rw [he]
    exact
      (hu.2 hx hy ha hb hab).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hwu x) ha)
          (mul_le_mul_of_nonneg_left (hwu y) hb))
  change w z ≤ a * w x + b * w y
  by_cases hzb : z ∈ ball c r
  · by_cases hzu : u z ≤ q z
    · have hzΩ : z ∈ Ω := hball (ball_subset_closedBall hzb)
      obtain ⟨R, _hR, hex, _hb⟩ :=
        exists_uniform_subgradient_bound_on_compact hΩ hq hqc (isCompact_singleton (x := z))
          (singleton_subset_iff.mpr hzΩ)
      obtain ⟨p, hp⟩ := hex z (mem_singleton z)
      have htrans :=
        subgradient_le_piecewise_max_ball hu (fun t ht => subset_closure (hball ht)) hboundary
          hzb hzu (fun t ht => hp t (hball ht))
      have he : w z = q z := by dsimp only [w]; rw [ite_eq_left hzb, max_eq_right hzu]
      have hpx : w z + ⟪p, x - z⟫ ≤ w x := by rw [he]; exact htrans x hx
      have hpy : w z + ⟪p, y - z⟫ ≤ w y := by rw [he]; exact htrans y hy
      have hi : a * ⟪p, x - z⟫ + b * ⟪p, y - z⟫ = 0 := by
        rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
        have hvec : a • (x - z) + b • (y - z) = 0 := by
          calc
            _ = (a • x + b • y) - (a + b) • z := by module
            _ = 0 := by rw [hab, one_smul]; exact sub_self z
        rw [hvec, inner_zero_right]
      have hm :=
        add_le_add (mul_le_mul_of_nonneg_left hpx ha) (mul_le_mul_of_nonneg_left hpy hb)
      have hcoeff : (a + b) * w z = w z := by rw [hab, one_mul]
      nlinarith only [hm, hi, hcoeff]
    · apply hsimple
      dsimp only [w]; rw [ite_eq_left hzb, max_eq_left (le_of_not_ge hzu)]
  · apply hsimple
    dsimp only [w]; rw [ite_eq_right hzb]

end Finite
end PiecewiseMaximum

end FunctionalInequalities.Analysis
