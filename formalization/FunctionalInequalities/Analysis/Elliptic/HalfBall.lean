module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The half-ball and its one-sided normal derivative

CNS1984 Lemma 5.1, p. 385: `C²(B_R^+) ∩ C¹(closure)`.

In `ℝ^{m+1}` (`x_n = x (Fin.last m)`), `B = {‖x‖ < R, 0 < xₙ}` and `K = {‖x‖ ≤ R, 0 ≤ xₙ}`.

* `interior_closedHalfBall`: `interior K = B`, through `interior_closedBall` and the open coordinate
  map
  `EuclideanSpace.proj (Fin.last m)` (surjective, hence open).
* `closure_halfBall`: `closure B = K`, from
  `Convex.closure_interior_eq_closure_of_nonempty_interior` with the
  interior point `(R/2) eₙ`.
* `uniqueDiffOn_closure_halfBall`: derivatives within the closure are unique
  (`uniqueDiffOn_convex`).
* `normal_derivative_halfBall`: for `v` of class `C¹` ON THE CLOSURE (no ambient differentiability),
  at a flat
  boundary point `z` the inward normal ray `t ↦ v (z + t eₙ)` has the one-sided derivative
  `fderivWithin ℝ v (closure B) z eₙ` on `[0, ∞)`, and the positive-ray slope converges to it. The
  ray stays in
  the closure on `[0, R - ‖z‖]`; the chain rule within sets and the slope characterization are
  Mathlib's.
-/

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology

namespace FunctionalInequalities.Analysis

private lemma closedHalfBall_eq {m : ℕ} {R : ℝ} :
    {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} =
      closedBall 0 R ∩ EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m) ⁻¹' Ici 0 := by
  ext x
  simp

private lemma half_mem_halfBall {m : ℕ} {R : ℝ} (hR : 0 < R) :
    (R / 2) • EuclideanSpace.single (Fin.last m) (1 : ℝ) ∈
      {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)} := by
  refine ⟨?_, ?_⟩
  · have hnorm : ‖(R / 2) • EuclideanSpace.single (Fin.last m) (1 : ℝ)‖ = R / 2 := by
      simp [norm_smul, abs_of_pos hR]
    rw [hnorm]
    linarith
  · have hcoord : ((R / 2) • EuclideanSpace.single (Fin.last m) (1 : ℝ)) (Fin.last m) = R / 2 := by
      simp
    rw [hcoord]
    positivity

/-- The interior of the closed half-ball is the open half-ball. -/
theorem interior_closedHalfBall {m : ℕ} {R : ℝ} (hR : 0 < R) :
    interior {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} =
      {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)} := by
  set p : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last m) with hp
  have hsurj : Function.Surjective p := fun a =>
    ⟨EuclideanSpace.single (Fin.last m) a, by simp [hp]⟩
  have hB :
    {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)} =
      ball 0 R ∩ p ⁻¹' Ioi 0 := by
    ext x
    simp [hp]
  rw [closedHalfBall_eq, ← hp, hB, interior_inter, interior_closedBall 0 hR.ne', ←
    (p.isOpenMap hsurj).preimage_interior_eq_interior_preimage p.continuous, interior_Ici]

/-- The closed half-ball is convex. -/
theorem convex_closedHalfBall {m : ℕ} {R : ℝ} :
    Convex ℝ {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} := by
  rw [closedHalfBall_eq]
  exact (convex_closedBall 0 R).inter
    ((convex_Ici 0).linear_preimage (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last m)).toLinearMap)

theorem closure_halfBall {m : ℕ} {R : ℝ} (hR : 0 < R) :
    closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)} =
      {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} := by
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} := by
    rw [closedHalfBall_eq]
    exact
      isClosed_closedBall.inter
        (isClosed_Ici.preimage (EuclideanSpace.proj (Fin.last m)).continuous)
  have hne :
    (interior {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)}).Nonempty := by
    rw [interior_closedHalfBall hR]
    exact ⟨_, half_mem_halfBall hR⟩
  rw [← interior_closedHalfBall hR,
    convex_closedHalfBall.closure_interior_eq_closure_of_nonempty_interior hne,
    hclosed.closure_eq]

/-- Derivatives within the closed half-ball are unique. -/
theorem uniqueDiffOn_closure_halfBall {m : ℕ} {R : ℝ} (hR : 0 < R) :
    UniqueDiffOn ℝ
      (closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)}) := by
  rw [closure_halfBall hR]
  refine uniqueDiffOn_convex convex_closedHalfBall ?_
  rw [interior_closedHalfBall hR]
  exact ⟨_, half_mem_halfBall hR⟩

theorem normal_derivative_halfBall {m : ℕ} {R : ℝ} (hR : 0 < R)
    {v : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hv :
      ContDiffOn ℝ 1 v
        (closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)}))
    {z : EuclideanSpace ℝ (Fin (m + 1))} (hz : ‖z‖ < R) (hzn : z (Fin.last m) = 0) :
    HasDerivWithinAt (fun t : ℝ => v (z + t • EuclideanSpace.single (Fin.last m) (1 : ℝ)))
        (fderivWithin ℝ v
          (closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)}) z
          (EuclideanSpace.single (Fin.last m) (1 : ℝ)))
        (Ici 0) 0 ∧
      Tendsto (fun t : ℝ => (v (z + t • EuclideanSpace.single (Fin.last m) (1 : ℝ)) - v z) / t)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (fderivWithin ℝ v
            (closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)}) z
            (EuclideanSpace.single (Fin.last m) (1 : ℝ)))) := by
  set e : EuclideanSpace ℝ (Fin (m + 1)) := EuclideanSpace.single (Fin.last m) (1 : ℝ) with he
  set K := closure {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)} with hK
  have hKeq : K = {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} :=
    closure_halfBall hR
  have hzK : z ∈ K := by
    rw [hKeq]
    exact
      ⟨hz.le, hzn.ge⟩
  -- the derivative within the SAME closure, at the ray's base point

  have hf : HasFDerivWithinAt v (fderivWithin ℝ v K z) K (z + (0 : ℝ) • e) := by
    rw [zero_smul, add_zero]
    exact
      (hv.differentiableOn one_ne_zero z hzK).hasFDerivWithinAt
  -- the inward normal ray and its generated containment in the closure on `[0, R - ‖z‖]`

  have hγ : HasDerivWithinAt (fun t : ℝ => z + t • e) e (Icc 0 (R - ‖z‖)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z).hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ => z + t • e) (Icc 0 (R - ‖z‖)) K := by
    intro t ht
    rw [hKeq]
    refine ⟨?_, ?_⟩
    · calc
        ‖z + t • e‖ ≤ ‖z‖ + ‖t • e‖ := norm_add_le _ _
        _ = ‖z‖ + t := by simp [he, norm_smul, abs_of_nonneg ht.1]
        _ ≤ R := by linarith [ht.2]
    · have hcoord : (z + t • e) (Fin.last m) = t := by simp [he, hzn]
      rw [hcoord]
      exact
        ht.1
  -- ONE within-derivative production, consumed by both conclusions

  have hd : HasDerivWithinAt (fun t : ℝ => v (z + t • e)) (fderivWithin ℝ v K z e) (Ici 0) 0 :=
    (hf.comp_hasDerivWithinAt (0 : ℝ) hγ hmaps).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE (by linarith [hz]))
  refine ⟨hd, ?_⟩
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hd
  have hIoi : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t
    simp [lt_iff_le_and_ne, eq_comm]
  rw [hIoi] at hs
  refine hs.congr' (Eventually.of_forall fun t => ?_)
  simp [slope_def_field]

/-- The same half-ball frontier consists exactly of its flat or curved part. -/
theorem frontier_halfBall {m : ℕ} {R : ℝ} (hR : 0 < R) :
    frontier {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)} =
      {x | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m) ∧ (‖x‖ = R ∨ x (Fin.last m) = 0)} := by
  have ho : IsOpen {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ 0 < x (Fin.last m)} := by
    rw [← interior_closedHalfBall hR]
    exact isOpen_interior
  rw [frontier, closure_halfBall hR, ho.interior_eq]
  ext x
  constructor
  · rintro ⟨⟨hn, hx⟩, hnot⟩
    refine ⟨hn, hx, ?_⟩
    by_cases hnr : ‖x‖ < R
    · right
      have hnpos : ¬0 < x (Fin.last m) := fun h => hnot ⟨hnr, h⟩
      exact le_antisymm (le_of_not_gt hnpos) hx
    · exact Or.inl (le_antisymm hn (le_of_not_gt hnr))
  · rintro ⟨hn, hx, h⟩
    refine ⟨⟨hn, hx⟩, ?_⟩
    rintro ⟨hni, hxi⟩
    rcases h with h | h
    · exact (ne_of_lt hni) h
    · exact (ne_of_gt hxi) h

end FunctionalInequalities.Analysis
