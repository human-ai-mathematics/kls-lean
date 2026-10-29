import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Coordinates of a vector-valued map against a linear isometry

The calculus layer of the componentwise route to the vector `C¹` pieces of a Lipschitz map
(`Analysis/Lipschitz/VectorPieces.lean`).  A linear isometry equivalence
`e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))` turns a map `u : V → W` into the family of
scalar coordinates `fun y => e (u y) i`, and the three lemmas here say that the passage is faithful
in both directions for the two pieces of data the coarea assembly needs:

* `lipschitzWith_coord` — a coordinate of a `K`-Lipschitz map is `K`-Lipschitz, so each coordinate
  is admissible input for the **scalar** `exists_contDiff_pieces`;
* `differentiableAt_of_coord` — differentiability is detected coordinatewise, the converse
  direction of `differentiableAt_pi` through `e`;
* `eq_and_fderiv_eq_of_coord` — coordinatewise agreement of values and of differentials at a point
  is agreement of the vector value and of the vector differential there.

Nothing here is about measure theory, and no regularity beyond differentiability at the single
point `x` is used.  The isometry `e` is an explicit argument everywhere: the conclusions do not
depend on the choice, but nothing below fixes one.
-/

noncomputable section

open Module
open scoped NNReal

namespace FunctionalInequalities.Analysis

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- **The coordinates of a Lipschitz map are Lipschitz, with the same constant.**  Taking a
coordinate of a Euclidean vector is `1`-Lipschitz and `e` is an isometry, so no constant is lost.
This is what feeds the scalar `exists_contDiff_pieces`. -/
theorem lipschitzWith_coord (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) {u : V → W}
    {K : ℝ≥0} (hu : LipschitzWith K u) (i : Fin (finrank ℝ W)) :
    LipschitzWith K (fun y => e (u y) i) := by
  intro a b
  calc edist (e (u a) i) (e (u b) i) ≤ edist (e (u a)) (e (u b)) := PiLp.edist_apply_le _ _ i
    _ = edist (u a) (u b) := e.edist_map _ _
    _ ≤ K * edist a b := hu a b

section CoordinateDerivatives

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
/-- **Differentiability is detected coordinatewise.**  The map factors as `e.symm` after the
Euclidean tuple of its coordinates, and both outer maps are continuous linear. -/
theorem differentiableAt_of_coord (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W)))
    {u : V → W} {x : V} (h : ∀ i, DifferentiableAt ℝ (fun y => e (u y) i) x) :
    DifferentiableAt ℝ u x := by
  have h1 : DifferentiableAt ℝ (fun y => (fun i => e (u y) i : Fin (finrank ℝ W) → ℝ)) x :=
    differentiableAt_pi.2 h
  have h2 : DifferentiableAt ℝ (fun y => e (u y)) x :=
    (((EuclideanSpace.equiv (Fin (finrank ℝ W)) ℝ).symm :
      (Fin (finrank ℝ W) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))).differentiableAt).comp
      x h1
  have h3 : DifferentiableAt ℝ (fun y => e.symm (e (u y))) x :=
    (e.symm.toLinearIsometry.toContinuousLinearMap.differentiableAt (x := e (u x))).comp x h2
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h3

/-- The differential of a coordinate is the coordinate of the differential. -/
theorem fderiv_coord_apply (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W)))
    {u : V → W} {x : V} (hu : DifferentiableAt ℝ u x) (i : Fin (finrank ℝ W)) (w : V) :
    fderiv ℝ (fun y => e (u y) i) x w = e (fderiv ℝ u x w) i := by
  have hd : HasFDerivAt (fun y => e (u y) i)
      ((EuclideanSpace.proj i).comp
        ((e.toLinearIsometry.toContinuousLinearMap).comp (fderiv ℝ u x))) x := by
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      ((e.toLinearIsometry.toContinuousLinearMap.hasFDerivAt).comp x hu.hasFDerivAt)
  rw [hd.fderiv]
  rfl

/-- **Componentwise first-order agreement is first-order agreement.**  If `u` and `v` are
differentiable at `x` and every coordinate of `v` matches the corresponding coordinate of `u` there
in value and in differential, then `v` matches `u` at `x` in value and in differential. -/
theorem eq_and_fderiv_eq_of_coord (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W)))
    {u v : V → W} {x : V} (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hval : ∀ i, e (v x) i = e (u x) i)
    (hder : ∀ i, fderiv ℝ (fun y => e (v y) i) x = fderiv ℝ (fun y => e (u y) i) x) :
    v x = u x ∧ fderiv ℝ v x = fderiv ℝ u x := by
  refine ⟨e.injective (PiLp.ext hval),
    ContinuousLinearMap.ext fun w => e.injective (PiLp.ext fun i => ?_)⟩
  rw [← fderiv_coord_apply e hv i w, ← fderiv_coord_apply e hu i w, hder i]

end CoordinateDerivatives

end FunctionalInequalities.Analysis
