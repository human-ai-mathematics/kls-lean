module

public import FunctionalInequalities.Analysis.BakryEmery.GradientForcing.SegmentCoefficient
public import FunctionalInequalities.Analysis.BakryEmery.DifferenceQuotient

/-!
# First-order linearization of the `W (∇u)` finite difference

Supporting Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, for the equation
`log det Hess u + u = W (∇u)`. For the scalar-step finite difference
`differenceQuotient u d q x = (u (x + d) - u x) / q` of one fixed `C²` function `u`:

* `fderiv_differenceQuotient_basisFun`: its coordinate derivatives are the finite differences of
  the gradient coordinates of `u`;
* `quotient_eq_sum_segmentForcingCoefficient`: for `C¹` `W`,
  `(W (∇u (x + d)) - W (∇u x)) / q = Σᵢ bᵢ ∂ᵢ(differenceQuotient u d q) x`, with the explicit
  coefficients `bᵢ = segmentForcingCoefficient W (gradient u) d x i`;
* `linearized_differenceQuotient_equation`: combined with the averaged-inverse equation, the finite
  difference satisfies the linear equation
  `Σᵢⱼ aᵢⱼ ∂ⱼᵢ(differenceQuotient) + differenceQuotient = Σᵢ bᵢ ∂ᵢ(differenceQuotient)` with
  `aᵢⱼ = averagedInverse (hessianMatrix u) d x i j`.

The identities hold for every `q` with Lean's total division; the linearized equation keeps an
explicit `q ≠ 0` premise. No third derivative of `u`, Schauder estimate, coefficient bound or
regularity gain is assumed or concluded.
-/

@[expose] public section
noncomputable section
namespace FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open Set MeasureTheory
open scoped BigOperators ContDiff
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Coordinate derivative of the scalar-step finite difference. The identity also holds at
`q = 0` by total division; classical clients keep an explicit nonzero-step premise. -/
theorem fderiv_differenceQuotient_basisFun {u : E → ℝ} (hu : ContDiff ℝ 2 u) (d : E) (q : ℝ)
    (x : E) (i : Fin n) :
    fderiv ℝ (differenceQuotient u d q) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      (gradient u (x + d) i - gradient u x i) / q := by
  rw [fderiv_differenceQuotient hu d q]
  change
    q⁻¹ *
        (fderiv ℝ u (x + d) (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      _
  rw [fderiv_basisFun_eq_gradient, fderiv_basisFun_eq_gradient]
  ring

/-- The `W (∇u)` finite difference is the first derivative of the same finite difference of `u`
paired with the explicit segment forcing coefficients. -/
theorem quotient_eq_sum_segmentForcingCoefficient {u W : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hW : ContDiff ℝ 1 W) (d : E) (q : ℝ) (x : E) :
    (W (gradient u (x + d)) - W (gradient u x)) / q =
      ∑ i,
        segmentForcingCoefficient W (gradient u) d x i *
          fderiv ℝ (differenceQuotient u d q) x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [sub_eq_sum_segmentMeanCoefficient hW, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_differenceQuotient_basisFun hu d q x i]
  simp only [segmentForcingCoefficient, div_eq_mul_inv]
  ring

/--
The first-order finite-difference equation at the original `C²` `u`, with the averaged-inverse
principal coefficients and the segment forcing coefficients. The nonzero step and the positive
definiteness and equation at both endpoints are explicit premises. -/
theorem linearized_differenceQuotient_equation {u W : E → ℝ} (hu : ContDiff ℝ 2 u)
    (hW : ContDiff ℝ 1 W) (x d : E) (q : ℝ) (_hq : q ≠ 0) (h0 : (hessianMatrix u x).PosDef)
    (h1 : (hessianMatrix u (x + d)).PosDef)
    (he0 : Real.log (hessianMatrix u x).det + u x = W (gradient u x))
    (he1 : Real.log (hessianMatrix u (x + d)).det + u (x + d) = W (gradient u (x + d))) :
    (∑ i,
          ∑ j,
            averagedInverse (hessianMatrix u) d x i j *
              hessianMatrix (differenceQuotient u d q) x j i) +
        differenceQuotient u d q x =
      ∑ i,
        segmentForcingCoefficient W (gradient u) d x i *
          fderiv ℝ (differenceQuotient u d q) x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have h :=
    logDet_quotient_eq_averagedInverse (H := hessianMatrix u) (F := fun y => W (gradient u y)) x
      d q h0 h1 he0 he1
  have hp :
    (∑ i,
          ∑ j,
            averagedInverse (hessianMatrix u) d x i j *
              hessianMatrix (differenceQuotient u d q) x j i) +
        differenceQuotient u d q x =
      (W (gradient u (x + d)) - W (gradient u x)) / q := by
    simpa only [hessianMatrix_differenceQuotient hu d q, Matrix.sub_apply,
      differenceQuotient] using h
  exact hp.trans (quotient_eq_sum_segmentForcingCoefficient hu hW d q x)

end FunctionalInequalities.Analysis.BakryEmery
