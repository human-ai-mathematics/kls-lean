import FunctionalInequalities.Analysis.Matrix.AveragedInverseEllipticity
import FunctionalInequalities.Analysis.BakryEmery.DifferenceQuotient

/-!
# Uniformly elliptic finite-difference equations of a `C²` function

Supporting Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, with the ellipticity required by
the interior Schauder estimate, Theorem 6.2, pp. 90–92.

`exists_uniform_elliptic_differenceQuotient_equations` extends
`exists_uniform_differenceQuotient_equations`: for one fixed `C²` function `u` with
`log det Hess u + u = W (∇u)`, positive definite Hessian and `α`-Hölder Hessian entries on
`closedBall c R`, the scalar-step finite differences `differenceQuotient u (q • v) q` satisfy, on
`closedBall c r` and for all `v` and `q ≠ 0` with `r + |q| ‖v‖ ≤ R`, the local equation with the
same `averagedInverse` coefficients, whose entry cap, Hölder constant and positive quadratic lower
and upper bounds `a ‖ξ‖² ≤ Σᵢⱼ aᵢⱼ ξᵢ ξⱼ ≤ b ‖ξ‖²` are chosen before `v` and `q`.

The ellipticity constants are derived from the compact continuous positive definite Hessian, not
assumed. The potential `u` is never replaced; the `W (∇u)` difference stays on the right-hand side,
and no third derivative, Schauder estimate or regularity gain is assumed or concluded.
-/
noncomputable section
namespace FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open Set MeasureTheory Metric
open scoped ContDiff NNReal BigOperators
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A step `q • v` from `closedBall c r` stays in `closedBall c R` when `r + |q| ‖v‖ ≤ R`. -/
private theorem add_smul_mem_closedBall (c v : E) (r R q : ℝ)
    (hstep : r + |q| * ‖v‖ ≤ R) {x : E} (hx : x ∈ closedBall c r) :
    x+q • v ∈ closedBall c R := by
  rw [mem_closedBall, dist_eq_norm] at hx ⊢
  have he : x+q • v-c = (x-c)+q • v := by abel
  rw [he]
  calc
    ‖(x-c)+q • v‖ ≤ ‖x-c‖+‖q • v‖ := norm_add_le _ _
    _ = ‖x-c‖+|q| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ r+|q| * ‖v‖ := by linarith
    _ ≤ R := hstep

/-- The finite-difference equation, the coefficient Hölder constant and entry cap, and positive
quadratic lower and upper ellipticity bounds for one fixed `C²` function `u`. All constants precede
every direction, nonzero scalar step and test vector; for an arbitrary direction `v` the containment
condition retains its norm. -/
theorem exists_uniform_elliptic_differenceQuotient_equations
    (u W : E → ℝ) (hu : ContDiff ℝ 2 u)
    (c : E) (r R : ℝ) (hrR : r ≤ R) (C α : ℝ≥0) (hα : 0 < α)
    (hhol : ∀ i j, HolderOnWith C α (fun x => hessianMatrix u x i j) (closedBall c R))
    (hpos : ∀ x ∈ closedBall c R, (hessianMatrix u x).PosDef)
    (he : ∀ x ∈ closedBall c R,
      Real.log (hessianMatrix u x).det+u x=W (gradient u x)) :
    ∃ (L : ℝ≥0) (a b : ℝ), 0 < L ∧ 0 < a ∧ 0 < b ∧
      ∀ (v : E) (q : ℝ), q ≠ 0 → r+|q| * ‖v‖ ≤ R →
        ContDiff ℝ 2 (differenceQuotient u (q • v) q) ∧
        (∀ i j, HolderOnWith ((n : ℝ≥0)^2*L^2*C) α
          (fun x => averagedInverse (hessianMatrix u) (q • v) x i j) (closedBall c r)) ∧
        (∀ x ∈ closedBall c r, ∀ i j,
          |averagedInverse (hessianMatrix u) (q • v) x i j| ≤ L) ∧
        (∀ x ∈ closedBall c r, ∀ ξ : E,
          a*‖ξ‖^2 ≤ (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j*ξ i*ξ j) ∧
          (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j*ξ i*ξ j) ≤ b*‖ξ‖^2) ∧
        ∀ x ∈ closedBall c r,
          (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j *
            hessianMatrix (differenceQuotient u (q • v) q) x j i) +
            differenceQuotient u (q • v) q x =
            (W (gradient u (x+q • v))-W (gradient u x))/q := by
  have hH : ContinuousOn (hessianMatrix u) (closedBall c R) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (hhol i j).continuousOn hα
  obtain ⟨a,b,ha,hb,hell⟩ := exists_uniform_averagedInverse_ellipticity
    (hessianMatrix u) (isCompact_closedBall c R) hH hpos
  obtain ⟨L,hL,hfirst⟩ :=
    exists_uniform_differenceQuotient_equations u W hu c r R hrR C α hα hhol hpos he
  refine ⟨L,a,b,hL,ha,hb,?_⟩
  intro v q hq hstep
  obtain ⟨hC2,hholder,hentries,heq⟩ := hfirst v q hq hstep
  refine ⟨hC2,hholder,hentries,?_,heq⟩
  intro x hx ξ
  exact hell (q • v) x (closedBall_subset_closedBall hrR hx)
    (add_smul_mem_closedBall c v r R q hstep hx) ξ

end FunctionalInequalities.Analysis.BakryEmery
