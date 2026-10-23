import FunctionalInequalities.Analysis.BakryEmery.GradientForcing
import FunctionalInequalities.Analysis.BakryEmery.UniformGradientForcing
import FunctionalInequalities.Analysis.BakryEmery.HessianEllipticity

/-!
# Linearized uniformly elliptic finite-difference equations

Supporting Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464: the difference quotients of a
solution of `log det Hess u + u = W (∇u)` satisfy a linear, uniformly elliptic equation whose
coefficients have the Hölder control needed for the interior Schauder estimate, Theorem 6.2,
pp. 90–92.

`exists_uniform_linearized_differenceQuotient_equations`: for one fixed `C²` function `u` whose
gradient is Lipschitz, whose Hessian is positive definite and `α`-Hölder (`0 < α ≤ 1`) on
`closedBall c R`, and with `C²` `W`, the finite differences `w = differenceQuotient u (q • v) q`
satisfy on `closedBall c r`, for every `v` and `q ≠ 0` with `r + |q| ‖v‖ ≤ R`,
`Σᵢⱼ aᵢⱼ ∂ⱼᵢw + w = Σᵢ bᵢ ∂ᵢw`, where `aᵢⱼ = averagedInverse (hessianMatrix u) (q • v) x i j` and
`bᵢ = segmentForcingCoefficient W (gradient u) (q • v) x i`. The entry cap and Hölder constant of
`a`, its quadratic ellipticity constants, and the cap and Hölder constant of `b` are all chosen
before `v` and `q`.

The equation concerns the actual `C²` finite difference of the same `u`; no Schauder estimate,
limit, regularity gain or replacement potential is assumed or concluded.
-/
noncomputable section
namespace FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open Set MeasureTheory Metric
open scoped BigOperators ContDiff NNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Linearized finite-difference equations for one fixed `C²` function `u`, with all principal and
lower-order coefficient bounds chosen before the direction `v` and the step `q`. The direction's
norm remains in the ball-containment condition. No regularity gain is concluded. -/
theorem exists_uniform_linearized_differenceQuotient_equations
    (u W : E → ℝ) (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 2 W)
    (c : E) (r R : ℝ) (hrR : r ≤ R) (G0 : ℝ≥0)
    (hG : LipschitzOnWith G0 (gradient u) (closedBall c R))
    (C α : ℝ≥0) (hα : 0 < α) (hα1 : α ≤ 1)
    (hhol : ∀ i j, HolderOnWith C α (fun x => hessianMatrix u x i j) (closedBall c R))
    (hpos : ∀ x ∈ closedBall c R, (hessianMatrix u x).PosDef)
    (he : ∀ x ∈ closedBall c R, Real.log (hessianMatrix u x).det+u x=W (gradient u x)) :
    ∃ (L B Cb : ℝ≥0) (a b : ℝ), 0 < L ∧ 0 < B ∧ 0 < Cb ∧ 0 < a ∧ 0 < b ∧
      ∀ (v : E) (q : ℝ), q ≠ 0 → r+|q| * ‖v‖ ≤ R →
        ContDiff ℝ 2 (differenceQuotient u (q • v) q) ∧
        (∀ i j, HolderOnWith ((n : ℝ≥0)^2*L^2*C) α
          (fun x => averagedInverse (hessianMatrix u) (q • v) x i j)
          (closedBall c r)) ∧
        (∀ x ∈ closedBall c r, ∀ i j,
          |averagedInverse (hessianMatrix u) (q • v) x i j| ≤ L) ∧
        (∀ x ∈ closedBall c r, ∀ ξ : E,
          a*‖ξ‖^2 ≤ (∑ i, ∑ j, averagedInverse (hessianMatrix u)
            (q • v) x i j*ξ i*ξ j) ∧
          (∑ i, ∑ j, averagedInverse (hessianMatrix u)
            (q • v) x i j*ξ i*ξ j) ≤ b*‖ξ‖^2) ∧
        (∀ x ∈ closedBall c r, ∀ i, |segmentForcingCoefficient W (gradient u) (q • v) x i| ≤ B) ∧
        (∀ i, HolderOnWith Cb α (fun x => segmentForcingCoefficient W (gradient u) (q • v) x i)
          (closedBall c r)) ∧
        ∀ x ∈ closedBall c r,
          (∑ i, ∑ j, averagedInverse (hessianMatrix u) (q • v) x i j *
            hessianMatrix (differenceQuotient u (q • v) q) x j i) +
            differenceQuotient u (q • v) q x =
            ∑ i, segmentForcingCoefficient W (gradient u) (q • v) x i *
              fderiv ℝ (differenceQuotient u (q • v) q) x
                (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  obtain ⟨L,a,b,hL,ha,hb,hprincipal⟩ := exists_uniform_elliptic_differenceQuotient_equations
    u W hu c r R hrR C α hα hhol hpos he
  obtain ⟨B,Cb,hB,hCb,hforcing⟩ :=
    exists_uniform_segmentForcingCoefficient_bounds hW (gradient u) G0 c r R hrR hG α hα1
  refine ⟨L,B,Cb,a,b,hL,hB,hCb,ha,hb,?_⟩
  intro v q hq hstep
  obtain ⟨hC2,hholder,hentries,hell,heq⟩ := hprincipal v q hq hstep
  obtain ⟨hbcap,hbholder⟩ :=
    hforcing (q • v) (by simpa only [norm_smul,Real.norm_eq_abs] using hstep)
  refine ⟨hC2,hholder,hentries,hell,hbcap,hbholder,?_⟩
  intro x hx
  exact (heq x hx).trans
    (quotient_eq_sum_segmentForcingCoefficient hu (hW.of_le (by norm_num)) (q • v) q x)

end FunctionalInequalities.Analysis.BakryEmery
