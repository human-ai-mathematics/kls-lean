module

public import FunctionalInequalities.Analysis.Matrix.AveragedInverse
public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Coordinates

/-!
# Finite differences of a `C²` function and their log-determinant equations

Supporting Gilbarg–Trudinger, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, at the
actual `C²` input. For `differenceQuotient u d q x = (u (x + d) - u x) / q`:

* `contDiff_differenceQuotient`, `fderiv_differenceQuotient`, `hessianMatrix_differenceQuotient`:
  the finite difference is `C²`, and its first derivative and Hessian are the finite differences of
  those of `u`; the Hessian of `u` is not differentiated;
* `exists_uniform_differenceQuotient_equations`: if `log det Hess u + u = W (∇u)` with positive
  definite Hessian and a Hölder Hessian on `closedBall c R`, the Hessian of the actual quotient
  satisfies a local equation on `closedBall c r` with the SAME `averagedInverse` coefficients, whose
  cap and Hölder constant are chosen before the direction and the nonzero step (`r + |q| ‖v‖ ≤ R`).

The `W (∇u)` difference stays on the right-hand side. No lower ellipticity, `D³`, Schauder,
compactness or regularity gain is assumed or concluded.
-/

@[expose] public section
noncomputable section
namespace FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein
open Set MeasureTheory
open scoped ContDiff NNReal BigOperators Matrix.Norms.Elementwise

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Scalar-step finite difference along displacement `d`. -/
def differenceQuotient (u : E → ℝ) (d : E) (q : ℝ) (x : E) : ℝ :=
  (u (x + d) - u x) / q

/-- A finite difference of a C² function is C² for each fixed scalar step.
The regularity statement is also valid at zero scalar step under total division. -/
theorem contDiff_differenceQuotient {u : E → ℝ} (hu : ContDiff ℝ 2 u) (d : E) (q : ℝ) :
    ContDiff ℝ 2 (differenceQuotient u d q) :=
  ((hu.comp (contDiff_id.add contDiff_const)).sub hu).div_const q

/-- The actual first derivative of the finite difference, using only C². -/
theorem fderiv_differenceQuotient {u : E → ℝ} (hu : ContDiff ℝ 2 u) (d : E) (q : ℝ) :
    fderiv ℝ (differenceQuotient u d q) = fun x => q⁻¹ • (fderiv ℝ u (x + d) - fderiv ℝ u x) := by
  have he : differenceQuotient u d q = q⁻¹ • ((fun x => u (x + d)) - u) := by
    ext x
    simp only [differenceQuotient, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [he, fderiv_const_smul_field]
  ext x y
  have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hds : DifferentiableAt ℝ (fun y => u (y + d)) x :=
    (differentiableAt_comp_add_right d).mpr (hd (x + d))
  rw [Pi.smul_apply, fderiv_sub hds (hd x), fderiv_comp_add_right]

/-- The Hessian of the *same* finite difference is the scalar quotient of
its endpoint Hessians; this does not differentiate the Hessian of `u`. -/
theorem hessianMatrix_differenceQuotient {u : E → ℝ} (hu : ContDiff ℝ 2 u) (d : E) (q : ℝ)
    (x : E) (i j : Fin n) :
    hessianMatrix (differenceQuotient u d q) x i j =
      (hessianMatrix u (x + d) i j - hessianMatrix u x i j) / q := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ u) := hD.differentiable (by norm_num)
  have hds : HasFDerivAt (fun y => fderiv ℝ u (y + d)) (fderiv ℝ (fderiv ℝ u) (x + d)) x :=
    (hasFDerivAt_comp_add_right d).mpr (hd (x + d)).hasFDerivAt
  have hdiff := (hds.sub (hd x).hasFDerivAt).const_smul q⁻¹
  have h2 :
    fderiv ℝ (fderiv ℝ (differenceQuotient u d q)) x =
      q⁻¹ • (fderiv ℝ (fderiv ℝ u) (x + d) - fderiv ℝ (fderiv ℝ u) x) := by
    rw [fderiv_differenceQuotient hu d q]
    exact hdiff.fderiv
  change
    (fderiv ℝ (fderiv ℝ (differenceQuotient u d q)) x (EuclideanSpace.basisFun (Fin n) ℝ i))
        (EuclideanSpace.basisFun (Fin n) ℝ j) =
      ((fderiv ℝ (fderiv ℝ u) (x + d) (EuclideanSpace.basisFun (Fin n) ℝ i))
            (EuclideanSpace.basisFun (Fin n) ℝ j) -
          (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ i))
            (EuclideanSpace.basisFun (Fin n) ℝ j)) /
        q
  rw [h2]
  simp only [smul_apply, sub_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/--
Direction normalization is explicit: an arbitrary direction `v` permits steps `|q|‖v‖ ≤ R-r`. -/
private theorem shifted_mem_closedBall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c v : F) (r R q : ℝ) (hstep : r + |q| * ‖v‖ ≤ R) {x : F} (hx : x ∈ Metric.closedBall c r) :
    x + q • v ∈ Metric.closedBall c R := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hx ⊢
  have he : x + q • v - c = (x - c) + q • v := by abel
  rw [he]
  calc
    ‖(x - c) + q • v‖ ≤ ‖x - c‖ + ‖q • v‖ := norm_add_le _ _
    _ = ‖x - c‖ + |q| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ r + |q| * ‖v‖ := by linarith
    _ ≤ R := hstep

/-- A genuine local equation on the Hessian of the actual scalar-step
quotient, with the SAME explicit coefficients carrying a cap and a Hölder
constant chosen before direction and step. This is a precursor to GT17.16,
not its full linearization: the lower-order `W(∇u)` quotient is retained on
the right and no Schauder or compactness conclusion is asserted. -/
theorem exists_uniform_differenceQuotient_equations (u W : E → ℝ) (hu : ContDiff ℝ 2 u) (c : E)
    (r R : ℝ) (hrR : r ≤ R) (C α : ℝ≥0) (hα : 0 < α)
    (hhol : ∀ i j, HolderOnWith C α (fun x => hessianMatrix u x i j) (Metric.closedBall c R))
    (hpos : ∀ x ∈ Metric.closedBall c R, (hessianMatrix u x).PosDef)
    (he :
      ∀ x ∈ Metric.closedBall c R, Real.log (hessianMatrix u x).det + u x = W (gradient u x)) :
    ∃ L : ℝ≥0,
      0 < L ∧
        ∀ (v : E) (q : ℝ),
          q ≠ 0 →
            r + |q| * ‖v‖ ≤ R →
              ContDiff ℝ 2 (differenceQuotient u (q • v) q) ∧
                (∀ i j,
                    HolderOnWith ((n : ℝ≥0) ^ 2 * L ^ 2 * C) α
                      (fun x => averagedInverse (hessianMatrix u) (q • v) x i j)
                      (Metric.closedBall c r)) ∧
                  (∀ x ∈ Metric.closedBall c r,
                      ∀ i j, |averagedInverse (hessianMatrix u) (q • v) x i j| ≤ L) ∧
                    ∀ x ∈ Metric.closedBall c r,
                      (∑ i,
                            ∑ j,
                              averagedInverse (hessianMatrix u) (q • v) x i j *
                                hessianMatrix (differenceQuotient u (q • v) q) x j i) +
                          differenceQuotient u (q • v) q x =
                        (W (gradient u (x + q • v)) - W (gradient u x)) / q := by
  obtain ⟨L, hL, hcap, hcoeff⟩ :=
    exists_uniform_averagedInverse_holder (hessianMatrix u) (isCompact_closedBall c R) C α hα
      hhol hpos
  refine ⟨L, hL, ?_⟩
  intro v q _hq hstep
  have hsmall : Metric.closedBall c r ⊆ Metric.closedBall c R :=
    Metric.closedBall_subset_closedBall hrR
  have hshift : ∀ x ∈ Metric.closedBall c r, x + q • v ∈ Metric.closedBall c R := fun _ hx =>
    shifted_mem_closedBall c v r R q hstep hx
  refine ⟨contDiff_differenceQuotient hu (q • v) q, ?_, ?_, ?_⟩
  · have hc := hcoeff (q • v) (Metric.closedBall c r) hsmall hshift
    rwa [Fintype.card_fin] at hc
  · intro x hx i j
    exact abs_averagedInverse_le hcap (hsmall hx) (hshift x hx) i j
  · intro x hx
    have h :=
      logDet_quotient_eq_averagedInverse (H := hessianMatrix u) (u := u) (F := fun y =>
        W (gradient u y)) x (q • v) q (hpos x (hsmall hx)) (hpos (x + q • v) (hshift x hx))
        (he x (hsmall hx)) (he (x + q • v) (hshift x hx))
    have hsum :
      (∑ i,
          ∑ j,
            averagedInverse (hessianMatrix u) (q • v) x i j *
              hessianMatrix (differenceQuotient u (q • v) q) x j i) =
        ∑ i,
          ∑ j,
            averagedInverse (hessianMatrix u) (q • v) x i j *
              ((hessianMatrix u (x + q • v) - hessianMatrix u x) j i / q) :=
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by
          rw [hessianMatrix_differenceQuotient hu, Matrix.sub_apply]
    rw [hsum]
    exact h

end FunctionalInequalities.Analysis.BakryEmery
