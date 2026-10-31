module

public import FunctionalInequalities.KLS.Klartag.DualLaplacian

/-! Klartag arXiv:1309.2767v1, Lemma 5.1: restated with its exact hypotheses (`K` open, `φ` smooth
on
`K` with positive definite Hessian there, `ρ` smooth on `K`, the dual transport equation (66) on
`K`, one of the smooth tests compactly supported in `K`) and the integration by parts identity
identifying the operator (67) with the Laplacian of `(K, ∇²φ, e^{-ρ} dx)`. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace KlartagAudit

theorem lemma_5_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
    [m.IsAddHaarMeasure] {K : Set E} (hK : IsOpen K) {φ ρ u v : E → ℝ} (hφ : ContDiffOn ℝ ∞ φ K)
    (hρ : ContDiffOn ℝ ∞ ρ K)
    (hPD : ∀ y ∈ K, ∀ w : E, w ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y w w)
    (hEq : ∀ y ∈ K, logDetHessian φ (stdOrthonormalBasis ℝ E) y = ⟪y, gradient φ y⟫ - φ y - ρ y)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hc : (HasCompactSupport u ∧ tsupport u ⊆ K) ∨ (HasCompactSupport v ∧ tsupport v ⊆ K)) :
    (∫ x in K,
        (∑ i,
            ∑ j,
              inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                  fderiv ℝ u x (stdOrthonormalBasis ℝ E i) *
                fderiv ℝ v x (stdOrthonormalBasis ℝ E j)) *
          Real.exp (-ρ x) ∂m) =
      -∫ x in K,
          v x *
              nondivergenceOperator (fun y => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y)
                (fun y i => ⟪y, stdOrthonormalBasis ℝ E i⟫) u x *
            Real.exp (-ρ x) ∂m :=
  FunctionalInequalities.Probability.MomentMeasure.integral_inverseHessian_gradient_mul_eq_neg_laplacian
    m hK hφ hρ hPD hEq hu hv hc

#print axioms lemma_5_1

end KlartagAudit
