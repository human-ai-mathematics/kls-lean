module

public import FunctionalInequalities.KLS.Klartag.TransportLaplacian

/-! Klartag arXiv:1309.2767v1, Lemma 4.3: restated with its exact hypotheses (smooth `ψ` with
positive definite Hessian, smooth `W`, `ρ` smooth on an open `K ⊇ ∇ψ(ℝⁿ)`, the transport equation
(50) everywhere) and the integration by parts identity defining the Laplacian (53)–(54). -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace KlartagAudit

theorem lemma_4_3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : Measure E)
    [m.IsAddHaarMeasure] {ψ W ρ u v : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hW : ContDiff ℝ ∞ W)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport u ∨ HasCompactSupport v)
    {K : Set E} (hK : IsOpen K) (hρ : ContDiffOn ℝ ∞ ρ K) (hRange : ∀ x, gradient ψ x ∈ K)
    (hEq : ∀ y, logDetHessian ψ (stdOrthonormalBasis ℝ E) y = -W y + ρ (gradient ψ y))
    (hPD : ∀ x, ∀ w : E, w ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x w w) :
    (∫ x, Real.exp (-W x) * (hessianInverseOperator ψ ρ u x * v x) ∂m) =
      -∫ x,
          Real.exp (-W x) *
            (∑ i,
              ∑ j,
                inverseHessianEntry ψ (stdOrthonormalBasis ℝ E) x i j *
                    fderiv ℝ u x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ v x (stdOrthonormalBasis ℝ E j)) ∂m :=
  FunctionalInequalities.Probability.MomentMeasure.integral_hessianInverseOperator_mul_eq_neg_weighted
    m hψ hW hu hv hc hK hρ hRange hEq hPD

#print axioms lemma_4_3

end KlartagAudit
