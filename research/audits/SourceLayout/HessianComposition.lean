import FunctionalInequalities.Analysis.BakryEmery.Hessian.Composition
import Lean

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

namespace HessianCompositionAudit

/-- First-order composition is available before the inverse-Hessian PDE layer. -/
theorem exponent_chain {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          ∑ k, hessianMatrix u x j k *
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
  ae_fderiv_mongeAmpere_exponent hu hG hV

run_cmd do
  let env ← Lean.getEnv
  for name in #[`FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy,
      `FunctionalInequalities.Analysis.localLp_hessian_flux_trace_forcing] do
    if (env.find? name).isSome then
      throwError "Coordinate composition imported a PDE application: {name}"

#print axioms exponent_chain
end HessianCompositionAudit
