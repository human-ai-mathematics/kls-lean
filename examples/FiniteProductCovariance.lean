module

public import FunctionalInequalities.Poincare.FiniteProduct.Tensorization
public import FunctionalInequalities.Poincare.Gaussian.Real
public import FunctionalInequalities.Probability.Transport

/-! A Gaussian product with variances 1, 0, 4, its empty boundary and covariance under translation.
-/

@[expose] public section
noncomputable section
namespace Examples.FiniteProductCovariance
open MeasureTheory
open FunctionalInequalities

private def variances : Fin 3 → NNReal := ![1, 0, 4]
private def factors (i : Fin 3) : Measure ℝ := ProbabilityTheory.gaussianReal (i : ℝ) (variances i)
private instance (i : Fin 3) : IsProbabilityMeasure (factors i) := by unfold factors; infer_instance

-- One factor is a Dirac law; tensorization still gives the exact constant 4.
example : Poincare.SmoothTest.constant (Poincare.SmoothTest.piMeasure factors) = (4 : ENNReal) := by
  rw [Poincare.SmoothTest.constant_pi_eq]
  norm_num [factors, Poincare.SmoothTest.constant_gaussianReal, variances, Matrix.cons_val_two]

example : factors 1 = Measure.dirac (1 : ℝ) := by
  simp [factors, variances, ProbabilityTheory.gaussianReal_zero_var]

example : Poincare.SmoothTest.constant
    (Poincare.SmoothTest.piMeasure (fun _ : Fin 0 => Measure.dirac (0 : ℝ))) = 0 :=
  Poincare.SmoothTest.constant_pi_empty

private def productLaw : ProbabilityMeasure (PiLp 2 (fun _ : Fin 3 => ℝ)) :=
  ⟨Poincare.SmoothTest.piMeasure factors, inferInstance⟩

-- Translate this same product law: the full covariance operator is unchanged.
example (c : PiLp 2 (fun _ : Fin 3 => ℝ)) :
    Covariance.operator (Probability.translateLaw productLaw c : Measure _) =
      Covariance.operator (Poincare.SmoothTest.piMeasure factors) :=
  Covariance.operator_translateLaw productLaw c
end Examples.FiniteProductCovariance
