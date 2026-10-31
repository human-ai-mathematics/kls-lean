module

public import Lean
public import FunctionalInequalities.Analysis.IteratedDerivative.LocalHolder
public import FunctionalInequalities.Analysis.IteratedDerivative.Bootstrap.Step
public import FunctionalInequalities.KLS.BKL.Cumulant.Energy.Basic
public import FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
public import FunctionalInequalities.KLS.CEK.MomentRegularity.BootstrapThree
public import FunctionalInequalities.Analysis.BakryEmery.InverseHessianEnergy
public import FunctionalInequalities.Energy.Euclidean.WeakDerivative
public import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak
meta import Lean

/-! Legacy contracts through their shared producers, with every module that held them imported.
Checks finite-index scope, partial-operator domains, named parameters and removed-name absence.
-/

@[expose] public section

open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.Semigroup

example {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    (T : ρ → κ → ℝ) {β : ℝ}
    (hT : ∀ v : κ → ℝ, ∑ j, (∑ k, v k * T j k) ^ 2 ≤ β * ∑ k, v k ^ 2)
    (S : ι → κ → ℝ) :
    ∑ i, ∑ j, (∑ k, S i k * T j k) ^ 2 ≤ β * ∑ i, ∑ k, S i k ^ 2 :=
  Tensor.sum_sq_contract_le (b := β) T hT S

example {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    [CompleteSpace H₀] [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    (f : (adjointComp T).domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (Generated.apply T hT hd h (f : H₀) - (f : H₀)) + adjointComp T f‖ < ε :=
  Generated.generator_limit T hT hd f hε

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x v : E) : inner ℝ (gradient f x) v = fderiv ℝ f x v :=
  inner_gradient_left

example {t d α : ℝ} (ht : 0 ≤ t) (htd : t ≤ d) (hα1 : α ≤ 1) :
    t ≤ d ^ (1 - α) * t ^ α :=
  le_rpow_one_sub_mul_rpow
    (t := t) (d := d) (α := α) (ht := ht) (htd := htd) (hα1 := hα1)

run_cmd do
  let env ← Lean.getEnv
  for name in #[
      `FunctionalInequalities.Analysis.le_rpow_mul_rpow_of_le,
      `FunctionalInequalities.Analysis.clm_eq_sum_basisFun_smul_proj,
      `FunctionalInequalities.KLS.BKL.sum_sq_contract_le_rows,
      `FunctionalInequalities.Analysis.Semigroup.Generated.right_derivative_zero,
      `FunctionalInequalities.Analysis.opNorm_le_sum_sum_abs_basisFun,
      `FunctionalInequalities.Analysis.BakryEmery.gradient_pairing_eq_fderiv,
      `FunctionalInequalities.Energy.Euclidean.inner_gradient_eq_fderiv_apply] do
    if env.find? name |>.isSome then
      throwError "Removed duplicate declaration survives: {name}"

#print axioms FunctionalInequalities.Analysis.Tensor.sum_sq_contract_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.generator_limit
#print axioms FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy
#print axioms FunctionalInequalities.Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one
