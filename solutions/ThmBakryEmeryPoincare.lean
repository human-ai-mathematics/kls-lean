module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Curvature
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lean certificate: `thm:bakry-emery-poincare`

Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (Grundlehren 348,
Springer 2014), Corollary 4.8.2: if `dμ = e^{-W} dx` is a probability measure on `ℝⁿ` with
`∇∇W ≥ ρ Id` for some `ρ > 0`, then `μ` satisfies the Poincaré inequality `P(1/ρ)` of
Definition 4.2.1, `Var_μ(f) ≤ ρ⁻¹ ∫ |∇f|² dμ`.

The certificate states the reviewed stronger form (`⇑`): `V` is any finite-dimensional real inner
product space with its Lebesgue measure (`EuclideanSpace ℝ (Fin n)` is `ℝⁿ`, `n = 0` included),
`W` is only `C²`, and `ν = volume.tilted (-W)` normalizes `e^{-W}` itself, so `∫ e^{-W} = 1` is
not required. The conclusion bounds the literature Poincaré optimum, the least constant valid for
every locally Lipschitz `f ∈ L²(ν)` of finite squared local-slope energy; this test class contains
the smooth functions, and `smoothTest` restates the inequality on smooth tests. Log-concavity and
full-dimensional support of `ν` are derived from the hypotheses, not assumed.

`gaussianLaw` constructs the scaled Gaussian `volume.tilted (-(ρ/2)‖·‖²)` as a probability measure
from Mathlib's Gaussian integrability, and `gaussian` applies the certificate to it with every
hypothesis discharged, so the hypotheses are jointly satisfiable in every dimension. Sharpness of
`1/ρ`, the general Markov-triple framework and Proposition 4.8.1 are not claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open scoped ContDiff RealInnerProductSpace

namespace Solutions.ThmBakryEmeryPoincare

section Quadratic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The scaled quadratic potential `W y = ρ/2 ‖y‖²`. -/
def potential (ρ : ℝ) : V → ℝ := fun y => ρ / 2 * ‖y‖ ^ 2

theorem contDiff_potential (ρ : ℝ) : ContDiff ℝ 2 (potential (V := V) ρ) := by
  have hconst : ContDiff ℝ 2 (fun _ : V => ρ / 2) := contDiff_const
  exact hconst.mul (contDiff_norm_sq ℝ)

theorem fderiv_potential_apply (ρ : ℝ) (y w : V) :
    fderiv ℝ (potential ρ) y w = ρ * ⟪y, w⟫ := by
  have h : HasFDerivAt (potential ρ) ((ρ / 2) • (2 • innerSL ℝ y)) y :=
    ((hasFDerivAt_id y).norm_sq).const_mul (ρ / 2)
  rw [h.fderiv]
  change ρ / 2 * (2 • (innerSL ℝ y) w) = ρ * ⟪y, w⟫
  rw [nsmul_eq_mul, innerSL_apply_apply]
  ring

/-- The Hessian form of the scaled quadratic potential is exactly `ρ ‖v‖²`. -/
theorem bilinearIteratedFDerivTwo_potential (ρ : ℝ) (x v : V) :
    bilinearIteratedFDerivTwo ℝ (potential ρ) x v v = ρ * ‖v‖ ^ 2 := by
  rw [Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply (contDiff_potential ρ) x v v]
  have hfun : (fun y : V => fderiv ℝ (potential ρ) y v) = fun y => ρ * ⟪y, v⟫ :=
    funext fun y => fderiv_potential_apply ρ y v
  have hinner : HasFDerivAt (fun y : V => ρ * ⟪y, v⟫) (ρ • innerSL ℝ v) x := by
    have h : HasFDerivAt (fun y : V => ⟪v, y⟫) (innerSL ℝ v) x := (innerSL ℝ v).hasFDerivAt
    simpa only [real_inner_comm v] using h.const_mul ρ
  rw [hfun, hinner.fderiv]
  change ρ * ⟪v, v⟫ = ρ * ‖v‖ ^ 2
  rw [real_inner_self_eq_norm_sq]

end Quadratic

section Law

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- **Bakry–Gentil–Ledoux (2014), Corollary 4.8.2**: for `ν = volume.tilted (-W)` with `W` of
class `C²` and `∇∇W ≥ ρ Id`, `ρ > 0`, the literature Poincaré constant satisfies
`C_P(ν) ≤ 1/ρ`. -/
theorem certificate {ν : ProbabilityMeasure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : ContDiff ℝ 2 W) {ρ : ℝ}
    (hρ : 0 < ρ) (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ :=
  LogConcave.literatureConstant_le_inv_of_eq_tilted hνW hW hρ hH

/-- The same corollary as the inequality `P(1/ρ)` on smooth tests:
`Var_ν(f) ≤ ρ⁻¹ ∫ ‖∇f‖² dν` for every `C^∞` function `f ∈ L²(ν)` with `‖∇f‖ ∈ L²(ν)`. -/
theorem smoothTest {ν : ProbabilityMeasure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : ContDiff ℝ 2 W) {ρ : ℝ}
    (hρ : 0 < ρ) (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v) :
    Poincare.SmoothTest.Holds (ν : Measure V) ρ⁻¹ :=
  LogConcave.smoothTest_holds_inv_of_eq_tilted hνW hW hρ hH

section Gaussian

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The Gaussian weight `e^{-ρ/2 ‖y‖²}` is Lebesgue integrable. -/
theorem integrable_exp_neg_potential {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun y : V => Real.exp ((-potential ρ) y)) := by
  have hb : 0 < ((ρ / 2 : ℝ) : ℂ).re := by simpa using half_pos hρ
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [potential, Complex.norm_exp, ← Complex.ofReal_pow]

/-- The scaled Gaussian law `volume.tilted (-(ρ/2)‖·‖²)`, constructed as a probability measure. -/
def gaussianLaw {ρ : ℝ} (hρ : 0 < ρ) : ProbabilityMeasure V :=
  ⟨(volume : Measure V).tilted (-potential ρ), isProbabilityMeasure_tilted
    (integrable_exp_neg_potential hρ)⟩

/-- Nonvacuity witness: the certificate applies to the constructed Gaussian law, with every
hypothesis discharged, in every finite-dimensional real inner product space. -/
theorem gaussian {ρ : ℝ} (hρ : 0 < ρ) :
    Poincare.LocalSlope.Intrinsic.constant (gaussianLaw (V := V) hρ) ≤ ENNReal.ofReal ρ⁻¹ ∧
      Poincare.SmoothTest.Holds ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)
        ρ⁻¹ :=
  ⟨certificate rfl (contDiff_potential ρ) hρ fun x v =>
      (bilinearIteratedFDerivTwo_potential ρ x v).ge,
    smoothTest rfl (contDiff_potential ρ) hρ fun x v =>
      (bilinearIteratedFDerivTwo_potential ρ x v).ge⟩

end Gaussian

/-- Typed application on `ℝⁿ`, every `n`. -/
example (n : ℕ) {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ}
    (hνW : (ν : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-W))
    (hW : ContDiff ℝ 2 W) {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ :=
  certificate hνW hW hρ hH

/-- The constructed Gaussian on `ℝ³`. -/
example : Poincare.LocalSlope.Intrinsic.constant
    (gaussianLaw (V := EuclideanSpace ℝ (Fin 3)) (ρ := 2) two_pos) ≤ ENNReal.ofReal 2⁻¹ :=
  (gaussian two_pos).1

/-- The constructed Gaussian in dimension zero. -/
example : Poincare.LocalSlope.Intrinsic.constant
    (gaussianLaw (V := EuclideanSpace ℝ (Fin 0)) (ρ := 1) one_pos) ≤ ENNReal.ofReal 1⁻¹ :=
  (gaussian one_pos).1

/--
info: 'Solutions.ThmBakryEmeryPoincare.certificate' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Solutions.ThmBakryEmeryPoincare.certificate

/--
info: 'Solutions.ThmBakryEmeryPoincare.smoothTest' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Solutions.ThmBakryEmeryPoincare.smoothTest

/--
info: 'Solutions.ThmBakryEmeryPoincare.gaussian' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Solutions.ThmBakryEmeryPoincare.gaussian

end Law

end Solutions.ThmBakryEmeryPoincare
