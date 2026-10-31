module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Curvature
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Audit: Bakry–Gentil–Ledoux (2014), Corollary 4.8.2 in the heat model, without ergodicity

This client checks the window-2 interfaces of the BGL Corollary 4.8.2 route:

* **Regression.** The conditional interface `literatureConstant_le_inv_of_tendsto` is restated
  verbatim and still elaborates, and the ergodicity it assumes is now supplied by
  `tendsto_norm_center_apply`.
* **Kernel and constants.** `closedWeightedOperator_eq_zero_iff` identifies `ker T̄` with the
  constants; it is applied to the constant one. Centered constants are zero.
* **Endpoint.** `literatureConstant_le_inv_of_eq_tilted` and `smoothTest_holds_inv_of_eq_tilted`
  are instantiated on `ℝⁿ` for every `n`, including `n = 0`. The Dirichlet-domain form
  `norm_center_sq_le_inv_mul` is instantiated in the heat model for every `u ∈ D(T̄)`.
* **Scaled Gaussian.** For `W x = ρ ‖x‖² / 2` (Hessian form `ρ ‖v‖²`, proved below) the endpoint
  gives `C_P ≤ 1/ρ` for the law `volume.tilted (-W)`, whose normalization is automatic. The client
  takes the probability law as a hypothesis and does not construct it. Elaboration does not prove
  that `1/ρ` is sharp.

Nothing here certifies the paper: the corollary's coverage needs a reviewed certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities FunctionalInequalities.KLS
  FunctionalInequalities.KLS.LogConcave FunctionalInequalities.Analysis.Semigroup
open scoped ContDiff RealInnerProductSpace

namespace BakryEmeryErgodicityAudit

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic potential is smooth. -/
theorem contDiff_half_mul_norm_sq (ρ : ℝ) : ContDiff ℝ 2 (fun y : E => ρ / 2 * ‖y‖ ^ 2) := by
  have hconst : ContDiff ℝ 2 (fun _ : E => ρ / 2) := contDiff_const
  have hnorm : ContDiff ℝ 2 (fun y : E => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  exact hconst.mul hnorm

/-- First derivative of the quadratic potential: `D W(y) w = ρ ⟪y, w⟫`. -/
theorem fderiv_half_mul_norm_sq (ρ : ℝ) (y w : E) :
    fderiv ℝ (fun y : E => ρ / 2 * ‖y‖ ^ 2) y w = ρ * ⟪y, w⟫ := by
  have h :
      HasFDerivAt (fun x : E => ρ / 2 * ‖x‖ ^ 2)
        ((ρ / 2) • (2 • innerSL ℝ y)) y :=
    ((hasFDerivAt_id y).norm_sq).const_mul (ρ / 2)
  have heval : (innerSL ℝ y) w = ⟪y, w⟫ := by
    rfl
  calc
    fderiv ℝ (fun x : E => ρ / 2 * ‖x‖ ^ 2) y w =
        (((ρ / 2) • (2 • innerSL ℝ y)) : E →L[ℝ] ℝ) w := by
          exact congrArg (fun L : E →L[ℝ] ℝ => L w) h.fderiv
    _ = ρ * ⟪y, w⟫ := by
      simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, heval]
      ring

/-- Hessian form of the quadratic potential: `D²W(x)(v, v) = ρ ‖v‖²`. -/
theorem bilinearIteratedFDerivTwo_half_mul_norm_sq (ρ : ℝ) (x v : E) :
    bilinearIteratedFDerivTwo ℝ (fun y : E => ρ / 2 * ‖y‖ ^ 2) x v v = ρ * ‖v‖ ^ 2 := by
  calc
    bilinearIteratedFDerivTwo ℝ (fun y : E => ρ / 2 * ‖y‖ ^ 2) x v v =
        fderiv ℝ
          (fun y : E => fderiv ℝ (fun z : E => ρ / 2 * ‖z‖ ^ 2) y v) x v := by
      exact
        FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
          (contDiff_half_mul_norm_sq ρ) x v v
    _ = fderiv ℝ (fun y : E => ρ * ⟪y, v⟫) x v := by
      have hfun :
          (fun y : E => fderiv ℝ (fun z : E => ρ / 2 * ‖z‖ ^ 2) y v) =
            (fun y : E => ρ * ⟪y, v⟫) := by
        funext y
        exact fderiv_half_mul_norm_sq ρ y v
      rw [hfun]
    _ = ρ * ‖v‖ ^ 2 := by
      have heq : (fun y : E => ⟪y, v⟫) = (innerSL ℝ v) := by
        funext y
        rw [real_inner_comm]
        rfl
      have hinner : HasFDerivAt (fun y : E => ⟪y, v⟫) (innerSL ℝ v) x := by
        rw [heq]
        exact (innerSL ℝ v).hasFDerivAt
      have hmul := hinner.const_mul ρ
      calc
        fderiv ℝ (fun y : E => ρ * ⟪y, v⟫) x v =
            ((ρ • (innerSL ℝ v)) : E →L[ℝ] ℝ) v := by
          exact congrArg (fun L : E →L[ℝ] ℝ => L v) hmul.fderiv
        _ = ρ * ‖v‖ ^ 2 := by
          change ρ * ⟪v, v⟫ = ρ * ‖v‖ ^ 2
          rw [real_inner_self_eq_norm_sq]

end Quadratic

section Constants

/-- The constant one equals the constant given by its mean, as the kernel identification needs. -/
theorem constant_one_eq_const_mean {α : Type*} [MeasurableSpace α] (ν : ProbabilityMeasure α) :
    (L2.const ν 1 : Lp ℝ 2 (ν : Measure α)) =
      L2.const ν (L2.mean ν (L2.const ν 1 : Lp ℝ 2 (ν : Measure α))) := by
  rw [L2.mean_const]

end Constants

section Model

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)

include hν hi hνU hU in
/-- Regression: the conditional interface is unchanged, and its hypothesis is now a theorem. -/
theorem regression_of_tendsto {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ :=
  literatureConstant_le_inv_of_tendsto m hν hi hνU hU hρ hH
    (fun u => tendsto_norm_center_apply m hν hi hνU hU (u : Lp ℝ 2 (ν : Measure V)))

include hνU hU in
/-- Kernel identification applied to the constant one. -/
theorem closedWeightedOperator_one_eq_zero' :
    hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨L2.const ν 1, one_mem_domain_closedWeightedOperator m _ hν hi⟩ = 0 :=
  (closedWeightedOperator_eq_zero_iff m hν hi hνU hU _).2 (constant_one_eq_const_mean ν)

include hν hi hνU hU in
/-- The Dirichlet-domain form on the whole form domain. -/
theorem dirichlet_form {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
      ρ⁻¹ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 :=
  norm_center_sq_le_inv_mul m hν hi hνU hU hρ hH u

end Model

section Endpoint

/-- Endpoint on `ℝⁿ`, every `n` (including `n = 0` below). -/
theorem endpoint_euclidean (n : ℕ) {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ}
    (hνW : (ν : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-W))
    (hW : ContDiff ℝ 2 W) {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ ∧
      Poincare.SmoothTest.Holds (ν : Measure (EuclideanSpace ℝ (Fin n))) ρ⁻¹ :=
  ⟨literatureConstant_le_inv_of_eq_tilted hνW hW hρ hH,
    smoothTest_holds_inv_of_eq_tilted hνW hW hρ hH⟩

/-- Dimension zero. -/
example {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))} {W : EuclideanSpace ℝ (Fin 0) → ℝ}
    (hνW : (ν : Measure (EuclideanSpace ℝ (Fin 0))) =
      (volume : Measure (EuclideanSpace ℝ (Fin 0))).tilted (-W))
    (hW : ContDiff ℝ 2 W) {ρ : ℝ} (hρ : 0 < ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ W x v v) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ :=
  (endpoint_euclidean 0 hνW hW hρ hH).1

/-- Scaled Gaussian: for `W x = ρ ‖x‖² / 2` the endpoint gives `C_P ≤ 1/ρ`. -/
theorem gaussian (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hνW : (ν : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-fun y => ρ / 2 * ‖y‖ ^ 2)) :
    Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal ρ⁻¹ :=
  (endpoint_euclidean n hνW (contDiff_half_mul_norm_sq ρ) hρ
    (fun x v => (bilinearIteratedFDerivTwo_half_mul_norm_sq ρ x v).ge)).1

end Endpoint

end BakryEmeryErgodicityAudit

#print axioms BakryEmeryErgodicityAudit.contDiff_half_mul_norm_sq
#print axioms BakryEmeryErgodicityAudit.fderiv_half_mul_norm_sq
#print axioms BakryEmeryErgodicityAudit.bilinearIteratedFDerivTwo_half_mul_norm_sq
#print axioms BakryEmeryErgodicityAudit.regression_of_tendsto
#print axioms BakryEmeryErgodicityAudit.constant_one_eq_const_mean
#print axioms BakryEmeryErgodicityAudit.closedWeightedOperator_one_eq_zero'
#print axioms BakryEmeryErgodicityAudit.dirichlet_form
#print axioms BakryEmeryErgodicityAudit.endpoint_euclidean
#print axioms BakryEmeryErgodicityAudit.gaussian
#print axioms FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_eq_zero_iff
#print axioms
  FunctionalInequalities.KLS.LogConcave.inner_center_eq_zero_of_closedWeightedOperator_eq_zero
#print axioms FunctionalInequalities.KLS.LogConcave.tendsto_norm_center_apply
#print axioms FunctionalInequalities.KLS.LogConcave.norm_center_sq_le_inv_mul
#print axioms FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv
#print axioms FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv_of_eq_tilted
#print axioms FunctionalInequalities.KLS.LogConcave.smoothTest_holds_inv_of_eq_tilted
#print axioms FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv_of_tendsto
#print axioms FunctionalInequalities.KLS.LogConcave.eq_const_mean_of_closedWeightedOperator_eq_zero
#print axioms FunctionalInequalities.KLS.LogConcave.integral_mul_fderiv_eq_neg_integral_mul_inner
#print axioms FunctionalInequalities.KLS.LogConcave.logConcave_of_eq_tilted
#print axioms FunctionalInequalities.KLS.LogConcave.interior_support_nonempty_of_eq_tilted
#print axioms
  FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_integral_mul_fderiv_eq_zero
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_apply_of_inner_eq_zero
