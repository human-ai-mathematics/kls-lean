import FunctionalInequalities.KLS.Geometry.SmoothDomain.GaussGreen
import FunctionalInequalities.KLS.Geometry.Perimeter.Mollification

/-! # Boundary formula and norm bound for mollified indicators

No coarea, Sard or perimeter-recovery dependency. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution RealInnerProductSpace

namespace FunctionalInequalities.KLS

universe u

namespace SmoothDomain

section Measure

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- The gradient of the mollified indicator `η ⋆ 𝟙_U` at `x` is minus the boundary integral of
`η(x - ·)` against the outward normal.  Taking norms and `‖ν‖ = 1` gives
`SmoothDomain.enorm_gradient_mollified_le`. -/
theorem gradient_mollifiedIndicator_eq (U : SmoothDomain V) (φ : ContDiffBump (0 : V)) (x : V) :
    gradient (U.mollifiedIndicator φ volume) x =
      -∫ y in frontier U.carrier, φ.normed volume (x - y) • U.outwardNormal y
        ∂(surfaceMeasure V) := by
  set η : V → ℝ := φ.normed volume with hη
  set f : V → ℝ := U.carrier.indicator 1 with hf
  have hcs : HasCompactSupport η := φ.hasCompactSupport_normed
  have hcd : ContDiff ℝ ∞ η := φ.contDiff_normed
  have hcontgrad : Continuous fun y => gradient η y := by
    have : Continuous (fderiv ℝ η) := hcd.continuous_fderiv (by simp)
    exact (InnerProductSpace.toDual ℝ V).symm.continuous.comp this
  -- the reflected test function
  set ηx : V → ℝ := fun y => η (x - y) with hηx
  have hcdx : ContDiff ℝ 1 ηx := (hcd.of_le (by simp)).comp (contDiff_const.sub contDiff_id)
  have hcsx : HasCompactSupport ηx := by
    have := hcs.comp_homeomorph (Homeomorph.subLeft x)
    simpa [hηx, Function.comp_def] using this
  have hgradx : ∀ y : V, gradient ηx y = -gradient η (x - y) := by
    intro y
    have hd : HasFDerivAt ηx (-(fderiv ℝ η (x - y))) y := by
      have h1 : HasFDerivAt (fun z : V => x - z) (-(ContinuousLinearMap.id ℝ V)) y :=
        (hasFDerivAt_id y).const_sub x
      have h2 : HasFDerivAt η (fderiv ℝ η (x - y)) (x - y) :=
        (hcd.differentiable (by simp) (x - y)).hasFDerivAt
      have h3 := h2.comp y h1
      rw [show (fderiv ℝ η (x - y)).comp (-(ContinuousLinearMap.id ℝ V))
          = -(fderiv ℝ η (x - y)) by ext v; simp] at h3
      exact h3
    refine (InnerProductSpace.toDual ℝ V).injective ?_
    rw [map_neg, toDual_gradient (𝕜 := ℝ), toDual_gradient (𝕜 := ℝ), hd.fderiv]
  -- the convolution derivative
  have hD : HasFDerivAt (U.mollifiedIndicator φ volume)
      ((f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR V, volume] fderiv ℝ η) x) x := by
    rw [U.mollifiedIndicator_eq φ volume]
    exact hcs.hasFDerivAt_convolution_right _ (U.locallyIntegrable_indicator volume) (hcd.of_le (by simp)) x
  have hcsgrad : HasCompactSupport (fun y => gradient η y) := by
    have h1 : HasCompactSupport (fderiv ℝ η) := hcs.fderiv ℝ
    have h2 := h1.comp_left (g := fun L : V →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ V).symm L)
      (by simp)
    simpa [gradient, Function.comp_def] using h2
  have hint : IntegrableOn (fun t => gradient η (x - t)) U.carrier volume :=
    (Continuous.integrable_of_hasCompactSupport
      (hcontgrad.comp (continuous_const.sub continuous_id))
      (hcsgrad.comp_homeomorph (Homeomorph.subLeft x))).integrableOn
  have hkey : gradient (U.mollifiedIndicator φ volume) x
      = ∫ t in U.carrier, gradient η (x - t) := by
    refine ext_inner_right ℝ fun v => ?_
    rw [inner_gradient_left, hD.fderiv,
      convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) (U.locallyIntegrable_indicator volume) (hcs.fderiv ℝ)
        (hcd.continuous_fderiv (by simp)) x v, convolution_def]
    have hind : ∀ t : V, (ContinuousLinearMap.lsmul ℝ ℝ) (f t) (fderiv ℝ η (x - t) v)
        = U.carrier.indicator (fun t => ⟪v, gradient η (x - t)⟫) t := by
      intro t
      by_cases ht : t ∈ U.carrier
      · simp only [hf, Set.indicator_of_mem ht, Pi.one_apply,
          ContinuousLinearMap.lsmul_apply, smul_eq_mul, one_mul]
        rw [real_inner_comm, inner_gradient_left]
      · simp [hf, Set.indicator_of_notMem ht]
    rw [integral_congr_ae (Eventually.of_forall hind), integral_indicator U.measurableSet,
      integral_inner hint v]
    exact real_inner_comm _ _
  have hC2 := U.setIntegral_gradient_eq_integral_smul_outwardNormal hcdx hcsx
  have hneg : ∫ y in U.carrier, gradient ηx y = -∫ t in U.carrier, gradient η (x - t) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun U.measurableSet fun y _ => hgradx y
  rw [hneg] at hC2
  rw [hkey, ← hC2, neg_neg]

/-- Gauss–Green consequence for smooth domains: the gradient of the mollified indicator at `x` is
minus the boundary integral of the outward normal against `η(x - ·)`, hence its norm is at most the
boundary integral of `η(x - ·)` against the surface measure.  This is the "distributional
derivative of `𝟙_U` is its oriented surface measure" step of the Blueprint, in the only form
the proof uses. -/
theorem enorm_gradient_mollified_le (U : SmoothDomain V) (φ : ContDiffBump (0 : V)) (x : V) :
    ‖gradient (U.mollifiedIndicator φ volume) x‖ₑ ≤
      ∫⁻ y in frontier U.carrier, ENNReal.ofReal (φ.normed volume (x - y))
        ∂(surfaceMeasure V) := by
  have hcs : HasCompactSupport (fun y : V => φ.normed volume (x - y)) :=
    φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  have hint := U.integrableOn_smul_outwardNormal
    (φ.continuous_normed.comp (continuous_const.sub continuous_id)) hcs
  rw [U.gradient_mollifiedIndicator_eq, enorm_neg, ← ofReal_norm]
  calc
    ENNReal.ofReal ‖∫ y in frontier U.carrier,
        φ.normed volume (x - y) • U.outwardNormal y ∂(surfaceMeasure V)‖
        ≤ ENNReal.ofReal (∫ y in frontier U.carrier,
          ‖φ.normed volume (x - y) • U.outwardNormal y‖ ∂(surfaceMeasure V)) :=
      ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
    _ = ∫⁻ y in frontier U.carrier,
        ‖φ.normed volume (x - y) • U.outwardNormal y‖ₑ ∂(surfaceMeasure V) :=
      ofReal_integral_norm_eq_lintegral_enorm hint
    _ = _ := by
      apply setLIntegral_congr_fun isClosed_frontier.measurableSet
      intro y hy
      dsimp only
      rw [← ofReal_norm, norm_smul, U.norm_outwardNormal hy, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed (x - y))]

end Measure

end SmoothDomain

end FunctionalInequalities.KLS
