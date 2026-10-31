module

public import FunctionalInequalities.Analysis.SmoothDomain.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! # Smooth mollification of domain indicators -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace FunctionalInequalities.KLS

universe u

namespace SmoothDomain

section Measure

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The mollified indicator `η ⋆ 𝟙_U` for a normalized bump `η = φ.normed m`. -/
def mollifiedIndicator (U : SmoothDomain V) (φ : ContDiffBump (0 : V)) (m : Measure V)
    (x : V) : ℝ :=
  ∫ y, φ.normed m (x - y) * U.carrier.indicator 1 y ∂m

omit [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The indicator of a smooth domain is bounded and measurable, hence locally integrable. -/
theorem locallyIntegrable_indicator (U : SmoothDomain V) (m : Measure V)
    [IsLocallyFiniteMeasure m] : LocallyIntegrable (U.carrier.indicator (1 : V → ℝ)) m := by
  intro x
  obtain ⟨s, hs, hsfin⟩ := m.finiteAt_nhds x
  refine ⟨s, hs, Measure.integrableOn_of_bounded hsfin.ne
    (measurable_one.indicator U.isOpen.measurableSet).aestronglyMeasurable (M := 1) ?_⟩
  filter_upwards with y
  by_cases hy : y ∈ U.carrier
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

omit [MeasurableSpace V] [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- The indicator of a smooth domain takes values in `[0, 1]`. -/
private theorem indicator_mem_Icc (U : SmoothDomain V) (y : V) :
    U.carrier.indicator (1 : V → ℝ) y ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hy : y ∈ U.carrier
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

omit [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The mollified indicator is the convolution of the indicator with the normalized bump. -/
theorem mollifiedIndicator_eq (U : SmoothDomain V) (φ : ContDiffBump (0 : V))
    (m : Measure V) :
    U.mollifiedIndicator φ m
      = (U.carrier.indicator (1 : V → ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] φ.normed m := by
  funext x
  rw [convolution_def]
  simp only [mollifiedIndicator, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact integral_congr_ae (Eventually.of_forall fun t ↦ mul_comm _ _)

omit [CompleteSpace V] in
/-- The mollified indicator is globally `C^∞`, globally Lipschitz, and takes values in `[0, 1]`. -/
theorem mollifiedIndicator_contDiff_lipschitz_mem_Icc (U : SmoothDomain V)
    (φ : ContDiffBump (0 : V)) (m : Measure V) [m.IsAddHaarMeasure] :
    ContDiff ℝ ∞ (U.mollifiedIndicator φ m) ∧
      (∃ K : ℝ≥0, LipschitzWith K (U.mollifiedIndicator φ m)) ∧
      ∀ x, U.mollifiedIndicator φ m x ∈ Set.Icc (0 : ℝ) 1 := by
  set f : V → ℝ := U.carrier.indicator 1 with hfdef
  set η : V → ℝ := φ.normed m with hηdef
  have hloc : LocallyIntegrable f m := U.locallyIntegrable_indicator m
  have hcs : HasCompactSupport η := φ.hasCompactSupport_normed
  have hcd : ContDiff ℝ ∞ η := φ.contDiff_normed
  have hηnn : ∀ t, 0 ≤ η t := fun t ↦ φ.nonneg_normed t
  have hintη : Integrable η m := φ.integrable_normed
  have hfmeas : Measurable f := measurable_one.indicator U.isOpen.measurableSet
  have hconv : U.mollifiedIndicator φ m
      = f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] η := U.mollifiedIndicator_eq φ m
  refine ⟨by rw [hconv]; exact hcs.contDiff_convolution_right _ hloc hcd, ?_, ?_⟩
  · -- globally Lipschitz, with constant the total mass of `‖∇η‖`
    have hcsd : HasCompactSupport (fderiv ℝ η) := hcs.fderiv (𝕜 := ℝ)
    have hcontd : Continuous (fderiv ℝ η) := hcd.continuous_fderiv (by simp)
    have hintd : Integrable (fun t ↦ ‖fderiv ℝ η t‖) m :=
      (hcontd.integrable_of_hasCompactSupport hcsd).norm
    set C : ℝ := ∫ t, ‖fderiv ℝ η t‖ ∂m with hC
    have hC0 : 0 ≤ C := integral_nonneg fun t ↦ norm_nonneg _
    have hD : ∀ x : V, HasFDerivAt (U.mollifiedIndicator φ m)
        ((f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR V, m] fderiv ℝ η) x) x := by
      intro x
      rw [hconv]
      exact hcs.hasFDerivAt_convolution_right _ hloc (hcd.of_le (by simp)) x
    refine ⟨⟨C, hC0⟩, lipschitzWith_of_nnnorm_fderiv_le
      (fun x ↦ (hD x).differentiableAt) fun x ↦ ?_⟩
    have hbound : ‖fderiv ℝ (U.mollifiedIndicator φ m) x‖ ≤ C := by
      rw [(hD x).fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v ↦ ?_
      rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hloc hcsd hcontd x v,
        convolution_eq_swap]
      have hbd : Integrable (fun t ↦ ‖fderiv ℝ η t‖ * ‖v‖) m := hintd.mul_const _
      refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun t ↦ ?_)).trans_eq ?_
      · have h1 : |f (x - t)| ≤ 1 := by
          rw [abs_of_nonneg (U.indicator_mem_Icc (x - t)).1]
          exact (U.indicator_mem_Icc (x - t)).2
        have h2 : |fderiv ℝ η t v| ≤ ‖fderiv ℝ η t‖ * ‖v‖ := by
          simpa [Real.norm_eq_abs] using (fderiv ℝ η t).le_opNorm v
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
        calc |f (x - t)| * |fderiv ℝ η t v| ≤ 1 * (‖fderiv ℝ η t‖ * ‖v‖) :=
              mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = ‖fderiv ℝ η t‖ * ‖v‖ := one_mul _
      · rw [integral_mul_const]
    exact hbound
  · -- values in `[0, 1]`
    intro x
    have hswap : U.mollifiedIndicator φ m x = ∫ t, f (x - t) * η t ∂m := by
      rw [hconv, convolution_eq_swap]
      simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hint : Integrable (fun t ↦ f (x - t) * η t) m := by
      refine hintη.mono' ((hfmeas.comp (measurable_const.sub measurable_id)).mul
        φ.continuous_normed.measurable).aestronglyMeasurable ?_
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (U.indicator_mem_Icc (x - t)).1,
        abs_of_nonneg (hηnn t)]
      exact mul_le_of_le_one_left (hηnn t) (U.indicator_mem_Icc (x - t)).2
    refine ⟨?_, ?_⟩
    · rw [hswap]
      exact integral_nonneg fun t ↦ mul_nonneg (U.indicator_mem_Icc (x - t)).1 (hηnn t)
    · rw [hswap]
      calc ∫ t, f (x - t) * η t ∂m ≤ ∫ t, η t ∂m :=
            integral_mono hint hintη fun t ↦
              mul_le_of_le_one_left (hηnn t) (U.indicator_mem_Icc (x - t)).2
        _ = 1 := φ.integral_normed

end Measure

end SmoothDomain

end FunctionalInequalities.KLS
