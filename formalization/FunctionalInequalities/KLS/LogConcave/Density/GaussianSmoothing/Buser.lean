import FunctionalInequalities.KLS.Geometry.Cheeger.Stability
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Approximation
import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Poincare
import FunctionalInequalities.KLS.LogConcave.SmoothBuser

/-!
# Nonsmooth pi Buser through actual Gaussian convolution

The actual normalized Gaussian approximants have smooth convex potentials,
Poincare upper stability, and setwise convergence. A uniform smooth-model
Cheeger bound passes through the smooth-test inequality to the nonsmooth
source law. The final theorem transports this coordinate result to any
finite-dimensional affine support, including dimension zero.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

private def sequence (ν : ProbabilityMeasure V) (n : ℕ) : ProbabilityMeasure V :=
  smoothedProbabilityLaw ν ((n : ℝ) + 1) (by positivity)

private theorem sequence_set_tendsto (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ)
    (D : Set V) (hD : MeasurableSet D) :
    Tendsto (fun n => (sequence ν n : Measure V) D) atTop
      (𝓝 ((ν : Measure V) D)) := by
  have hs : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have h := (smoothedLaw_set_tendsto hρ hD).comp hs
  simpa only [Function.comp_def, sequence, smoothedProbabilityLaw, ProbabilityMeasure.coe_mk] using h

private theorem error_tendsto_zero :
    Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (2 * ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
  have hreal : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ) using 1
    · funext n
      field_simp
    · ring_nf
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal

private theorem sequence_poincare_bound (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ) (n : ℕ) :
    Poincare.LocalSlope.Intrinsic.constant (sequence ν n) ≤
      Poincare.LocalSlope.Intrinsic.constant ν +
        ENNReal.ofReal (1 / (2 * ((n : ℝ) + 1))) := by
  exact smoothedProbabilityLaw_literatureConstant_le ν hρ (by positivity)

private theorem sequence_poincare_eventually_le (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ)
    (C : NNReal) (hC : Poincare.LocalSlope.Intrinsic.constant ν < (C : ENNReal)) :
    ∀ᶠ n in atTop, Poincare.LocalSlope.Intrinsic.constant (sequence ν n) ≤
      (C : ENNReal) := by
  let L := Poincare.LocalSlope.Intrinsic.constant ν
  have hlim : Tendsto (fun n : ℕ => L +
      ENNReal.ofReal (1 / (2 * ((n : ℝ) + 1)))) atTop (𝓝 L) := by
    simpa only [zero_add, add_zero] using
      ((tendsto_const_nhds (x := L)).add error_tendsto_zero)
  filter_upwards [hlim.eventually_lt_const hC] with n hn
  exact (sequence_poincare_bound ν hρ n).trans hn.le

private theorem sequence_support_eq_univ (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ)
    (n : ℕ) : (sequence ν n : Measure V).support = Set.univ := by
  have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hden := normalizedDensity_isBorellDensity hρ hs
  have hac : (volume : Measure V) ≪ (sequence ν n : Measure V) := by
    change (volume : Measure V) ≪ smoothedLaw (ν : Measure V) ((n : ℝ) + 1)
    rw [← hden.withDensity_eq]
    apply withDensity_absolutelyContinuous'
    · exact (normalizedDensity_measurable hρ.measurable hs).ennreal_ofReal.aemeasurable
    · exact Filter.Eventually.of_forall fun x =>
        (ENNReal.ofReal_pos.mpr (normalizedDensity_pos hρ hs x)).ne'
  apply Set.eq_univ_of_forall
  intro x
  exact hac.support_mono (by simpa only [Measure.support_eq_univ] using Set.mem_univ x)

/-- A strict finite upper bound on the source literature constant gives the
pi Buser inequality at that finite bound for the nonsmooth source law. -/
theorem inv_minkowskiConstant_sq_le_pi_mul_of_borell
    (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ)
    (C : NNReal) (hC : 0 < C)
    (hLit : Poincare.LocalSlope.Intrinsic.constant ν < (C : ENNReal)) :
    (FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal (Real.pi * (C : ℝ)) := by
  let k : ENNReal := ENNReal.ofReal (Real.sqrt (Real.pi * (C : ℝ)))
  have hkpos : 0 < k := ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr
    (mul_pos Real.pi_pos (by exact_mod_cast hC)))
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hksq : k ^ 2 = ENNReal.ofReal (Real.pi * (C : ℝ)) := by
    dsimp [k]
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
      Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by exact_mod_cast hC.le))]
  have hbound : ∀ᶠ n in atTop, k⁻¹ ≤
      FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant (sequence ν n) := by
    filter_upwards [sequence_poincare_eventually_le ν hρ C hLit] with n hn
    have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hlc := smoothedProbabilityLaw_logConcave hρ hs
    have hi : (interior (sequence ν n : Measure V).support).Nonempty := by
      rw [sequence_support_eq_univ ν hρ n, interior_univ]
      exact Set.univ_nonempty
    have htilt : (sequence ν n : Measure V) =
        (volume : Measure V).tilted (-(potential ρ ((n : ℝ) + 1))) := by
      exact smoothedLaw_eq_tilted_potential hρ hs
    have hmain := FunctionalInequalities.KLS.LogConcave.inv_minkowskiConstant_sq_le_pi_mul
      volume hlc hi htilt (potential_contDiff_infty hρ hs)
      (potential_convex hρ hs) C hC hn (normalizedDensity_isBorellDensity hρ hs)
    have hinv : (FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant (sequence ν n))⁻¹
        ≤ k := by
      apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
      rwa [hksq]
    simpa using ENNReal.inv_le_inv.mpr hinv
  have hac : (ν : Measure V) ≪ volume := by
    rw [← hρ.withDensity_eq]
    exact withDensity_absolutelyContinuous _ _
  have hlow := FunctionalInequalities.KLS.Isoperimetry.le_minkowskiConstant_of_setwise_tendsto
    (sequence ν) ν hac k⁻¹ (by simpa using hkpos.ne')
      (sequence_set_tendsto ν hρ) hbound
  have hinv : (FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant ν)⁻¹ ≤ k := by
    simpa using ENNReal.inv_le_inv.mpr hlow
  exact (pow_le_pow_left₀ (by positivity) hinv 2).trans_eq hksq

/-- Exact nonsmooth pi Buser bound for a Borell probability law in its
full-dimensional coordinate space, including dimension zero. -/
theorem inv_minkowskiConstant_sq_le_pi_literature_of_borell
    (ν : ProbabilityMeasure V) {ρ : V → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity (ν : Measure V) volume ρ) :
    (FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant ν := by
  let L := Poincare.LocalSlope.Intrinsic.constant ν
  let X := (FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant ν)⁻¹ ^ 2
  by_cases htop : L = ⊤
  · have hpi : ENNReal.ofReal Real.pi ≠ 0 := (ENNReal.ofReal_pos.mpr Real.pi_pos).ne'
    change X ≤ ENNReal.ofReal Real.pi * L
    rw [htop, ENNReal.mul_top hpi]
    exact le_top
  let c : NNReal := L.toNNReal
  have hc : (c : ENNReal) = L := ENNReal.coe_toNNReal htop
  let C : ℕ → NNReal := fun n => c + 1 / ((n : NNReal) + 1)
  have hCpos (n : ℕ) : 0 < C n := by
    dsimp [C]
    positivity
  have hLC (n : ℕ) : L < (C n : ENNReal) := by
    rw [← hc]
    dsimp [C]
    exact_mod_cast (lt_add_of_pos_right c (by positivity : (0 : NNReal) < 1 / ((n : NNReal) + 1)))
  have hCseq : Tendsto C atTop (𝓝 c) := by
    simpa only [C, add_zero] using
      (tendsto_const_nhds (x := c)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal))
  have hCreal : Tendsto (fun n => (C n : ℝ)) atTop (𝓝 (c : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hCseq
  have hRHS : Tendsto (fun n => ENNReal.ofReal (Real.pi * (C n : ℝ))) atTop
      (𝓝 (ENNReal.ofReal Real.pi * L)) := by
    have h := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := Real.pi)).mul hCreal)
    convert h using 1
    rw [ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_coe_nnreal, hc]
  change X ≤ ENNReal.ofReal Real.pi * L
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hRHS
  intro n
  exact inv_minkowskiConstant_sq_le_pi_mul_of_borell ν hρ (C n) (hCpos n) (hLC n)

end FunctionalInequalities.KLS.LogConcave.GaussianSmoothing

namespace FunctionalInequalities.KLS.LogConcave
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The exact general log-concave pi Buser comparison, in every affine-support
dimension, including zero dimension and extended optimal constants. -/
theorem inverseScale_sq_le_pi_literature
    {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ := by
  let ν := Probability.intrinsicMeasure μ
  obtain ⟨ρ, hρ⟩ := hμ.exists_isBorellDensity volume
  have hmain := GaussianSmoothing.inv_minkowskiConstant_sq_le_pi_literature_of_borell ν hρ
  have hP : Poincare.LocalSlope.Intrinsic.constant ν =
      Poincare.LocalSlope.Intrinsic.constant μ := by
    rw [← (hμ.intrinsicMeasure).smoothTest_constant_eq_localSlope]
    exact (hμ.smoothTest_constant_eq_intrinsic_and_localSlope).2
  rw [hP] at hmain
  simpa only [Isoperimetry.inverseScale,
    Isoperimetry.constant_eq_minkowskiConstant_intrinsic] using hmain

end FunctionalInequalities.KLS.LogConcave
