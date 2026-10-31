module

public import FunctionalInequalities.KLS.Geometry.Perimeter.LocalLipschitzTests
public import FunctionalInequalities.Energy.LocalSlope.Gradient
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Independent full-signature clients for the locally Lipschitz test-class bridge on proper
spaces: the global Lipschitz bound of the truncation, the explicit approximating sequence, and
the perimeter bound. A genuine non-globally-Lipschitz input: `x ↦ x²` on `ℝ` is locally Lipschitz
but has no global Lipschitz constant, and for the two-atom law `(δ₀ + δ₁)/2` it coincides with
`1_{{1}}` on both atoms, so the constant sequence converges in `L¹` and the perimeter of `{1}` is
at most its slope integral, which equals `1`. Degenerate cases: the empty carrier, the zero
measure, and the empty set with the zero sequence. Proper-space scope only; no `L¹_loc`
convergence and no relaxation-infimum identification is claimed. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVLocalLipschitzAudit

open FunctionalInequalities
open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem truncationLipschitz (x₀ : X) (R : ℝ) {f : X → ℝ} (hf : LocallyLipschitz f) :
    ∃ K : ℝ≥0, LipschitzWith K (truncateFun x₀ R f) := by
  exact lipschitzWith_truncateFun_of_locallyLipschitz x₀ R hf

theorem explicitSequence (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X) {B : Set X}
    {f : ℕ → X → ℝ} (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => indicatorDistance ν (Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n)) B)
        atTop (𝓝 0) ∧
      liminf (fun n : ℕ => cost ν (Test.truncateOfLocallyLipschitz x₀ n (f n) (hf n))) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
  ⟨tendsto_indicatorDistance_truncateOfLocallyLipschitz ν x₀ hf hconv,
    liminf_cost_truncateOfLocallyLipschitz_le ν x₀ hf⟩

theorem existenceForm (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  exact exists_approximatingSequence_of_locallyLipschitz ν hf hconv

theorem perimeterBound (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, LocallyLipschitz (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  exact perimeter_le_liminf_of_locallyLipschitz ν hf hconv

/-- The globally Lipschitz bridge is the special case of a globally Lipschitz sequence. -/
theorem globalCase (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (f n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
  perimeter_le_liminf_of_locallyLipschitz ν (fun n => (hf n).choose_spec.locallyLipschitz) hconv

/-- Empty carrier: the bound holds for every sequence (all functions are locally Lipschitz). -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) (f : ℕ → Empty → ℝ) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  refine perimeter_le_liminf_of_locallyLipschitz ν (fun n x => x.elim) ?_
  simp [Measure.eq_zero_of_isEmpty ν]

/-- The zero measure: every locally Lipschitz sequence converges, and the bound gives zero
perimeter. -/
theorem zeroMeasure (B : Set ℝ) {f : ℕ → ℝ → ℝ} (hf : ∀ n, LocallyLipschitz (f n)) :
    perimeter (0 : Measure ℝ) B = 0 := by
  have h := perimeter_le_liminf_of_locallyLipschitz (0 : Measure ℝ) hf (B := B) (by simp)
  simp only [lintegral_zero_measure, liminf_const] at h
  exact le_antisymm h bot_le

/-- The empty set with the zero sequence: the bound is consistent with `perimeter_empty`. -/
theorem emptySetZero (ν : Measure X) [IsFiniteMeasure ν] :
    perimeter ν (∅ : Set X) ≤ liminf (fun _ : ℕ => (0 : ℝ≥0∞)) atTop := by
  have h := perimeter_le_liminf_of_locallyLipschitz ν (B := (∅ : Set X))
    (f := fun _ _ => (0 : ℝ)) (fun _ => LocallyLipschitz.const 0) (by simp)
  simpa [FunctionalInequalities.Energy.LocalSlope.apply_const] using h

/-- `x ↦ x²` is locally Lipschitz on `ℝ`. -/
theorem squareLocallyLipschitz : LocallyLipschitz (fun x : ℝ => x ^ 2) :=
  (by fun_prop : ContDiff ℝ 1 (fun x : ℝ => x ^ 2)).locallyLipschitz

/-- `x ↦ x²` has no global Lipschitz constant: at `x = K + 1` and `y = 0` the secant is
`K + 1 > K`. -/
theorem squareNotLipschitz : ¬ ∃ K : ℝ≥0, LipschitzWith K (fun x : ℝ => x ^ 2) := by
  rintro ⟨K, hK⟩
  have hK0 : (0 : ℝ) ≤ K := K.2
  have h : |((K : ℝ) + 1) ^ 2 - (0 : ℝ) ^ 2| ≤ K * |(K : ℝ) + 1 - 0| := by
    simpa [Real.dist_eq] using hK.dist_le_mul ((K : ℝ) + 1) 0
  rw [zero_pow two_ne_zero, sub_zero, sub_zero,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)] at h
  nlinarith

/-- The two-atom law `(δ₀ + δ₁)/2` on `ℝ`. -/
def twoAtom : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

instance : IsFiniteMeasure twoAtom := by
  refine ⟨?_⟩
  simp only [twoAtom, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 two_pos) (by norm_num)

theorem twoAtom_lintegral (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x ∂twoAtom = (2 : ℝ≥0∞)⁻¹ * (g 0 + g 1) := by
  simp [twoAtom, lintegral_smul_measure, lintegral_add_measure, lintegral_dirac, mul_add]

/-- `x²` equals `1_{{1}}` at both atoms, so the constant sequence converges in `L¹(twoAtom)`. -/
theorem square_indicator_dist :
    ∫⁻ x, ‖(fun x : ℝ => x ^ 2) x - ({1} : Set ℝ).indicator (1 : ℝ → ℝ) x‖ₑ ∂twoAtom = 0 := by
  rw [twoAtom_lintegral]
  simp

/-- The slope integral of `x²` for the two-atom law is `1`: the slope is `|2x|`, which is `0`
at `0` and `2` at `1`. -/
theorem square_slope_integral :
    ∫⁻ x, Energy.LocalSlope.apply (fun x : ℝ => x ^ 2) x ∂twoAtom = 1 := by
  have hslope : ∀ x : ℝ, Energy.LocalSlope.apply (fun x : ℝ => x ^ 2) x =
      ENNReal.ofReal |2 * x| := fun x => by
    rw [FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient _ _
      (by fun_prop : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) x)]
    have hg : gradient (fun x : ℝ => x ^ 2) x = 2 * x := by
      simpa using (hasDerivAt_pow 2 x).hasGradientAt.gradient
    rw [hg, Real.norm_eq_abs]
  rw [twoAtom_lintegral]
  simp only [hslope]
  norm_num
  rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- A non-globally-Lipschitz input: the perimeter of `{1}` for the two-atom law is at most the
slope integral of `x²`, namely `1`. -/
theorem squareBound :
    perimeter twoAtom ({1} : Set ℝ) ≤
        liminf (fun _ : ℕ => ∫⁻ x, Energy.LocalSlope.apply (fun x : ℝ => x ^ 2) x ∂twoAtom)
          atTop ∧
      perimeter twoAtom ({1} : Set ℝ) ≤ 1 := by
  have h := perimeter_le_liminf_of_locallyLipschitz twoAtom (B := ({1} : Set ℝ))
    (f := fun _ => fun x : ℝ => x ^ 2) (fun _ => squareLocallyLipschitz)
    (by simp only [square_indicator_dist]; exact tendsto_const_nhds)
  refine ⟨h, ?_⟩
  rw [liminf_const, square_slope_integral] at h
  exact h

#print axioms truncationLipschitz
#print axioms explicitSequence
#print axioms existenceForm
#print axioms perimeterBound
#print axioms globalCase
#print axioms emptyCarrier
#print axioms zeroMeasure
#print axioms emptySetZero
#print axioms squareLocallyLipschitz
#print axioms squareNotLipschitz
#print axioms square_indicator_dist
#print axioms square_slope_integral
#print axioms squareBound

end MetricBVLocalLipschitzAudit
