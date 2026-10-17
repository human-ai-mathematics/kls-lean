import FunctionalInequalities.KLS.Geometry.Perimeter.LocalLipschitzTests
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-! Independent full-signature clients for the bounded-ball `L¹` bridge: locally Lipschitz
sequences converging to `1_B` in `L¹(ν)` on every closed ball, on a proper space with a finite
measure, yield an actual approximating test sequence and the perimeter bound. The premise is
genuinely local: a perturbation `u n + (1/(n+1)) · h` by an arbitrary locally Lipschitz `h`
(no integrability of `h` on the whole space) satisfies it whenever `u n` does, since `h` is
bounded on each compact closed ball. The finite-measure clamp lemma is exercised without
properness, the compact-set corollary through the proved implication, and the empty carrier, the
zero measure and the empty set. No global `L¹` convergence is assumed anywhere. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVLocalL1Audit

open FunctionalInequalities
open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

section Generic

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The clamp lemma needs a finite measure, not properness. -/
theorem clampLemma (ν : Measure X) [IsFiniteMeasure ν] (x₀ : X) {B : Set X} {f : ℕ → X → ℝ}
    (hloc : ∀ r : ℝ, 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖clampUnit (f n x) - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0) := by
  exact tendsto_lintegral_clampUnit_of_forall_closedBall ν x₀ hloc

omit [BorelSpace X] in
theorem compactFromBalls (ν : Measure X) {g : ℕ → X → ℝ≥0∞}
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r →
      Tendsto (fun n => ∫⁻ x in Metric.closedBall x₀ r, g n x ∂ν) atTop (𝓝 0))
    {K : Set X} (hK : IsCompact K) :
    Tendsto (fun n => ∫⁻ x in K, g n x ∂ν) atTop (𝓝 0) := by
  exact tendsto_setLIntegral_of_isCompact ν hloc hK

variable [ProperSpace X]

theorem existenceForm (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    ∃ g : ApproximatingSequence ν B,
      liminf (fun n => cost ν (g.1 n)) atTop ≤
        liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  exact exists_approximatingSequence_of_locallyLipschitz_of_forall_closedBall ν hf hloc

theorem perimeterBound (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  exact perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall ν hf hloc

theorem compactCorollary (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {f : ℕ → X → ℝ}
    (hf : ∀ n, LocallyLipschitz (f n))
    (hloc : ∀ K : Set X, IsCompact K → Tendsto (fun n =>
      ∫⁻ x in K, ‖f n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0)) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop := by
  exact perimeter_le_liminf_of_locallyLipschitz_of_forall_isCompact ν hf hloc

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
/-- Sums with scalar multiples of locally Lipschitz functions are locally Lipschitz (direct from
the definition, on the intersected neighbourhoods). -/
theorem locallyLipschitz_add_const_mul {u h : X → ℝ} (hu : LocallyLipschitz u)
    (hh : LocallyLipschitz h) (c : ℝ) : LocallyLipschitz (fun x => u x + c * h x) := by
  intro x
  obtain ⟨K₁, t₁, ht₁, h₁⟩ := hu x
  obtain ⟨K₂, t₂, ht₂, h₂⟩ := hh x
  refine ⟨K₁ + ‖c‖₊ * K₂, t₁ ∩ t₂, Filter.inter_mem ht₁ ht₂,
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  have e1 := h₁.dist_le_mul a ha.1 b hb.1
  have e2 := h₂.dist_le_mul a ha.2 b hb.2
  rw [Real.dist_eq] at e1 e2 ⊢
  calc |u a + c * h a - (u b + c * h b)| = |(u a - u b) + c * (h a - h b)| := by congr 1; ring
    _ ≤ |u a - u b| + |c| * |h a - h b| := by rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ K₁ * dist a b + |c| * (K₂ * dist a b) :=
        add_le_add e1 (mul_le_mul_of_nonneg_left e2 (abs_nonneg c))
    _ = ((K₁ + ‖c‖₊ * K₂ : ℝ≥0) : ℝ) * dist a b := by
        push_cast
        rw [Real.norm_eq_abs]
        ring

/-- A genuinely local premise: perturbing a locally convergent sequence by `(n + 1)⁻¹ · h` with
`h` locally Lipschitz but of no assumed integrability keeps convergence on every closed ball,
because `h` is bounded on the compact ball; the perimeter bound follows for the perturbed
sequence. -/
theorem perturbedSequence (ν : Measure X) [IsFiniteMeasure ν] {B : Set X} {u : ℕ → X → ℝ}
    (hu : ∀ n, LocallyLipschitz (u n))
    (hloc : ∀ (x₀ : X) (r : ℝ), 0 < r → Tendsto (fun n =>
      ∫⁻ x in Metric.closedBall x₀ r, ‖u n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν) atTop (𝓝 0))
    {h : X → ℝ} (hh : LocallyLipschitz h) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply
      (fun x => u n x + ((n : ℝ) + 1)⁻¹ * h x) x ∂ν) atTop := by
  refine perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall ν
    (fun n => locallyLipschitz_add_const_mul (hu n) hh _) fun x₀ r hr => ?_
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall x₀ r).exists_bound_of_continuousOn hh.continuous.continuousOn
  have hmeas : MeasurableSet (Metric.closedBall x₀ r) := Metric.isClosed_closedBall.measurableSet
  have hzero : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * ENNReal.ofReal C *
      ν (Metric.closedBall x₀ r)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (ENNReal.Tendsto.mul_const (ENNReal.Tendsto.mul_const h1
      (Or.inr ENNReal.ofReal_ne_top)) (Or.inr (measure_ne_top ν _)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (hloc x₀ r hr).add hzero) (fun _ => zero_le) fun n => ?_
  have hc : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  calc ∫⁻ x in Metric.closedBall x₀ r,
        ‖u n x + ((n : ℝ) + 1)⁻¹ * h x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν
      ≤ ∫⁻ x in Metric.closedBall x₀ r, (‖u n x - B.indicator (1 : X → ℝ) x‖ₑ +
          ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * ENNReal.ofReal C) ∂ν :=
        setLIntegral_mono' hmeas fun x hx => by
          rw [show u n x + ((n : ℝ) + 1)⁻¹ * h x - B.indicator (1 : X → ℝ) x =
            (u n x - B.indicator (1 : X → ℝ) x) + ((n : ℝ) + 1)⁻¹ * h x by ring]
          refine (enorm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
          gcongr
          simpa [Real.norm_eq_abs] using hC x hx
    _ = ∫⁻ x in Metric.closedBall x₀ r, ‖u n x - B.indicator (1 : X → ℝ) x‖ₑ ∂ν +
          ENNReal.ofReal ((n : ℝ) + 1)⁻¹ * ENNReal.ofReal C * ν (Metric.closedBall x₀ r) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]

end Generic

/-- Empty carrier: the bound holds for every sequence; the local premise is vacuous. -/
theorem emptyCarrier (ν : Measure Empty) (B : Set Empty) (f : ℕ → Empty → ℝ) :
    perimeter ν B ≤ liminf (fun n => ∫⁻ x, Energy.LocalSlope.apply (f n) x ∂ν) atTop :=
  perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall ν (fun _ x => x.elim)
    fun x₀ _ _ => x₀.elim

/-- The zero measure on `ℝ`: every locally Lipschitz sequence satisfies the local premise. -/
theorem zeroMeasure (B : Set ℝ) {f : ℕ → ℝ → ℝ} (hf : ∀ n, LocallyLipschitz (f n)) :
    perimeter (0 : Measure ℝ) B = 0 := by
  have h := perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall (0 : Measure ℝ) hf
    (B := B) (fun _ _ _ => by simp)
  simp only [lintegral_zero_measure, liminf_const] at h
  exact le_antisymm h bot_le

/-- The empty set with the zero sequence. -/
theorem emptySet {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] :
    perimeter ν (∅ : Set X) ≤ liminf (fun _ : ℕ => (0 : ℝ≥0∞)) atTop := by
  have h := perimeter_le_liminf_of_locallyLipschitz_of_forall_closedBall ν (B := (∅ : Set X))
    (f := fun _ _ => (0 : ℝ)) (fun _ => LocallyLipschitz.const 0) (fun _ _ _ => by simp)
  simpa [Energy.LocalSlope.apply_const] using h

#print axioms clampLemma
#print axioms compactFromBalls
#print axioms existenceForm
#print axioms perimeterBound
#print axioms compactCorollary
#print axioms locallyLipschitz_add_const_mul
#print axioms perturbedSequence
#print axioms emptyCarrier
#print axioms zeroMeasure
#print axioms emptySet

end MetricBVLocalL1Audit
