module

public import FunctionalInequalities.Analysis.MetricBV.Finite
public import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski

/-! Independent full-signature clients for Minkowski recovery of the metric BV perimeter: the
explicit measurable recovery sets `minkowskiRecoverySet (ν : Measure V) hB n` converge to `B` in
`L¹` with
Minkowski contents (and perimeters) converging to the perimeter of `B`, for every set of finite
perimeter under a probability law on a normed group. Boundary checks: the measurable-`B` form,
zero perimeter (empty set, measurable null sets, the whole space), dimension zero, and the
general lower bound, which forces infinite liminf contents at infinite perimeter (no recovery is
claimed there). No mass constraint, no pointwise `content = perimeter`, no Cheeger infimum. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVMinkowskiRecoveryAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

theorem lowerBound (ν : ProbabilityMeasure V) {B : Set V} {A : ℕ → Set V}
    (hA : ∀ n, MeasurableSet (A n))
    (hconv :
      Tendsto
        (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
        atTop (𝓝 0)) :
    perimeter (ν : Measure V) B ≤
      liminf (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (A n)) atTop := by
  exact perimeter_le_liminf_minkowskiContent (ν : Measure V) hA hconv

/-- The explicit sequence: measurability, per-term bounds and the three convergences. -/
theorem explicitSequence (ν : ProbabilityMeasure V) {B : Set V}
    (hB : perimeter (ν : Measure V) B < ⊤) :
    (∀ n, MeasurableSet (minkowskiRecoverySet (ν : Measure V) hB n)) ∧
      (∀ n,
          ∫⁻ x,
              ‖(minkowskiRecoverySet (ν : Measure V) hB n).indicator (1 : V → ℝ) x -
                  B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
            ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
        (∀ n,
            Isoperimetry.minkowskiContent (ν : Measure V)
                (minkowskiRecoverySet (ν : Measure V) hB n) ≤
              (perimeter (ν : Measure V) B + ENNReal.ofReal (1 / ((n : ℝ) + 1))) /
                  ENNReal.ofReal (1 - 2 * recoveryWidth n) +
                ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
          Tendsto
              (fun n =>
                ∫⁻ x,
                  ‖(minkowskiRecoverySet (ν : Measure V) hB n).indicator (1 : V → ℝ) x -
                      B.indicator 1 x‖ₑ ∂(ν : Measure V))
              atTop (𝓝 0) ∧
            Tendsto
                (fun n =>
                  Isoperimetry.minkowskiContent (ν : Measure V)
                    (minkowskiRecoverySet (ν : Measure V) hB n))
                atTop (𝓝 (perimeter (ν : Measure V) B)) ∧
              Tendsto
                (fun n => perimeter (ν : Measure V) (minkowskiRecoverySet (ν : Measure V) hB n))
                atTop (𝓝 (perimeter (ν : Measure V) B)) := by
  exact
    ⟨measurableSet_minkowskiRecoverySet (ν : Measure V) hB,
      lintegral_enorm_minkowskiRecoverySet_sub_le (ν : Measure V) hB,
      minkowskiContent_minkowskiRecoverySet_le (ν : Measure V) hB,
      tendsto_indicator_minkowskiRecoverySet (ν : Measure V) hB,
      tendsto_minkowskiContent_minkowskiRecoverySet (ν : Measure V) hB,
      tendsto_perimeter_minkowskiRecoverySet (ν : Measure V) hB⟩

theorem widths :
    (∀ n, 0 < recoveryWidth n) ∧ (∀ n, recoveryWidth n < 1 / 2) ∧
      Tendsto recoveryWidth atTop (𝓝 0) :=
  ⟨recoveryWidth_pos, recoveryWidth_lt_half, tendsto_recoveryWidth⟩

/-- The form for a measurable `B` with finite perimeter. -/
theorem measurableRecovery (ν : ProbabilityMeasure V) {B : Set V} (_hBm : MeasurableSet B)
    (hB : perimeter (ν : Measure V) B < ⊤) :
    ∃ A : ℕ → Set V, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (A n)) atTop
        (𝓝 (perimeter (ν : Measure V) B)) := by
  exact exists_minkowskiRecovery (ν : Measure V) hB

/-- Zero perimeter: recovery with contents tending to zero. -/
theorem zeroPerimeter (ν : ProbabilityMeasure V) {B : Set V}
    (h0 : perimeter (ν : Measure V) B = 0) :
    ∃ A : ℕ → Set V,
      (∀ n, MeasurableSet (A n)) ∧
        Tendsto
            (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
            atTop (𝓝 0) ∧
          Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (A n)) atTop (𝓝 0) := by
  have h :=
    exists_minkowskiRecovery (ν : Measure V)
      (h0 ▸ ENNReal.zero_lt_top : perimeter (ν : Measure V) B < ⊤)
  rwa [h0] at h

theorem emptySet (ν : ProbabilityMeasure V) :
    ∃ A : ℕ → Set V, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - (∅ : Set V).indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (A n)) atTop (𝓝 0) :=
  zeroPerimeter ν (perimeter_empty _)

/-- A measurable null set has zero perimeter (it is the `L¹` limit of `∅`), hence recovery with
vanishing contents. -/
theorem nullSet (ν : ProbabilityMeasure V) {B : Set V} (hBm : MeasurableSet B)
    (hnull : (ν : Measure V) B = 0) :
    ∃ A : ℕ → Set V,
      (∀ n, MeasurableSet (A n)) ∧
        Tendsto
            (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
            atTop (𝓝 0) ∧
          Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (A n)) atTop (𝓝 0) := by
  refine zeroPerimeter ν (le_antisymm ?_ bot_le)
  have hdist :
    ∫⁻ x, ‖(∅ : Set V).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) = 0 := by
    have hfun :
      (fun x => ‖(∅ : Set V).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ) = B.indicator 1 := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [hfun, lintegral_indicator_one hBm, hnull]
  have h :=
    perimeter_le_liminf_of_tendsto (ν : Measure V) (Bn := fun _ => (∅ : Set V)) (B := B)
      (fun _ => MeasurableSet.empty) (by simp only [hdist]; exact tendsto_const_nhds)
  simpa only [perimeter_empty, liminf_const] using h

/-- The whole space of a probability law has zero perimeter (constant one), hence recovery with
vanishing contents. -/
theorem fullSet (ν : ProbabilityMeasure V) :
    ∃ A : ℕ → Set V, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - (Set.univ : Set V).indicator 1 x‖ₑ
        ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (A n)) atTop (𝓝 0) := by
  refine zeroPerimeter ν (le_antisymm ?_ bot_le)
  have h := perimeter_le_liminf_of_lipschitz (ν : Measure V) (B := Set.univ)
    (f := fun _ _ => (1 : ℝ)) (fun _ => ⟨0, LipschitzWith.const 1⟩) (by simp)
  simpa only [FunctionalInequalities.Energy.LocalSlope.apply_const, lintegral_zero,
    liminf_const] using h

/-- Dimension zero: every set has zero perimeter. -/
theorem zeroDimensional (ν : ProbabilityMeasure (Fin 0 → ℝ)) (B : Set (Fin 0 → ℝ)) :
    ∃ A : ℕ → Set (Fin 0 → ℝ),
      (∀ n, MeasurableSet (A n)) ∧
        Tendsto
            (fun n =>
              ∫⁻ x,
                ‖(A n).indicator (1 : (Fin 0 → ℝ) → ℝ) x -
                    B.indicator 1 x‖ₑ ∂(ν : Measure (Fin 0 → ℝ)))
            atTop (𝓝 0) ∧
          Tendsto (fun n => Isoperimetry.minkowskiContent (ν : Measure (Fin 0 → ℝ)) (A n)) atTop
            (𝓝 0) :=
  zeroPerimeter ν (perimeter_eq_zero_of_subsingleton _ _)

/-- Infinite perimeter: no recovery is claimed, and every measurable `L¹` approximation has
contents with infinite liminf. -/
theorem infinitePerimeter (ν : ProbabilityMeasure V) {B : Set V}
    (htop : perimeter (ν : Measure V) B = ⊤) {A : ℕ → Set V} (hA : ∀ n, MeasurableSet (A n))
    (hconv : Tendsto (fun n => ∫⁻ x, ‖(A n).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ
      ∂(ν : Measure V)) atTop (𝓝 0)) :
    liminf (fun n => Isoperimetry.minkowskiContent (ν : Measure V) (A n)) atTop = ⊤ :=
  top_le_iff.mp (htop ▸ perimeter_le_liminf_minkowskiContent (ν : Measure V) hA hconv)

#print axioms lowerBound
#print axioms explicitSequence
#print axioms widths
#print axioms measurableRecovery
#print axioms zeroPerimeter
#print axioms emptySet
#print axioms nullSet
#print axioms fullSet
#print axioms zeroDimensional
#print axioms infinitePerimeter

end MetricBVMinkowskiRecoveryAudit
