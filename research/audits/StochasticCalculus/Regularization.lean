import LevyStochCalc.Martingale.CadlagModification
import Lean

/-! Independent clients for the synchronized external regularization interfaces.

The martingale and submartingale conclusions retain a right-continuous filtration.
The expectation premise is used only for the submartingale result. The original
LevyStochCalc client keeps its existing right-continuity-in-measure interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace StochasticCalculusRegularizationAudit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

example (hX : Martingale X 𝓕 μ) : IsRealQuasimartingale 𝓕 X μ :=
  hX.isRealQuasimartingale

example [𝓕.IsRightContinuous] (hX : Martingale X 𝓕 μ) (t : ℝ≥0) :
    rightContModifReal X t =ᵐ[μ] X t :=
  hX.rightContModifReal_ae_eq t

example [𝓕.IsRightContinuous] (hX : Martingale X 𝓕 μ) (t : ℝ≥0) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  hX.cadlagModifReal_ae_eq t

example [𝓕.IsRightContinuous] (hX : Submartingale X 𝓕 μ) (t : ℝ≥0)
    (hE : Tendsto (fun s ↦ ∫ ω, X s ω ∂μ) (𝓝[>] t) (𝓝 (∫ ω, X t ω ∂μ))) :
    cadlagModifReal X t =ᵐ[μ] X t :=
  hX.cadlagModifReal_ae_eq t hE

example [𝓕.IsRightContinuous] (hX : Martingale X 𝓕 μ)
    (hrc : ∀ t, TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Adapted 𝓕 Y ∧ (∀ t, Y t =ᵐ[μ] X t) ∧
      ∀ᵐ ω ∂μ, IsCadlag (fun t ↦ Y t ω) :=
  LevyStochCalc.Martingale.exists_adapted_ae_isCadlag_nnreal hX hrc

run_cmd do
  let env ← Lean.getEnv
  for name in #[`ProbabilityTheory.uniformIntegrable_of_countable,
      `ProbabilityTheory.rightContModif_ae_eq_of_integral_tendsto,
      `ProbabilityTheory.cadlagModif_ae_eq_of_continuousWithinAt_integral,
      `MeasureTheory.Martingale.cadlagModif_ae_eq] do
    if env.contains name then
      throwError "Obsolete upstream interface is still present: {name}"
  if env.header.moduleNames.contains `BrownianMotion.StochasticIntegral.UniformIntegrable then
    throwError "The unrelated upstream UniformIntegrable module entered the selected closure"

end StochasticCalculusRegularizationAudit
