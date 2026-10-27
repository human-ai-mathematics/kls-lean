import FunctionalInequalities.Probability.ExponentialMoments.Norm
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.MeasureTheory.Function.L2Space

/-! # Temperate functions in L2 under exponential moments

The source is a second-countable real normed space with its Borel structure;
the target is an arbitrary real normed space. No Hilbert, finite-dimensional
or probability normalization hypothesis is needed.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace FunctionalInequalities.Probability

section TemperateL2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/-- Temperate functions belong to L2 under all norm exponential moments. -/
theorem memLp_two_of_hasTemperateGrowth {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → H}
    (hf : f.HasTemperateGrowth) : MemLp f 2 μ := by
  obtain ⟨k, C, hb⟩ := hf.2 0
  have hb' : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := fun x => by
    simpa only [norm_iteratedFDeriv_zero] using hb x
  refine (memLp_two_iff_integrable_sq_norm hf.1.continuous.aestronglyMeasurable).2 ?_
  refine integrable_of_norm_le_pow μ hexp (hf.1.continuous.aestronglyMeasurable.norm.pow 2)
    (C := C ^ 2) (k := 2 * k) (fun x => ?_)
  have h0 : 0 ≤ ‖f x‖ := norm_nonneg _
  have hsq : ‖f x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := pow_le_pow_left₀ h0 (hb' x) 2
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖f x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ k) ^ 2 := hsq
    _ = C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by ring


end TemperateL2

end FunctionalInequalities.Probability
