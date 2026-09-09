import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Finite second moments of Borel laws -/

open MeasureTheory

namespace FunctionalInequalities.Probability

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The identity has finite second moment exactly when its extended squared norm has finite
lower integral. This includes real laws and needs no Hilbert or finite-dimensional structure. -/
theorem memLp_id_two_iff_lintegral_enorm_rpow_lt_top (ν : Measure E) :
    MemLp (id : E → E) 2 ν ↔ ∫⁻ x, ‖x‖ₑ ^ (2 : ℝ) ∂ν < ⊤ := by
  have h := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (f := (id : E → E)) (μ := ν)
    (p := 2) two_ne_zero ENNReal.ofNat_ne_top
  simp only [id_eq, ENNReal.toReal_ofNat] at h
  exact ⟨fun hν ↦ h.1 hν.2, fun hν ↦ ⟨aestronglyMeasurable_id, h.2 hν⟩⟩

end FunctionalInequalities.Probability
