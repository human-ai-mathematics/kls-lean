module

public import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic

/-! Independent full-signature client for Haar-a.e. Borell density continuity. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace BorellDensityContinuityAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem ae_continuous {ν m : Measure V} [m.IsAddHaarMeasure]
    {ρ : V → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity ν m ρ) :
    ∀ᵐ x ∂m, ContinuousAt ρ x :=
  hρ.ae_continuous

end BorellDensityContinuityAudit

#print axioms BorellDensityContinuityAudit.ae_continuous
