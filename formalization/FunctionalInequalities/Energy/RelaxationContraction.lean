import FunctionalInequalities.Energy.RelaxationLowerSemicontinuous

/-!
# Contraction bounds under sequential relaxation

This module isolates a generic mechanism for transferring an energy bound from concrete tests to
their sequential relaxation. The hypothesis is deliberately stated using the already-relaxed
energy at the transformed test: it does not require the transformation to preserve the concrete
test class.

Continuity of the transformation and lower semicontinuity of the relaxation then extend the bound
to every ambient point. No lattice, truncation, or Markov structure is asserted here.
-/

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy

namespace PreEnergy

universe u

section TopologicalSpace

variable {X : Type u} [TopologicalSpace X] (P : PreEnergy X)

/-- A transformation does not increase the relaxed energy of any realized concrete test. -/
def RelaxedContractionBound (C : X → X) : Prop :=
  ∀ f : P.Test,
    P.sequentialRelaxation (C (P.toAmbient f)) ≤ (P.energy f : ENNReal)

/-- Recovery sequences at transformed concrete tests imply the relaxed contraction bound. -/
theorem relaxedContractionBound_of_recovery_sequences {C : X → X}
    (h : ∀ f : P.Test, ∃ approximation : P.ApproximatingSequence (C (P.toAmbient f)),
      Tendsto (fun n ↦ (P.energy (approximation.1 n) : ENNReal)) atTop
        (𝓝 (P.energy f : ENNReal))) :
    P.RelaxedContractionBound C := by
  intro f
  obtain ⟨approximation, henergy⟩ := h f
  calc
    P.sequentialRelaxation (C (P.toAmbient f)) ≤ P.sequenceEnergy approximation :=
      P.sequentialRelaxation_le_sequenceEnergy approximation
    _ = (P.energy f : ENNReal) := henergy.liminf_eq

end TopologicalSpace

section PseudoMetricSpace

variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

/-- A continuous transformation satisfying the relaxed contraction bound on concrete tests does
not increase the sequential relaxation anywhere. -/
theorem RelaxedContractionBound.sequentialRelaxation_comp_le {C : X → X}
    (h : P.RelaxedContractionBound C) (hC : Continuous C) :
    ∀ x : X, P.sequentialRelaxation (C x) ≤ P.sequentialRelaxation x := by
  intro x
  rw [P.sequentialRelaxation_apply]
  refine le_iInf fun approximation ↦ ?_
  have hC_tendsto :
      Tendsto (fun n ↦ C (P.toAmbient (approximation.1 n))) atTop (𝓝 (C x)) :=
    (hC.tendsto x).comp approximation.2
  have hlsc_along : P.sequentialRelaxation (C x) ≤
      liminf (fun n ↦
        P.sequentialRelaxation (C (P.toAmbient (approximation.1 n)))) atTop := by
    refine le_of_forall_lt fun c hc ↦ ?_
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    have hd_eventually : ∀ᶠ n in atTop,
        d < P.sequentialRelaxation (C (P.toAmbient (approximation.1 n))) :=
      hC_tendsto.eventually
        (P.lowerSemicontinuous_sequentialRelaxation (C x) d hd)
    exact hcd.trans_le
      (le_liminf_of_le (by isBoundedDefault)
        (hd_eventually.mono fun _ hn ↦ hn.le))
  calc
    P.sequentialRelaxation (C x) ≤ liminf (fun n ↦
        P.sequentialRelaxation (C (P.toAmbient (approximation.1 n)))) atTop := hlsc_along
    _ ≤ liminf (fun n ↦ (P.energy (approximation.1 n) : ENNReal)) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n ↦ h (approximation.1 n))
    _ = P.sequenceEnergy approximation := rfl

end PseudoMetricSpace

end PreEnergy

end FunctionalInequalities.Energy
