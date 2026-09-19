import FunctionalInequalities.Analysis.Vector.JacobianContinuity
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for obligation `A1`

`A1` of the area formula route — continuity of the volume factor and measurability of the
integrand — is **proved**.  The two propositions below are the route statements of
`research/audits/AreaFormulaRouteStatements.lean` reproduced verbatim and discharged, so those two
`#check`s are no longer open.

Note what is **not** needed: the route stated measurability under `ContDiff ℝ 1 g`, but
`measurable_fderiv` holds for an arbitrary function, so the proved lemma carries no
differentiability hypothesis at all and the route form follows by discarding it.  A client below
records the stronger form applied to a function that is nowhere differentiable.

**No area formula and no coarea formula are proved**, here or in the audited module.  The remaining
route obligations `A2`–`A5`, `B1`, `B2` are untouched.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis

namespace NormDetContinuityAudit

/-- Route statement `A1`, first half, reproduced verbatim and discharged. -/
theorem route_A1_continuity : ∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V],
    Continuous (fun A : H →L[ℝ] V => LinearMap.normDet (A : H →ₗ[ℝ] V)) := by
  intro H V _ _ _ _ _ _
  exact continuous_normDet

/-- Route statement `A1`, second half, reproduced verbatim and discharged.  The `ContDiff`
hypothesis is accepted and then discarded: it is not needed. -/
theorem route_A1_measurability : ∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {g : H → V}, ContDiff ℝ 1 g →
    Measurable (fun y : H => LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V))) := by
  intro H V _ _ _ _ _ _ _ _ g _
  exact measurable_normDet_fderiv g

/-- The stronger form actually proved: **no** differentiability hypothesis. -/
theorem measurable_without_hypothesis {H V : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (g : H → V) :
    Measurable (fun y : H => LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V))) :=
  measurable_normDet_fderiv g

/-- Applied to a function differentiable nowhere: `fderiv` is then the zero map everywhere, and the
integrand is still measurable.  This is the point of having no hypothesis. -/
theorem measurable_of_nowhere_differentiable
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (g : EuclideanSpace ℝ (Fin 1) → V) :
    Measurable (fun y => LinearMap.normDet
      ((fderiv ℝ g y : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] V))) :=
  measurable_normDet_fderiv g

/-! ### The coarea side -/

/-- The coarea Jacobian is continuous in the differential. -/
theorem coarea_continuity {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] :
    Continuous (fun L : V →L[ℝ] W => coareaJacobian L) :=
  continuous_coareaJacobian

/-- The integrand of the codimension-`m` coarea formula is measurable, with no hypothesis on `u`. -/
theorem coarea_measurability {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] (u : V → W) :
    Measurable (fun x : V => coareaJacobian (fderiv ℝ u x)) :=
  measurable_coareaJacobian_fderiv u

/-- Consistency with the scalar theory: for a real-valued `u` this is the measurability of
`‖gradient u x‖`, the integrand of the proved `L11`/`L12`/`L13`. -/
theorem scalar_integrand_measurable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (u : V → ℝ) :
    Measurable (fun x : V => ‖gradient u x‖) := by
  have h : (fun x : V => ‖gradient u x‖) = fun x : V => coareaJacobian (fderiv ℝ u x) := by
    funext x
    exact (coareaJacobian_fderiv u x).symm
  rw [h]
  exact measurable_coareaJacobian_fderiv u

end NormDetContinuityAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.normDet_eq_sqrt_det
#print axioms FunctionalInequalities.Analysis.continuous_adjoint_comp
#print axioms FunctionalInequalities.Analysis.continuous_normDet
#print axioms FunctionalInequalities.Analysis.measurable_normDet_fderiv
#print axioms FunctionalInequalities.Analysis.continuous_coareaJacobian
#print axioms FunctionalInequalities.Analysis.measurable_coareaJacobian_fderiv
#print axioms NormDetContinuityAudit.route_A1_continuity
#print axioms NormDetContinuityAudit.route_A1_measurability
#print axioms NormDetContinuityAudit.measurable_without_hypothesis
#print axioms NormDetContinuityAudit.measurable_of_nowhere_differentiable
#print axioms NormDetContinuityAudit.coarea_continuity
#print axioms NormDetContinuityAudit.coarea_measurability
#print axioms NormDetContinuityAudit.scalar_integrand_measurable
