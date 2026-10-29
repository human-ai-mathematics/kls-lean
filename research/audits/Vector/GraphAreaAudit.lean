import FunctionalInequalities.Analysis.Vector.Graph.Area
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the codimension-`m` area formula

**The codimension-`m` area formula for `C¹` graphs is proved**, in both the raw and the normalized
Hausdorff convention.  Route obligation **`B2`** of
`research/audits/Graph/AreaFormulaRouteStatements.lean` is reproduced verbatim below and
discharged.

**A correction to the route statements.**  Obligation `B1` as written in
`research/audits/Graph/AreaFormulaRouteStatements.lean` pairs the **raw** `μH[k]` on the left with
**Lebesgue** measure on the right.  Those two normalizations differ:
`Analysis.hausdorffMeasure_finrank_eq_smul_volume` gives `μH[k] = (2^k / ω_k) • volume` on the
parameter space, and `2^k = ω_k` only for `k ≤ 1`.  So that statement is **not** what is proved
here, and for `k ≥ 2` it is false as written.  The two correct pairings are proved below: raw with
raw (`corrected_B1`), and normalized with Lebesgue (`route_B2`, which is the form the program
actually consumes and which the route stated correctly).  The route statements file is left
**byte-unchanged**; the correction is recorded here.

What this is and is **not**: it is the area formula for a **graph** in arbitrary codimension.  It is
**not** the Federer area formula for an arbitrary injective `C¹` parametrization.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

namespace VectorGraphAreaAudit

/-- **Route statement `B2` of `AreaFormulaRouteStatements.lean`, reproduced verbatim and
discharged.**  The normalized `k`-dimensional measure of a `C¹` graph over a measurable parameter
set is the Lebesgue integral of `√det (1 + Dγᵀ Dγ)`. -/
theorem route_B2 : ∀ {H K V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V), (∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) →
    ∀ {γ : H → K} {s : Set H}, ContDiff ℝ 1 γ → MeasurableSet s →
    KLS.hausdorffNormalized V (Module.finrank ℝ H) ((fun y => ι y + κ (γ y)) '' s)
      = ∫⁻ y in s, ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.id +
          LinearMap.adjoint ((fderiv ℝ γ y : H →ₗ[ℝ] K)) ∘ₗ (fderiv ℝ γ y : H →ₗ[ℝ] K))))
          ∂(volume : Measure H) := by
  intro H K V _ _ _ _ _ _ _ _ _ _ _ _ _ ι κ hperp γ s hγ hs
  have h := hausdorffNormalized_image_vectorGraphMap ι κ hperp hγ hs
  simp only [normDet_graphMapLinear ι κ hperp] at h
  exact h

/-- **The corrected nonlinear graph area formula**: raw Hausdorff measure on both sides.  Obligation
`B1` of `AreaFormulaRouteStatements.lean` mixed the two normalizations; this is the statement that
holds. -/
theorem corrected_B1 : ∀ {H K V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V), (∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) →
    ∀ {γ : H → K} {s : Set H}, ContDiff ℝ 1 γ → MeasurableSet s →
    μH[(Module.finrank ℝ H : ℝ)] ((fun y => ι y + κ (γ y)) '' s)
      = ∫⁻ y in s, ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.id +
          LinearMap.adjoint ((fderiv ℝ γ y : H →ₗ[ℝ] K)) ∘ₗ (fderiv ℝ γ y : H →ₗ[ℝ] K))))
          ∂(μH[(Module.finrank ℝ H : ℝ)] : Measure H) := by
  intro H K V _ _ _ _ _ _ _ _ _ _ _ _ _ ι κ hperp γ s hγ hs
  have h := hausdorffMeasure_image_vectorGraphMap ι κ hperp hγ hs
  simp only [normDet_graphMapLinear ι κ hperp] at h
  exact h

/-- The two measures on the parameter space really are different objects; this is why the two
pairings above are the correct ones. -/
theorem normalization_differs {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] :
    (μH[(Module.finrank ℝ H : ℝ)] : Measure H)
      = ENNReal.ofReal (2 ^ Module.finrank ℝ H
          / KLS.unitBallVolume (Module.finrank ℝ H)) • (volume : Measure H) :=
  hausdorffMeasure_finrank_eq_smul_volume H

/-! ### Boundary clients -/

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- No finiteness hypothesis: the whole parameter space is allowed. -/
theorem whole_space (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ) :
    KLS.hausdorffNormalized V (Module.finrank ℝ H) (vectorGraphMap ι κ γ '' Set.univ)
      = ∫⁻ y, ENNReal.ofReal
          (LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V)))
          ∂(volume : Measure H) := by
  have h := hausdorffNormalized_image_vectorGraphMap ι κ hperp hγ MeasurableSet.univ
  simpa using h

/-- A zero-dimensional parameter space is inside the statement. -/
theorem zero_dimensional_parameter (ι : EuclideanSpace ℝ (Fin 0) →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : EuclideanSpace ℝ (Fin 0)) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    {γ : EuclideanSpace ℝ (Fin 0) → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set (EuclideanSpace ℝ (Fin 0))} (hs : MeasurableSet s) :
    KLS.hausdorffNormalized V (Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)))
        (vectorGraphMap ι κ γ '' s)
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet
          ((graphMapLinear ι κ (fderiv ℝ γ y) : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] V)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 0))) :=
  hausdorffNormalized_image_vectorGraphMap ι κ hperp hγ hs

end VectorGraphAreaAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.continuous_graphMapLinear_normDet
#print axioms FunctionalInequalities.Analysis.exists_approximating_partition_with_jacobian
#print axioms FunctionalInequalities.Analysis.vectorGraphMap_estimates
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_image_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.hausdorffNormalized_image_vectorGraphMap
#print axioms VectorGraphAreaAudit.route_B2
#print axioms VectorGraphAreaAudit.corrected_B1
#print axioms VectorGraphAreaAudit.normalization_differs
#print axioms VectorGraphAreaAudit.whole_space
#print axioms VectorGraphAreaAudit.zero_dimensional_parameter
