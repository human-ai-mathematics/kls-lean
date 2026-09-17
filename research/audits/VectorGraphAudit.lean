import FunctionalInequalities.Analysis.VectorGraph
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the vector-valued graph infrastructure (`B1`, first part)

The codimension-`m` graph area formula `B1` is being built by mirroring the five phases of the
codimension-one file `Analysis/AreaFormula.lean`.  This round covers its second and third phases:
the graph map of a `K`-valued slope, its retraction, injectivity, derivative, image measurability
and linear approximation, plus the linear case, which needs no shear argument here.

**The area formula itself is NOT proved.**  The remaining phases — the two-sided estimates and the
limit — are the rest of `B1`, and the route obligations `A2`–`A5` and `B2` are untouched.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

namespace VectorGraphAudit

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K] [MeasurableSpace V]
  [BorelSpace V] in
/-- **The explicit left inverse**, which is exactly what the general area-formula route `A3` lacks:
the parameter retraction recovers the parameter from any point of the graph, for an arbitrary
slope. -/
theorem explicit_left_inverse (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (y : H) :
    graphProj ι (vectorGraphMap ι κ γ y) = y :=
  graphProj_vectorGraphMap ι κ hperp γ y

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K] [MeasurableSpace V]
  [BorelSpace V] in
/-- Injectivity needs **no** hypothesis on the slope: no `InjOn` assumption and no multiplicity. -/
theorem injective_without_hypothesis (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) :
    Function.Injective (vectorGraphMap ι κ γ) :=
  vectorGraphMap_injective ι κ hperp γ

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ H] [FiniteDimensional ℝ K] [FiniteDimensional ℝ V] in
/-- The derivative of a graph map is the linear graph map of the derivative, so the volume factor
of the previous round is the right one pointwise. -/
theorem derivative_is_linear_graph (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) {γ : H → K} {y : H}
    (hγ : DifferentiableAt ℝ γ y) :
    HasFDerivAt (vectorGraphMap ι κ γ) (graphMapLinear ι κ (fderiv ℝ γ y)) y :=
  hasFDerivAt_vectorGraphMap ι κ hγ

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ H] [FiniteDimensional ℝ K] [FiniteDimensional ℝ V] in
/-- Linear approximation on a ball where the derivative varies little. -/
theorem linear_approximation (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    {γ : H → K} (hγ : ContDiff ℝ 1 γ) {y₀ : H} {r : ℝ} {ε : ℝ≥0}
    (hball : ∀ z ∈ Metric.ball y₀ r, ‖fderiv ℝ γ z - fderiv ℝ γ y₀‖ ≤ (ε : ℝ))
    {t : Set H} (hts : t ⊆ Metric.ball y₀ r) :
    ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ (fderiv ℝ γ y₀)) t ε :=
  approximatesLinearOn_vectorGraphMap ι κ hγ hball hts

omit [FiniteDimensional ℝ K] in
/-- Images of measurable parameter sets are measurable. -/
theorem image_measurable (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : Continuous γ)
    {E : Set H} (hE : MeasurableSet E) :
    MeasurableSet (vectorGraphMap ι κ γ '' E) :=
  measurableSet_image_vectorGraphMap ι κ hperp hγ hE

/-- **The linear case of `B1`**: the area formula holds for a linear slope, with the volume factor
`√det (1 + Aᵀ A)`.  No shear argument was needed. -/
theorem linear_case (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) (s : Set H) :
    μH[(Module.finrank ℝ H : ℝ)] (graphMapLinear ι κ A '' s)
      = ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.id +
          LinearMap.adjoint (A : H →ₗ[ℝ] K) ∘ₗ (A : H →ₗ[ℝ] K))))
        * μH[(Module.finrank ℝ H : ℝ)] s :=
  hausdorffMeasure_image_graphMapLinear ι κ hperp A s

omit [MeasurableSpace V] [BorelSpace V] in
/-- The volume factor along a slope is measurable, so the right-hand side of `B1` is a genuine
lower integral.  This consumes obligation `A1`. -/
theorem jacobian_measurable (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (γ : H → K) :
    Measurable (fun y : H =>
      LinearMap.normDet ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) :=
  measurable_vectorGraphJacobian ι κ γ

/-! ### Boundary cases -/

omit [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ H] [FiniteDimensional ℝ V] in
/-- Codimension zero: a subsingleton second factor makes the graph map the embedding itself. -/
theorem codimension_zero [Subsingleton K] (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (γ : H → K) (y : H) :
    vectorGraphMap ι κ γ y = ι y := by
  have hz : γ y = 0 := Subsingleton.elim _ _
  rw [vectorGraphMap_apply, hz, map_zero, add_zero]

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ H] [FiniteDimensional ℝ K] [FiniteDimensional ℝ V] in
/-- A constant slope is a flat graph: its derivative is the embedding, with factor one. -/
theorem constant_slope (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V) (c : K) (y : H) :
    HasFDerivAt (vectorGraphMap ι κ (fun _ => c)) (graphMapLinear ι κ 0) y := by
  have h := hasFDerivAt_vectorGraphMap ι κ (γ := fun _ : H => c) (y := y)
    (differentiableAt_const c)
  rwa [fderiv_const_apply] at h

omit [FiniteDimensional ℝ K] [MeasurableSpace V] [BorelSpace V] in
/-- A zero-dimensional parameter space is inside the statements. -/
theorem zero_dimensional_parameter (ι : EuclideanSpace ℝ (Fin 0) →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : EuclideanSpace ℝ (Fin 0)) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    (γ : EuclideanSpace ℝ (Fin 0) → K) :
    Function.Injective (vectorGraphMap ι κ γ) :=
  vectorGraphMap_injective ι κ hperp γ

end VectorGraphAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.vectorGraphMap
#print axioms FunctionalInequalities.Analysis.graphProj_apply_of_perp
#print axioms FunctionalInequalities.Analysis.graphProj_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.vectorGraphMap_injective
#print axioms FunctionalInequalities.Analysis.hasFDerivAt_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.approximatesLinearOn_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.image_vectorGraphMap_eq
#print axioms FunctionalInequalities.Analysis.measurableSet_image_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_image_graphMapLinear
#print axioms FunctionalInequalities.Analysis.measurable_vectorGraphJacobian
#print axioms VectorGraphAudit.explicit_left_inverse
#print axioms VectorGraphAudit.injective_without_hypothesis
#print axioms VectorGraphAudit.derivative_is_linear_graph
#print axioms VectorGraphAudit.linear_approximation
#print axioms VectorGraphAudit.image_measurable
#print axioms VectorGraphAudit.linear_case
#print axioms VectorGraphAudit.jacobian_measurable
#print axioms VectorGraphAudit.codimension_zero
#print axioms VectorGraphAudit.constant_slope
#print axioms VectorGraphAudit.zero_dimensional_parameter
