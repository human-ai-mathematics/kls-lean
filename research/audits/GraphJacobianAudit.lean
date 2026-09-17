import FunctionalInequalities.Analysis.GraphJacobian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the codimension-`m` graph Jacobian

Step two of the codimension-`m` coarea program, linear layer.  The area formula already proved in
this repository is **codimension one**: its graph is the graph of a *real-valued* function, with
volume factor `graphJacobian a = √(1 + ‖a‖²)`.  Fibres of a map into an `m`-dimensional target have
codimension `m`, so a `K`-valued slope is needed.

Reported below: the Gram operator of a graph map is `1 + Aᵀ A` on the **parameter** space, hence
the volume factor is `√det (1 + Aᵀ A)`, independent of the ambient embedding; and the
codimension-one case agrees exactly with the existing `graphJacobian`, which identifies this
repository's codimension-one framework with Mathlib's general `normDet`.

**The nonlinear area formula is NOT proved.**  The final `#check` in this file is a proposition
type-check of that open target, not a proof of it, in the style of the weighted coarea route file.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

namespace GraphJacobianAudit

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
/-- The Gram operator of a graph map lives on the parameter space and is `1 + Aᵀ A`. -/
theorem gram_operator (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    LinearMap.adjoint ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) ∘ₗ (graphMapLinear ι κ A : H →ₗ[ℝ] V)
      = LinearMap.id + LinearMap.adjoint (A : H →ₗ[ℝ] K) ∘ₗ (A : H →ₗ[ℝ] K) :=
  adjoint_comp_graphMapLinear ι κ hperp A

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
/-- **The volume factor in arbitrary codimension**, a determinant on the parameter space and
therefore independent of the ambient embedding. -/
theorem volume_factor (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V))
      = Real.sqrt (LinearMap.det
          (LinearMap.id + LinearMap.adjoint (A : H →ₗ[ℝ] K) ∘ₗ (A : H →ₗ[ℝ] K))) :=
  normDet_graphMapLinear ι κ hperp A

omit [FiniteDimensional ℝ V] in
/-- **The codimension-one case agrees with the already proved area formula.**  The repository's
`graphJacobian` and Mathlib's `normDet` are the same number, so the proved codimension-one area
formula is the `m = 1` case of the general volume factor. -/
theorem codimension_one_agrees (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) (a : H) :
    LinearMap.normDet ((graphLinear ι e a : H →ₗ[ℝ] V)) = graphJacobian a :=
  normDet_graphLinear ι he hperp a

/-! ### Boundary cases -/

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
/-- A flat graph has unit factor. -/
theorem flat_graph (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) :
    LinearMap.normDet ((graphMapLinear ι κ (0 : H →L[ℝ] K) : H →ₗ[ℝ] V)) = 1 := by
  rw [normDet_graphMapLinear ι κ hperp]
  simp

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
/-- Codimension zero: a subsingleton target leaves the factor at one, and the statement does not
exclude it. -/
theorem codimension_zero [Subsingleton K] (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) = 1 := by
  have hA : A = 0 := by
    ext y
    exact Subsingleton.elim _ _
  rw [hA]
  exact flat_graph ι κ hperp

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V] in
/-- A zero-dimensional parameter space is inside the statement too. -/
theorem zero_dimensional_parameter (ι : EuclideanSpace ℝ (Fin 0) →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : EuclideanSpace ℝ (Fin 0)) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    (A : EuclideanSpace ℝ (Fin 0) →L[ℝ] K) :
    LinearMap.normDet ((graphMapLinear ι κ A : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] V))
      = Real.sqrt (LinearMap.det
          (LinearMap.id + LinearMap.adjoint (A : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] K)
            ∘ₗ (A : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] K))) :=
  normDet_graphMapLinear ι κ hperp A

end GraphJacobianAudit

/-! ### The open nonlinear target

The following is a **proposition type-check, not a proof**: the Federer area formula for an
injective `C¹` parametrization, which the codimension-`m` coarea program still needs and which
nothing in this repository proves.  It is recorded here so that the next round has an exact
statement to aim at, exactly as `WeightedCoareaRouteStatements.lean` did for the scalar route. -/

#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {g : H → V} {s : Set H}, ContDiff ℝ 1 g → Set.InjOn g s → MeasurableSet s →
    μH[(Module.finrank ℝ H : ℝ)] (g '' s)
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V)))
          ∂(volume : Measure H))

/-! ### Axiom audit: every proved report is standard-only -/

#print axioms FunctionalInequalities.Analysis.graphMapLinear
#print axioms FunctionalInequalities.Analysis.adjoint_comp_graphMapLinear
#print axioms FunctionalInequalities.Analysis.normDet_graphMapLinear_sq
#print axioms FunctionalInequalities.Analysis.normDet_graphMapLinear
#print axioms FunctionalInequalities.Analysis.normDet_graphLinear
#print axioms GraphJacobianAudit.gram_operator
#print axioms GraphJacobianAudit.volume_factor
#print axioms GraphJacobianAudit.codimension_one_agrees
#print axioms GraphJacobianAudit.flat_graph
#print axioms GraphJacobianAudit.codimension_zero
#print axioms GraphJacobianAudit.zero_dimensional_parameter
