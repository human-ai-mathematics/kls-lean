import FunctionalInequalities.Analysis.Vector.Graph.Sandwich
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the vector-valued sandwich estimates

Reported: the Pythagorean identity across the two factors, the expansiveness it gives the graph
map, injectivity of the linear model, the two sandwich estimates, and the approximating partition
that feeds the limit argument of the codimension-`m` graph area formula.

**The area formula is not proved here**: the limit `ε → 0` and the countable patching are audited
in `GraphAreaAudit.lean`.
-/

noncomputable section

open Set MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

namespace VectorGraphSandwichAudit

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Pythagoras across the two orthogonal factors. -/
theorem pythagoras (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (y : H) (z : K) :
    ‖ι y + κ z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 :=
  norm_add_sq_of_perp ι κ hperp y z

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Expansiveness**: a graph map never moves points closer together.  This is the lower-bound
input that the general area-formula route has to get from an inverse it does not have. -/
theorem expansive (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (y y' : H) :
    ‖y - y'‖ ≤ ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖ :=
  norm_sub_le_norm_sub_vectorGraphMap ι κ hperp γ y y'

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [FiniteDimensional ℝ K]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The linear model is injective, again with no hypothesis. -/
theorem linear_model_injective (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    Function.Injective (graphMapLinear ι κ A) :=
  injective_graphMapLinear ι κ hperp A

/-- **Upper estimate.** -/
theorem upper (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (A : H →L[ℝ] K)
    {t : Set H} {ε : ℝ≥0}
    (happ : ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ A) t ε) :
    μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' t)
      ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
        * ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)))
        * μH[(Module.finrank ℝ H : ℝ)] t :=
  hausdorffMeasure_image_vectorGraphMap_le ι κ hperp γ A happ

omit [FiniteDimensional ℝ K] in
/-- **Lower estimate.** -/
theorem lower (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (A : H →L[ℝ] K)
    {t : Set H} {ε : ℝ≥0}
    (happ : ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ A) t ε) :
    ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)))
        * μH[(Module.finrank ℝ H : ℝ)] t
      ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
        * μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' t) :=
  le_hausdorffMeasure_image_vectorGraphMap ι κ hperp γ A happ

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ K] in
/-- The approximating partition, the input of the limit argument. -/
theorem partition (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    {γ : H → K} (hγ : ContDiff ℝ 1 γ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (t : ℕ → Set H) (A : ℕ → (H →L[ℝ] K)),
      (∀ n, MeasurableSet (t n)) ∧ Pairwise (Function.onFun Disjoint t) ∧
      (⋃ n, t n) = Set.univ ∧
      (∀ n, ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ (A n)) (t n) ε) ∧
      (∀ n, ∀ z ∈ t n, ‖fderiv ℝ γ z - A n‖ ≤ (ε : ℝ)) :=
  exists_approximating_partition_vectorGraph ι κ hγ hε

/-! ### Boundary case -/

/-- At `ε = 0` the two estimates pin the measure exactly: a graph map that is *exactly* its linear
model has the linear image measure.  This is the sandwich degenerating correctly, not the area
formula. -/
theorem exact_at_zero (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (A : H →L[ℝ] K)
    {t : Set H}
    (happ : ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ A) t 0) :
    μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' t)
      = ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)))
        * μH[(Module.finrank ℝ H : ℝ)] t := by
  have hup := hausdorffMeasure_image_vectorGraphMap_le ι κ hperp γ A happ
  have hlo := le_hausdorffMeasure_image_vectorGraphMap ι κ hperp γ A happ
  simp only [add_zero, ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hup hlo
  exact le_antisymm hup hlo

end VectorGraphSandwichAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.norm_add_sq_of_perp
#print axioms FunctionalInequalities.Analysis.norm_sub_vectorGraphMap_sq
#print axioms FunctionalInequalities.Analysis.norm_sub_le_norm_sub_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.norm_le_norm_graphMapLinear
#print axioms FunctionalInequalities.Analysis.injective_graphMapLinear
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_image_vectorGraphMap_le
#print axioms FunctionalInequalities.Analysis.le_hausdorffMeasure_image_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.exists_approximating_partition_vectorGraph
#print axioms VectorGraphSandwichAudit.pythagoras
#print axioms VectorGraphSandwichAudit.expansive
#print axioms VectorGraphSandwichAudit.linear_model_injective
#print axioms VectorGraphSandwichAudit.upper
#print axioms VectorGraphSandwichAudit.lower
#print axioms VectorGraphSandwichAudit.partition
#print axioms VectorGraphSandwichAudit.exact_at_zero
