import FunctionalInequalities.Probability.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Support

/-!
# Intrinsic affine coordinates of a finite-dimensional probability measure

For a probability measure on a finite-dimensional real Hilbert space, this module takes the
affine span of its topological support and expresses the law on the direction of that affine
subspace. The resulting coordinate space is again a finite-dimensional real Hilbert space.

The construction removes directions normal to the affine support. It does not claim that an
ambient gradient pre-energy is closable for every singular law inside that support; atomic and
lower-dimensional non-affine singularities still require relaxation or a separate core theorem.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Probability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

/-- The affine span of the topological support of a probability measure.

This is the canonical affine carrier used here. It is not merely the topological support itself:
the latter need not be an affine space.
-/
def affineSupport (μ : ProbabilityMeasure E) : AffineSubspace ℝ E :=
  affineSpan ℝ (μ : Measure E).support

/-- The topological support is contained in its affine support. -/
theorem support_subset_affineSupport (μ : ProbabilityMeasure E) :
    (μ : Measure E).support ⊆ affineSupport μ :=
  subset_affineSpan ℝ _

/-- The affine support is closed in finite dimension. -/
theorem isClosed_affineSupport (μ : ProbabilityMeasure E) :
    IsClosed (affineSupport μ : Set E) :=
  (affineSupport μ).closed_of_finiteDimensional

/-- The affine support is Borel measurable. -/
theorem measurableSet_affineSupport (μ : ProbabilityMeasure E) :
    MeasurableSet (affineSupport μ : Set E) :=
  (isClosed_affineSupport μ).measurableSet

/-- The affine support has full measure. -/
theorem measure_compl_affineSupport (μ : ProbabilityMeasure E) :
    (μ : Measure E) (affineSupport μ : Set E)ᶜ = 0 := by
  apply measure_mono_null (Set.compl_subset_compl.mpr (support_subset_affineSupport μ))
  exact Measure.measure_compl_support

/-- Almost every point lies in the affine support. -/
theorem ae_mem_affineSupport (μ : ProbabilityMeasure E) :
    ∀ᵐ x ∂(μ : Measure E), x ∈ affineSupport μ := by
  filter_upwards [Measure.support_mem_ae (μ := (μ : Measure E))] with x hx
  exact support_subset_affineSupport μ hx

/-- The affine support is the smallest closed affine subspace of full measure. -/
theorem affineSupport_le_of_ae_mem (μ : ProbabilityMeasure E) (A : AffineSubspace ℝ E)
    (hA : IsClosed (A : Set E)) (hμ : ∀ᵐ x ∂(μ : Measure E), x ∈ A) :
    affineSupport μ ≤ A := by
  apply affineSpan_le.mpr
  exact Measure.support_subset_of_isClosed hA hμ

/-- A chosen point of the topological support, used only to put vector coordinates on the affine
carrier. Different choices give affinely isometric coordinate presentations. -/
def supportPoint (μ : ProbabilityMeasure E) : E :=
  ((μ : Measure E).nonempty_support (IsProbabilityMeasure.ne_zero (μ : Measure E))).choose

/-- The chosen point really belongs to the topological support. -/
theorem supportPoint_mem_support (μ : ProbabilityMeasure E) :
    supportPoint μ ∈ (μ : Measure E).support :=
  ((μ : Measure E).nonempty_support
    (IsProbabilityMeasure.ne_zero (μ : Measure E))).choose_spec

/-- The chosen support point, regarded as a point of the affine support. -/
def origin (μ : ProbabilityMeasure E) : affineSupport μ :=
  ⟨supportPoint μ, support_subset_affineSupport μ (supportPoint_mem_support μ)⟩

instance instNonemptyAffineSupport (μ : ProbabilityMeasure E) : Nonempty (affineSupport μ) :=
  ⟨origin μ⟩

/-- Translation by the chosen origin identifies the direction vector space with the affine
support isometrically. -/
def coordinateEquiv (μ : ProbabilityMeasure E) :
    (affineSupport μ).direction ≃ᵃⁱ[ℝ] affineSupport μ :=
  AffineIsometryEquiv.vaddConst ℝ (origin μ)

/-- A measurable retraction onto the affine support. Outside the full-measure carrier it uses the
chosen origin; this arbitrary branch has no effect on the induced probability law. -/
def retraction (μ : ProbabilityMeasure E) (x : E) : affineSupport μ :=
  by
    classical
    exact if hx : x ∈ affineSupport μ then ⟨x, hx⟩ else origin μ

/-- The affine-support retraction is measurable. -/
theorem measurable_retraction (μ : ProbabilityMeasure E) : Measurable (retraction μ) := by
  classical
  change Measurable (fun x ↦
    if hx : x ∈ affineSupport μ then (⟨x, hx⟩ : affineSupport μ) else origin μ)
  exact Measurable.dite measurable_id measurable_const (measurableSet_affineSupport μ)

/-- On the affine support, the retraction is the identity. -/
@[simp]
theorem coe_retraction_of_mem (μ : ProbabilityMeasure E) {x : E}
    (hx : x ∈ affineSupport μ) : (retraction μ x : E) = x := by
  classical
  simp [retraction, hx]

/-- The affine-support retraction agrees almost everywhere with the ambient identity. -/
theorem coe_retraction_ae (μ : ProbabilityMeasure E) :
    (fun x ↦ (retraction μ x : E)) =ᵐ[(μ : Measure E)] fun x ↦ x := by
  filter_upwards [ae_mem_affineSupport μ] with x hx
  exact coe_retraction_of_mem μ hx

/-- Intrinsic vector coordinates of an ambient point. -/
def intrinsicMap (μ : ProbabilityMeasure E) (x : E) : (affineSupport μ).direction :=
  (coordinateEquiv μ).symm (retraction μ x)

/-- The intrinsic-coordinate map is measurable. -/
theorem measurable_intrinsicMap (μ : ProbabilityMeasure E) : Measurable (intrinsicMap μ) :=
  (coordinateEquiv μ).symm.continuous.measurable.comp (measurable_retraction μ)

/-- The original probability law expressed on the direction vector space of its affine support. -/
def intrinsicMeasure (μ : ProbabilityMeasure E) :
    ProbabilityMeasure (affineSupport μ).direction :=
  μ.map (measurable_intrinsicMap μ).aemeasurable

/-- Reconstruction from intrinsic vector coordinates back into the ambient space, bundled as an
affine isometry. -/
def reconstruct (μ : ProbabilityMeasure E) : (affineSupport μ).direction →ᵃⁱ[ℝ] E :=
  (affineSupport μ).subtypeₐᵢ.comp (coordinateEquiv μ).toAffineIsometry

/-- Reconstruction is continuous. -/
theorem continuous_reconstruct (μ : ProbabilityMeasure E) : Continuous (reconstruct μ) :=
  (reconstruct μ).continuous

/-- Reconstruction is measurable. -/
theorem measurable_reconstruct (μ : ProbabilityMeasure E) : Measurable (reconstruct μ) :=
  (reconstruct μ).continuous.measurable

/-- Taking intrinsic coordinates after reconstruction recovers the original coordinates. -/
@[simp]
theorem intrinsicMap_reconstruct (μ : ProbabilityMeasure E)
    (v : (affineSupport μ).direction) :
    intrinsicMap μ (reconstruct μ v) = v := by
  have hmem : reconstruct μ v ∈ affineSupport μ :=
    (coordinateEquiv μ v).property
  have hret : retraction μ (reconstruct μ v) = coordinateEquiv μ v := by
    apply Subtype.ext
    exact coe_retraction_of_mem μ hmem
  rw [intrinsicMap, hret]
  exact (coordinateEquiv μ).symm_apply_apply v

/-- Reconstruction after taking intrinsic coordinates is the ambient identity almost everywhere. -/
theorem reconstruct_intrinsicMap_ae (μ : ProbabilityMeasure E) :
    (fun x ↦ reconstruct μ (intrinsicMap μ x)) =ᵐ[(μ : Measure E)] fun x ↦ x := by
  filter_upwards [ae_mem_affineSupport μ] with x hx
  simp [reconstruct, intrinsicMap, coordinateEquiv, retraction, hx]

/-- Taking intrinsic coordinates preserves the probability law by construction. -/
theorem measurePreserving_intrinsicMap (μ : ProbabilityMeasure E) :
    MeasurePreserving (intrinsicMap μ) (μ : Measure E) (intrinsicMeasure μ : Measure _) :=
  ⟨measurable_intrinsicMap μ, rfl⟩

/-- Reconstructing the intrinsic law gives back the original ambient probability law exactly. -/
theorem measurePreserving_reconstruct (μ : ProbabilityMeasure E) :
    MeasurePreserving (reconstruct μ) (intrinsicMeasure μ : Measure _) (μ : Measure E) := by
  refine ⟨measurable_reconstruct μ, ?_⟩
  rw [intrinsicMeasure, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (measurable_reconstruct μ) (measurable_intrinsicMap μ)]
  have hcomp : reconstruct μ ∘ intrinsicMap μ =ᵐ[(μ : Measure E)] id := by
    filter_upwards [reconstruct_intrinsicMap_ae μ] with x hx
    simpa only [Function.comp_apply, id_eq] using hx
  rw [Measure.map_congr hcomp, Measure.map_id]

end FunctionalInequalities.Probability
