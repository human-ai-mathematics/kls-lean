module

public import FunctionalInequalities.Analysis.MetricBV.Finite
public import FunctionalInequalities.KLS.Geometry.Perimeter.ConvexSupport
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent full-signature clients for the metric BV perimeter on a closed convex support:
the nearest-point projection (infimum, variational inequality, fixed points, nonexpansiveness)
and the equality `perimeter ν B = perimeter (closedSupportLaw ν) (Subtype.val ⁻¹' B)` under the
sole hypothesis that the support is convex. Checks: the measurable-`B` form, sets with the same
trace have the same perimeter, a proper convex support (the uniform law on `[0, 1]` in `ℝ`, whose
support is computed to be `Icc 0 1`), and a singleton support (`dirac 0` on `ℝ`), where every set
has perimeter zero. No `intrinsicHalfConstant` identification is claimed. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace MetricBVConvexSupportAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E}

theorem projectionProperties (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    (∀ u : E, ‖u - nearestPoint hne hc hconv u‖ = ⨅ w : K, ‖u - w‖) ∧
      (∀ (u : E) {w : E}, w ∈ K →
        ⟪u - nearestPoint hne hc hconv u, w - nearestPoint hne hc hconv u⟫ ≤ 0) ∧
      (∀ z : K, nearestPoint hne hc hconv z = z) ∧
      LipschitzWith 1 (nearestPoint hne hc hconv) :=
  ⟨norm_sub_nearestPoint hne hc hconv, fun u _ hw => inner_sub_nearestPoint_le hne hc hconv u hw,
    nearestPoint_coe hne hc hconv, lipschitzWith_nearestPoint hne hc hconv⟩

end Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem convexSupport (ν : ProbabilityMeasure E) (hconv : Convex ℝ (ν : Measure E).support)
    (B : Set E) :
    perimeter (ν : Measure E) B =
      perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B) := by
  exact perimeter_eq_closedSupportLaw_of_convex ν hconv B

/-- The form with measurable `B`. -/
theorem convexSupportMeasurable (ν : ProbabilityMeasure E)
    (hconv : Convex ℝ (ν : Measure E).support) {B : Set E} (_hB : MeasurableSet B) :
    perimeter (ν : Measure E) B =
      perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B) := by
  exact perimeter_eq_closedSupportLaw_of_convex ν hconv B

/-- Consequence: the perimeter depends only on the trace on the convex support. -/
theorem traceDetermines (ν : ProbabilityMeasure E) (hconv : Convex ℝ (ν : Measure E).support)
    {B B' : Set E}
    (htr : (Subtype.val : (ν : Measure E).support → E) ⁻¹' B = Subtype.val ⁻¹' B') :
    perimeter (ν : Measure E) B = perimeter (ν : Measure E) B' := by
  rw [perimeter_eq_closedSupportLaw_of_convex ν hconv B,
    perimeter_eq_closedSupportLaw_of_convex ν hconv B', htr]

/-- The uniform law on `[0, 1]`. -/
def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Set.Icc 0 1), ⟨by simp⟩⟩

/-- Its support is exactly `Icc 0 1`: the interval is closed and carries all mass, and its
interior lies in the support of Lebesgue measure. -/
theorem uniformInterval_support :
    (uniformInterval : Measure ℝ).support = Set.Icc 0 1 := by
  change ((volume : Measure ℝ).restrict (Set.Icc 0 1)).support = Set.Icc 0 1
  refine subset_antisymm
    (Measure.support_subset_of_isClosed isClosed_Icc (ae_restrict_mem measurableSet_Icc)) ?_
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ ((volume : Measure ℝ).restrict (Set.Icc 0 1)).support := by
    have h := Measure.interior_inter_support (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    rwa [interior_Icc, Measure.support_eq_univ, Set.inter_univ] at h
  calc Set.Icc (0 : ℝ) 1 = closure (Set.Ioo 0 1) := (closure_Ioo zero_ne_one).symm
    _ ⊆ _ := closure_minimal hsub Measure.isClosed_support

/-- A proper convex support: perimeters for the uniform law on `ℝ` equal perimeters of traces on
`[0, 1]`, and the support misses `2`. -/
theorem uniformIntervalConvex (B : Set ℝ) :
    perimeter (uniformInterval : Measure ℝ) B =
        perimeter (closedSupportLaw uniformInterval : Measure (uniformInterval : Measure ℝ).support)
          (Subtype.val ⁻¹' B) ∧
      (2 : ℝ) ∉ (uniformInterval : Measure ℝ).support := by
  refine ⟨perimeter_eq_closedSupportLaw_of_convex _ ?_ B, ?_⟩
  · rw [uniformInterval_support]
    exact convex_Icc 0 1
  · rw [uniformInterval_support]
    norm_num

/-- The Dirac law at `0` on `ℝ`: its support is the singleton `{0}`. -/
def diracZero : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

theorem diracZero_support : (diracZero : Measure ℝ).support = {0} := by
  change (Measure.dirac (0 : ℝ)).support = {0}
  refine subset_antisymm (Measure.support_subset_of_isClosed isClosed_singleton ?_) ?_
  · rw [mem_ae_iff, Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl]
    simp
  · rintro x rfl
    refine (Measure.mem_support_iff_forall _).2 fun U hU => ?_
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
    exact zero_lt_one

/-- A singleton support: the equality applies, and every set has zero perimeter under the Dirac
law, since the support is a one-point space. -/
theorem diracSingleton (B : Set ℝ) :
    perimeter (diracZero : Measure ℝ) B = 0 := by
  have hconv : Convex ℝ (diracZero : Measure ℝ).support := by
    rw [diracZero_support]
    exact convex_singleton 0
  have hS : Subsingleton (diracZero : Measure ℝ).support := by
    rw [diracZero_support]
    infer_instance
  have hN : Nonempty (diracZero : Measure ℝ).support := by
    rw [diracZero_support]
    infer_instance
  rw [perimeter_eq_closedSupportLaw_of_convex _ hconv B]
  exact perimeter_eq_zero_of_subsingleton _ _

#print axioms projectionProperties
#print axioms convexSupport
#print axioms convexSupportMeasurable
#print axioms traceDetermines
#print axioms uniformInterval_support
#print axioms uniformIntervalConvex
#print axioms diracZero_support
#print axioms diracSingleton

end MetricBVConvexSupportAudit
