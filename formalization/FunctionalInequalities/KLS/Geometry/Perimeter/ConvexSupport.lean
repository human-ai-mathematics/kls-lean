module

public import FunctionalInequalities.Analysis.MetricBV.Basic
public import FunctionalInequalities.Analysis.MetricBV.Transport
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Metric BV perimeter on a closed convex support

For a probability law on a real Hilbert space whose closed support is convex, the metric BV
perimeter of a set equals the perimeter of its trace for the closed-support law
(`perimeter_eq_closedSupportLaw_of_convex`). The retraction required by
`perimeter_eq_comap_subtype_of_retraction` is the actual nearest-point projection onto the
support (`nearestPoint`), which fixes the support (`nearestPoint_coe`) and is `1`-Lipschitz
(`lipschitzWith_nearestPoint`), by the variational inequality of the projection. The support
is nonempty and carries all mass for every probability law on a second-countable space; it may be
unbounded or a single point, and no density or full ambient support is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.MetricBV

section NearestPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E}

/-- The nearest point of a nonempty complete convex set. -/
def nearestPoint (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) (u : E) : K :=
  ⟨Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hc hconv u),
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hc hconv u)).1⟩

theorem norm_sub_nearestPoint (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K)
    (u : E) : ‖u - nearestPoint hne hc hconv u‖ = ⨅ w : K, ‖u - w‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hc hconv u)).2

/-- Variational inequality of the nearest point. -/
theorem inner_sub_nearestPoint_le (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K)
    (u : E) {w : E} (hw : w ∈ K) :
    ⟪u - nearestPoint hne hc hconv u, w - nearestPoint hne hc hconv u⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv (nearestPoint hne hc hconv u).2).1
    (norm_sub_nearestPoint hne hc hconv u) w hw

/-- The nearest point of a point of the set is the point itself. -/
theorem nearestPoint_coe (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) (z : K) :
    nearestPoint hne hc hconv z = z := by
  have h := inner_sub_nearestPoint_le hne hc hconv (z : E) z.2
  have h0 : (z : E) - nearestPoint hne hc hconv z = 0 := real_inner_self_nonpos.1 h
  exact Subtype.ext (sub_eq_zero.1 h0).symm

/-- The nearest-point map is nonexpansive. -/
theorem lipschitzWith_nearestPoint (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    LipschitzWith 1 (nearestPoint hne hc hconv) := by
  refine LipschitzWith.of_dist_le_mul fun u₁ u₂ => ?_
  set a : E := (nearestPoint hne hc hconv u₁ : E) with ha
  set b : E := (nearestPoint hne hc hconv u₂ : E) with hb
  have h₁ : ⟪u₁ - a, b - a⟫ ≤ 0 :=
    inner_sub_nearestPoint_le hne hc hconv u₁ (nearestPoint hne hc hconv u₂).2
  have h₂ : ⟪u₂ - b, a - b⟫ ≤ 0 :=
    inner_sub_nearestPoint_le hne hc hconv u₂ (nearestPoint hne hc hconv u₁).2
  have hsum : ⟪a - b, a - b⟫ ≤ ⟪u₁ - u₂, a - b⟫ := by
    have e₁ : ⟪u₁ - a, b - a⟫ = -⟪u₁ - a, a - b⟫ := by
      rw [← inner_neg_right, neg_sub]
    have e₂ : ⟪u₁ - u₂, a - b⟫ - ⟪a - b, a - b⟫ = ⟪u₁ - a, a - b⟫ - ⟪u₂ - b, a - b⟫ := by
      rw [← inner_sub_left, ← inner_sub_left]
      congr 1
      abel
    linarith
  have hcs : ⟪u₁ - u₂, a - b⟫ ≤ ‖u₁ - u₂‖ * ‖a - b‖ := real_inner_le_norm _ _
  rw [real_inner_self_eq_norm_sq] at hsum
  have hab : ‖a - b‖ ≤ ‖u₁ - u₂‖ := by
    nlinarith [norm_nonneg (a - b), norm_nonneg (u₁ - u₂)]
  rw [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  exact hab

end NearestPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- On a probability law with convex closed support, the metric BV perimeter of a set equals the
perimeter of its trace for the closed-support law. The nearest-point projection onto the support
is the nonexpansive retraction; the support is nonempty and carries all mass. -/
theorem perimeter_eq_closedSupportLaw_of_convex (ν : ProbabilityMeasure E)
    (hconv : Convex ℝ (ν : Measure E).support) (B : Set E) :
    perimeter (ν : Measure E) B =
      perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B) := by
  have hne : (ν : Measure E).support.Nonempty :=
    Measure.nonempty_support (IsProbabilityMeasure.ne_zero (ν : Measure E))
  have hc : IsComplete (ν : Measure E).support := Measure.isClosed_support.isComplete
  exact perimeter_eq_comap_subtype_of_retraction (ν : Measure E)
    Measure.isClosed_support.measurableSet Measure.measure_compl_support
    (lipschitzWith_nearestPoint hne hc hconv) (nearestPoint_coe hne hc hconv) B

end FunctionalInequalities.KLS.MetricBV
