import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Fubini across an orthogonal splitting of the target

Obligation `R6` of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md` and stated in
`research/audits/RankDeficientRouteStatements.lean`.  **Only `R6` is proved here**; with `R1`, `R2`
of `Analysis/Vector/RankDeficient/Stratification.lean`, `R3` of `Analysis/Vector/RankDeficient/RightInverseBound.lean` and `R4` of
`Analysis/Vector/RankDeficient/TangentialLipschitz.lean` that is five of the route's obligations.  `R0`, `R5`,
`R7`–`R10`, `N1` and `N2` remain open, and so does the rank-deficient part of the codimension-`m`
coarea critical set.  Nothing here is a coarea formula, a slicing statement or a Sard theorem.

**What `R6` is for.**  The route slices twice: first in codimension `r` by the regular component
`P ∘ u`, then in codimension `m − r` by `Q ∘ u` inside each fibre.  What that produces is "for
almost every `s ∈ W₁`, for almost every `τ ∈ W₁ᗮ`", while the conclusion has to be about almost
every `t ∈ W`.  `R6` is the bookkeeping that joins the two levels.

**It is bookkeeping, but it was not available.**  Mathlib supplies every part —
`LinearIsometryEquiv.measurePreserving`, `WithLp.volume_preserving_toLp` and `Measure.prod_apply` —
and this module only assembles them.  The splitting is presented abstractly, as a linear isometry
onto `WithLp 2 (W₁ × W₂)`, so that the caller decides how to produce it; for an orthogonal
complement `Submodule.orthogonalDecomposition` is exactly such an isometry.

No differentiability, no Hausdorff measure and no regularity appears: this is a statement about one
measurable set.
-/

noncomputable section

open MeasureTheory Set

namespace FunctionalInequalities.Analysis

section TargetSplit

variable {W W₁ W₂ : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [MeasurableSpace W₁] [BorelSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
  [MeasurableSpace W₂] [BorelSpace W₂]

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ W₁] in
/-- The set of pairs whose image under the splitting lies in `N`.  Its slices are exactly the sets
the second slicing produces. -/
theorem measurableSet_splitPreimage (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) {N : Set W}
    (hN : MeasurableSet N) :
    MeasurableSet {p : W₁ × W₂ | e.symm (WithLp.toLp 2 p) ∈ N} := by
  have hmeas : Measurable fun p : W₁ × W₂ => e.symm (WithLp.toLp 2 p) :=
    e.symm.continuous.measurable.comp (MeasurableEquiv.toLp 2 (W₁ × W₂)).measurable
  exact hmeas hN

/-- **`R6`: Fubini across an orthogonal splitting of the target.**  If almost every first-coordinate
slice of `N` is null, then `N` is null.

This is what turns the route's "for almost every `s`, for almost every `τ`" into "for almost every
`t`".  The splitting is an arbitrary linear isometry onto `WithLp 2 (W₁ × W₂)`; for the route it is
the orthogonal decomposition along the range of the differential. -/
theorem measure_eq_zero_of_ae_slice_eq_zero (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) {N : Set W}
    (hN : MeasurableSet N)
    (h : ∀ᵐ s ∂(volume : Measure W₁),
        (volume : Measure W₂) {τ : W₂ | e.symm (WithLp.toLp 2 (s, τ)) ∈ N} = 0) :
    (volume : Measure W) N = 0 := by
  classical
  set N' : Set (WithLp 2 (W₁ × W₂)) := (fun q : WithLp 2 (W₁ × W₂) => e.symm q) ⁻¹' N with hN'
  have hN'meas : MeasurableSet N' := e.symm.continuous.measurable hN
  set M : Set (W₁ × W₂) := {p : W₁ × W₂ | e.symm (WithLp.toLp 2 p) ∈ N} with hM
  have hMmeas : MeasurableSet M := measurableSet_splitPreimage e hN
  have hMeq : M = (fun p : W₁ × W₂ => WithLp.toLp 2 p) ⁻¹' N' := rfl
  -- the `WithLp` synonym and the isometry are both measure preserving
  have hprod : (volume : Measure (W₁ × W₂)) M = (volume : Measure (WithLp 2 (W₁ × W₂))) N' := by
    rw [hMeq]
    exact (WithLp.volume_preserving_toLp W₁ W₂).measure_preimage hN'meas.nullMeasurableSet
  have hiso : (volume : Measure (WithLp 2 (W₁ × W₂))) N' = (volume : Measure W) N :=
    (e.symm.measurePreserving).measure_preimage hN.nullMeasurableSet
  -- Fubini for the product measure
  have hslice : (volume : Measure (W₁ × W₂)) M
      = ∫⁻ s, (volume : Measure W₂) (Prod.mk s ⁻¹' M) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hMmeas]
  have hzero : ∫⁻ s, (volume : Measure W₂) (Prod.mk s ⁻¹' M) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [h] with s hs
    simpa [hM, Set.preimage] using hs
  rw [← hiso, ← hprod, hslice, hzero]

end TargetSplit

end FunctionalInequalities.Analysis
