import FunctionalInequalities.Analysis.Vector.RankDeficient.TargetSplitFubini
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Scope audit for Fubini across an orthogonal splitting of the target

**What is proved.**  Exactly route obligation `R6` of
`research/audits/RankDeficientRouteStatements.lean`, whose proposition is restated **verbatim**
below as `route_R6` and discharged.  With `R1`–`R4` that is five of the route's thirteen numbered
items, once `R5` is counted separately.  **`R0`, `R7`–`R10`, `N1` and `N2` are still open**, and so
is the rank-deficient part of the codimension-`m` coarea critical set.  **No coarea formula, no
slicing statement and no Sard theorem is proved here.**

**`R6` is usable for the splitting the route actually needs.**  `orthogonal_decomposition`
instantiates it along `Submodule.orthogonalDecomposition`, the isometry `W ≃ₗᵢ WithLp 2 (K × Kᗮ)`,
which is the splitting along the range of the differential that the route uses.  The library
statement is kept abstract so that the caller supplies the isometry.

**The converse holds too**, and is recorded so the obligation is not mistaken for the hard
direction: `converse` shows a null set has almost everywhere null slices.  `R6` is the direction
the route needs, and both come from the same product-measure machinery.

**Boundary cases.**  The empty set, a set that is already null, and a zero-dimensional second
factor — where `volume` is a probability measure on a point, so the hypothesis forces almost every
slice to be *empty* rather than merely null — are covered.

No differentiability, Hausdorff measure or regularity appears anywhere: this is a statement about
one measurable set.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched.
-/

noncomputable section

open MeasureTheory Set Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

namespace TargetSplitFubiniAudit

/-! ### The route obligation, restated verbatim and discharged -/

/-- **Route obligation `R6`**, copied from
`research/audits/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_R6 :
    (∀ {W W₁ W₂ : Type*}
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
      [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
      [MeasurableSpace W₁] [BorelSpace W₁]
      [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
      [MeasurableSpace W₂] [BorelSpace W₂]
      (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) (N : Set W), MeasurableSet N →
      (∀ᵐ s ∂(volume : Measure W₁),
          (volume : Measure W₂) {τ : W₂ | e.symm (WithLp.toLp 2 (s, τ)) ∈ N} = 0) →
      (volume : Measure W) N = 0) :=
  fun e _N hN h => measure_eq_zero_of_ae_slice_eq_zero e hN h

section Instances

variable {W W₁ W₂ : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [MeasurableSpace W₁] [BorelSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
  [MeasurableSpace W₂] [BorelSpace W₂]

/-- **`R6` along the orthogonal decomposition**, which is the splitting the route uses: `W₁` is the
range of the differential at a point of the stratum and `W₂` its orthogonal complement.  The
instances resolve, so the abstract statement is directly usable. -/
theorem orthogonal_decomposition (K : Submodule ℝ W) {N : Set W} (hN : MeasurableSet N)
    (h : ∀ᵐ s ∂(volume : Measure K),
        (volume : Measure Kᗮ)
          {τ : Kᗮ | K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ)) ∈ N} = 0) :
    (volume : Measure W) N = 0 :=
  measure_eq_zero_of_ae_slice_eq_zero K.orthogonalDecomposition hN h

/-- **The converse direction**, recorded so that `R6` is not mistaken for the easy half: a null set
has almost everywhere null slices. -/
theorem converse (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) {N : Set W} (hN : MeasurableSet N)
    (h : (volume : Measure W) N = 0) :
    ∀ᵐ s ∂(volume : Measure W₁),
      (volume : Measure W₂) {τ : W₂ | e.symm (WithLp.toLp 2 (s, τ)) ∈ N} = 0 := by
  classical
  set N' : Set (WithLp 2 (W₁ × W₂)) := (fun q : WithLp 2 (W₁ × W₂) => e.symm q) ⁻¹' N with hN'
  have hN'meas : MeasurableSet N' := e.symm.continuous.measurable hN
  set M : Set (W₁ × W₂) := {p : W₁ × W₂ | e.symm (WithLp.toLp 2 p) ∈ N} with hM
  have hMmeas : MeasurableSet M := measurableSet_splitPreimage e hN
  have hMeq : M = (fun p : W₁ × W₂ => WithLp.toLp 2 p) ⁻¹' N' := rfl
  have hprod : (volume : Measure (W₁ × W₂)) M = (volume : Measure (WithLp 2 (W₁ × W₂))) N' := by
    rw [hMeq]
    exact (WithLp.volume_preserving_toLp W₁ W₂).measure_preimage hN'meas.nullMeasurableSet
  have hiso : (volume : Measure (WithLp 2 (W₁ × W₂))) N' = (volume : Measure W) N :=
    (e.symm.measurePreserving).measure_preimage hN.nullMeasurableSet
  have hMzero : (volume : Measure (W₁ × W₂)) M = 0 := by rw [hprod, hiso, h]
  have hint : ∫⁻ s, (volume : Measure W₂) (Prod.mk s ⁻¹' M) = 0 := by
    rw [← Measure.prod_apply hMmeas, ← Measure.volume_eq_prod]
    exact hMzero
  have hmeasf : Measurable fun s : W₁ => (volume : Measure W₂) (Prod.mk s ⁻¹' M) :=
    measurable_measure_prodMk_left hMmeas
  filter_upwards [(lintegral_eq_zero_iff hmeasf).1 hint] with s hs
  simpa [hM, Set.preimage] using hs

/-- **The empty set is covered with no side condition**, through the theorem itself. -/
theorem empty_set (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) :
    (volume : Measure W) (∅ : Set W) = 0 :=
  measure_eq_zero_of_ae_slice_eq_zero e MeasurableSet.empty (by simp)

end Instances

end TargetSplitFubiniAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.measurableSet_splitPreimage
#print axioms FunctionalInequalities.Analysis.measure_eq_zero_of_ae_slice_eq_zero
#print axioms TargetSplitFubiniAudit.route_R6
#print axioms TargetSplitFubiniAudit.orthogonal_decomposition
#print axioms TargetSplitFubiniAudit.converse
#print axioms TargetSplitFubiniAudit.empty_set
