import FunctionalInequalities.Analysis.Hausdorff.SurfaceSlicing

/-!
# Strict audit client for null slicing

Independent client of `Analysis/Hausdorff/SurfaceSlicing.lean` and `Analysis/Hausdorff/Slicing.lean`.
`target` states obligation `L2` of `research/audits/Coarea/WeightedRouteStatements.lean`
quantifier for quantifier, with no added hypothesis: `N` is
not measurable, `V` may be zero-dimensional, `u` is Lipschitz on `N` only, `K` is an arbitrary
`ℝ≥0`, and `surfaceMeasure` keeps the repository's normalized Hausdorff definition.

The remaining declarations are consumers, not repetitions of the proof: they use the result
without measurability of `N`, at `K = 0`, in dimensions zero, one and two, in the
`lintegral`-over-slices form the coarea route needs, and they pin the degenerate normalizations by
computation — `ℋ^{0-1}` on a one-point space is the unit mass, `ℋ⁰` on the line counts points, and
the plane's `ℋ¹` of a nondegenerate segment is nonzero.  The last three show the conclusion is not
obtained by replacing `surfaceMeasure` with the zero measure, and that the exceptional level set
is real: at `t = 0` the slices of `dim_one` and `constant_on_null` are not null.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal

namespace NullSlicingAudit

/-! ### The obligation itself -/

-- The statement text of obligation `L2` of `Coarea/WeightedRouteStatements.lean`.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {N : Set V}, LipschitzOnWith K u N →
    (volume : Measure V) N = 0 →
    ∀ᵐ t ∂(volume : Measure ℝ), KLS.surfaceMeasure V (N ∩ {x | u x = t}) = 0)

/-- The route target, restated and proved. -/
theorem target : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {N : Set V}, LipschitzOnWith K u N →
    (volume : Measure V) N = 0 →
    ∀ᵐ t ∂(volume : Measure ℝ), KLS.surfaceMeasure V (N ∩ {x | u x = t}) = 0 := by
  intro V _ _ _ _ _ _ u K N hu hN
  exact ae_surfaceMeasure_inter_levelSet_eq_zero hu hN

/-! ### Consumers -/

section Consumers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- No measurability of `N` anywhere: an arbitrary subset of a Lebesgue-null set. -/
theorem subset_of_null {u : V → ℝ} {K : ℝ≥0} {M N : Set V} (hu : LipschitzOnWith K u N)
    (hM : (volume : Measure V) M = 0) (hNM : N ⊆ M) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | u x = t}) = 0 :=
  ae_surfaceMeasure_inter_levelSet_eq_zero hu (measure_mono_null hNM hM)

/-- `K = 0`: a function constant on `N`.  Only the level `t = c` can meet `N`, and there the
slice is all of `N`, so the conclusion is genuinely almost-everywhere. -/
theorem constant_on_null (c : ℝ) {N : Set V} (hN : (volume : Measure V) N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), surfaceMeasure V (N ∩ {x | (fun _ : V => c) x = t}) = 0 :=
  ae_surfaceMeasure_inter_levelSet_eq_zero (K := 0) (LipschitzWith.const c).lipschitzOnWith hN

/-- The form the coarea route consumes: an arbitrary `ℝ≥0∞` weight, with no measurability of the
weight, of `N`, or of the slice function, integrates to zero over almost every slice. -/
theorem ae_setLIntegral_eq_zero {u : V → ℝ} {K : ℝ≥0} {N : Set V} (g : V → ℝ≥0∞)
    (hu : LipschitzOnWith K u N) (hN : (volume : Measure V) N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      (∫⁻ y in N ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) = 0 := by
  filter_upwards [ae_surfaceMeasure_inter_levelSet_eq_zero hu hN] with t ht
  exact setLIntegral_measure_zero _ _ ht

end Consumers

/-! ### Dimension zero -/

/-- The zero-dimensional `surfaceMeasure` is the unit mass of the one-point space, by the
repository's natural-subtraction convention `ℋ^{0-1} = ℋ⁰`.  It is not the zero measure. -/
theorem dim_zero_surfaceMeasure_univ :
    surfaceMeasure (EuclideanSpace ℝ (Fin 0)) Set.univ = 1 := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 0)) = 0 := by simp
  have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := Module.finrank_zero_iff.1 hn
  have huniv : (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) = {0} := by
    ext x; simp [Subsingleton.elim x 0]
  rw [surfaceMeasure, hn, Nat.zero_sub, hausdorffNormalized, Measure.smul_apply, smul_eq_mul,
    huniv, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton]
  simp [unitBallVolume]

/-- The obligation in dimension zero. -/
theorem dim_zero {u : EuclideanSpace ℝ (Fin 0) → ℝ} {K : ℝ≥0}
    {N : Set (EuclideanSpace ℝ (Fin 0))} (hu : LipschitzOnWith K u N)
    (hN : (volume : Measure (EuclideanSpace ℝ (Fin 0))) N = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure (EuclideanSpace ℝ (Fin 0)) (N ∩ {x | u x = t}) = 0 :=
  ae_surfaceMeasure_inter_levelSet_eq_zero hu hN

/-! ### Dimension one -/

/-- On the line the fibre measure is `ℋ⁰`, which counts: the slice of `{0}` at the level `0` has
surface measure one.  The exceptional level set of `dim_one` is therefore nonempty. -/
theorem dim_one_exceptional_level :
    surfaceMeasure ℝ (({0} : Set ℝ) ∩ {x : ℝ | id x = 0}) = 1 := by
  have hset : ({0} : Set ℝ) ∩ {x : ℝ | id x = 0} = {(0 : ℝ)} := by ext x; simp
  have hn : Module.finrank ℝ ℝ = 1 := by simp
  rw [hset, surfaceMeasure, hn, show (1 : ℕ) - 1 = 0 from rfl, hausdorffNormalized,
    Measure.smul_apply, smul_eq_mul, Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton]
  simp [unitBallVolume]

/-- The obligation in dimension one, for the identity on the Lebesgue-null set `{0}`. -/
theorem dim_one :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure ℝ (({0} : Set ℝ) ∩ {x : ℝ | id x = t}) = 0 :=
  ae_surfaceMeasure_inter_levelSet_eq_zero (K := 1) LipschitzWith.id.lipschitzOnWith (by simp)

/-- `u` Lipschitz on `N` only: this `u` is unbounded near the null set `N = {0}` and is not
Lipschitz on any neighbourhood of it, yet the obligation applies with `K = 0`. -/
theorem lipschitzOnWith_only :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure ℝ (({0} : Set ℝ) ∩ {x : ℝ | (if x = 0 then (0 : ℝ) else 1 / x) = t}) = 0 := by
  refine ae_surfaceMeasure_inter_levelSet_eq_zero (K := 0)
    (LipschitzOnWith.of_dist_le_mul ?_) (by simp)
  intro x hx y hy
  rw [show x = 0 from hx, show y = 0 from hy]
  simp

/-! ### Positive codimension -/

/-- In the plane the fibre measure of a nondegenerate segment is nonzero, so the conclusion is
not vacuous in positive codimension either. -/
theorem plane_segment_ne_zero {e : EuclideanSpace ℝ (Fin 2)} (he : e ≠ 0) :
    surfaceMeasure (EuclideanSpace ℝ (Fin 2)) (segment ℝ 0 e) ≠ 0 := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  rw [surfaceMeasure, hn, show (2 : ℕ) - 1 = 1 from rfl, hausdorffNormalized,
    Measure.smul_apply, smul_eq_mul, Nat.cast_one, hausdorffMeasure_segment]
  simp only [ne_eq, mul_eq_zero, not_or]
  refine ⟨?_, ?_⟩
  · simp only [ENNReal.ofReal_eq_zero, not_le]
    unfold unitBallVolume
    positivity
  · rw [edist_eq_zero]
    exact fun h => he h.symm

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.Analysis.exists_cover_of_hausdorffMeasure_eq_zero
#print axioms FunctionalInequalities.Analysis.exists_levelSlab
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.KLS.ae_surfaceMeasure_inter_levelSet_eq_zero
#print axioms NullSlicingAudit.target
#print axioms NullSlicingAudit.subset_of_null
#print axioms NullSlicingAudit.constant_on_null
#print axioms NullSlicingAudit.ae_setLIntegral_eq_zero
#print axioms NullSlicingAudit.dim_zero_surfaceMeasure_univ
#print axioms NullSlicingAudit.dim_zero
#print axioms NullSlicingAudit.dim_one_exceptional_level
#print axioms NullSlicingAudit.dim_one
#print axioms NullSlicingAudit.lipschitzOnWith_only
#print axioms NullSlicingAudit.plane_segment_ne_zero

end NullSlicingAudit
