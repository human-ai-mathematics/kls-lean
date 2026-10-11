import FunctionalInequalities.KLS.Definitions
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Geometry of the compact-set log-concavity convention

These lemmas use the existing `KLS.LogConcave` definition. Read affine-isometric pullback,
then the intrinsic-coordinate corollary. They provide the coordinate reduction for the
absolute-continuity step in the general log-concave literature comparison. No density is
included in the definition and no representation theorem is assumed here.
-/

noncomputable section

open MeasureTheory Set Topology

namespace FunctionalInequalities.KLS.LogConcave

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A probability law reconstructed by an affine isometry inherits compact-set log-concavity
from its ambient law. Images of compact sets supply the exact test sets. -/
theorem of_affineIsometry_map {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (ν : ProbabilityMeasure F) (f : F →ᵃⁱ[ℝ] E)
    (hmap : Measure.map f (ν : Measure F) = (μ : Measure E)) : LogConcave ν := by
  intro K L hK hL t ht ht1
  have hm (S : Set F) (hS : IsCompact S) : (μ : Measure E) (f '' S) = (ν : Measure F) S := by
    rw [← hmap, Measure.map_apply f.continuous.measurable (hS.image f.continuous).measurableSet,
      Set.preimage_image_eq _ f.injective]
  have hcomb : f '' {z | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
      {z | ∃ x ∈ f '' K, ∃ y ∈ f '' L, z = t • x + (1 - t) • y} := by
    have hf (x y : F) : f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y := by
      simpa only [AffineMap.lineMap_apply_module, sub_sub_cancel, AffineIsometry.coe_toAffineMap]
        using f.toAffineMap.apply_lineMap x y (1 - t)
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, hf x y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨t • x + (1 - t) • y, ⟨x, hx, y, hy, rfl⟩, hf x y⟩
  have hc : IsCompact {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he : {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : F × F => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x,y), ⟨hx,hy⟩, rfl⟩
      · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩; exact ⟨x,hx,y,hy,rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  have h := hμ (f '' K) (f '' L) (hK.image f.continuous) (hL.image f.continuous) t ht ht1
  rwa [hm K hK, hm L hL, ← hcomb, hm _ hc] at h

/-- Pushforward along an affine isometric embedding of a complete space preserves compact-set log-concavity
(the converse direction of `of_affineIsometry_map`; lower-dimensional images allowed, no density assumed). -/
theorem map_affineIsometry [CompleteSpace F]
    (ν : ProbabilityMeasure F) (hν : LogConcave ν)
    (μ : ProbabilityMeasure E) (f : F →ᵃⁱ[ℝ] E)
    (hmap : (μ : Measure E) = (ν : Measure F).map f) :
    LogConcave μ := by
  intro K L hK hL t ht0 ht1
  have hK' := f.isometry.isClosedEmbedding.isProperMap.isCompact_preimage hK
  have hL' := f.isometry.isClosedEmbedding.isProperMap.isCompact_preimage hL
  have h := hν (f ⁻¹' K) (f ⁻¹' L) hK' hL' t ht0 ht1
  have hf (x y : F) : f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y := by
    simpa only [AffineMap.lineMap_apply_module, sub_sub_cancel, AffineIsometry.coe_toAffineMap]
      using f.toAffineMap.apply_lineMap x y (1 - t)
  have hc : IsCompact {z : E | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he : {z : E | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : E × E => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  rw [hmap, Measure.map_apply f.continuous.measurable hK.measurableSet,
    Measure.map_apply f.continuous.measurable hL.measurableSet,
    Measure.map_apply f.continuous.measurable hc.measurableSet]
  apply h.trans (measure_mono ?_)
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨f x, hx, f y, hy, hf x y⟩

variable [ProperSpace E]

omit [BorelSpace E] in
/-- Equal-radius closed-ball masses inherit the log-concavity inequality. This is the
pointwise inequality needed for ball-average regularizations of the measure. -/
theorem closedBall_mul_le {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (x y : E) (r t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (μ : Measure E) (Metric.closedBall x r) ^ t *
        (μ : Measure E) (Metric.closedBall y r) ^ (1 - t) ≤
      (μ : Measure E) (Metric.closedBall (t • x + (1 - t) • y) r) := by
  refine (hμ _ _ (isCompact_closedBall x r) (isCompact_closedBall y r) t ht ht1).trans
    (measure_mono ?_)
  rintro z ⟨u, hu, v, hv, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_eq_norm] at hu hv
  have heq : t • u + (1 - t) • v - (t • x + (1 - t) • y) =
      t • (u - x) + (1 - t) • (v - y) := by simp only [smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖t • (u - x)‖ + ‖(1 - t) • (v - y)‖ := norm_add_le _ _
    _ = t * ‖u - x‖ + (1 - t) * ‖v - y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos ht, abs_of_pos (sub_pos.mpr ht1)]
    _ ≤ t * r + (1 - t) * r :=
      add_le_add (mul_le_mul_of_nonneg_left hu ht.le)
        (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr ht1.le))
    _ = r := by ring

omit [BorelSpace E] in
/-- Compact-set log-concavity forces the topological support to be convex. This uses positive
neighborhood masses, without presupposing an ambient density. -/
theorem convex_support {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    Convex ℝ (μ : Measure E).support := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hbeq : b = 1 - a := by linarith
  apply Metric.nhds_basis_closedBall.mem_measureSupport.mpr
  intro r hr
  have hxr := (Measure.mem_support_iff_forall x).mp hx _ (Metric.closedBall_mem_nhds x hr)
  have hyr := (Measure.mem_support_iff_forall y).mp hy _ (Metric.closedBall_mem_nhds y hr)
  have hpos : 0 < (μ : Measure E) (Metric.closedBall x r) ^ a *
      (μ : Measure E) (Metric.closedBall y r) ^ (1 - a) := by positivity
  simpa only [hbeq] using hpos.trans_le (hμ.closedBall_mul_le x y r a ha' ha1)

omit [BorelSpace E] in
/-- Superlevel sets of equal-radius closed-ball masses are convex. -/
theorem convex_closedBall_superlevel {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (r : ℝ) (A : ENNReal) :
    Convex ℝ {x | A ≤ (μ : Measure E) (Metric.closedBall x r)} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have ha1 : a < 1 := by have : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0); linarith
  have hbeq : b = 1 - a := by linarith
  change A ≤ _
  calc
    A = A ^ a * A ^ b := by
      rw [← ENNReal.rpow_add_of_nonneg a b ha hb, hab, ENNReal.rpow_one]
    _ ≤ (μ : Measure E) (Metric.closedBall x r) ^ a *
        (μ : Measure E) (Metric.closedBall y r) ^ b := by
      gcongr
      · exact hx
      · exact hy
    _ ≤ _ := by simpa only [hbeq] using hμ.closedBall_mul_le x y r a ha' ha1

end Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- Log-concavity is retained on the direction of the affine support, even for singular
ambient laws and a zero-dimensional carrier. -/
theorem intrinsicMeasure {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    LogConcave (Probability.intrinsicMeasure μ) :=
  hμ.of_affineIsometry_map (Probability.intrinsicMeasure μ) (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ).map_eq

omit [CompleteSpace E] in
/-- The intrinsic support has nonempty interior. This includes the singleton topology in
dimension zero and does not assert that the boundary has zero probability mass. -/
theorem interior_intrinsic_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    (interior (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support).Nonempty := by
  apply hμ.intrinsicMeasure.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
  exact Probability.affineSupport_intrinsicMeasure μ

omit [CompleteSpace E] in
/-- The intrinsic support boundary is Haar-null. Transferring this null set to the probability
law still requires the separate absolute-continuity theorem. -/
theorem haar_frontier_intrinsic_support {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [Measure.IsAddHaarMeasure m] :
    m (frontier (Probability.intrinsicMeasure μ : Measure _).support) = 0 :=
  hμ.intrinsicMeasure.convex_support.addHaar_frontier m

end FunctionalInequalities.KLS.LogConcave
