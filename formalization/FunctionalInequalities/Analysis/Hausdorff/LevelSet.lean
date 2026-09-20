import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Regular level sets as local Lipschitz graphs

At a regular point of a C¹ function, the level set is locally a Lipschitz image of a bounded
subset of the derivative kernel. In finite dimensions this gives locally finite Hausdorff
measure. The graph statement retains its Banach-space scope; regularity is pointwise.
No assertion of local finiteness at excluded boundary points is made.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise

namespace FunctionalInequalities

universe u

namespace Analysis

section LipschitzGraph

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Lipschitz-graph form of the implicit function theorem: near a regular point `x` of a `C¹`
function, the level set through `x` is contained in the image of a bounded subset of the tangent
hyperplane `ker (Dφ x)` under a Lipschitz map.  No finite-dimensionality is needed; completeness
is what the implicit function theorem uses. -/
theorem exists_lipschitzOnWith_levelSet_subset_image {φ : V → ℝ} (hφ : ContDiff ℝ 1 φ) {x : V}
    (hx : fderiv ℝ φ x ≠ 0) :
    ∃ (N : Set V) (K : ℝ≥0) (s : Set (LinearMap.ker (fderiv ℝ φ x).toLinearMap))
      (g : LinearMap.ker (fderiv ℝ φ x).toLinearMap → V),
      N ∈ 𝓝 x ∧ Bornology.IsBounded s ∧ LipschitzOnWith K g s ∧
        N ∩ {y | φ y = φ x} ⊆ g '' s := by
  classical
  have hne : (fderiv ℝ φ x).toLinearMap ≠ 0 := fun h =>
    hx (ContinuousLinearMap.coe_injective (h.trans ContinuousLinearMap.toLinearMap_zero.symm))
  have hrange : (fderiv ℝ φ x).range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hne
  have hstrict : HasStrictFDerivAt φ (fderiv ℝ φ x) x := hφ.hasStrictFDerivAt one_ne_zero
  have hker : (fderiv ℝ φ x).ker.ClosedComplemented :=
    (fderiv ℝ φ x).ker_closedComplemented_of_finiteDimensional_range
  set P := Classical.choose hker with hPdef
  set g := hstrict.implicitFunctionOfComplemented φ (fderiv ℝ φ x) hrange hker (φ x) with hgdef
  have hgd : HasStrictFDerivAt g (fderiv ℝ φ x).ker.subtypeL 0 :=
    hstrict.to_implicitFunctionOfComplemented hrange hker
  obtain ⟨K, t, ht, hlip⟩ := hgd.exists_lipschitzOnWith
  have hPcont : Continuous fun y : V => P (y - x) := P.continuous.comp (continuous_id.sub continuous_const)
  have hpre : (fun y : V => P (y - x)) ⁻¹' t ∈ 𝓝 x := by
    exact hPcont.continuousAt.preimage_mem_nhds (by simpa using ht)
  obtain ⟨A, hA, hAsub⟩ := Filter.eventually_iff_exists_mem.mp
    (hstrict.eq_implicitFunctionOfComplemented hrange hker)
  refine ⟨A ∩ ((fun y : V => P (y - x)) ⁻¹' t) ∩ Metric.ball x 1, K,
    (fun y : V => P (y - x)) '' ((A ∩ ((fun y : V => P (y - x)) ⁻¹' t) ∩ Metric.ball x 1)
      ∩ {y | φ y = φ x}), g, ?_, ?_, ?_, ?_⟩
  · exact Filter.inter_mem (Filter.inter_mem hA hpre) (Metric.ball_mem_nhds x one_pos)
  · refine (Metric.isBounded_closedBall (x := (0 : LinearMap.ker (fderiv ℝ φ x).toLinearMap))
      (r := ‖P‖)).subset ?_
    rintro _ ⟨y, ⟨⟨⟨-, -⟩, hy1⟩, -⟩, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    refine (P.le_opNorm _).trans ?_
    have : ‖y - x‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact (Metric.mem_ball.mp hy1).le
    nlinarith [norm_nonneg P, norm_nonneg (y - x)]
  · refine hlip.mono ?_
    rintro _ ⟨y, ⟨⟨⟨-, hy2⟩, -⟩, -⟩, rfl⟩
    exact hy2
  · rintro y ⟨hyN, hylev⟩
    refine ⟨(fun y : V => P (y - x)) y, ⟨y, ⟨hyN, hylev⟩, rfl⟩, ?_⟩
    have h1 := hAsub y hyN.1.1
    rw [hgdef, ← hylev]
    exact h1

end LipschitzGraph

section LevelSet

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- At a regular point of a `C¹` function the level set through that point has finite
`(n-1)`-dimensional Hausdorff measure in some neighbourhood.  General form of
`SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`. -/
theorem exists_hausdorffMeasure_levelSet_lt_top {φ : V → ℝ} (hφ : ContDiff ℝ 1 φ) {x : V}
    (hx : fderiv ℝ φ x ≠ 0) :
    ∃ N ∈ 𝓝 x, μH[(Module.finrank ℝ V : ℝ) - 1] (N ∩ {y | φ y = φ x}) < ⊤ := by
  classical
  obtain ⟨N, K, s, g, hN, hsb, hg, hsub⟩ := exists_lipschitzOnWith_levelSet_subset_image hφ hx
  refine ⟨N, hN, ?_⟩
  have hne : (fderiv ℝ φ x).toLinearMap ≠ 0 := fun h =>
    hx (ContinuousLinearMap.coe_injective (h.trans ContinuousLinearMap.toLinearMap_zero.symm))
  have hrank :
      Module.finrank ℝ (LinearMap.ker (fderiv ℝ φ x).toLinearMap) + 1 = Module.finrank ℝ V :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hne
  have hd : ((Module.finrank ℝ V : ℝ) - 1)
      = (Module.finrank ℝ (LinearMap.ker (fderiv ℝ φ x).toLinearMap) : ℝ) := by
    rw [← hrank]; push_cast; ring
  rw [hd]
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  refine lt_of_le_of_lt (hg.hausdorffMeasure_image_le (Nat.cast_nonneg _)) ?_
  refine ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (Nat.cast_nonneg _) ENNReal.coe_ne_top) ?_
  obtain ⟨r, hr⟩ := hsb.subset_closedBall 0
  exact lt_of_le_of_lt (measure_mono hr)
    ((isCompact_closedBall (0 : LinearMap.ker (fderiv ℝ φ x).toLinearMap) r).measure_lt_top)

end LevelSet

end Analysis

end FunctionalInequalities
