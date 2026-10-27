import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Local finite-order and smooth extensions

A function of class `C^m`, for `m ≤ ∞`, on an open set agrees locally with a
function of the same class on the whole finite-dimensional real normed space.
The bump construction gives agreement on a ball; it does not extend the
function on its entire domain or assert real analyticity.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-- Local extension with an explicit agreement ball, for finite order or `C^∞`. -/
theorem exists_contDiff_eqOn_ball {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ∞} {f : E → F} {O : Set E} {z : E} (hO : IsOpen O) (hf : ContDiffOn ℝ m f O) (hz : z ∈ O) :
    ∃ (ρ : ℝ) (w : E → F), 0 < ρ ∧ Metric.ball z ρ ⊆ O ∧ ContDiff ℝ m w ∧
      Set.EqOn w f (Metric.ball z ρ) := by
  classical
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO z hz
  set χ : ContDiffBump z := ⟨r / 3, r / 2, by positivity, by linarith⟩ with hχ
  have hχsmall : Metric.ball z (r / 3) ⊆ O := fun y hy =>
    hrO (Metric.ball_subset_ball (by linarith) hy)
  have htsupp : tsupport (χ : E → ℝ) ⊆ O := by
    rw [χ.tsupport_eq]
    exact fun y hy => hrO (by
      simp only [Metric.mem_closedBall] at hy
      simpa [Metric.mem_ball] using hy.trans_lt (by simp [hχ]; linarith))
  refine ⟨r / 3, fun y => if y ∈ O then (χ y) • f y else 0, by positivity, hχsmall, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ O
    · refine ContDiffAt.congr_of_eventuallyEq
        ((χ.contDiff (n := m)).contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hy))) ?_
      filter_upwards [hO.mem_nhds hy] with y' hy'
      simp [hy']
    · have hyt : y ∈ (tsupport (χ : E → ℝ))ᶜ := fun hc => hy (htsupp hc)
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : F))) ?_
      filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hyt] with y' hy'
      have hzero : χ y' = 0 := image_eq_zero_of_notMem_tsupport hy'
      by_cases hy'O : y' ∈ O <;> simp [hy'O, hzero]
  · intro y hy
    have hyO : y ∈ O := hχsmall hy
    have hone : χ y = 1 := χ.one_of_mem_closedBall (by
      simpa [Metric.mem_closedBall, hχ] using (Metric.mem_ball.mp hy).le)
    simp [hyO, hone]


/-- Local extension expressed as equality in a neighbourhood of the chosen point. -/
theorem exists_contDiff_eventuallyEq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ∞} {f : E → F} {O : Set E} {z : E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ m f O) (hz : z ∈ O) :
    ∃ g : E → F, ContDiff ℝ m g ∧ g =ᶠ[𝓝 z] f := by
  obtain ⟨r, g, hr, _, hg, heq⟩ := exists_contDiff_eqOn_ball hO hf hz
  exact ⟨g, hg, Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Metric.ball z r, Metric.ball_mem_nhds z hr, heq⟩⟩

end FunctionalInequalities.Analysis
