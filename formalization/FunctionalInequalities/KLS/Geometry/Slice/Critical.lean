import FunctionalInequalities.KLS.Geometry.Surface.Slicing
import Mathlib.MeasureTheory.Function.Jacobian

/-! # The critical part of a `C¹` function has null level slices

Obligation `L10` of the weighted coarea route: for a `C¹` real function on a finite-dimensional
inner-product space, almost every level meets the critical set `{x | fderiv ℝ u x = 0}` in a set of
zero `surfaceMeasure`.

This is **not** Sard's theorem and does not imply it.  Sard asserts that the *image* of the
critical set is Lebesgue-null in `ℝ`, which in high dimension needs regularity `C^(finrank)` and
remains an unproved obligation (`Analysis.sard`).  The statement here is about the codimension-one
measure of the critical *part of each slice*, and it holds for merely `C¹` functions in every
dimension.  A `C¹` function may well have a positive-measure set of critical values; the assertion
is only that the critical part of almost every slice is `ℋ^{n-1}`-null.

The proof is the first genuine consumer of the Eilenberg bound `L1`
(`KLS.exists_measurable_majorant`).  On the critical set the derivative vanishes, so Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` — whose approximating linear maps are
values of the derivative — covers it by countably many **pairwise disjoint measurable** pieces on
which `u` is `ε`-Lipschitz, for any prescribed `ε > 0`.  Applying `L1` on each piece inside a ball
of radius `R` and summing gives a measurable majorant of the slice measure whose integral is at
most `eilenbergConstant V * ε * volume (closedBall 0 R)`.  Taking the pointwise infimum over
`ε = (k + 1)⁻¹` produces a measurable majorant of integral zero, so the slice measure vanishes
almost everywhere inside each ball, and a countable union over the radii removes the ball.

The critical set is closed because `fderiv ℝ u` is continuous, so no measurability hypothesis is
needed.  `u` is not assumed Lipschitz, bounded or proper, and `V` may be zero-dimensional. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

section Critical

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The critical set of a `C¹` function is closed: the derivative is continuous. -/
theorem isClosed_critical {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    IsClosed {x : V | fderiv ℝ u x = 0} :=
  isClosed_eq (hu.continuous_fderiv one_ne_zero) continuous_const

/-- Countably many pairwise disjoint measurable pieces covering the critical set, on each of which
`u` is `ε`-Lipschitz.  The approximating linear maps of
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` are values of the derivative, which
vanishes on the critical set, so the linear part drops out and the approximation becomes a genuine
Lipschitz estimate. -/
theorem exists_lipschitzOnWith_critical_cover {u : V → ℝ} (hu : ContDiff ℝ 1 u) {ε : ℝ≥0}
    (hε : ε ≠ 0) :
    ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧ (∀ n, MeasurableSet (T n)) ∧
      {x : V | fderiv ℝ u x = 0} ⊆ ⋃ n, T n ∧
      ∀ n, LipschitzOnWith ε u ({x : V | fderiv ℝ u x = 0} ∩ T n) := by
  rcases Set.eq_empty_or_nonempty {x : V | fderiv ℝ u x = 0} with hC | hC
  · refine ⟨fun _ => ∅, fun i j _ => by simp, fun _ => MeasurableSet.empty, by simp [hC], ?_⟩
    intro n
    simp only [Set.inter_empty]
    exact LipschitzOnWith.of_dist_le_mul fun x hx => absurd hx (Set.notMem_empty x)
  obtain ⟨T, A, hdisj, hmeas, hcov, happrox, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u {x : V | fderiv ℝ u x = 0}
      (fderiv ℝ u) (fun x _ => ((hu.differentiable one_ne_zero) x).hasFDerivAt.hasFDerivWithinAt)
      (fun _ => ε) (fun _ => hε)
  refine ⟨T, hdisj, hmeas, hcov, fun n => ?_⟩
  obtain ⟨y, hy, hAy⟩ := hA hC n
  have hA0 : A n = 0 := by rw [hAy]; exact hy
  refine LipschitzOnWith.of_dist_le_mul fun x hx y' hy' => ?_
  have h := happrox n x hx y' hy'
  rw [hA0] at h
  simpa [Real.dist_eq, Real.norm_eq_abs, dist_eq_norm] using h

/-- The critical slices inside a fixed ball are null at almost every level. -/
theorem ae_surfaceMeasure_critical_ball_eq_zero {u : V → ℝ} (hu : ContDiff ℝ 1 u) (R : ℕ) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ Metric.closedBall 0 R ∩ {x | u x = t})
        = 0 := by
  set C : Set V := {x : V | fderiv ℝ u x = 0} with hC
  set B : Set V := Metric.closedBall (0 : V) R with hB
  have hCmeas : MeasurableSet C := (isClosed_critical hu).measurableSet
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  have hBtop : (volume : Measure V) B ≠ (⊤ : ℝ≥0∞) := measure_closedBall_lt_top.ne
  -- A majorant at each scale `(k + 1)⁻¹`.
  have hscale : ∀ k : ℕ, ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ t, surfaceMeasure V (C ∩ B ∩ {x | u x = t}) ≤ G t) ∧
      (∫⁻ t, G t ∂(volume : Measure ℝ))
        ≤ (eilenbergConstant V : ℝ≥0∞) * volume B * ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro k
    obtain ⟨T, hdisj, hTmeas, hcov, hlip⟩ :=
      exists_lipschitzOnWith_critical_cover hu (ε := ((k : ℝ≥0) + 1)⁻¹) (by positivity)
    set D : ℕ → Set V := fun n => C ∩ B ∩ T n with hD
    have hDmeas : ∀ n, MeasurableSet (D n) := fun n => (hCmeas.inter hBmeas).inter (hTmeas n)
    have hDdisj : Pairwise (Function.onFun Disjoint D) := fun i j hij =>
      ((hdisj hij).mono Set.inter_subset_right Set.inter_subset_right)
    have hDunion : ⋃ n, D n = C ∩ B := by
      refine Set.Subset.antisymm (Set.iUnion_subset fun n => Set.inter_subset_left) fun x hx => ?_
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hcov hx.1)
      exact Set.mem_iUnion.2 ⟨n, hx, hn⟩
    choose F hFmeas hFdom hFint using fun n =>
      exists_measurable_majorant (u := u) (S := D n)
        ((hlip n).mono (fun x hx => ⟨hx.1.1, hx.2⟩))
    refine ⟨fun t => ∑' n, F n t, ?_, fun t => ?_, ?_⟩
    · simp only [ENNReal.tsum_eq_iSup_sum]
      exact Measurable.iSup fun s => Finset.measurable_sum s fun n _ => hFmeas n
    · calc surfaceMeasure V (C ∩ B ∩ {x | u x = t})
          = surfaceMeasure V (⋃ n, D n ∩ {x | u x = t}) := by
            rw [← Set.iUnion_inter, hDunion]
        _ ≤ ∑' n, surfaceMeasure V (D n ∩ {x | u x = t}) := measure_iUnion_le _
        _ ≤ ∑' n, F n t := ENNReal.tsum_le_tsum fun n => hFdom n t
    · rw [lintegral_tsum fun n => (hFmeas n).aemeasurable]
      calc ∑' n, ∫⁻ t, F n t ∂(volume : Measure ℝ)
          ≤ ∑' n, (eilenbergConstant V : ℝ≥0∞) * (((k : ℝ≥0) + 1)⁻¹ : ℝ≥0) * volume (D n) :=
            ENNReal.tsum_le_tsum hFint
        _ = (eilenbergConstant V : ℝ≥0∞) * (((k : ℝ≥0) + 1)⁻¹ : ℝ≥0) * volume (C ∩ B) := by
            rw [ENNReal.tsum_mul_left, ← measure_iUnion hDdisj hDmeas, hDunion]
        _ ≤ (eilenbergConstant V : ℝ≥0∞) * volume B * ((k : ℝ≥0∞) + 1)⁻¹ := by
            rw [ENNReal.coe_inv (by positivity)]
            push_cast
            rw [mul_assoc, mul_assoc, mul_comm ((k : ℝ≥0∞) + 1)⁻¹]
            gcongr
            exact Set.inter_subset_right
  choose G hGmeas hGdom hGint using hscale
  -- The pointwise infimum is a measurable majorant of integral zero.
  have hHzero : ∫⁻ t, ⨅ k : ℕ, G k t ∂(volume : Measure ℝ) = 0 := by
    have htend : Tendsto
        (fun k : ℕ => (eilenbergConstant V : ℝ≥0∞) * volume B * ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have hinv : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have h : (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) = fun k : ℕ => ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          funext k; norm_cast
        rw [h]
        exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      have := ENNReal.Tendsto.const_mul (a := (eilenbergConstant V : ℝ≥0∞) * volume B) hinv
        (Or.inr (by simp [ENNReal.mul_eq_top, hBtop]))
      simpa using this
    refine le_antisymm (ge_of_tendsto' htend fun k => ?_) (by simp)
    exact (lintegral_mono fun t => iInf_le _ k).trans (hGint k)
  filter_upwards [(lintegral_eq_zero_iff (Measurable.iInf hGmeas)).1 hHzero] with t ht
  refine le_antisymm ?_ (by simp)
  simpa [ht] using le_iInf fun k => hGdom k t

/-- **The critical part of almost every level is null** (obligation `L10`).

Not Sard's theorem: nothing is claimed about the Lebesgue measure of the set of critical *values*,
which for a merely `C¹` function may well be positive. -/
theorem ae_surfaceMeasure_critical_inter_levelSet_eq_zero {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 := by
  filter_upwards [(ae_all_iff (ι := ℕ)).2 fun R => ae_surfaceMeasure_critical_ball_eq_zero hu R]
    with t ht
  have hsplit : {x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}
      = ⋃ R : ℕ, ({x : V | fderiv ℝ u x = 0} ∩ Metric.closedBall 0 R ∩ {x | u x = t}) := by
    rw [← Set.iUnion_inter, ← Set.inter_iUnion, Metric.iUnion_closedBall_nat, Set.inter_univ]
  rw [hsplit]
  exact measure_iUnion_null ht

end Critical

end FunctionalInequalities.KLS
