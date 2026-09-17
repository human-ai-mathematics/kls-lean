import FunctionalInequalities.Analysis.Graph.Integral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Weighted graph area over an open parameter domain

Obligation `L8` of the weighted coarea route: the weighted change of variables
`setLIntegral_image_graphChartMap` of `Analysis/Graph/Integral.lean` requires the graph function to
be `C¹` on the **whole** parameter space.  Here it is localized to a function that is `C¹` only on
an open set `O`, for measurable parameter sets `S ⊆ O`.

A `ContDiffOn` function on an open set does **not** extend to a globally `C¹` function — `1 / x`
on `(0, ∞)` is the standard counterexample — so the localization is genuinely countable and cannot
be done by one global extension.  What is true, and is what `exists_contDiff_one_eqOn_ball` proves,
is that every point of `O` has a ball on which some globally `C¹` function agrees with the given
one: multiply by a `ContDiffBump` supported inside `O`.  This is the interior localization the route
prescribes; it is **not** the Whitney extension from a closed set, which is the separate unproved
obligation `L6`.

Second countability then extracts a countable subfamily of such balls covering `O`, `disjointed`
turns it into countably many pairwise disjoint measurable pieces of `S`, and the graph map is
injective (`graphMap_injective`), so the images of the pieces are disjoint and measurable.  Both
sides of the identity are countably additive over those pieces, and on each piece the global
theorem applies to the local extension; the gradients agree because the functions agree on an
**open** ball around each point (`Filter.EventuallyEq.gradient_eq`).

`Analysis/Sard/Smooth.lean` already contains the `C^∞` analogue `exists_contDiff_eventuallyEq`, with
an eventual equality rather than an explicit ball.  It is deliberately left untouched: generalizing
its order or strengthening its conclusion would change a published signature, so the `C¹` variant
needed here is proved separately.

No integrability, boundedness or finiteness hypothesis is used; the weight may be unbounded or
identically `∞`, `S` need not be bounded or of finite measure, and `O = ∅` or `S = ∅` are covered.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section Extension

/-- A function that is `C¹` on an open set agrees with a globally `C¹` function on a ball around
any of its points.  Multiplication by a bump supported in the open set; differentiability is a
local property.  The `C^∞` analogue is `Analysis.exists_contDiff_eventuallyEq`. -/
theorem exists_contDiff_one_eqOn_ball {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O : Set E} {z : E} (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) (hz : z ∈ O) :
    ∃ (ρ : ℝ) (w : E → F), 0 < ρ ∧ Metric.ball z ρ ⊆ O ∧ ContDiff ℝ 1 w ∧
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
        ((χ.contDiff (n := 1)).contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hy))) ?_
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

end Extension

section OpenGraph

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The weighted change of variables for the untranslated graph map: the `x₀ = 0` case of
`setLIntegral_image_graphChartMap`. -/
theorem setLIntegral_image_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in graphMap ι e g '' s, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y)) * f (graphMap ι e g y)
          ∂(volume : Measure H) := by
  have h : graphChartMap ι e 0 g = graphMap ι e g := by
    funext y; rw [graphChartMap, zero_add]
  simpa [h] using setLIntegral_image_graphChartMap ι he hperp 0 hg hs hf

/-- **Weighted graph area over an open parameter domain** (obligation `L8`).  The graph function is
`C¹` only on the open set `O`, and the parameter set is any measurable `S ⊆ O`.

No integrability of the weight, no boundedness or finite measure of `S`, and no global regularity
of `v` outside `O`; `O = ∅` and `S = ∅` are covered. -/
theorem setLIntegral_image_graphMap_of_contDiffOn (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {O S : Set H} {v : H → ℝ} {f : V → ℝ≥0∞}
    (hO : IsOpen O) (hv : ContDiffOn ℝ 1 v O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hf : Measurable f) :
    ∫⁻ x in graphMap ι e v '' S, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · simp [hSe]
  -- every point of `O` carries a ball with a global `C¹` representative
  choose ρ w hρ hballO hwC hwEq using fun z : O => exists_contDiff_one_eqOn_ball hO hv z.2
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : O => Metric.ball (z : H) (ρ z)) (fun _ => Metric.isOpen_ball)
  have hOcov : ⋃ z : O, Metric.ball ((z : H)) (ρ z) = O :=
    Set.Subset.antisymm (Set.iUnion_subset fun z => hballO z) fun y hy =>
      Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hρ ⟨y, hy⟩)⟩
  have hTne : T.Nonempty := by
    have : z₀ ∈ ⋃ z ∈ T, Metric.ball ((z : H)) (ρ z) := by rw [hTu, hOcov]; exact hSO hz₀
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  set B : ℕ → Set H := fun n => Metric.ball ((σ n : O) : H) (ρ (σ n)) with hB
  have hBcov : O ⊆ ⋃ n, B n := by
    rw [← hOcov, ← hTu, hσ, Set.biUnion_range]
  have hWeq : ∀ n, Set.EqOn (w (σ n)) v (B n) := fun n => hwEq (σ n)
  -- disjoint measurable pieces of `S`
  set P : ℕ → Set H := disjointed fun n => S ∩ B n with hP
  have hPmeas : ∀ n, MeasurableSet (P n) :=
    MeasurableSet.disjointed fun n => hS.inter Metric.isOpen_ball.measurableSet
  have hPdisj : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed _
  have hPsub : ∀ n, P n ⊆ B n := fun n =>
    (disjointed_subset _ n).trans Set.inter_subset_right
  have hPunion : ⋃ n, P n = S := by
    rw [hP, iUnion_disjointed, ← Set.inter_iUnion]
    exact Set.inter_eq_self_of_subset_left (hSO.trans hBcov)
  -- the images are the images of the local representatives
  have himgEq : ∀ n, graphMap ι e v '' P n = graphMap ι e (w (σ n)) '' P n := fun n =>
    (Set.image_congr fun y hy => by
      simp only [graphMap]; rw [hWeq n (hPsub n hy)]).symm
  have himgMeas : ∀ n, MeasurableSet (graphMap ι e v '' P n) := fun n => by
    rw [himgEq n]
    exact measurableSet_image_graphMap ι hperp (hwC (σ n)).continuous (hPmeas n)
  have himgDisj : Pairwise (Function.onFun Disjoint fun n => graphMap ι e v '' P n) := by
    intro i j hij
    exact (Set.disjoint_image_iff (graphMap_injective ι hperp v)).2 (hPdisj hij)
  calc ∫⁻ x in graphMap ι e v '' S, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ x in ⋃ n, graphMap ι e v '' P n, f x
          ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)) := by
        rw [← Set.image_iUnion, hPunion]
    _ = ∑' n, ∫⁻ x in graphMap ι e v '' P n, f x
          ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)) :=
        lintegral_iUnion himgMeas himgDisj f
    _ = ∑' n, ∫⁻ y in P n, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := by
        refine tsum_congr fun n => ?_
        rw [himgEq n, setLIntegral_image_graphMap ι he hperp (hwC (σ n)) (hPmeas n) hf]
        refine setLIntegral_congr_fun (hPmeas n) fun y hy => ?_
        have hnb : w (σ n) =ᶠ[𝓝 y] v :=
          Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (hPsub n hy)) (hWeq n)
        simp only [graphMap]
        rw [hnb.gradient_eq, hWeq n (hPsub n hy)]
    _ = ∫⁻ y in ⋃ n, P n, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := (lintegral_iUnion hPmeas hPdisj _).symm
    _ = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := by rw [hPunion]

end OpenGraph

end FunctionalInequalities.Analysis
