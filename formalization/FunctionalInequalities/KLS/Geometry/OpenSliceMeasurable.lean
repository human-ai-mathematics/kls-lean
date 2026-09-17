import FunctionalInequalities.Analysis.Graph.OpenIntegral
import FunctionalInequalities.KLS.Geometry.SurfaceSlicing

/-! # Measurability of weighted slices on an open C¹ domain

The measurability component of L9. No regular-point hypothesis is needed for this component.
Local C¹ representatives and disjoint Borel pieces reduce it to the Lipschitz-on-set result.
This module does not assert the coarea equality.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Weighted slices of a Borel subset of an open C¹ domain are a.e. measurable.
The weight may take the value `∞`, and no regularity outside the domain is assumed. -/
theorem aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn
    {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) (hS : MeasurableSet S)
    (hSO : S ⊆ O) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) := by
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · simp [hSe]
  choose ρ w hρ hballO hwC hwEq using fun z : O =>
    Analysis.exists_contDiff_one_eqOn_ball hO hu z.2
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : O => Metric.ball (z : V) (ρ z)) (fun _ => Metric.isOpen_ball)
  have hOcov : ⋃ z : O, Metric.ball (z : V) (ρ z) = O :=
    Set.Subset.antisymm (Set.iUnion_subset fun z => hballO z) fun y hy =>
      Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hρ ⟨y, hy⟩)⟩
  have hTne : T.Nonempty := by
    have : z₀ ∈ ⋃ z ∈ T, Metric.ball (z : V) (ρ z) := by
      rw [hTu, hOcov]; exact hSO hz₀
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  let B : ℕ → Set V := fun n => Metric.ball ((σ n : O) : V) (ρ (σ n))
  have hBcov : O ⊆ ⋃ n, B n := by
    rw [← hOcov, ← hTu, hσ, Set.biUnion_range]
  set P : ℕ → Set V := disjointed fun n => S ∩ B n with hP
  have hPmeas : ∀ n, MeasurableSet (P n) :=
    MeasurableSet.disjointed fun n => hS.inter Metric.isOpen_ball.measurableSet
  have hPdisj : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed _
  have hPsub : ∀ n, P n ⊆ B n := fun n =>
    (disjointed_subset _ n).trans Set.inter_subset_right
  have hPunion : ⋃ n, P n = S := by
    rw [hP, iUnion_disjointed, ← Set.inter_iUnion]
    exact Set.inter_eq_self_of_subset_left (hSO.trans hBcov)
  have hslice : ∀ n t, P n ∩ {x | u x = t} = P n ∩ {x | w (σ n) x = t} := by
    intro n t
    ext x
    constructor <;> rintro ⟨hx, ht⟩ <;>
      exact ⟨hx, by simpa [hwEq (σ n) (hPsub n hx)] using ht⟩
  have hm : ∀ n, AEMeasurable
      (fun t : ℝ => ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) volume := by
    intro n
    obtain ⟨K, hK⟩ := (hwC (σ n)).contDiffOn.exists_lipschitzOnWith
      (by simp) (convex_closedBall ((σ n : O) : V) (ρ (σ n)))
      (isCompact_closedBall ((σ n : O) : V) (ρ (σ n)))
    simp_rw [hslice]
    exact aemeasurable_setLIntegral_inter_levelSet (hwC (σ n)).continuous
      (hK.mono fun x hx => Metric.ball_subset_closedBall (hPsub n hx)) (hPmeas n) hg
  have heq : ∀ t, (∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) =
      ∑' n, ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V) := by
    intro t
    rw [← hPunion, Set.iUnion_inter]
    apply lintegral_iUnion
    · intro n
      rw [hslice]
      exact (hPmeas n).inter ((hwC (σ n)).continuous.measurable (measurableSet_singleton t))
    · intro i j hij
      exact (hPdisj hij).mono Set.inter_subset_left Set.inter_subset_left
  simp_rw [heq]
  exact AEMeasurable.tsum hm

end FunctionalInequalities.KLS
