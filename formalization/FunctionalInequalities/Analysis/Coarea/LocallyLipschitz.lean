import FunctionalInequalities.Analysis.Coarea.Lipschitz

/-! # Weighted coarea for locally Lipschitz functions

locally Lipschitz coarea: the weighted coarea formula and slice `AEMeasurable` with **no global Lipschitz bound and no
global modulus of any kind** — only `LocallyLipschitz u`.  This is a common generalization of the
two results it is built from: `LipschitzWith K u → LocallyLipschitz u` gives back globally Lipschitz coarea
(`coarea_of_lipschitz`), and `ContDiff ℝ 1 u → LocallyLipschitz u` gives back the hypothesis of
C¹ coarea (`coarea_of_contDiff`), so neither a Lipschitz constant nor `C¹` regularity is needed any
more.  Both original theorems keep their statements; nothing is restated through this one.

The reduction is by half-open annuli.  A finite-dimensional real normed space is proper, so `u` is
Lipschitz on each closed ball; McShane's extension replaces it there by a **globally** Lipschitz
`v k`, and globally Lipschitz coarea applies to `v k` on the piece `S ∩ (ball 0 (k+1) \ ball 0 k)`.  Each piece is
contained in the **open** ball, where `u` and `v k` agree on a neighbourhood of every point, so the
gradients agree pointwise and the level sets of `u` and `v k` cut each piece identically.  Countable
additivity over the disjoint pieces then assembles both conclusions; the sum is exchanged with the
outer integral by `lintegral_tsum`, whose hypothesis is exactly the per-piece `AEMeasurable` that
globally Lipschitz coarea supplies.

No boundedness, finite-volume, integrability, positive-dimension or `SFinite` surface-measure
assumption is imposed, the set `S` is an arbitrary measurable set, and the `ℝ≥0∞` weight may be
identically infinity.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal ContDiff Topology

namespace FunctionalInequalities.KLS

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **locally Lipschitz coarea**: weighted coarea for a locally Lipschitz function, including almost-everywhere slice
measurability.  No global Lipschitz constant and no `C¹` regularity is assumed. -/
theorem coarea_of_locallyLipschitz {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hu : LocallyLipschitz u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  classical
  have hcont : Continuous u := hu.continuous
  -- Globally Lipschitz representatives of `u` on the closed balls, by compactness and McShane.
  have hext : ∀ k : ℕ, ∃ w : V → ℝ, (∃ K : ℝ≥0, LipschitzWith K w) ∧
      EqOn u w (closedBall (0 : V) (k + 1)) := by
    intro k
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : V) ((k : ℝ) + 1)) hu.locallyLipschitzOn
    obtain ⟨w, hw, hweq⟩ := hK.extend_real
    exact ⟨w, ⟨K, hw⟩, hweq⟩
  choose v hvL hveq using hext
  -- The half-open annuli `k ≤ ‖x‖ < k + 1` are disjoint, measurable and cover `V`.
  let A : ℕ → Set V := fun k => ball (0 : V) (k + 1) \ ball (0 : V) k
  have hAsub : ∀ k, A k ⊆ ball (0 : V) ((k : ℝ) + 1) := fun _ => sdiff_subset
  have hAm : ∀ k, MeasurableSet (A k) := fun _ => measurableSet_ball.diff measurableSet_ball
  have hAd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    have key : ∀ i j : ℕ, i < j → Disjoint (A i) (A j) := by
      intro i j hij
      refine Set.disjoint_left.2 ?_
      rintro x ⟨hx1, -⟩ ⟨-, hx2⟩
      exact hx2 (ball_subset_ball (by exact_mod_cast Nat.succ_le_of_lt hij) hx1)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hAcover : ∀ x : V, ∃ k : ℕ, x ∈ A k := by
    intro x
    refine ⟨⌊‖x‖⌋₊, ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right] using Nat.lt_floor_add_one ‖x‖
    · simpa only [mem_ball, dist_zero_right, not_lt] using Nat.floor_le (norm_nonneg x)
  let P : ℕ → Set V := fun k => S ∩ A k
  have hPm : ∀ k, MeasurableSet (P k) := fun k => hS.inter (hAm k)
  have hPd : Pairwise (fun i j => Disjoint (P i) (P j)) := fun i j hij =>
    (hAd hij).mono inter_subset_right inter_subset_right
  have hPunion : (⋃ k, P k) = S := by
    refine Subset.antisymm (iUnion_subset fun _ => inter_subset_left) fun x hx => ?_
    obtain ⟨k, hk⟩ := hAcover x
    exact mem_iUnion.2 ⟨k, hx, hk⟩
  have hball : ∀ k, ∀ x ∈ P k, ball (0 : V) ((k : ℝ) + 1) ∈ 𝓝 x := fun k x hx =>
    isOpen_ball.mem_nhds (hAsub k hx.2)
  -- On the open ball the two functions agree, hence so do their gradients and their level sets.
  have hgrad : ∀ k, ∀ x ∈ P k, gradient u x = gradient (v k) x := fun k x hx =>
    EventuallyEq.gradient_eq
      (Filter.eventually_of_mem (hball k x hx) fun _ hy => hveq k (ball_subset_closedBall hy))
  have hslice : ∀ (k : ℕ) (t : ℝ), P k ∩ {x | v k x = t} = P k ∩ {x | u x = t} := by
    intro k t
    ext x
    constructor <;> rintro ⟨hx, ht⟩ <;> refine ⟨hx, ?_⟩ <;>
      simp only [mem_ofPred_eq] at ht ⊢
    · rwa [hveq k (ball_subset_closedBall (hAsub k hx.2))]
    · rwa [← hveq k (ball_subset_closedBall (hAsub k hx.2))]
  -- globally Lipschitz coarea on each piece, transported back to `u`.
  have hL12 : ∀ k,
      AEMeasurable (fun t : ℝ => ∫⁻ y in P k ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) volume ∧
      (∫⁻ x in P k, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
        ∫⁻ t, ∫⁻ y in P k ∩ {x | u x = t}, g y ∂(surfaceMeasure V) := by
    intro k
    obtain ⟨K, hK⟩ := hvL k
    have h := coarea_of_lipschitz (S := P k) (u := v k) (g := g) hK (hPm k) hg
    simp_rw [hslice k] at h
    refine ⟨h.1, ?_⟩
    rw [← h.2]
    exact setLIntegral_congr_fun (hPm k) fun x hx => by rw [hgrad k x hx]
  have hlevel : ∀ t : ℝ, MeasurableSet {x : V | u x = t} := fun t =>
    hcont.measurable (measurableSet_singleton t)
  have hsum : ∀ t : ℝ, (∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      = ∑' k, ∫⁻ y in P k ∩ {x | u x = t}, g y ∂(surfaceMeasure V) := by
    intro t
    rw [← hPunion, iUnion_inter]
    exact lintegral_iUnion (fun k => (hPm k).inter (hlevel t))
      (fun i j hij => (hPd hij).mono inter_subset_left inter_subset_left) g
  refine ⟨?_, ?_⟩
  · simp_rw [hsum]
    exact AEMeasurable.tsum fun k => (hL12 k).1
  · calc (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V))
        = ∑' k, ∫⁻ x in P k, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) := by
          rw [← hPunion]
          exact lintegral_iUnion hPm hPd _
      _ = ∑' k, ∫⁻ t, ∫⁻ y in P k ∩ {x | u x = t}, g y ∂(surfaceMeasure V) :=
          tsum_congr fun k => (hL12 k).2
      _ = ∫⁻ t, ∑' k, ∫⁻ y in P k ∩ {x | u x = t}, g y ∂(surfaceMeasure V) :=
          (lintegral_tsum fun k => (hL12 k).1).symm
      _ = _ := by simp_rw [← hsum]

end FunctionalInequalities.KLS
