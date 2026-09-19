import FunctionalInequalities.Analysis.Lipschitz.Annuli
import FunctionalInequalities.Analysis.Lipschitz.Extension
import FunctionalInequalities.Analysis.Lipschitz.VectorCoarea
import FunctionalInequalities.Analysis.Vector.Jacobian
import FunctionalInequalities.KLS.Geometry.Surface.Measure

/-! # From the globally Lipschitz coarea formula to the locally Lipschitz one

`X2`, `X4` and `X5` of the route recorded in
`research/decisions/2026-09-19-locally-lipschitz-vector-coarea-route.md`.

`X2` is the compactness step: a locally Lipschitz map on a finite-dimensional space is Lipschitz on
every closed ball.  `X4` is the locality step: two maps agreeing on an open set have the same
differential and the same level sets on any piece inside it.  `X5` is the assembly, and it is the
codimension-`m` transcription of the scalar argument of
`KLS/Geometry/Coarea/LocallyLipschitz.lean`, step for step: the annuli of
`Analysis/Lipschitz/Annuli.lean` cut the ambient set into countably many disjoint measurable
pieces, on the piece of index `n` the map is replaced by a **globally** Lipschitz extension
supplied by `Analysis/Lipschitz/Extension.lean`, the hypothesis is applied to that extension, `X4`
carries the coarea Jacobian and the level sets back to the original map, and countable additivity
sums the pieces.

`X5` is stated as an **implication**: the globally Lipschitz codimension-`m` coarea formula is not
proved here and is not assumed to hold; it is a hypothesis.  Nothing in this file proves a coarea
formula, and the relation `k + finrank ℝ W = finrank ℝ V` between the codimension and the
dimensions is never used — it belongs to the hypothesis, which carries its own.

No boundedness, finiteness, integrability, positive-dimension or critical-set hypothesis is added:
`S` is an arbitrary measurable set and the weight `g` may be identically infinite.
-/

noncomputable section

open MeasureTheory Metric Module Set Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

/-- **`X2`: a locally Lipschitz map is Lipschitz on every closed ball.**  The closed balls of a
finite-dimensional normed space are compact, and a locally Lipschitz map is Lipschitz on a compact
set.  No relation between the constant and the radius is claimed. -/
theorem exists_lipschitzOnWith_closedBall {V W : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] {u : V → W} (hu : LocallyLipschitz u) (r : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K u (closedBall (0 : V) r) :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_closedBall (0 : V) r)
    hu.locallyLipschitzOn

/-- **`X4`: agreement on an open set transfers the differential and the level sets to any piece
inside it.**  The differential is a local notion, so `Filter.EventuallyEq.fderiv_eq` applies at each
point of the piece; the level sets agree by set extensionality.  No differentiability is assumed:
where neither map is differentiable both `fderiv`s are `0` and the identity still holds. -/
theorem fderiv_eq_and_inter_levelSet_eq_of_eqOn {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] {u v : V → W} {P O : Set V}
    (hO : IsOpen O) (hPO : P ⊆ O) (huv : EqOn u v O) :
    (∀ x ∈ P, fderiv ℝ u x = fderiv ℝ v x) ∧
      ∀ t : W, P ∩ {x | u x = t} = P ∩ {x | v x = t} := by
  refine ⟨fun x hx => Filter.EventuallyEq.fderiv_eq ?_, fun t => ?_⟩
  · exact Filter.eventually_of_mem (hO.mem_nhds (hPO hx)) fun y hy => huv hy
  · ext x
    constructor <;> rintro ⟨hx, ht⟩ <;> refine ⟨hx, ?_⟩ <;>
      simp only [Set.mem_ofPred_eq] at ht ⊢
    · rwa [← huv (hPO hx)]
    · rwa [huv (hPO hx)]

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **`X5`: the codimension-`m` coarea formula for globally Lipschitz maps implies the one for
locally Lipschitz maps.**  The hypothesis `hL` is the globally Lipschitz statement, which is **not**
proved here; the conclusion is the same statement with `LipschitzWith K u` weakened to
`LocallyLipschitz u`, so no global Lipschitz constant and no modulus of continuity survives.

The proof is the codimension-`m` copy of `KLS.coarea_of_locallyLipschitz`: half-open annuli, a
globally Lipschitz extension on each of them, locality of the differential and of the level sets,
and countable additivity.  The slice `AEMeasurable` conclusion is assembled by `AEMeasurable.tsum`
from the per-piece ones, because a locally Lipschitz map need not be Lipschitz on an unbounded
`S`. -/
theorem coarea_of_locallyLipschitz_of_lipschitz {k : ℕ}
    (hL : ∀ {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞}, LipschitzWith K u →
      MeasurableSet S → Measurable g →
      AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
          (volume : Measure W) ∧
        (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
              ∂(volume : Measure W)))
    {S : Set V} {u : V → W} {g : V → ℝ≥0∞} (hu : LocallyLipschitz u)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)) := by
  classical
  set ν : Measure V := KLS.hausdorffNormalized V k
  have hcont : Continuous u := hu.continuous
  -- Globally Lipschitz representatives of `u` on the closed balls: `X2` then `X1`.
  have hext : ∀ n : ℕ, ∃ w : V → W, (∃ K : ℝ≥0, LipschitzWith K w) ∧
      EqOn u w (closedBall (0 : V) ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_closedBall hu ((n : ℝ) + 1)
    obtain ⟨K', w, hwL, hweq⟩ := exists_lipschitzWith_eqOn_of_lipschitzOnWith hK
    exact ⟨w, ⟨K', hwL⟩, hweq.symm⟩
  choose v hvL hveq using hext
  -- The pieces: the half-open annuli, intersected with `S`.
  set P : ℕ → Set V := fun n => S ∩ annulus V n
  have hPm : ∀ n, MeasurableSet (P n) := fun n => hS.inter (measurableSet_annulus n)
  have hPd : Pairwise fun i j => Disjoint (P i) (P j) := fun i j hij =>
    (pairwise_disjoint_annulus V hij).mono inter_subset_right inter_subset_right
  have hPunion : (⋃ n, P n) = S := by
    refine Subset.antisymm (iUnion_subset fun _ => inter_subset_left) fun x hx => ?_
    have : x ∈ ⋃ n : ℕ, annulus V n := by rw [iUnion_annulus V]; trivial
    obtain ⟨n, hn⟩ := mem_iUnion.1 this
    exact mem_iUnion.2 ⟨n, hx, hn⟩
  -- `X4` on the open ball of radius `n + 1`, which contains the `n`-th piece.
  have hloc : ∀ n : ℕ, (∀ x ∈ P n, fderiv ℝ u x = fderiv ℝ (v n) x) ∧
      ∀ t : W, P n ∩ {x : V | u x = t} = P n ∩ {x : V | v n x = t} := fun n =>
    fderiv_eq_and_inter_levelSet_eq_of_eqOn (O := ball (0 : V) ((n : ℝ) + 1)) isOpen_ball
      (fun _ hx => annulus_subset_ball n hx.2)
      ((hveq n).mono ball_subset_closedBall)
  -- The hypothesis on the extension, transported back to `u`.
  have hpiece : ∀ n : ℕ,
      AEMeasurable (fun t : W => ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν)
          (volume : Measure W) ∧
        (∫⁻ x in P n, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W)) := by
    intro n
    obtain ⟨K, hK⟩ := hvL n
    have h := hL (S := P n) (u := v n) (g := g) hK (hPm n) hg
    simp_rw [← (hloc n).2] at h
    refine ⟨h.1, ?_⟩
    rw [← h.2]
    exact setLIntegral_congr_fun (hPm n) fun x hx => by rw [(hloc n).1 x hx]
  -- Countable additivity of both sides.
  have hlevel : ∀ t : W, MeasurableSet {x : V | u x = t} := fun t =>
    hcont.measurable (measurableSet_singleton t)
  have hsum : ∀ t : W, (∫⁻ y in S ∩ {x : V | u x = t}, g y ∂ν)
      = ∑' n, ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν := by
    intro t
    rw [← hPunion, iUnion_inter]
    exact lintegral_iUnion (fun n => (hPm n).inter (hlevel t))
      (fun i j hij => (hPd hij).mono inter_subset_left inter_subset_left) g
  refine ⟨?_, ?_⟩
  · simp_rw [hsum]
    exact AEMeasurable.tsum fun n => (hpiece n).1
  · calc (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V))
        = ∑' n, ∫⁻ x in P n, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
            ∂(volume : Measure V) := by
          rw [← hPunion]
          exact lintegral_iUnion hPm hPd _
      _ = ∑' n, ∫⁻ t, ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
          tsum_congr fun n => (hpiece n).2
      _ = ∫⁻ t, ∑' n, ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
          (lintegral_tsum fun n => (hpiece n).1).symm
      _ = _ := by simp_rw [← hsum]

/-- **`N0`: the codimension-`m` coarea formula for locally Lipschitz maps.**  `coarea_of_contDiff`
with `ContDiff ℝ 1 u` replaced by `LocallyLipschitz u`: no global Lipschitz constant, no `C¹`
regularity, no hypothesis on the critical set, no boundedness of `S`, no positivity of the
codimension.  It is `X5` applied to the proved globally Lipschitz formula `coarea_of_lipschitz`
(`L0`), and it is the common generalization of `L0` and of `coarea_of_contDiff`.  **It is not a
Sard theorem.** -/
theorem coarea_of_locallyLipschitz {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hu : LocallyLipschitz u)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)) :=
  coarea_of_locallyLipschitz_of_lipschitz (fun hu' hS' hg' => coarea_of_lipschitz hk hu' hS' hg')
    hu hS hg

end FunctionalInequalities.Analysis
