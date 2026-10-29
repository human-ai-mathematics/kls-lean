import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import FunctionalInequalities.KLS.CEK.MomentRegularity.BootstrapThree
import FunctionalInequalities.Analysis.BakryEmery.SchauderBootstrap
import FunctionalInequalities.Analysis.BakryEmery.LineSmoothness

/-!
# The strong regular-class moment potential is smooth

Letwin, arXiv:2607.24164v1, Lemma 2.2, restricted to smooth globally uniformly convex W.
For every n > 0, the same regular moment potential retains every field of the C² producer and becomes C∞,
with locally Hölder derivatives of every order and a smooth gradient inverse on interior K.
The source's merely convex class is treated separately: `GivenGradient.lean` proves smoothness of a
given moment potential with Lipschitz gradient, and `KLS/Letwin/MomentMap.lean` applies it to a
limit potential.
-/
noncomputable section
namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms
open Set Metric Filter Topology MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff BigOperators ENNReal


variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A given regular moment potential is smooth, retaining the potential and all its existing
properties. C², local Hölder Hessian bounds and the positive Monge–Ampère equation are inputs;
no higher regularity, source-law existence or replacement potential is assumed. -/
theorem smooth_of_regular_moment_fields (hn : 0 < n) {u W : E → ℝ}
    (hC2 : ContDiff ℝ 2 u) (hW : ContDiff ℝ ∞ W)
    {L G : NNReal} (hl : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hPD : ∀ x, (hessianMatrix u x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix u x).det = -u x + W (gradient u x))
    (hLocal : ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
      ∀ i j : Fin n, HolderWith C η (fun x : ball (0 : E) s => hessianMatrix u x.val i j)) :
    ContDiff ℝ ∞ u ∧ ∀ m : ℕ, LocHolderDeriv m u := by
  by_cases hn2 : 2 ≤ n
  · obtain ⟨h3, hholder⟩ := contDiff_three_of_regular_fields hn2 hC2
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hl hG (fun x => ⟨hPD x, hMA x⟩) hLocal
    have hu : LocHolderDeriv 3 u := by
      refine ⟨h3, fun s hs => ?_⟩
      obtain ⟨η, C, hη0, hη1, _hC, _hbound, hhol⟩ := hholder s hs
      refine ⟨η, hη0, hη1, C, C.coe_nonneg, fun x hx y hy => ?_⟩
      rw [norm_iteratedFDeriv_three_sub]
      exact hhol x hx y hy
    have hall := locHolderDeriv_all_of_mongeAmpere hn2 hu hW hPD hMA
    exact ⟨contDiff_infty.mpr fun m => (hall m).contDiff, hall⟩
  have hn1 : n = 1 := by omega
  subst n
  have hsm := contDiff_infty_of_mongeAmpere_one hC2 hW hPD hMA
  refine ⟨hsm, fun m => ⟨hsm.of_le (natCast_le_infty m), ?_⟩⟩
  exact LocHolderMap.of_contDiff_one (hsm.iteratedFDeriv_right (m := 1) (i := m)
    (by
      change (↑(1 + m : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top))

section SameWitness
variable (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
  {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- Smooth potential and smooth inverse at the same strong regular-class witness; n ≥ 2. -/
private theorem exists_regular_moment_potential_smooth_of_two_le :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ContDiff ℝ 2 u ∧ Continuous (hessianMatrix u) ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)-hessianMatrix u x).PosSemidef) ∧
      (∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        ∀ i j : Fin n, HolderWith C η
          (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s => hessianMatrix u x.val i j)) ∧
      (∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ interior K,
        ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = gradient u x) ∧
      (∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 1 Ψ (interior K)) ∧
      ContDiff ℝ 3 u ∧
      (∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C) ∧
        ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
          ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
            ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
              C * ‖x - y‖ ^ (η : ℝ)) ∧
      (∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 2 Ψ (interior K)) ∧
      ContDiff ℝ ∞ u ∧ (∀ m : ℕ, LocHolderDeriv m u) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) := by
  have hn0 : 0 < n := by omega
  obtain ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHc,
      hEvery, hLocal, he, hΨ, h3, hholder, hΨ2⟩ :=
    exists_regular_moment_potential_contDiff_three hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hu : LocHolderDeriv 3 u := by
    refine ⟨h3, fun s hs => ?_⟩
    obtain ⟨η, C, hη0, hη1, hC, _hbound, hhol⟩ := hholder s hs
    refine ⟨η, hη0, hη1, C, C.coe_nonneg, fun x hx y hy => ?_⟩
    rw [norm_iteratedFDeriv_three_sub]
    exact hhol x hx y hy
  have hall := locHolderDeriv_all_of_mongeAmpere hn hu hW
    (fun x => (hEvery x).1) (fun x => (hEvery x).2.1)
  have hsm : ContDiff ℝ ∞ u := contDiff_infty.mpr fun m => (hall m).contDiff
  have hΨsm := Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn0
    (k := ∞) (by simp) hl hconv hnorm (by simpa using hsm) (fun x => (hEvery x).1)
    hK hKc hKint hW.continuous (hmap.trans hμ)
  exact ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHc,
    hEvery, hLocal, he, hΨ, h3, hholder, hΨ2, hsm, hall, hΨsm⟩

end SameWitness
section PositiveDimension
variable (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
  {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- The same strong regular-class moment potential and its gradient inverse are smooth, in every n > 0. -/
theorem exists_regular_moment_potential_smooth :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ContDiff ℝ 2 u ∧ Continuous (hessianMatrix u) ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)-hessianMatrix u x).PosSemidef) ∧
      (∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        ∀ i j : Fin n, HolderWith C η
          (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s => hessianMatrix u x.val i j)) ∧
      (∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ interior K,
        ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = gradient u x) ∧
      (∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 1 Ψ (interior K)) ∧
      ContDiff ℝ ∞ u ∧ (∀ m : ℕ, LocHolderDeriv m u) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) := by
  by_cases hn2 : 2 ≤ n
  · obtain ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHc,
        hEvery, hLocal, he, hΨ, _h3, _hholder, _hΨ2, hsm, hall, hΨsm⟩ :=
      exists_regular_moment_potential_smooth_of_two_le hn2 hκ hK hKc hKint hW hstrong μ hμ hiso
    exact ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHc,
      hEvery, hLocal, he, hΨ, hsm, hall, hΨsm⟩
  have hn1 : n = 1 := by omega
  subst n
  obtain ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHc,
      hEvery, hLocal, he, hΨ⟩ :=
    exists_regular_moment_potential_holder_hessian_inverse hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hsm := contDiff_infty_of_mongeAmpere_one hC2 hW
    (fun x => (hEvery x).1) (fun x => (hEvery x).2.1)
  have hall : ∀ m : ℕ, LocHolderDeriv m u := by
    intro m
    refine ⟨hsm.of_le (natCast_le_infty m), ?_⟩
    exact LocHolderMap.of_contDiff_one (hsm.iteratedFDeriv_right (m := 1) (i := m)
      (by change (↑(1 + m : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
  have hΨsm := Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn
    (k := ∞) (by simp) hl hconv hnorm (by simpa using hsm) (fun x => (hEvery x).1)
    hK hKc hKint hW.continuous (hmap.trans hμ)
  exact ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHc,
    hEvery, hLocal, he, hΨ, hsm, hall, hΨsm⟩

end PositiveDimension

end FunctionalInequalities.Analysis
