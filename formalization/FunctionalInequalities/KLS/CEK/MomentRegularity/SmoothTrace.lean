module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.Smooth
public import FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein

/-!
# A smooth regular moment potential with the sharp trace bound

Letwin arXiv:2607.24164v1, Theorem 2.5 in the strong regular class, every n > 0.
Select one actual weak moment potential with the sharp trace inequality. Apply the given-potential
Hölder-Hessian and smoothness theorems to this same u. Every field of the earlier smooth producer
is retained, followed by the mean Hessian identity and the exact bound
`∫ tr(B Hess u B Hess u) ≤ 2 tr(B²)` for every real symmetric B. No equality of unrelated
existential witnesses or uniqueness theorem is used. The merely convex source class is separate.
-/

@[expose] public section
noncomputable section
namespace FunctionalInequalities.Analysis
open Set Metric Filter Topology MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff ENNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

section SameWitness
variable (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
  {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

set_option maxHeartbeats 1000000 in
/-- **Smooth regular moment potential with the sharp trace bound, at one witness.** Every field of
`exists_regular_moment_potential_smooth` in the same order, then the mean-identity field and the
weak Theorem 2.5 bound
`E tr(B Hess u B Hess u) ≤ 2 tr(B²)` for every real symmetric `B`, all for the SAME `u`, `L`, `LF`,
`T`. -/
theorem exists_regular_moment_potential_smooth_trace :
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
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
              S)) ∧
      ContDiff ℝ 2 u ∧ Continuous (hessianMatrix u) ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ)-hessianMatrix u x).PosSemidef) ∧
      (∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        ∀ i j : Fin n, HolderWith C η
          (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s => hessianMatrix u x.val i j)) ∧
      (∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ interior K,
        ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = gradient u x) ∧
      (∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 1 Ψ (interior K)) ∧
      ContDiff ℝ ∞ u ∧ (∀ m : ℕ, LocHolderDeriv m u) ∧
      (∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K)) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace) := by
    obtain ⟨u, L, LF, T, hCanonical⟩ :=
      exists_regular_moment_weak_stein_coupling hn hκ hK hKc hKint hW hstrong μ hμ hiso
    have hT25 := hCanonical.1.1.2
    obtain ⟨hbase, _hcutoffs⟩ := hCanonical.1.1.1.1.1.1
    obtain
      ⟨hconv, hl, hnorm, hmap, hC1, hG, hF, _hw, hd, hT, _he, hfirst, hInv, hmean, _hq,
        _hflux, _hweighted, _hbounded⟩ :=
      hbase
    obtain ⟨hC2, hHcont, hEvery, hLocal⟩ :=
      holder_hessian_of_weak_evolution_fields hn hκ hW hstrong μ
        ⟨hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hfirst, hInv⟩
    -- the gradient homeomorphism and the `C¹` inverse (as in `Inverse.lean`)

    have hm := hmap.trans hμ
    have he :=
      Probability.MomentMeasure.exists_gradient_homeomorph_interior_of_map_gradient hn
        hl hconv hnorm hC1 hK hKc hKint hW.continuous hm
    have hΨ :=
      Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn (k := 1)
        (by norm_num) hl hconv hnorm (by convert hC2 using 1; norm_num)
        (fun x => (hEvery x).1) hK hKc hKint hW.continuous hm
    obtain ⟨hsm, hall⟩ :=
      smooth_of_regular_moment_fields hn hC2 hW hl hG (fun x => (hEvery x).1)
        (fun x => (hEvery x).2.1) hLocal
    have hΨsm :=
      Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn (k := ∞)
        (by simp) hl hconv hnorm (by simpa using hsm) (fun x => (hEvery x).1) hK hKc
        hKint hW.continuous hm
    exact
      ⟨u, L, LF, T, hconv, hl, hnorm, hmap, hC1, hG, hF, hd, hT, hC2, hHcont, hEvery,
        hLocal, he, hΨ, hsm, hall, hΨsm, hmean, hT25⟩

end SameWitness
end FunctionalInequalities.Analysis
