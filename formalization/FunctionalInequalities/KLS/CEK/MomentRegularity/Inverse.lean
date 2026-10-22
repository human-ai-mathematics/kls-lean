import FunctionalInequalities.KLS.CEK.MomentRegularity.HessianHolder
import FunctionalInequalities.Probability.MomentMeasure.Gradient

/-!
# Regular moment potentials with a gradient inverse

At the regular moment potential `u` of `exists_regular_moment_potential_holder_hessian` (smooth `κ`-uniformly convex `W`,
compact convex `K` with nonempty interior, normalized isotropic `1_K e^{−W}` law; Letwin, arXiv:2607.24164v1, Lemma 2.2 support),
one call of that producer keeps `u`, `L`, `LF`, `T` and all of its fields, and adds a homeomorphism `∇u : ℝⁿ ≃ₜ interior K`
and a `C¹` left inverse of `∇u` on `interior K` for the same `u`. Not full Schauder/`C^∞` regularity and not the merely convex
Lemma 2.2.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

section RegularMomentInverse

open Set Metric MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
open scoped Topology NNReal ContDiff ENNReal

section SameWitness
variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- **Regular moment potential with a gradient inverse** (Letwin, arXiv:2607.24164v1, Lemma 2.2 support, strong class). For
the same `u`, `L`, `LF` and `T`, every field of `exists_regular_moment_potential_holder_hessian` in the same order, followed
by a homeomorphism `∇u : ℝⁿ ≃ₜ interior K` and a `C¹` left inverse `Ψ` of `∇u` on `interior K`. Not full Schauder/`C^∞`
regularity and not the merely convex Lemma 2.2. -/
theorem exists_regular_moment_potential_holder_hessian_inverse :
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
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 1 Ψ (interior K) := by
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hC2,hHcont,hEvery,hLocal⟩ :=
    Analysis.exists_regular_moment_potential_holder_hessian hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hm := hmap.trans hμ
  have he := Probability.MomentMeasure.exists_gradient_homeomorph_interior_of_map_gradient hn hl hconv hnorm hC1
    hK hKc hKint hW.continuous hm
  have hi := Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn (k := 1) (by norm_num) hl hconv hnorm
    (by convert hC2 using 1; norm_num) (fun x => (hEvery x).1) hK hKc hKint hW.continuous hm
  exact ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hC2,hHcont,hEvery,hLocal,he,hi⟩

end SameWitness

end RegularMomentInverse

end FunctionalInequalities.Analysis
