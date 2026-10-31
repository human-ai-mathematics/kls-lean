module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.HessianHolder

/-!
# Audit: the regular moment potential with Hölder Hessian

Real client of `exists_regular_moment_potential_holder_hessian` (Letwin, arXiv:2607.24164v1, Lemma
2.2 support, strong class).
From the original inputs only — smooth `κ`-uniformly convex `W`, compact convex `K` with nonempty
interior and the normalized
isotropic law `1_K e^{−W}` — it extracts one potential `u` with the gradient transport `(∇u)_*
e^{−u} = μ`, `C²` regularity, a
local Hölder Hessian on every ball, and the log-determinant equation with positive definite Hessian
and cap `16/κ` at every
point. It does not claim the full smooth lemma, Schauder/`C^∞` regularity or the merely convex
source class.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Matrix
open scoped ContDiff ENNReal NNReal

namespace LetwinHessianHolderAudit
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

section RegularMomentPotential
variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
  {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
  (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ :
    (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/--
One potential transports the tilted law to `μ`, is `C²` with a locally Hölder Hessian, and satisfies
the log-determinant
equation with positive definite Hessian and cap `16/κ` at every point — all for the same `u`. -/
theorem regular_moment_potential_transport_c2_holder_everywhere :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
          (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
        ContDiff ℝ 2 u ∧
          (∀ s : ℝ,
              0 < s →
                ∃ η C : ℝ≥0,
                  0 < η ∧
                    0 < C ∧
                      ∀ i j : Fin n,
                        HolderWith C η
                          (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s =>
                            hessianMatrix u x.val i j)) ∧
            ∀ x,
              (hessianMatrix u x).PosDef ∧
                Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
                  ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
  obtain
    ⟨u, _L, _LF, _T, _hconv, _hl, _hnorm, hmap, _hC1, _hG, _hF, _hd, _hT, hC2, _hHc, hEvery,
      hHol⟩ :=
    exists_regular_moment_potential_holder_hessian hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, hmap, hC2, fun s hs => ?_, hEvery⟩
  obtain ⟨η, C, hη, -, hC, hH⟩ := hHol s hs
  exact ⟨η, C, hη, hC, hH⟩

end RegularMomentPotential
end LetwinHessianHolderAudit

#print axioms LetwinHessianHolderAudit.regular_moment_potential_transport_c2_holder_everywhere
