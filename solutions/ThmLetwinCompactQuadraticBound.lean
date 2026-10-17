import FunctionalInequalities.KLS.Letwin.CompactBound

/-!
# Lean certificate: `thm:letwin-compact-quadratic-bound`

Letwin, *The KLS constant is O(log^(1/4) n)* (arXiv:2607.24164v1, PDF SHA-256
`5dd9194cf36d91e2e4929a48564fe99d8d163a0a5ec7b31d80dc1f58a41778f1`), Theorem 1.2, in its **compact**
counterpart: for every `n > 0`, every compactly supported isotropic log-concave probability measure `μ` on
`EuclideanSpace ℝ (Fin n)` and every self-adjoint continuous linear `M` (singular and indefinite included),

`∫ (⟪M x, x⟫ - ∫ ⟪M y, y⟫ dμ)² dμ ≤ 8 ∑ᵢⱼ ⟪M eᵢ, eⱼ⟫²`

in the standard orthonormal basis, i.e. `Var_μ ⟨M X, X⟩ ≤ 8 ‖M‖²_HS`. This is exactly the existing
`KLS.LogConcave.Suspension.LetwinCompactBound` (with `Analysis.BakryEmery.LetwinQuadraticBound`), the input of
Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 4.2. No regular-class, smoothness, moment-map or input inequality is
assumed.

`certificate` states the expanded source form; `bound` states the named predicate. Both are proved by the canonical
`letwinCompactBound` (`KLS/Letwin/CompactBound.lean`). The noncompact Theorem 1.2 (every isotropic log-concave law),
Theorem 1.1, BKL Theorem 4.1 and KLS are not certified here.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Solutions.ThmLetwinCompactQuadraticBound

/-- **Letwin Theorem 1.2, compact counterpart**, in the expanded source form. -/
theorem certificate (n : ℕ) (hn : 0 < n) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ)
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hM : IsSelfAdjoint M) :
    ∫ x, (⟪M x, x⟫ - ∫ y, ⟪M y, y⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ^ 2
        ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      8 * ∑ i, ∑ j, ⟪M (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) i),
        stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) j⟫ ^ 2 :=
  FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound n hn μ hLC hiso hc M hM

/-- The named compact predicate used by the BKL localization argument. -/
theorem bound : FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound :=
  FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound

/--
info: 'Solutions.ThmLetwinCompactQuadraticBound.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmLetwinCompactQuadraticBound.certificate

/--
info: 'Solutions.ThmLetwinCompactQuadraticBound.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmLetwinCompactQuadraticBound.bound

end Solutions.ThmLetwinCompactQuadraticBound
