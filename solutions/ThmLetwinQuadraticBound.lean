import FunctionalInequalities.KLS.Letwin.QuadraticBound

/-!
# Lean source-form certificate: `thm:letwin-quadratic-bound`

Letwin, *The KLS constant is O(log^(1/4) n)*, arXiv:2607.24164v1, Theorem 1.2,
PDF SHA-256 `5dd9194cf36d91e2e4929a48564fe99d8d163a0a5ec7b31d80dc1f58a41778f1`:
for every `n > 0`, every isotropic log-concave probability law `μ` on `ℝⁿ`, and every
real symmetric matrix `M`, `Var_μ(XᵀMX) ≤ 8 tr(M²) = 2 E_μ ‖∇(XᵀMX)‖²`.
Singular and indefinite matrices are included, without compact support or an extra moment premise.

The library proof passes the separate compact constant-eight bound through centered,
covariance-whitened growing-ball truncations and convergence of mixed moments of degree at most
four. The compact certificate keeps its narrower statement and remains the BKL input.
This certificate packages Theorem 1.2; Theorem 1.1 has its own alternative-route certificate.
-/

open MeasureTheory ProbabilityTheory

namespace Solutions.ThmLetwinQuadraticBound

/-- Letwin Theorem 1.2 for arbitrary isotropic log-concave laws, in matrix source form. -/
theorem certificate (n : ℕ) (hn : 0 < n)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    variance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, M i j * x i * x j)
      (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ 8 * Matrix.trace (M * M) :=
  hLC.matrix_variance_le_eight hn hiso M hM

/--
info: 'Solutions.ThmLetwinQuadraticBound.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmLetwinQuadraticBound.certificate

end Solutions.ThmLetwinQuadraticBound
