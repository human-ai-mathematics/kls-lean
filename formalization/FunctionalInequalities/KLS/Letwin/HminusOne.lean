module

public import FunctionalInequalities.KLS.LogConcave.HminusOneApproximation
public import FunctionalInequalities.KLS.BKL.Poincare

/-!
# Letwin Proposition 2.8 for general log-concave laws

Letwin, arXiv:2607.24164v1, Proposition 2.8 (quoting Barthe–Klartag, Proposition 10), display
(2.20), for every full-dimensional log-concave probability law on `ℝⁿ`. The family theorem
`KLS.LogConcave.variance_le_sum_dualNorm_sq_of_conjecture` assumes the KLS conjecture only to
bound Poincaré constants uniformly along its approximation; here that hypothesis is discharged by
the proved dimension-free bound `KLS.BKL.Localization.conjecture`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.KLS.LogConcave

/-- **Letwin Proposition 2.8 / Barthe–Klartag Proposition 10** (arXiv:2607.24164v1, (2.19)–(2.20)):
for a log-concave probability law `μ` on `ℝⁿ` with `affineSupport μ = ⊤` and a locally Lipschitz
`f` with `f ∈ L²(μ)` and every Fréchet partial derivative `∂ᵢ f = Df(·) eᵢ ∈ L²(μ)`,
`Var_μ f ≤ Σᵢ ‖∂ᵢ f‖²_{H⁻¹(μ)}`, the `H⁻¹` norm being `Energy.Dual.dualNorm` (supremum of
`∫ ∂ᵢ f · h dμ` over locally Lipschitz `h ∈ L²(μ)` with `∫ ‖∇h‖² dμ ≤ 1`). The right side may be
`⊤`. The source premise `E ∂ᵢ f = 0` is omitted because a finite right side forces it
(`Energy.Dual.integral_eq_zero_of_dualNorm_ne_top`). No isotropy or regularity of `μ` is assumed;
laws of lower affine dimension are excluded because the ambient-gradient statement fails there
(Gaussian on `{xₙ = 0}`, `f = x₁ + |xₙ|`). -/
theorem variance_le_sum_dualNorm_sq {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyLipschitz f) (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ENNReal.ofReal (variance f (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      ∑ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ^ 2 :=
  variance_le_sum_dualNorm_sq_of_conjecture BKL.Localization.conjecture hμ hfull hf hf2 hdf

end FunctionalInequalities.KLS.LogConcave
