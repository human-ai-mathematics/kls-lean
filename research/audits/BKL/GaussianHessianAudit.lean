import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Hessian

/-!
# Audit: upper Hessian bound of the Gaussian-smoothed potential (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5 (regular approximation:
`∇²V_ε ≤ ε⁻¹ Id`; the kernel `e^{-s‖x-y‖²}` has variance `ε = 1/(2s)`, so the bound is `2s`).
Clients: the unit direction at `s = 3` gives the bound `6` and the posterior variance bound `1/6`
for every probability law with a Borell density on `ℝ¹`; dimension zero gives the bound `0`.
Neither polynomial growth of all derivatives nor the regular approximation theorem is asserted.
Clients adapted from the Codex bundle `Gaussian-Hessian-Upper/Clients.lean`.
-/

open MeasureTheory ProbabilityTheory FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace GaussianHessianAudit

theorem upper_at_s_three {μ : Measure (EuclideanSpace ℝ (Fin 1))} [IsProbabilityMeasure μ]
    {ρ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    (x : EuclideanSpace ℝ (Fin 1)) :
    bilinearIteratedFDerivTwo ℝ (potential ρ 3) x
      (EuclideanSpace.basisFun (Fin 1) ℝ 0) (EuclideanSpace.basisFun (Fin 1) ℝ 0) ≤ 6 := by
  have h := bilinearIteratedFDerivTwo_potential_le hρ (by norm_num : (0 : ℝ) < 3)
    x (EuclideanSpace.basisFun (Fin 1) ℝ 0)
  have he : ‖EuclideanSpace.basisFun (Fin 1) ℝ 0‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 1) ℝ).norm_eq_one 0
  norm_num [he, EuclideanSpace.basisFun_apply] at h ⊢
  exact h

theorem posterior_variance_at_s_three
    {μ : Measure (EuclideanSpace ℝ (Fin 1))} [IsProbabilityMeasure μ]
    {ρ : EuclideanSpace ℝ (Fin 1) → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    (x : EuclideanSpace ℝ (Fin 1)) :
    variance (fun y => ⟪y, EuclideanSpace.basisFun (Fin 1) ℝ 0⟫)
      (μ.tilted (fun y => -(3 : ℝ) * ‖x - y‖ ^ 2)) ≤ 1 / 6 := by
  have h := variance_inner_posterior_le hρ (by norm_num : (0 : ℝ) < 3) x
    (EuclideanSpace.basisFun (Fin 1) ℝ 0)
  have he : ‖EuclideanSpace.basisFun (Fin 1) ℝ 0‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 1) ℝ).norm_eq_one 0
  norm_num [he, EuclideanSpace.basisFun_apply] at h ⊢
  exact h

theorem zero_dimension {μ : Measure (EuclideanSpace ℝ (Fin 0))} [IsProbabilityMeasure μ]
    {ρ : EuclideanSpace ℝ (Fin 0) → ℝ}
    (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {s : ℝ} (hs : 0 < s) (x v : EuclideanSpace ℝ (Fin 0)) :
    bilinearIteratedFDerivTwo ℝ (potential ρ s) x v v ≤ 0 := by
  have h := bilinearIteratedFDerivTwo_potential_le hρ hs x v
  have hv : v = 0 := Subsingleton.elim _ _
  simpa only [hv, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using h

end GaussianHessianAudit

#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_line_factorization
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_line_cgf
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bilinearIteratedFDerivTwo_potential_eq_sub_variance_score
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bilinearIteratedFDerivTwo_potential_eq_sub_variance_inner
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.bilinearIteratedFDerivTwo_potential_le
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.variance_inner_posterior_le
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.memLp_two_score_posterior
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.memLp_two_inner_posterior
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.memLp_two_id_posterior
#print axioms GaussianHessianAudit.upper_at_s_three
#print axioms GaussianHessianAudit.posterior_variance_at_s_three
#print axioms GaussianHessianAudit.zero_dimension
