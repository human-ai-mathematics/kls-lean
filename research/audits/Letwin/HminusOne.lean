import FunctionalInequalities.KLS.Letwin.HminusOne

/-!
# Client of Letwin Proposition 2.8 for general log-concave laws

The unconditional `H⁻¹` variance inequality is used in real form: finite real bounds `N_i` on the
dual norms of the partial derivatives bound the variance by `Σ N_i²`. The audit prints the axioms of
every new public declaration of the approximation route.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LetwinHminusOneAudit

open FunctionalInequalities

/-- Real form of Proposition 2.8: real bounds `‖∂ᵢ f‖_{H⁻¹(μ)} ≤ N_i` give `Var_μ f ≤ Σ N_i²`. -/
theorem variance_le_sum_sq_of_dualNorm_le {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyLipschitz f) (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (N : Fin n → ℝ) (hN0 : ∀ i, 0 ≤ N i)
    (hN : ∀ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ≤ ENNReal.ofReal (N i)) :
    variance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ∑ i, N i ^ 2 := by
  have h := KLS.LogConcave.variance_le_sum_dualNorm_sq hμ hfull hf hf2 hdf
  have h2 : ∑ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ^ 2 ≤
      ENNReal.ofReal (∑ i, N i ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [ENNReal.ofReal_pow (hN0 i)]
    exact pow_le_pow_left₀ bot_le (hN i) 2
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => sq_nonneg _)).mp (h.trans h2)

end LetwinHminusOneAudit

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Energy.Dual.gradient_const_mul_fn
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Energy.Dual.inner_toLp_le_mul_sqrt_energy
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Energy.Dual.abs_inner_toLp_le_mul_sqrt_energy
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Energy.Dual.integral_eq_zero_of_dualNorm_ne_top
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Energy.Dual.dualNorm_add_le
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Energy.Dual.dualNorm_le_of_variance_le

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.bddBelow
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.le_of_mem
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.le_self
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.le_of_forall
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.ge_of_bound
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.le_add_mul_norm
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.dist_le
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.lipschitzWith
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.continuous
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.convexOn
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.mono
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.ge_mul_norm_sub
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.lipschitzEnvelope.ge_of_ge_on_ball

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.Mollification.contDiff_normed_convolution
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.Mollification.convexOn_normed_convolution
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.Mollification.abs_normed_convolution_sub_le

set_option pp.fullNames true in
#print axioms FunctionalInequalities.KLS.IsBorellDensity.exists_le_mul_exp_neg_norm
set_option pp.fullNames true in
#print axioms FunctionalInequalities.KLS.IsBorellDensity.exists_smooth_convex_lower_approximation

set_option pp.fullNames true in
#print axioms FunctionalInequalities.KLS.LogConcave.variance_le_sum_dualNorm_sq_of_conjecture
set_option pp.fullNames true in
#print axioms FunctionalInequalities.KLS.LogConcave.variance_le_sum_dualNorm_sq
set_option pp.fullNames true in
#print axioms LetwinHminusOneAudit.variance_le_sum_sq_of_dualNorm_le
