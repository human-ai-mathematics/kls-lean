module

public import FunctionalInequalities.Probability.Posterior.CompactQuadratic
public import FunctionalInequalities.KLS.Isotropic
/-!
# Initial parameter response of the BKL posterior for isotropic priors

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19: at the initial parameters `c = Q = 0` of the
localization (67), the response of a linear statistic of a compactly supported isotropic prior to
the
linear parameter is the isotropic covariance pairing. This is the deterministic first variation
only;
the stochastic equations (67)–(71) are not constructed.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory FunctionalInequalities.Probability.Posterior
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
**Initial linear response** (BKL p. 19, the stage `c = Q = 0` before (67)): for a compactly
supported
isotropic law, `t ↦ ∫ ⟪u, x⟫ d(μ.tilted (t⟪h, ·⟫))` has derivative `⟪u, h⟫` at `t = 0`, the
isotropic
covariance pairing. -/
theorem Isotropic.posterior_linear_response (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (u h : E) :
    HasDerivAt (fun t : ℝ => ∫ x, ⟪u, x⟫ ∂((μ : Measure E).tilted (fun x => t * ⟪h, x⟫))) ⟪u, h⟫
      0 := by
  have hf : Continuous (fun x : E => ⟪u, x⟫) := by fun_prop
  obtain ⟨C, hC, hb⟩ := exists_bound_on_support_of_compact μ hc hf
  have hd :=
    expectation_hasDerivAt_quadraticExponent_of_compact μ hc 0 h 0 0 hf.measurable hC hb
  have hcov : covariance (fun x : E => ⟪u, x⟫) (fun x : E => ⟪h, x⟫) (μ : Measure E) = ⟪u, h⟫ := by
    rw [← covarianceBilin_apply_eq_cov hiso.memLp_two, ← Covariance.operator_inner,
      hiso.covariance_identity, ContinuousLinearMap.id_apply]
  have hbase : quadraticExponent (0 : E) (0 : E →L[ℝ] E) = (0 : E → ℝ) := by
    funext x
    simp [quadraticExponent]
  have hscore : quadraticExponent h (0 : E →L[ℝ] E) = fun x => ⟪h, x⟫ := by
    funext x
    simp [quadraticExponent]
  have hphase (t : ℝ) :
    quadraticExponent (0 + t • h) (0 + t • (0 : E →L[ℝ] E)) = fun x => t * ⟪h, x⟫ := by
    funext x
    simp [quadraticExponent, real_inner_smul_left]
  simpa only [hphase, hbase, hscore, tilted_zero, hcov] using hd

/-- The one-dimensional initial response equals `1`. -/
theorem Isotropic.posterior_response_real (μ : ProbabilityMeasure ℝ)
    (hc : IsCompact (μ : Measure ℝ).support) (hiso : KLS.Isotropic μ) :
    HasDerivAt (fun t : ℝ => ∫ x, x ∂((μ : Measure ℝ).tilted (fun x => t * x))) 1 0 := by
  simpa only [Real.inner_apply, one_mul, mul_one] using
    Isotropic.posterior_linear_response μ hc hiso 1 1

/-- The initial response in a nonzero direction `u` is `‖u‖² > 0`. -/
theorem Isotropic.posterior_response_pos (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) {u : E} (hu : u ≠ 0) :
    HasDerivAt (fun t : ℝ => ∫ x, ⟪u, x⟫ ∂((μ : Measure E).tilted (fun x => t * ⟪u, x⟫)))
        (‖u‖ ^ 2) 0 ∧
      0 < ‖u‖ ^ 2 := by
  exact
    ⟨by
      simpa only [real_inner_self_eq_norm_sq] using
        Isotropic.posterior_linear_response μ hc hiso u u,
      sq_pos_of_pos (norm_pos_iff.mpr hu)⟩

end FunctionalInequalities.KLS
