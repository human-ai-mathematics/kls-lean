import FunctionalInequalities.Probability.Posterior.CompactDomain
import FunctionalInequalities.KLS.IsotropicSupport
import FunctionalInequalities.Probability.Posterior.Generator
import FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt
import FunctionalInequalities.Analysis.Operator.InverseSqrt
import FunctionalInequalities.Probability.Posterior.JointRegularity
import FunctionalInequalities.Probability.Transport
import FunctionalInequalities.KLS.LogConcave.Isotropic
import FunctionalInequalities.Probability.IntrinsicTranslation
import FunctionalInequalities.Probability.Covariance.CauchySchwarz
import FunctionalInequalities.Probability.CoordinateThirdMoment
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

/-!
# Covariance of the BKL posterior for isotropic compact priors

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (67)–(68): for a compactly supported isotropic prior every
posterior `μ_{c,Q}` has a strictly positive, self-adjoint covariance which is a unit; its canonical
inverse is self-adjoint and strictly positive, the symmetric positive rate `Cov⁻¹` of the source; with this
rate the deterministic generator of the posterior expectation cancels (the zero drift of (68)), and at
`c = Q = 0` the rate is `Id`; the principal inverse square root `Cov⁻¹ᐟ²` of (67) has its full coefficient
algebra (positive branch, `σσ* = Cov⁻¹`, cancellation, initial value `Id`); and the coefficients of (67) are
regular on the whole parameter space `E × (E →L[ℝ] E)`: `Cov⁻¹` and the drift `Cov⁻¹ a` are jointly `C^∞`, the
diffusion coefficient `Cov⁻¹ᐟ²` and the triple `(Cov⁻¹ᐟ², Cov⁻¹ a, Cov⁻¹)` are locally Lipschitz; and the SAME
principal root standardises the posterior: the image of the centred posterior under `Cov⁻¹ᐟ²` is isotropic
(section `CanonicalStandardisation`, the transported law of (75)–(77)); and for a prior supported in the closed ball
of radius `r`, every posterior covariance has operator norm at most `r²` (section `CovarianceRadius`, no isotropy
needed); and the noise coefficient of the expectation equation (68) is bounded: for a statistic `f` bounded by `C` on
the prior support, `‖D_c(∫ f dμ_{·,Q})(c) ∘ Cov⁻¹ᐟ²‖² ≤ Var_{μ_{c,Q}} f ≤ C²` (section `NoiseBound`). No stochastic
equation, strong solution, non-explosion or Theorem 4.1 claim is made. Proof bodies: Codex bkl bundle `Posterior-Covariance-Domain` (independently accepted) and its
Codex root reviewer (canonical inverse), Codex q_batch bundle `Posterior-Generator-Inverse` (generator at the
source rate), Codex bkl bundle `Principal-Inverse-SquareRoot` (diffusion coefficient), Codex q_batch bundles
`Posterior-Joint-Regularity` and `Principal-Root-Regularity` (coefficient regularity), Luna units TW1 and TU1b with recorded
Claude closing repairs (canonical standardisation, covariance radius) and the Luna NB4a/NB4b round-8 bodies in Claude's
accepted assembly (noise bound), all independently accepted; statements and placement: Claude.
-/

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
open Set

namespace FunctionalInequalities.KLS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For a compactly supported isotropic prior every posterior has strictly positive covariance. -/
theorem Isotropic.compactPosterior_covariance_pos (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    (c : E) (Q : E →L[ℝ] E) {v : E} (hv : v ≠ 0) :
    0 < ⟪Covariance.operator (compactPosterior μ hc c Q : Measure E) v, v⟫ :=
  compactPosterior_covariance_pos_of_affineSupport_eq_top μ hc (hiso.affineSupport_eq_top) c Q hv

/-- The posterior covariance is a unit. -/
theorem Isotropic.compactPosterior_covariance_isUnit (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    IsUnit (Covariance.operator (compactPosterior μ hc c Q : Measure E)) :=
  Analysis.isUnit_of_inner_self_pos _ (fun _ hv => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv)

/-- The posterior covariance has a two-sided inverse. -/
theorem Isotropic.compactPosterior_exists_covariance_inverse (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ B : E →L[ℝ] E,
      (Covariance.operator (compactPosterior μ hc c Q : Measure E)).comp B = ContinuousLinearMap.id ℝ E ∧
      B.comp (Covariance.operator (compactPosterior μ hc c Q : Measure E)) = ContinuousLinearMap.id ℝ E :=
  Analysis.exists_inverse_of_inner_self_pos _ (fun _ hv => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv)

/-- The posterior covariance has a self-adjoint, strictly positive two-sided inverse (the symmetric
positive rate `M = Cov⁻¹` of the source; no square root is taken). -/
theorem Isotropic.compactPosterior_exists_positive_symmetric_inverse (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ B : E →L[ℝ] E, IsSelfAdjoint B ∧ (∀ v : E, v ≠ 0 → 0 < ⟪B v, v⟫) ∧
      (Covariance.operator (compactPosterior μ hc c Q : Measure E)).comp B = ContinuousLinearMap.id ℝ E ∧
      B.comp (Covariance.operator (compactPosterior μ hc c Q : Measure E)) = ContinuousLinearMap.id ℝ E := by
  obtain ⟨B, hAB, hBA⟩ := Isotropic.compactPosterior_exists_covariance_inverse μ hc hiso c Q
  refine ⟨B, Analysis.isSelfAdjoint_of_comp_eq_id _ _ (Covariance.operator_isSelfAdjoint _) hAB,
    fun _ hv => Analysis.inner_self_pos_of_comp_eq_id _ _ ?_ hAB hv, hAB, hBA⟩
  exact fun _ hw => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hw

/-- The canonical inverse `Ring.inverse (Cov μ_{c,Q})` is a two-sided, self-adjoint, strictly positive inverse
(Codex root reviewer of the Posterior-Covariance-Domain bundle). -/
theorem Isotropic.compactPosterior_ringInverse_covariance (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    A.comp (Ring.inverse A) = ContinuousLinearMap.id ℝ E ∧
    (Ring.inverse A).comp A = ContinuousLinearMap.id ℝ E ∧
    IsSelfAdjoint (Ring.inverse A) ∧
    (∀ v : E, v ≠ 0 → 0 < ⟪Ring.inverse A v, v⟫) := by
  dsimp only
  let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
  have hu : IsUnit A := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  have hright : A.comp (Ring.inverse A) = ContinuousLinearMap.id ℝ E :=
    Ring.mul_inverse_cancel A hu
  have hleft : (Ring.inverse A).comp A = ContinuousLinearMap.id ℝ E :=
    Ring.inverse_mul_cancel A hu
  exact ⟨hright, hleft, Analysis.isSelfAdjoint_of_comp_eq_id A _ (Covariance.operator_isSelfAdjoint _) hright,
    fun v hv => Analysis.inner_self_pos_of_comp_eq_id A _
      (fun w hw => Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hw) hright hv⟩

/-- **The BKL posterior of a log-concave compact prior is log-concave for `Q ≥ 0`** (p. 19: "each `μ_t` is
log-concave since `Q_t ≥ 0`"); singular priors, `Q = 0`, any `c` and rank zero included. -/
theorem compactPosterior_logConcave (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hLC : KLS.LogConcave μ)
    (c : E) (Q : E →L[ℝ] E) (hSym : IsSelfAdjoint Q)
    (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) : KLS.LogConcave (compactPosterior μ hc c Q) := by
  apply LogConcave.logConcave_of_concave_tilt μ (compactPosterior μ hc c Q) hLC (quadraticExponent c Q)
    (by unfold quadraticExponent; fun_prop)
  · exact Probability.Posterior.quadraticExponent_concave c Q
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSym) hQ
  · rfl

/-- The posterior covariance is a positive operator. -/
theorem Isotropic.compactPosterior_covariance_isPositive (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    (Covariance.operator (compactPosterior μ hc c Q : Measure E)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff' _).mpr
  refine ⟨Covariance.operator_isSelfAdjoint _, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (Isotropic.compactPosterior_covariance_pos μ hc hiso c Q hv).le

/-- **The diffusion coefficient `A^{-1/2}` of (67)**: for a compactly supported isotropic prior and every finite
`(c, Q)` (including `0`, negative `Q`, rank zero), `σ = inverseSqrt (Cov μ_{c,Q})` is self-adjoint, positive,
strictly positive, `σ² = σσ* = Cov⁻¹` and `Cov σσ* = σσ* Cov = 1`. Coefficient algebra only; no regularity,
SDE, Itô or martingale statement. -/
theorem Isotropic.compactPosterior_inverseSqrt_spec (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    let σ := inverseSqrt A
    IsSelfAdjoint σ ∧ σ.IsPositive ∧ (∀ v : E, v ≠ 0 → 0 < ⟪σ v, v⟫) ∧
      σ * σ = Ring.inverse A ∧ σ * σ.adjoint = Ring.inverse A ∧
      A * (σ * σ.adjoint) = 1 ∧ (σ * σ.adjoint) * A = 1 := by
  dsimp only
  let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
  have hp := Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hu := Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  obtain ⟨hpos, hsa, hsquare, hgram, hl, hr⟩ := inverseSqrt_spec A hp hu
  exact ⟨hsa, hpos, fun _ hv => inverseSqrtIn_inner_self_pos _ A hp hu hv,
    hsquare, hgram, hl, hr⟩

/-- At the initial pair `c = Q = 0` the diffusion coefficient is `Id`. -/
theorem Isotropic.inverseSqrt_covariance_compactPosterior_zero
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    inverseSqrt (Covariance.operator (compactPosterior μ hc 0 0 : Measure E)) =
      ContinuousLinearMap.id ℝ E := by
  rw [compactPosterior_zero, hiso.covariance_identity]
  change inverseSqrt (1 : E →L[ℝ] E) = 1
  apply inverseSqrt_unique _ _ isUnit_one
  · exact ContinuousLinearMap.isPositive_one
  · simp

variable {ι : Type*} [Fintype ι]

/-- **Generator cancellation at the source rate** `M = Cov(μ_{c,Q})⁻¹` (BKL (67)–(68), deterministic part): for a
compactly supported isotropic prior, every finite `(c, Q)` and measurable `f` bounded on the support,
`D_c[M a] + ∂_Q[M] + ½ Σ_i D²_c[M e_i, e_i] = 0`; the symmetry of the literal `Ring.inverse` of the constructed
posterior covariance comes from the covariance domain. Not an inverse-square-root, SDE, Itô or martingale
statement. -/
theorem Isotropic.compactPosterior_generator_cancellation (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (c : E) (Q : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) :
    let A := Covariance.operator (compactPosterior μ hc c Q : Measure E)
    let M := Ring.inverse A
    fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (M (posteriorMean μ c Q)) +
      deriv (fun t : ℝ => posteriorExpectation μ c (Q + t • M) f) 0 +
      (1 / 2 : ℝ) * (∑ i, bilinearIteratedFDerivTwo ℝ
        (fun y => posteriorExpectation μ y Q f) c (M (b i)) (b i)) = 0 := by
  dsimp only
  have hsa := (Isotropic.compactPosterior_ringInverse_covariance μ hc hiso c Q).2.2.1
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa
  apply posteriorExpectation_generator_cancellation μ hc hf hC hfb c Q _ b
  intro u v
  exact hs u v

/-- At the initial parameters `c = Q = 0` the posterior is the isotropic prior, so the rate is `Id`; this
describes the initial pair only. -/
theorem Isotropic.ringInverse_covariance_compactPosterior_zero (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    Ring.inverse (Covariance.operator (compactPosterior μ hc 0 0 : Measure E)) =
      ContinuousLinearMap.id ℝ E := by
  rw [compactPosterior_zero, hiso.covariance_identity]
  exact Ring.inverse_one (E →L[ℝ] E)

section JointCoefficients

/-- **Joint smoothness of the rate** `A⁻¹ = Cov(μ_{c,Q})⁻¹` of (67): isotropy makes the posterior covariance a
unit at every finite `(c, Q)`, and the Banach-algebra inverse is analytic there. -/
theorem Isotropic.contDiff_ringInverse_covariance_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hs := (contDiff_posteriorCovariance_joint μ hc).contDiffAt (x := p)
  obtain ⟨u, hu⟩ := Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  have hi : ContDiffAt ℝ ∞ Ring.inverse
      (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  exact hi.comp p hs

/-- **Joint smoothness of the drift** `A⁻¹ a` of (67). -/
theorem Isotropic.contDiff_covarianceDrift_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    ContDiff ℝ ∞ (fun p : E × (E →L[ℝ] E) =>
      Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
        (posteriorMean μ p.1 p.2)) :=
  (Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).clm_apply
    (contDiff_posteriorMean_joint μ hc)

/-- **Local Lipschitz property of the diffusion coefficient** `A^{-1/2} = inverseSqrt (Cov μ_{c,Q})` of (67)
on the whole parameter space (operator norm); positivity, invertibility and `C¹` of the inverse are derived
from compactness and isotropy. -/
theorem Isotropic.locallyLipschitz_inverseSqrt_covariance_joint (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    LocallyLipschitz (fun p : E × (E →L[ℝ] E) =>
      inverseSqrt (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))) := by
  apply locallyLipschitz_inverseSqrt_of_contDiff_ringInverse
  · intro p
    have hs := Isotropic.compactPosterior_ringInverse_covariance μ hc hiso p.1 p.2
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨hs.2.2.1, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst v
      change 0 ≤ ⟪Ring.inverse (Covariance.operator
        (compactPosterior μ hc p.1 p.2 : Measure E)) (0 : E), (0 : E)⟫
      simp
    · exact (hs.2.2.2 v hv).le
  · intro p
    exact Isotropic.compactPosterior_covariance_isUnit μ hc hiso p.1 p.2
  · exact (Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).of_le (by simp)

/-- **Coefficient regularity of (67)** (BKL p. 19): the coefficient map `(c, Q) ↦ (A^{-1/2}, A⁻¹ a, A⁻¹)` of the
localization equations, built from `compactPosterior`, is locally Lipschitz on all of `E × (E →L[ℝ] E)` for a
compactly supported isotropic prior (all finite `(c, Q)`, including `Q = 0`, non-symmetric `Q` and dimension
zero). Deterministic: no process, strong solution or non-explosion statement. -/
theorem Isotropic.locallyLipschitz_coefficients67 (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) :
    LocallyLipschitz (fun p : E × (E →L[ℝ] E) =>
      (inverseSqrt (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E)),
       (Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))
         (posteriorMean μ p.1 p.2),
        Ring.inverse (Covariance.operator (compactPosterior μ hc p.1 p.2 : Measure E))))) :=
  (Isotropic.locallyLipschitz_inverseSqrt_covariance_joint μ hc hiso).prodMk
    (((Isotropic.contDiff_covarianceDrift_joint μ hc hiso).of_le (by simp)).locallyLipschitz.prodMk
      ((Isotropic.contDiff_ringInverse_covariance_joint μ hc hiso).of_le (by simp)).locallyLipschitz)

end JointCoefficients

section CanonicalStandardisation

/-- **Canonical standardisation of the posterior**: the principal inverse square root of the posterior covariance,
as a continuous linear equivalence `W`, transports the centred posterior to an isotropic law. -/
theorem Isotropic.exists_inverseSqrt_equiv_isotropic_standardized (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ) (c : E) (Q : E →L[ℝ] E) :
    ∃ W : E ≃L[ℝ] E,
      (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)) ∧
      KLS.Isotropic (Probability.mapContinuousLinearEquiv
        (Probability.translateLaw (compactPosterior μ hc c Q) (-posteriorMean μ c Q)) W) := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    let ν : ProbabilityMeasure E := compactPosterior μ hc c Q
    let A : E →L[ℝ] E := Covariance.operator (ν : Measure E)
    let σ : E →L[ℝ] E := inverseSqrt A
    have hpos :=
      Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
    have hunit :=
      Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
    have hσ : IsUnit σ := by
      change IsUnit (inverseSqrtIn (stdOrthonormalBasis ℝ E) A)
      exact inverseSqrtIn_isUnit (stdOrthonormalBasis ℝ E) A hpos hunit
    let W : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hσ.unit
    have hW : (W : E →L[ℝ] E) = σ := by
      change (↑hσ.unit : E →L[ℝ] E) = σ
      exact hσ.unit_spec
    have hνlp : MemLp id 2 (ν : Measure E) := by
      simpa [ν] using compactPosterior_memLp_id_two μ hc c Q
    have hint : Integrable id (ν : Measure E) :=
      hνlp.integrable (by norm_num)
    have ht : MemLp id 2
        (Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E) :=
      Probability.memLp_id_two_translateLaw ν _ hνlp
    let η : ProbabilityMeasure E :=
      Probability.mapContinuousLinearEquiv
        (Probability.translateLaw ν (-posteriorMean μ c Q)) W
    have hηcoe :
        (η : Measure E) =
          ((Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E).map W) := by
      change
        (Probability.mapContinuousLinearEquiv
          (Probability.translateLaw ν (-posteriorMean μ c Q)) W : Measure E) =
          ((Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E).map W)
      rfl
    have hηlp : MemLp id 2 (η : Measure E) := by
      rw [hηcoe, memLp_map_measure_iff measurable_id.aestronglyMeasurable]
      · simpa [Function.comp_def] using
          (W : E →L[ℝ] E).comp_memLp' ht
      · exact W.continuous.aemeasurable
    have hzero :
        ∫ x, x ∂(Probability.translateLaw ν
          (-posteriorMean μ c Q) : Measure E) = 0 := by
      have hzero' :
          ∫ x, x ∂(Probability.translateLaw ν
            (-(∫ y, y ∂(ν : Measure E))) : Measure E) = 0 :=
        Probability.integral_id_translateLaw_neg_integral ν hint
      exact hzero'
    have hmean : ∫ x, x ∂(η : Measure E) = 0 := by
      rw [hηcoe]
      change ∫ x, id x ∂
          ((Probability.translateLaw ν (-posteriorMean μ c Q) : Measure E).map W) = 0
      rw [integral_map W.continuous.aemeasurable hηlp.aestronglyMeasurable]
      simp only [id_eq]
      rw [W.integral_comp_comm]
      simpa using congrArg W hzero
    have hself : (σ.adjoint : E →L[ℝ] E) = σ := by
      change ContinuousLinearMap.adjoint (inverseSqrt A) = inverseSqrt A
      exact (inverseSqrt_spec A hpos hunit).2.1
    have halg : (σ.comp A).comp σ = 1 := by
      ext x
      simpa [σ, ContinuousLinearMap.comp_apply] using
        congrArg (fun T : E →L[ℝ] E => T x)
          (inverseSqrt_mul_mul_inverseSqrt A hpos hunit)
    refine ⟨W, ?_, ?_⟩
    · simpa [A, σ, ν] using hW
    · refine
        { memLp_two := hηlp
          mean_zero := hmean
          covariance_identity := ?_ }
      rw [hηcoe]
      rw [Covariance.operator_map_continuousLinearEquiv]
      rw [Covariance.operator_translateLaw]
      rw [hW, hself]
      exact halg

end CanonicalStandardisation

section CovarianceRadius

open ProbabilityTheory

/-- **Posterior covariance radius bound**: if the prior support lies in the closed ball of radius `r`, then
`‖Cov μ_{c,Q}‖ ≤ r²` for every finite `(c, Q)`. Route: `⟪A v, w⟫ = cov(⟪v,·⟫, ⟪w,·⟫)`, Cauchy–Schwarz,
`Var⟪v,·⟫ ≤ ∫ ⟪v,x⟫² ≤ r² ‖v‖²` on the support, then `‖A v‖² = ⟪A v, A v⟫ ≤ r² ‖v‖ ‖A v‖`. -/
theorem opNorm_covariance_compactPosterior_le_sq_radius (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure E).support ⊆ Metric.closedBall (0 : E) r) (c : E) (Q : E →L[ℝ] E) :
    ‖Covariance.operator (compactPosterior μ hc c Q : Measure E)‖ ≤ r ^ 2 := by
    let ν : Measure E := compactPosterior μ hc c Q
    let A : E →L[ℝ] E := Covariance.operator ν
    have hprob : IsProbabilityMeasure ν := by
      dsimp [ν]
      infer_instance
    change ‖A‖ ≤ r ^ 2

    have hid : MemLp id 2 ν := by
      simpa only [ν] using compactPosterior_memLp_id_two μ hc c Q

    have hmem (v : E) :
        MemLp (fun x : E => ⟪v, x⟫) 2 ν := by
      have hh : MemLp (fun x : E => ⟪id x, v⟫) 2 ν :=
        hid.inner_const v
      simpa [real_inner_comm] using hh

    have hvar (v : E) :
        variance (fun x : E => ⟪v, x⟫) ν ≤ r ^ 2 * ‖v‖ ^ 2 := by
      have hle :
          (∫ x, (⟪v, x⟫) ^ 2 ∂ν) ≤
            ∫ _x, r ^ 2 * ‖v‖ ^ 2 ∂ν := by
        apply integral_mono_ae
        · exact (hmem v).integrable_sq
        · exact integrable_const _
        · filter_upwards [Measure.support_mem_ae (μ := ν)] with x hx
          have hx' : x ∈ (μ : Measure E).support := by
            rw [← compactPosterior_support μ hc c Q]
            exact hx
          have hxball : x ∈ Metric.closedBall (0 : E) r :=
            hsupp hx'
          have hnorm : ‖x‖ ≤ r := by
            simpa [mem_closedBall_zero_iff] using hxball
          have habs : |⟪v, x⟫| ≤ r * ‖v‖ := by
            calc
              |⟪v, x⟫| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
              _ ≤ ‖v‖ * r :=
                mul_le_mul_of_nonneg_left hnorm (norm_nonneg v)
              _ = r * ‖v‖ := by ring
          have hsquare : ⟪v, x⟫ ^ 2 ≤ (r * ‖v‖) ^ 2 := by
            rw [← sq_abs]
            nlinarith [habs, abs_nonneg ⟪v, x⟫,
              mul_self_nonneg (r * ‖v‖ - |⟪v, x⟫|)]
          calc
            ⟪v, x⟫ ^ 2 ≤ (r * ‖v‖) ^ 2 := hsquare
            _ = r ^ 2 * ‖v‖ ^ 2 := by ring
      have hv :=
        variance_le_expectation_sq
          (μ := ν) (X := fun x : E => ⟪v, x⟫)
          (hmem v).aestronglyMeasurable
      have hv' :
          variance (fun x : E => ⟪v, x⟫) ν ≤
            ∫ x, (⟪v, x⟫) ^ 2 ∂ν := by
        simpa only [Pi.pow_apply] using hv
      calc
        variance (fun x : E => ⟪v, x⟫) ν ≤
            ∫ x, (⟪v, x⟫) ^ 2 ∂ν := hv'
        _ ≤ ∫ _x, r ^ 2 * ‖v‖ ^ 2 ∂ν := hle
        _ = r ^ 2 * ‖v‖ ^ 2 := by simp

    have hcov (v w : E) :
        |⟪A v, w⟫| ≤ r ^ 2 * ‖v‖ * ‖w‖ := by
      have hcs :=
        Probability.covariance_sq_le_variance_mul_variance
          (hmem v) (hmem w)
      have hsq :
          |⟪A v, w⟫| ^ 2 ≤
            (r ^ 2 * ‖v‖ * ‖w‖) ^ 2 := by
        rw [Covariance.operator_inner]
        rw [covarianceBilin_apply_eq_cov
          (compactPosterior_memLp_id_two μ hc c Q)]
        calc
          |covariance (fun x : E => ⟪v, x⟫)
              (fun x : E => ⟪w, x⟫) ν| ^ 2
              = covariance (fun x : E => ⟪v, x⟫)
                  (fun x : E => ⟪w, x⟫) ν ^ 2 := by
                    rw [sq_abs]
          _ ≤ variance (fun x : E => ⟪v, x⟫) ν *
                variance (fun x : E => ⟪w, x⟫) ν := hcs
          _ ≤ (r ^ 2 * ‖v‖ ^ 2) * (r ^ 2 * ‖w‖ ^ 2) := by
            exact mul_le_mul (hvar v) (hvar w)
              (variance_nonneg _ _) (by positivity)
          _ = (r ^ 2 * ‖v‖ * ‖w‖) ^ 2 := by ring
      have hnonneg : 0 ≤ r ^ 2 * ‖v‖ * ‖w‖ := by positivity
      by_contra h
      have hlt : r ^ 2 * ‖v‖ * ‖w‖ < |⟪A v, w⟫| :=
        lt_of_not_ge h
      nlinarith [hsq, abs_nonneg ⟪A v, w⟫]

    apply ContinuousLinearMap.opNorm_le_bound A
    · exact pow_nonneg hr 2
    · intro v
      have hsq : ‖A v‖ ^ 2 ≤ r ^ 2 * ‖v‖ * ‖A v‖ := by
        calc
          ‖A v‖ ^ 2 = ⟪A v, A v⟫ := by
            symm
            exact real_inner_self_eq_norm_sq _
          _ ≤ |⟪A v, A v⟫| := le_abs_self _
          _ ≤ r ^ 2 * ‖v‖ * ‖A v‖ := hcov v (A v)
      by_cases hz : ‖A v‖ = 0
      · simp [hz]
        positivity
      · have hpos : 0 < ‖A v‖ := norm_pos_iff.mpr (by
          intro hav
          apply hz
          simp [hav])
        nlinarith

end CovarianceRadius

section NoiseBound

open ProbabilityTheory

/-- **Noise functional of (68), variance bound**: `‖D_c(∫ f dμ_{·,Q})(c) ∘ A^{-1/2}‖² ≤ Var_{μ_{c,Q}} f`. -/
theorem Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q : E →L[ℝ] E) :
    ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)))‖ ^ 2 ≤
      variance f (compactPosterior μ hc c Q : Measure E) := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    let ν : Measure E := compactPosterior μ hc c Q
    let A : E →L[ℝ] E := Covariance.operator ν
    let S : E →L[ℝ] E := inverseSqrt A

    have hS : IsSelfAdjoint S := by
      simpa [S, A, ν] using
        (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso c Q).1

    have hsand : S * Covariance.operator ν * S = 1 := by
      simpa [S, A] using
        (Analysis.inverseSqrt_mul_mul_inverseSqrt
          (Covariance.operator ν)
          (Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q)
          (Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q))

    have h2 : MemLp (id : E → E) 2 ν := by
      simpa [ν] using compactPosterior_memLp_id_two μ hc c Q

    have hop :
        ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S‖
          ≤ Real.sqrt (variance f ν) := by
      apply ContinuousLinearMap.opNorm_le_bound
        ((fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S)
        (Real.sqrt_nonneg _)
      intro h

      have hX : MemLp f 2 ν := by
        change MemLp f 2 ((μ : Measure E).tilted (quadraticExponent c Q))
        exact
          memLp_two_tilted_of_compact μ hc
            (φ := quadraticExponent c Q)
            (by
              unfold quadraticExponent
              fun_prop)
            hf hfb

      have hY : MemLp (fun x => ⟪S h, x⟫) 2 ν := by
        change
          MemLp (fun x => ⟪S h, x⟫) 2
            ((μ : Measure E).tilted (quadraticExponent c Q))
        exact
          memLp_two_tilted_quadraticExponent_of_compact μ hc c Q
            (by fun_prop)

      have hcov :
          covariance f (fun x => ⟪S h, x⟫) ν ^ 2
            ≤ variance f ν * variance (fun x => ⟪S h, x⟫) ν :=
        Probability.covariance_sq_le_variance_mul_variance hX hY

      have hvar :
          variance (fun x => ⟪S h, x⟫) ν = ‖h‖ ^ 2 :=
        Covariance.variance_inner_eq_of_sandwich ν h2 S hS hsand h

      have hsq :
          covariance f (fun x => ⟪S h, x⟫) ν ^ 2
            ≤ variance f ν * ‖h‖ ^ 2 := by
        calc
          covariance f (fun x => ⟪S h, x⟫) ν ^ 2
              ≤ variance f ν * variance (fun x => ⟪S h, x⟫) ν := hcov
          _ = variance f ν * ‖h‖ ^ 2 := by rw [hvar]

      have hfd :
          fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (S h)
            = covariance f (fun x => ⟪S h, x⟫) ν := by
        change
          fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (S h)
            = covariance f (fun x => ⟪S h, x⟫)
                ((μ : Measure E).tilted (quadraticExponent c Q))
        exact fderiv_posteriorExpectation_c_apply μ hc hf hC hfb c Q (S h)

      have habs :
          |covariance f (fun x => ⟪S h, x⟫) ν|
            ≤ Real.sqrt (variance f ν) * ‖h‖ := by
        have hv : 0 ≤ variance f ν := variance_nonneg f ν
        have hs : (Real.sqrt (variance f ν)) ^ 2 = variance f ν :=
          Real.sq_sqrt hv
        have hn :
            0 ≤ Real.sqrt (variance f ν) * ‖h‖ :=
          mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
        nlinarith [hsq, hs,
          sq_abs (covariance f (fun x => ⟪S h, x⟫) ν)]

      change
        ‖fderiv ℝ (fun y => posteriorExpectation μ y Q f) c (S h)‖
          ≤ Real.sqrt (variance f ν) * ‖h‖
      rw [hfd, Real.norm_eq_abs]
      exact habs

    have hsq :
        ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S‖ ^ 2
          ≤ variance f ν := by
      have hv : 0 ≤ variance f ν := variance_nonneg f ν
      have hs : (Real.sqrt (variance f ν)) ^ 2 = variance f ν :=
        Real.sq_sqrt hv
      nlinarith [hop, norm_nonneg
        ((fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp S)]

    simpa [S, A, ν] using hsq


/-- **Noise functional of (68), uniform bound**: `‖D_c(∫ f dμ_{·,Q})(c) ∘ A^{-1/2}‖² ≤ C²` for `f` bounded by `C` on
the prior support (the posterior has the prior's support). -/
theorem Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_sq
    (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support) (hiso : KLS.Isotropic μ)
    {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C) (c : E) (Q : E →L[ℝ] E) :
    ‖(fderiv ℝ (fun y => posteriorExpectation μ y Q f) c).comp
        (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure E)))‖ ^ 2 ≤ C ^ 2 := by
    let ν : Measure E := compactPosterior μ hc c Q
    have hbound : ∀ᵐ x ∂ν, ‖f x‖ ≤ C := by
      filter_upwards [Measure.support_mem_ae] with x hx
      apply hfb x
      rw [← compactPosterior_support μ hc c Q]
      exact hx
    have hLp : MemLp f 2 ν := by
      exact MemLp.of_bound hf.aestronglyMeasurable C hbound
    have hsq : ∀ᵐ x ∂ν, f x ^ 2 ≤ C ^ 2 := by
      filter_upwards [hbound] with x hx
      have hx' : |f x| ≤ C := by
        simpa [Real.norm_eq_abs] using hx
      have h₁ : -C ≤ f x := (abs_le.mp hx').1
      have h₂ : f x ≤ C := (abs_le.mp hx').2
      nlinarith
    have hsq_int : (∫ x, f x ^ 2 ∂ν) ≤ C ^ 2 := by
      calc
        (∫ x, f x ^ 2 ∂ν) ≤ ∫ _x, C ^ 2 ∂ν :=
          integral_mono_ae hLp.integrable_sq (integrable_const _) hsq
        _ = C ^ 2 := by simp [ν]
    have hvar : variance f ν ≤ C ^ 2 := by
      calc
        variance f ν =
            (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
          simpa [Pi.pow_apply] using variance_eq_sub hLp
        _ ≤ C ^ 2 := by
          linarith [hsq_int, sq_nonneg (∫ x, f x ∂ν)]
    exact
      (Isotropic.opNorm_sq_fderiv_posteriorExpectation_comp_inverseSqrt_le_variance
        μ hc hiso hf hC hfb c Q).trans (by simpa [ν] using hvar)

end NoiseBound

section SixthMoment

/-- **Canonical sixth moment of the posterior**: `∫ ‖Cov(μ_{c,Q})^{-1/2} (x − a)‖⁶ dμ_{c,Q} ≤ C₆(n)` with the explicit
isotropic log-concave constant, for every finite self-adjoint PSD `Q` and every `c`. -/
theorem Isotropic.integral_norm_pow_six_inverseSqrt_sub_posteriorMean_le {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) (hiso : KLS.Isotropic μ)
    (hLC : KLS.LogConcave μ) (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hSym : IsSelfAdjoint Q)
    (hQ : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪Q x, x⟫) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
          (x - posteriorMean μ c Q)‖ ^ 6) (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ‖inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
          (x - posteriorMean μ c Q)‖ ^ 6 ∂(compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      (Nat.factorial 6 : ℝ) / (Real.log 3 / (4 * (2 * Real.sqrt ((n : ℝ) + 1)))) ^ 6 *
        ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
    obtain ⟨W, hW, hη⟩ :=
      Isotropic.exists_inverseSqrt_equiv_isotropic_standardized μ hc hiso c Q
    let ν := compactPosterior μ hc c Q
    let a := posteriorMean μ c Q
    let η :=
      Probability.mapContinuousLinearEquiv
        (Probability.translateLaw ν (-a)) W
    have hLCν : KLS.LogConcave ν :=
      compactPosterior_logConcave μ hc hLC c Q hSym hQ
    have hLCη : KLS.LogConcave η := by
      dsimp [η]
      exact (hLCν.translateLaw (-a)).mapContinuousLinearEquiv W
    have hm :=
      KLS.LogConcave.integral_norm_pow_le_of_isotropic hLCη hη 6
    dsimp only at hm
    obtain ⟨hint, hle⟩ := hm
    have hWν :
        (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) =
          inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))) := by
      simpa [ν] using hW
    have hmap :
        (η : Measure (EuclideanSpace ℝ (Fin n))) =
          (ν : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) =>
              inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a)) := by
      dsimp [η]
      rw [Probability.coe_mapContinuousLinearEquiv,
        Probability.coe_translateLaw]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      change
        (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (-a + x) =
          inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
            (x - a)
      rw [hWν]
      simp only [map_add, map_neg, sub_eq_add_neg]
      abel
    have hmeas :
        Measurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
              (x - a)) :=
      Measurable.comp
        ((inverseSqrt
            (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))).continuous.measurable)
        (measurable_id.sub measurable_const)
    have hint_map :
        Integrable (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ ^ 6)
          ((ν : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) =>
              inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a))) := by
      rw [← hmap]
      exact hint
    have hint' :
        Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ‖inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a)‖ ^ 6)
          (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      have h :=
        (integrable_map_measure
          (μ := (ν : Measure (EuclideanSpace ℝ (Fin n))))
          (f := fun x : EuclideanSpace ℝ (Fin n) =>
            inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
              (x - a))
          (g := fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ ^ 6)
          hint_map.aestronglyMeasurable hmeas.aemeasurable).mp hint_map
      simpa [Function.comp_def] using h
    have hle_map := hle
    rw [hmap] at hle_map
    have hI :
        (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ 6
            ∂((ν : Measure (EuclideanSpace ℝ (Fin n))).map
              (fun x : EuclideanSpace ℝ (Fin n) =>
                inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                  (x - a)))) =
          ∫ x : EuclideanSpace ℝ (Fin n),
            ‖inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
                (x - a)‖ ^ 6
            ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      exact integral_map hmeas.aemeasurable (by fun_prop)
    rw [hI] at hle_map
    dsimp [ν, a] at hint' hle_map
    exact ⟨hint', hle_map⟩

end SixthMoment

section NoiseEntries

/-- **Principal-root noise entries of (69)**: `(P H_i P) j k = ∫ (σV)_j (σV)_k (σV)_i dν`. -/
theorem Isotropic.operatorMatrix_inverseSqrt_mul_thirdMomentMatrix_mul_apply {n : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support) (hiso : KLS.Isotropic μ)
    (c : EuclideanSpace ℝ (Fin n)) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (i j k : Fin n) :
    (operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ)
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))) *
        (Matrix.of fun j' k' : Fin n =>
          ∫ x, (x - posteriorMean μ c Q) j' * (x - posteriorMean μ c Q) k' *
            ⟪inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
                (EuclideanSpace.basisFun (Fin n) ℝ i), x - posteriorMean μ c Q⟫
            ∂(compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n)))) *
        operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ)
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n)))))) j k =
      ∫ x, (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (x - posteriorMean μ c Q)) j *
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (x - posteriorMean μ c Q)) k *
          (inverseSqrt (Covariance.operator (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
              (x - posteriorMean μ c Q)) i
        ∂(compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨R, hR⟩ :=
      FunctionalInequalities.Probability.Posterior.compactPosterior_exists_ae_norm_sub_le
        μ hc c Q (posteriorMean μ c Q)
    have hσ :
        IsSelfAdjoint
          (inverseSqrt
            (Covariance.operator
              (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))) :=
      (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso c Q).1
    exact
      FunctionalInequalities.Probability.operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le
        (ν := (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))))
        (posteriorMean μ c Q) R hR _ hσ i j k

end NoiseEntries

end FunctionalInequalities.KLS
