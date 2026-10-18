import FunctionalInequalities.KLS.BKL.CumulantEnergy.Bound
import FunctionalInequalities.KLS.BKL.Localization.Coefficients
import FunctionalInequalities.KLS.BKL.Localization.Standardization
import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
import FunctionalInequalities.KLS.BKL.Posterior.Covariance
import FunctionalInequalities.KLS.BKL.Posterior.Standardization

/-!
# A-priori posterior energy bounds
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis

namespace FunctionalInequalities.KLS.BKL
open FunctionalInequalities.Analysis.BakryEmery

variable {n : ℕ}
namespace Localization

private theorem posterior_energy_transfer
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hSym : IsSelfAdjoint Q) (hQ : ∀ x, 0 ≤ ⟪Q x, x⟫)
    {d : ℕ} (hd : 1 ≤ d) {b : ℝ}
    (h : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      KLS.LogConcave ν → KLS.Isotropic ν →
      IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∑ J : Fin d → Fin n,
          cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤
          b * ‖u‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    cumulantEnergy (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) d v ≤
      b * ⟪Covariance.operator
        (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫ := by
  let π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := compactPosterior μ hc c Q
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Covariance.operator (π : Measure (EuclideanSpace ℝ (Fin n)))
  let σ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := inverseSqrt A
  let a : EuclideanSpace ℝ (Fin n) := posteriorMean μ c Q
  let η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := Probability.translateLaw π (-a)
  obtain ⟨W, hW, hνiso⟩ :=
    Isotropic.exists_inverseSqrt_equiv_isotropic_standardized μ hc hiso c Q
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
    Probability.mapContinuousLinearEquiv η W
  have hW' : (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = σ := by
    simpa [π, A, σ] using hW
  have hpos : A.IsPositive := by
    simpa [π, A] using Isotropic.compactPosterior_covariance_isPositive μ hc hiso c Q
  have hunit : IsUnit A := by
    simpa [π, A] using Isotropic.compactPosterior_covariance_isUnit μ hc hiso c Q
  have hself : ContinuousLinearMap.adjoint σ = σ := by
    change ContinuousLinearMap.adjoint (inverseSqrt A) = inverseSqrt A
    exact (inverseSqrt_spec A hpos hunit).2.1
  have halg : (σ.comp A).comp σ = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change σ (A (σ x)) = x
    simpa [σ] using
      congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T x)
        (inverseSqrt_mul_mul_inverseSqrt A hpos hunit)
  have hνcoe :
      (ν : Measure (EuclideanSpace ℝ (Fin n))) =
        Measure.map (fun x => W (x - a)) (π : Measure (EuclideanSpace ℝ (Fin n))) := by
    change
      (Probability.mapContinuousLinearEquiv η W : Measure (EuclideanSpace ℝ (Fin n))) =
        Measure.map (fun x => W (x - a)) (π : Measure (EuclideanSpace ℝ (Fin n)))
    rw [Probability.coe_mapContinuousLinearEquiv, Probability.coe_translateLaw,
      Measure.map_map W.continuous.measurable (measurable_const_add _)]
    congr 1
    funext x
    simp [sub_eq_add_neg, add_comm]
  have hπLC : KLS.LogConcave π := by
    simpa [π] using compactPosterior_logConcave μ hc hLC c Q hSym hQ
  have hηLC : KLS.LogConcave η := by
    simpa [η] using hπLC.translateLaw (-a)
  have hmapback :
      Measure.map (W.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (ν : Measure (EuclideanSpace ℝ (Fin n))) =
          (η : Measure (EuclideanSpace ℝ (Fin n))) :=
    (Probability.measurePreserving_mapContinuousLinearEquiv_symm η W).map_eq
  have hνLC : KLS.LogConcave ν :=
    LogConcave.of_continuousLinearEquiv_map hηLC ν W.symm hmapback
  have hπcompact : IsCompact (π : Measure (EuclideanSpace ℝ (Fin n))).support := by
    change IsCompact (compactPosterior μ hc c Q : Measure (EuclideanSpace ℝ (Fin n))).support
    rw [compactPosterior_support μ hc c Q]
    exact hc
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun x => W (x - a)) '' (π : Measure (EuclideanSpace ℝ (Fin n))).support
  have hKcompact : IsCompact K := by
    apply hπcompact.image
    exact W.continuous.comp (continuous_id.sub continuous_const)
  have hKae : K ∈ ae (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hνcoe]
    apply (ae_map_iff
      (W.continuous.comp (continuous_id.sub continuous_const)).aemeasurable
      hKcompact.measurableSet).2
    filter_upwards [Measure.support_mem_ae
      (μ := (π : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
    exact ⟨x, hx, rfl⟩
  have hνcompact : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support := by
    apply IsCompact.of_isClosed_subset hKcompact
    · exact Measure.isClosed_support
    · exact Measure.support_subset_of_isClosed hKcompact.isClosed hKae
  have hexp (r : ℝ) :
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (r * ‖x‖))
        (π : Measure (EuclideanSpace ℝ (Fin n))) :=
    compact_support_integrable_exp _ hπcompact r
  have hk : 2 ≤ d + 1 := by omega
  have hcum (J : Fin d → Fin n) :
      cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons (W.symm v) fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) =
      cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons v fun k => σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) := by
    rw [hνcoe, cumulant_map_affine W a (π : Measure (EuclideanSpace ℝ (Fin n))) hexp hk]
    have hWadj :
        ContinuousLinearMap.adjoint
          (W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = σ := by
      rw [hW', hself]
    congr 1
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero, hWadj]
      rw [← hW']
      exact W.apply_symm_apply v
    · simp only [Fin.cons_succ, hWadj]
  have hsum :
      ∑ J : Fin d → Fin n,
        cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons (W.symm v) fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 =
      ∑ J : Fin d → Fin n,
        cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
          (Fin.cons v fun k => σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2 := by
    apply Finset.sum_congr rfl
    intro J _
    rw [hcum]
  have hnorm : ‖W.symm v‖ ^ 2 = ⟪A v, v⟫ := by
    let u := W.symm v
    have hv : v = σ u := by
      dsimp [u]
      rw [← hW']
      exact (W.apply_symm_apply v).symm
    have hu : σ (A (σ u)) = u := by
      simpa [ContinuousLinearMap.comp_apply] using
        congrArg (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => T u) halg
    calc
      ‖u‖ ^ 2 = ⟪u, u⟫ := (real_inner_self_eq_norm_sq u).symm
      _ = ⟪σ (A (σ u)), u⟫ := by rw [hu]
      _ = ⟪A (σ u), (ContinuousLinearMap.adjoint σ) u⟫ :=
        (ContinuousLinearMap.adjoint_inner_right σ (A (σ u)) u).symm
      _ = ⟪A (σ u), σ u⟫ := by rw [hself]
      _ = ⟪A v, v⟫ := by rw [← hv]
  change
    (∑ J : Fin d → Fin n,
      cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
        (Fin.cons v fun k => σ (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2) ≤
      b * ⟪A v, v⟫
  rw [← hsum, ← hnorm]
  exact h ν hνLC hνiso hνcompact (W.symm v)

variable (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

/-- The posterior mean lies in the ball carrying the prior. -/
theorem norm_posteriorMean_le {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (p : Param n) :
    ‖posteriorMean μ p.1 p.2‖ ≤ r := by
  have hc' : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r).of_isClosed_subset
      Measure.isClosed_support hsupp
  have hae : ∀ᵐ x ∂(compactPosterior μ hc' p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))),
      ‖x‖ ≤ max r 0 := by
    rw [compactPosterior_ae μ hc' p.1 p.2]
    filter_upwards [Measure.support_mem_ae
      (μ := (μ : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
    exact (mem_closedBall_zero_iff.mp (hsupp hx)).trans (le_max_left r 0)
  have hb :
      ‖∫ x, x ∂(compactPosterior μ hc' p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))‖ ≤ r := by
    simpa [max_eq_left hr] using norm_integral_le_of_norm_le_const hae
  change ‖∫ x, x ∂((μ : Measure (EuclideanSpace ℝ (Fin n))).tilted
    (quadraticExponent p.1 p.2))‖ ≤ r
  exact hb

/-- A-priori bound on the cumulant energies along the localization. -/
theorem exists_cumulantEnergy_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 r) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Param n, IsSelfAdjoint p.2 → (∀ x, 0 ≤ ⟪p.2 x, x⟫) →
      ∀ u : EuclideanSpace ℝ (Fin n),
        cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C * ‖u‖ ^ 2 := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨r ^ 2, sq_nonneg r, ?_⟩
    intro p _ _ u
    let π : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := compactPosterior μ hc p.1 p.2
    have hπcompact : IsCompact (π : Measure (EuclideanSpace ℝ (Fin n))).support := by
      change IsCompact (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))).support
      rw [compactPosterior_support]
      exact hc
    have hfirst (v : Fin 1 → EuclideanSpace ℝ (Fin n)) :
        cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) 1 v =
          ⟪v 0, posteriorMean μ p.1 p.2⟫ := by
      rw [cumulant, iteratedFDeriv_one_apply,
        ← tiltAverage_inner_eq_fderiv_logLaplace
          (π : Measure (EuclideanSpace ℝ (Fin n)))
          (fun t => compact_support_integrable_exp _ hπcompact t) (v 0) 0]
      have hzero :
          (fun x : EuclideanSpace ℝ (Fin n) => ⟪(0 : EuclideanSpace ℝ (Fin n)), x⟫) = 0 := by
        funext x
        simp
      rw [tiltAverage, expTilt, hzero, tilted_zero]
      exact integral_inner_eq_inner_posteriorMean μ hc p.1 p.2 (v 0)
    have habs : |⟪u, posteriorMean μ p.1 p.2⟫| ≤ ‖u‖ * r :=
      (abs_real_inner_le_norm u _).trans
        (mul_le_mul_of_nonneg_left (norm_posteriorMean_le μ hr hsupp p) (norm_nonneg u))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg u) hr)).2 habs
    have he :
        cumulantEnergy (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 0 u =
          ⟪u, posteriorMean μ p.1 p.2⟫ ^ 2 := by
      change (∑ J : Fin 0 → Fin n,
        cumulant (π : Measure (EuclideanSpace ℝ (Fin n))) 1
          (Fin.cons u fun k => inverseSqrt (Covariance.operator (π : Measure (EuclideanSpace ℝ (Fin n))))
            (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2) = _
      simp only [hfirst, Fin.cons_zero]
      simp
    rw [he]
    simpa only [sq_abs, mul_pow, mul_comm] using hsq
  · obtain ⟨b, hb, hbound⟩ := exists_sum_sq_cumulant_le_isotropic (n := n) d
    refine ⟨b * r ^ 2, mul_nonneg hb (sq_nonneg r), ?_⟩
    intro p hSym hQ u
    have htransfer := posterior_energy_transfer μ hc hiso hLC p.1 p.2 hSym hQ
      (by omega : 1 ≤ d) hbound u
    let A := Covariance.operator
      (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
    have hA : ‖A‖ ≤ r ^ 2 :=
      opNorm_covariance_compactPosterior_le_sq_radius μ hc hr hsupp p.1 p.2
    have hinner : ⟪A u, u⟫ ≤ r ^ 2 * ‖u‖ ^ 2 := by
      calc
        ⟪A u, u⟫ ≤ ‖A u‖ * ‖u‖ := real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖u‖) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg u)
        _ ≤ (r ^ 2 * ‖u‖) * ‖u‖ := by
          gcongr
        _ = r ^ 2 * ‖u‖ ^ 2 := by ring
    calc
      _ ≤ b * ⟪A u, u⟫ := htransfer
      _ ≤ b * (r ^ 2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hinner hb
      _ = (b * r ^ 2) * ‖u‖ ^ 2 := by ring

end Localization

end FunctionalInequalities.KLS.BKL
