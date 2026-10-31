module

public import FunctionalInequalities.KLS.LogConcave.BrascampLieb
public import FunctionalInequalities.KLS.BKL.GaussianTaylor
public import FunctionalInequalities.KLS.LogConcave.Regular.Isotropic

/-!
# Audit: the scalar Brascamp–Lieb inequality is sharp for the standard Gaussian law on `ℝ`

Source: Letwin, arXiv:2607.24164v1, Lemma A.6 for a given potential (support only). For the
canonical regular-potential Gaussian law `e^{−x²/2}` on `ℝ`, potential `U = x²/2` and test
`f = id`: the actual gradient is `1`, the actual Hessian operator and its ring inverse are the
identity, the energy is integrable with integral `1`, the law is isotropic (from its actual
moments), the variance is `1`, and `scalar_brascamp_lieb_finite_energy` is invoked, so equality
holds. No premise. Not a source-law moment-map client.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave
open scoped ContDiff RealInnerProductSpace


namespace LetwinScalarBrascampLiebAudit

section CanonicalGaussian

open FunctionalInequalities ProbabilityTheory

/-- The actual gradient of the nonzero identity test on the real line. -/
theorem canonicalGaussian_real_gradient_id (x : ℝ) :
    gradient (id : ℝ → ℝ) x = 1 := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hd : fderiv ℝ (id : ℝ → ℝ) x v = v := by
    simp
  have hi : inner ℝ (1 : ℝ) v = v := by
    rw [Real.inner_apply, one_mul]
  exact hd.trans hi.symm

/-- The actual Hessian operator of the potential `x² / 2` is the identity. -/
theorem canonicalGaussian_real_hessian_half_sq (x : ℝ) :
    hessianOperator (fun y : ℝ => y ^ 2 / 2) x = (1 : ℝ →L[ℝ] ℝ) := by
  let U : ℝ → ℝ := fun y => y ^ 2 / 2
  change hessianOperator U x = (1 : ℝ →L[ℝ] ℝ)
  have hU2 : ContDiff ℝ 2 U :=
    (contDiff_id.pow 2).div_const 2
  have hform :
      bilinearIteratedFDerivTwo ℝ U x (1 : ℝ) (1 : ℝ) = (1 : ℝ) ^ 2 := by
    simpa only [U, Real.norm_eq_abs, sq_abs] using
      (FunctionalInequalities.KLS.bilinearIteratedFDerivTwo_half_norm_sq x (1 : ℝ))
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hU2] at hform
  have hone : hessianOperator U x (1 : ℝ) = 1 := by
    have hi : inner ℝ (hessianOperator U x (1 : ℝ)) (1 : ℝ) =
        hessianOperator U x (1 : ℝ) := by
      rw [Real.inner_apply, mul_one]
    rw [hi, one_pow] at hform
    exact hform
  apply ContinuousLinearMap.ext
  intro v
  calc
    hessianOperator U x v = hessianOperator U x (v • (1 : ℝ)) := by simp
    _ = v • hessianOperator U x 1 := by rw [map_smul]
    _ = (1 : ℝ →L[ℝ] ℝ) v := by rw [hone]; simp

/-- Isotropy of the canonical regular-potential Gaussian law on the real line. -/
theorem canonicalGaussian_real_isotropic :
    FunctionalInequalities.KLS.Isotropic
      (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).law := by
  let ν : ProbabilityMeasure ℝ :=
    (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).law
  change FunctionalInequalities.KLS.Isotropic ν
  have h2 : MemLp (id : ℝ → ℝ) 2 (ν : Measure ℝ) :=
    (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).memLp_id_two
  have hsqInt : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq h2.aestronglyMeasurable).mp h2
  have h0 : (∫ x : ℝ, x ∂(ν : Measure ℝ)) = 0 := by
    change (∫ x : ℝ, x ∂((volume : Measure ℝ).tilted
      (-fun y : ℝ => ‖y‖ ^ 2 / 2))) = 0
    exact FunctionalInequalities.KLS.integral_id_tilted_half_norm_sq (E := ℝ)
  have hsq : (∫ x : ℝ, x ^ 2 ∂(ν : Measure ℝ)) = 1 := by
    change (∫ x : ℝ, x ^ 2 ∂((volume : Measure ℝ).tilted
      (-fun y : ℝ => ‖y‖ ^ 2 / 2))) = 1
    simpa only [Real.inner_apply, one_mul, norm_one, one_pow] using
      (FunctionalInequalities.KLS.integral_inner_sq_tilted_half_norm_sq (1 : ℝ))
  have hmoments (u v : ℝ) :
      Integrable (fun x : ℝ => inner ℝ u x * inner ℝ v x) (ν : Measure ℝ) ∧
        (∫ x : ℝ, inner ℝ u x * inner ℝ v x ∂(ν : Measure ℝ)) =
          inner ℝ u v := by
    have hfun : (fun x : ℝ => inner ℝ u x * inner ℝ v x) =
        (fun x : ℝ => (u * v) * x ^ 2) := by
      funext x
      simp only [Real.inner_apply]
      ring
    rw [hfun]
    refine ⟨hsqInt.const_mul (u * v), ?_⟩
    rw [integral_const_mul, hsq, mul_one, Real.inner_apply]
  exact FunctionalInequalities.KLS.isotropic_of_moments ν h2 h0
    (fun u v => (hmoments u v).2)

/-- Unit variance of the actual identity test under the canonical Gaussian law. -/
theorem canonicalGaussian_real_variance_id :
    ProbabilityTheory.variance (id : ℝ → ℝ)
      ((FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).law :
        Measure ℝ) = 1 := by
  let ν : ProbabilityMeasure ℝ :=
    (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).law
  change ProbabilityTheory.variance (id : ℝ → ℝ) (ν : Measure ℝ) = 1
  have hmem : MemLp (id : ℝ → ℝ) 2 (ν : Measure ℝ) :=
    (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).memLp_id_two
  have hiso : FunctionalInequalities.KLS.Isotropic ν :=
    canonicalGaussian_real_isotropic
  rcases hiso with ⟨_, _, hcov⟩
  have hcov11 := congrArg
    (fun T : ℝ →L[ℝ] ℝ => inner ℝ (T 1) (1 : ℝ)) hcov
  rw [Covariance.operator_inner, covarianceBilin_self hmem] at hcov11
  have h11 : inner ℝ ((ContinuousLinearMap.id ℝ ℝ) (1 : ℝ)) (1 : ℝ) = 1 := by
    change inner ℝ (1 : ℝ) (1 : ℝ) = 1
    rw [Real.inner_apply, mul_one]
  have hleft : (fun y : ℝ => inner ℝ (1 : ℝ) y) = (id : ℝ → ℝ) := by
    funext y
    change inner ℝ (1 : ℝ) y = y
    rw [Real.inner_apply, one_mul]
  rw [hleft, h11] at hcov11
  exact hcov11

/-- A no-premise, nonzero, equality-sharp client under the canonical Gaussian
law on `ℝ`. The actual potential is `x² / 2`, the actual test is `id`, and the
Brascamp--Lieb inequality is obtained by invoking the finite-energy theorem. -/
theorem canonicalGaussian_real_brascamp_lieb_sharp :
    let ν : ProbabilityMeasure ℝ :=
      (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).law
    let U : ℝ → ℝ := fun x => x ^ 2 / 2
    (ν : Measure ℝ) = (volume : Measure ℝ).tilted (-U) ∧
    (∀ x : ℝ, gradient (id : ℝ → ℝ) x = 1) ∧
    (∀ x : ℝ, hessianOperator U x = (1 : ℝ →L[ℝ] ℝ)) ∧
    (∀ x : ℝ, Ring.inverse (hessianOperator U x) = (1 : ℝ →L[ℝ] ℝ)) ∧
    (∫ x, inner ℝ (gradient (id : ℝ → ℝ) x)
      (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x))
      ∂(ν : Measure ℝ)) = 1 ∧
    ProbabilityTheory.variance (id : ℝ → ℝ) (ν : Measure ℝ) = 1 ∧
    ProbabilityTheory.variance (id : ℝ → ℝ) (ν : Measure ℝ) ≤
      (∫ x, inner ℝ (gradient (id : ℝ → ℝ) x)
        (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x))
        ∂(ν : Measure ℝ)) ∧
    ProbabilityTheory.variance (id : ℝ → ℝ) (ν : Measure ℝ) =
      (∫ x, inner ℝ (gradient (id : ℝ → ℝ) x)
        (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x))
        ∂(ν : Measure ℝ)) := by
  let hG : FunctionalInequalities.KLS.RegularPotential
      (fun x : ℝ => ‖x‖ ^ 2 / 2) 1 1 :=
    FunctionalInequalities.KLS.regularPotential_half_norm_sq
  let ν : ProbabilityMeasure ℝ := hG.law
  let U : ℝ → ℝ := fun x => x ^ 2 / 2
  have hpotential : (fun x : ℝ => ‖x‖ ^ 2 / 2) = U := by
    funext x
    simp only [U, Real.norm_eq_abs, sq_abs]
  have hνU : (ν : Measure ℝ) = (volume : Measure ℝ).tilted (-U) := by
    change (volume : Measure ℝ).tilted (-(fun x : ℝ => ‖x‖ ^ 2 / 2)) =
      (volume : Measure ℝ).tilted (-U)
    rw [hpotential]
  have hU : ContDiff ℝ ∞ U := by
    exact (contDiff_id.pow 2).div_const 2
  have hU2 : ContDiff ℝ 2 U :=
    hU.of_le (WithTop.coe_le_coe.mpr le_top)
  have hform (x v : ℝ) :
      bilinearIteratedFDerivTwo ℝ U x v v = v ^ 2 := by
    simpa only [U, Real.norm_eq_abs, sq_abs] using
      (FunctionalInequalities.KLS.bilinearIteratedFDerivTwo_half_norm_sq x v)
  have hPD : ∀ x v : ℝ, v ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ U x v v := by
    intro x v hv
    rw [hform]
    exact sq_pos_of_ne_zero hv
  have hgrad (x : ℝ) : gradient (id : ℝ → ℝ) x = 1 :=
    canonicalGaussian_real_gradient_id x
  have hH (x : ℝ) : hessianOperator U x = (1 : ℝ →L[ℝ] ℝ) :=
    canonicalGaussian_real_hessian_half_sq x
  have hInv (x : ℝ) :
      Ring.inverse (hessianOperator U x) = (1 : ℝ →L[ℝ] ℝ) := by
    rw [hH]
    simp
  have he (x : ℝ) :
      inner ℝ (gradient (id : ℝ → ℝ) x)
        (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x)) = 1 := by
    rw [hgrad x, hInv x]
    change inner ℝ (1 : ℝ) (1 : ℝ) = 1
    rw [Real.inner_apply, mul_one]
  have henergy : Integrable
      (fun x => inner ℝ (gradient (id : ℝ → ℝ) x)
        (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x)))
      (ν : Measure ℝ) := by
    have hefun :
        (fun x : ℝ => inner ℝ (gradient (id : ℝ → ℝ) x)
          (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x))) =
        (fun _ : ℝ => (1 : ℝ)) := funext he
    rw [hefun]
    exact integrable_const (1 : ℝ)
  have henergyIntegral :
      (∫ x, inner ℝ (gradient (id : ℝ → ℝ) x)
        (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x))
        ∂(ν : Measure ℝ)) = 1 := by
    calc
      (∫ x, inner ℝ (gradient (id : ℝ → ℝ) x)
          (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x))
          ∂(ν : Measure ℝ)) =
          ∫ _ : ℝ, (1 : ℝ) ∂(ν : Measure ℝ) :=
        integral_congr_ae (Filter.Eventually.of_forall he)
      _ = 1 := by simp
  have hmem : MemLp (id : ℝ → ℝ) 2 (ν : Measure ℝ) := hG.memLp_id_two
  have hvariance : ProbabilityTheory.variance (id : ℝ → ℝ) (ν : Measure ℝ) = 1 :=
    canonicalGaussian_real_variance_id
  have hBL : ProbabilityTheory.variance (id : ℝ → ℝ) (ν : Measure ℝ) ≤
      (∫ x, inner ℝ (gradient (id : ℝ → ℝ) x)
        (Ring.inverse (hessianOperator U x) (gradient (id : ℝ → ℝ) x))
        ∂(ν : Measure ℝ)) :=
    scalar_brascamp_lieb_finite_energy (ν := ν) (U := U) (f := id)
      (volume : Measure ℝ) hG.logConcave_law hνU hU2 hPD contDiff_id hmem henergy
  refine ⟨hνU, hgrad, hH, hInv, henergyIntegral, hvariance, hBL, ?_⟩
  exact hvariance.trans henergyIntegral.symm

end CanonicalGaussian

end LetwinScalarBrascampLiebAudit

#print axioms FunctionalInequalities.KLS.LogConcave.scalar_brascamp_lieb_finite_energy
#print axioms FunctionalInequalities.KLS.LogConcave.scalar_brascamp_lieb_extended_energy
#print axioms FunctionalInequalities.KLS.LogConcave.scalar_brascamp_lieb_extended_energy_of_bounded
#print axioms FunctionalInequalities.KLS.LogConcave.compact_variational_estimate
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessian_inverse_young
#print axioms FunctionalInequalities.Analysis.BakryEmery.continuous_inverse_hessian_gradient_energy
#print axioms LetwinScalarBrascampLiebAudit.canonicalGaussian_real_isotropic
#print axioms LetwinScalarBrascampLiebAudit.canonicalGaussian_real_variance_id
#print axioms LetwinScalarBrascampLiebAudit.canonicalGaussian_real_brascamp_lieb_sharp
