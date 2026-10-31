module

public import FunctionalInequalities.KLS.LogConcave.Stein
public import FunctionalInequalities.KLS.BKL.GaussianTaylor
public import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate

/-!
# Audit (client-only): the standard Gaussian has the identity Stein kernel

Nonvacuity audit for the Letwin Stein-kernel definitions (arXiv:2607.24164v1, Definition 2.6,
(2.19), A.7, Lemma 2.9): the standard Gaussian on `ℝ¹` with `τ = Id` satisfies the compact-test
Stein
identity (normalized weighted-Laplacian integration by parts), the linear unit-energy test has
pairing
`1`, so the `H^{-1}` norm of the linear input is exactly `1` (upper bound from Lemma 2.9, lower
bound
from the test), the input is a nonzero `L²` class, and A.7 is exercised on the nonsmooth norm test.
This audit is outside the active implication chain: it constructs no general Stein kernel and
asserts nothing about the moment map, Letwin Theorems 1.1–1.2 or BKL Theorem 4.1. The heavy
`GaussianTaylor` import is client-only.
-/

@[expose] public section

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace ContDiff

namespace GaussianSteinAudit

private theorem norm_test_A7 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n)
    (hK : Probability.Stein.IsSteinKernel μ τ) (hLC : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) (hSym : Probability.Stein.SymmetricAE μ τ)
    (hHS :
      MemLp (fun x => Probability.Stein.hsNorm (τ x)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ⟪x, v⟫ * ‖x‖ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x,
          ⟪Probability.Stein.action (τ x) v,
            gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)
              x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      |∫ x, ⟪x, v⟫ * ‖x‖ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| ≤
        Real.sqrt
            (∫ x,
              ‖Probability.Stein.action (τ x) v‖ ^
                2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) *
          Real.sqrt
            (∫ x,
              ‖gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) x‖ ^
                2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hμ2 :=
    (KLS.LogConcave.absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull).2
  have hnorm2 : MemLp (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) 2 (μ : Measure _) := by
    simpa only [id_eq] using hμ2.norm
  have hlip : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) :=
    lipschitzWith_one_norm
  have hgrad2 : MemLp (gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)) 2 (μ : Measure _) :=
    MemLp.of_bound (aestronglyMeasurable_gradient _ _) 1
      (Filter.Eventually.of_forall fun x => norm_gradient_le_of_lipschitz hlip x)
  exact
    KLS.LogConcave.stein_identity_of_affineSupport_eq_top μ τ hK hLC hfull hSym hHS
      (fun x => ‖x‖) hlip.locallyLipschitz hnorm2 hgrad2 v

abbrev E := EuclideanSpace ℝ (Fin 1)
private noncomputable def V (x : E) : ℝ := ‖x‖ ^ 2 / 2
noncomputable def gaussian : ProbabilityMeasure E :=
  (KLS.regularPotential_half_norm_sq (E := E)).law
noncomputable def kernel : E → Probability.Stein.KernelMatrix 1 := fun _ => 1
noncomputable def direction : E := EuclideanSpace.basisFun (Fin 1) ℝ 0

theorem gaussian_logConcave : KLS.LogConcave gaussian :=
  (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law

theorem gaussian_full : Probability.affineSupport gaussian = ⊤ := by
  change affineSpan ℝ ((gaussian : Measure E).support) = ⊤
  exact gaussian_logConcave.convex_support.interior_nonempty_iff_affineSpan_eq_top.mp
    (KLS.regularPotential_half_norm_sq (E := E)).interior_support_law

theorem gaussian_id_memLp : MemLp (id : E → E) 2 (gaussian : Measure E) :=
  (KLS.LogConcave.absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top gaussian
      gaussian_logConcave gaussian_full).2

private theorem half_norm_sq_hasFDerivAt (x : E) :
    HasFDerivAt V (innerSL ℝ x) x := by
  have h : HasFDerivAt (fun y : E => ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa using (hasFDerivAt_id x).norm_sq
  have hf : V = fun y : E => 1 / 2 * ‖y‖ ^ 2 := by funext y; unfold V; ring
  have hL : innerSL ℝ x = (1 / 2 : ℝ) • (2 • innerSL ℝ x) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; norm_num
  rw [hf, hL]
  exact h.const_mul (1 / 2 : ℝ)

private theorem gradient_V (x : E) : gradient V x = x := by
  rw [gradient, (half_norm_sq_hasFDerivAt x).fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply x

private theorem gradient_linear (v x : E) : gradient (fun y : E => ⟪v, y⟫) x = v := by
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (innerSL ℝ v) x) = v
  rw [(innerSL ℝ v).hasFDerivAt.fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply v

private theorem laplacian_linear (v x : E) : Laplacian.laplacian (fun y : E => ⟪v, y⟫) x = 0 := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  have hd : fderiv ℝ (fun y : E => ⟪v, y⟫) = fun _ => innerSL ℝ v := by
    funext y
    exact (innerSL ℝ v).hasFDerivAt.fderiv
  rw [hd]
  simp

/-- True normalized Gaussian compact-test IBP produces the coordinate Stein identity. -/
theorem gaussian_compact_identity (f : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (i : Fin 1) :
    (∫ x, x i * f x ∂(gaussian : Measure E)) =
      ∫ x, Probability.Stein.action (kernel x) (gradient f x) i ∂(gaussian : Measure E) := by
  let e : E := EuclideanSpace.basisFun (Fin 1) ℝ i
  have hV : ContDiff ℝ 1 V := (contDiff_norm_sq ℝ).div_const 2
  have hu : ContDiff ℝ 2 (fun x : E => ⟪e, x⟫) := (innerSL ℝ e).contDiff
  have hlap (x : E) : weightedLaplacian V (fun y : E => ⟪e, y⟫) x = -x i := by
    rw [weightedLaplacian_apply, gradient_V, gradient_linear, laplacian_linear]
    simp only [e, EuclideanSpace.inner_basisFun_real, zero_sub]
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have h := integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport
    (volume : Measure E) hV hu hf2 hc
  have hmeasure : (volume : Measure E).tilted (-V) = (gaussian : Measure E) := rfl
  rw [hmeasure] at h
  simp_rw [hlap, gradient_linear] at h
  have h' : -(∫ x, x i * f x ∂(gaussian : Measure E)) =
      -(∫ x, gradient f x i ∂(gaussian : Measure E)) := by
    simpa only [e, EuclideanSpace.basisFun_inner, neg_mul, integral_neg]
      using h
  have h'' := neg_injective h'
  simpa only [kernel, Probability.Stein.action, Matrix.one_mulVec, WithLp.toLp_ofLp] using h''

/-- The actual law and identity matrix satisfy precisely Definition 2.6. -/
theorem gaussian_stein : Probability.Stein.IsSteinKernel gaussian kernel where
  integrable_id := gaussian_id_memLp.integrable (by norm_num)
  mean_zero := KLS.integral_id_tilted_half_norm_sq
  measurable_entries := fun _ _ => measurable_const
  local_entries := fun i j => locallyIntegrable_const ((1 : Probability.Stein.KernelMatrix 1) i j)
  compact_identity := gaussian_compact_identity

theorem kernel_symmetric : Probability.Stein.SymmetricAE gaussian kernel := by
  exact Filter.Eventually.of_forall fun _ i j => by simp [kernel, Matrix.one_apply, eq_comm]

theorem kernel_hs_memLp :
    MemLp (fun x => Probability.Stein.hsNorm (kernel x)) 2 (gaussian : Measure E) :=
  memLp_const (Probability.Stein.hsNorm (1 : Probability.Stein.KernelMatrix 1))

/-- Every source premise is discharged for this actual nonzero Gaussian direction. -/
theorem actual_source_Lemma29 :
    let q := Probability.Stein.linearLp gaussian gaussian_id_memLp direction
    (∫ x, q x ∂(gaussian : Measure E)) = 0 ∧
      Energy.Dual.dualNorm gaussian q ≠ ⊤ ∧
        (Energy.Dual.dualNorm gaussian q).toReal =
            sSup (Energy.Dual.signedPairings gaussian q) ∧
          (Energy.Dual.dualNorm gaussian q).toReal ^ 2 ≤
            ∫ x, ‖Probability.Stein.action (kernel x) direction‖ ^ 2 ∂(gaussian : Measure E) := by
  exact
    KLS.LogConcave.dualNorm_linear_sq_le_of_affineSupport_eq_top gaussian kernel gaussian_stein
      gaussian_logConcave gaussian_full kernel_symmetric kernel_hs_memLp direction


theorem direction_norm : ‖direction‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 1) ℝ).norm_eq_one 0

theorem direction_ne_zero : direction ≠ 0 := by
  intro h
  have hn := direction_norm
  rw [h, norm_zero] at hn
  norm_num at hn

theorem gradient_linear_direction (x : E) :
    gradient (fun y : E => ⟪direction, y⟫) x = direction := by
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (innerSL ℝ direction) x) = direction
  rw [(innerSL ℝ direction).hasFDerivAt.fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply direction

/-- The linear test lies in the entire actual source class, with its energy derived exactly. -/
noncomputable def linearTest : Energy.Dual.UnitEnergyTest gaussian where
  fn := fun x => ⟪direction, x⟫
  locallyLipschitz := (innerSL ℝ direction).lipschitzWith.locallyLipschitz
  memLp := by simpa only [id_eq] using gaussian_id_memLp.const_inner (𝕜 := ℝ) direction
  gradLp := by
    have hg : gradient (fun x : E => ⟪direction, x⟫) = fun _ => direction :=
      funext gradient_linear_direction
    rw [hg]
    exact memLp_const direction
  energy := by
    apply (Energy.Dual.unit_gradient_norm_iff gaussian _).mpr
    simp_rw [gradient_linear_direction, direction_norm]
    simp

noncomputable def linearInput : Lp ℝ 2 (gaussian : Measure E) :=
  Probability.Stein.linearLp gaussian gaussian_id_memLp direction

/-- Actual normalized Gaussian covariance supplies the nonzero linear Energy.Dual.pairing. -/
theorem linear_pairing_one : Energy.Dual.pairing gaussian linearInput linearTest = 1 := by
  have hlin : MemLp (fun x : E => ⟪x, direction⟫) 2 (gaussian : Measure E) := by
    simpa only [id_eq] using gaussian_id_memLp.inner_const (𝕜 := ℝ) direction
  have heq :
    Energy.Dual.pairing gaussian linearInput linearTest =
      ∫ x, ⟪x, direction⟫ * ⟪direction, x⟫ ∂(gaussian : Measure E) := by
    simpa only [Energy.Dual.pairing, linearInput, Probability.Stein.linearLp, linearTest,
      Real.inner_apply] using (L2.integral_inner_toLp hlin linearTest.memLp).symm
  rw [heq]
  have hf : (fun x : E => ⟪x, direction⟫ * ⟪direction, x⟫) = fun x => ⟪direction, x⟫ ^ 2 := by
    funext x
    rw [real_inner_comm x direction, sq]
  rw [hf]
  have h := KLS.integral_inner_sq_tilted_half_norm_sq direction
  have hmeasure :
    (volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2) = (gaussian : Measure E) := rfl
  rw [hmeasure] at h
  simpa only [direction_norm, one_pow] using h

/-- Exact H^-1 value; every source premise and both upper/lower bounds are genuinely proved. -/
theorem linear_dualNorm_eq_one : Energy.Dual.dualNorm gaussian linearInput = 1 := by
  have hs := actual_source_Lemma29
  dsimp only at hs
  have hfinite : Energy.Dual.dualNorm gaussian linearInput ≠ ⊤ := hs.2.1
  have hupper : (Energy.Dual.dualNorm gaussian linearInput).toReal ^ 2 ≤ 1 := by
    simpa only [linearInput, kernel, Probability.Stein.action, Matrix.one_mulVec,
      WithLp.toLp_ofLp, direction_norm, one_pow, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul] using hs.2.2.2
  have hlower := Energy.Dual.pairing_le_toReal_of_ne_top gaussian linearInput hfinite linearTest
  rw [linear_pairing_one] at hlower
  have hreal : (Energy.Dual.dualNorm gaussian linearInput).toReal = 1 := by nlinarith
  exact (ENNReal.toReal_eq_one_iff _).mp hreal

theorem linear_signed_sSup_eq_one :
    sSup (Energy.Dual.signedPairings gaussian linearInput) = 1 := by
  have hfinite : Energy.Dual.dualNorm gaussian linearInput ≠ ⊤ := by
    rw [linear_dualNorm_eq_one]; norm_num
  rw [← Energy.Dual.toReal_dualNorm_eq_signed_sSup gaussian linearInput hfinite,
    linear_dualNorm_eq_one]
  exact ENNReal.toReal_one

/-- The input is a nonzero L2 class, not merely a nonzero coordinate direction. -/
theorem linearInput_ne_zero : linearInput ≠ 0 := by
  intro hzero
  have h := linear_pairing_one
  rw [Energy.Dual.pairing, hzero, inner_zero_left] at h
  norm_num at h

/--
Source A.7 is exercised on the true nonsmooth/noncompact norm test and true Gaussian kernel. -/
theorem actual_norm_test_A7 :
    (∫ x, ⟪x, direction⟫ * ‖x‖ ∂(gaussian : Measure E)) =
        (∫ x,
          ⟪Probability.Stein.action (kernel x) direction,
            gradient (fun x : E => ‖x‖) x⟫ ∂(gaussian : Measure E)) ∧
      |∫ x, ⟪x, direction⟫ * ‖x‖ ∂(gaussian : Measure E)| ≤
        Real.sqrt
            (∫ x, ‖Probability.Stein.action (kernel x) direction‖ ^ 2 ∂(gaussian : Measure E)) *
          Real.sqrt (∫ x, ‖gradient (fun x : E => ‖x‖) x‖ ^ 2 ∂(gaussian : Measure E)) :=
  norm_test_A7 gaussian kernel gaussian_stein gaussian_logConcave gaussian_full kernel_symmetric
    kernel_hs_memLp direction

end GaussianSteinAudit

#print axioms GaussianSteinAudit.gaussian_stein
#print axioms GaussianSteinAudit.actual_source_Lemma29
#print axioms GaussianSteinAudit.linear_pairing_one
#print axioms GaussianSteinAudit.linear_dualNorm_eq_one
#print axioms GaussianSteinAudit.linear_signed_sSup_eq_one
#print axioms GaussianSteinAudit.linearInput_ne_zero
#print axioms GaussianSteinAudit.actual_norm_test_A7
