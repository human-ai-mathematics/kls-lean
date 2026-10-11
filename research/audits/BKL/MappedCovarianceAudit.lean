import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.LogConcave.Translation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Audit clients for the mapped covariance of Letwin, arXiv:2607.24164v1, proof of Theorem 1.2, p. 14 (the covariance
step `Cov Z = |M|`, `Z = |M|^{1/2} X`, preceding (2.21)) (consumer chain: Letwin Theorem 1.2,
then Bizeul–Klartag–Lehec Lemma 4.2): `KLS.Isotropic.covarianceBilin_map_sqrt_abs_matrix` in `KLS/Isotropic.lean`
(root-accepted Astra v5 proof) and its spectral prerequisites in `Analysis/Matrix/Sign.lean`. Inputs are genuine: an
arbitrary isotropic law, an indefinite matrix, the singular zero matrix, an actual isotropic law on `Fin 0`, the scale
matrix `-4 • 1` (factor `2`, covariance `4 ⟪a, b⟫`), and the actual standard Gaussian on `EuclideanSpace ℝ (Fin 1)`,
whose isotropy proof is verbatim from `LocalThirdCumulantAudit.lean`. No transformed covariance is assumed. -/

noncomputable section
open MeasureTheory
open scoped MatrixOrder RealInnerProductSpace
open FunctionalInequalities

namespace BKLMappedCovarianceClients

/-- The API through its named arguments, for every isotropic law and every real symmetric matrix. -/
theorem general {n : Type*} [Fintype n] [DecidableEq n] (μ : ProbabilityMeasure (EuclideanSpace ℝ n))
    (hμ : KLS.Isotropic μ) (M : Matrix n n ℝ) (hM : M.IsSymm) (a b : EuclideanSpace ℝ n) :
    ProbabilityTheory.covarianceBilin ((μ : Measure (EuclideanSpace ℝ n)).map
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (CFC.sqrt (CFC.sqrt (M * M))))) a b =
      inner ℝ a ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (CFC.sqrt (M * M))) b) :=
  KLS.Isotropic.covarianceBilin_map_sqrt_abs_matrix (μ := μ) (hμ := hμ) (M := M) (hM := hM) a b

/-- The spectral prerequisites for an arbitrary symmetric matrix, with no positivity or invertibility. -/
theorem spectral {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (hM : M.IsSymm) :
    CFC.sqrt (CFC.sqrt (M * M)) * CFC.sqrt (CFC.sqrt (M * M)) = CFC.sqrt (M * M) ∧
      CFC.sqrt (CFC.sqrt (M * M)) * cfc (fun x : ℝ => (SignType.sign x : ℝ)) M *
        CFC.sqrt (CFC.sqrt (M * M)) = M := by
  have h := Analysis.symmetric_matrix_sign_factorization M hM
  exact ⟨h.1, h.2.1⟩

/-- An indefinite symmetric matrix. -/
def signFlip : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem signFlip_symm : signFlip.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem signFlip_mul_self : signFlip * signFlip = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signFlip, Matrix.mul_apply, Fin.sum_univ_two]

theorem signFlip_not_posSemidef : ¬ signFlip.PosSemidef := by
  intro h
  have := h.diag_nonneg (i := 1)
  simp [signFlip] at this
  linarith

/-- Indefinite case: `|M| = 1`, so the mapped law keeps the identity covariance of the input law. -/
theorem indefinite (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (hμ : KLS.Isotropic μ)
    (a b : EuclideanSpace ℝ (Fin 2)) :
    ProbabilityTheory.covarianceBilin (μ : Measure (EuclideanSpace ℝ (Fin 2))) a b = inner ℝ a b := by
  have h := KLS.Isotropic.covarianceBilin_map_sqrt_abs_matrix μ hμ signFlip signFlip_symm a b
  simp only [signFlip_mul_self, CFC.sqrt_one, map_one] at h
  simpa using h

/-- Singular case `M = 0`: the mapped law has zero covariance. -/
theorem singular_zero {n : Type*} [Fintype n] [DecidableEq n] (μ : ProbabilityMeasure (EuclideanSpace ℝ n))
    (hμ : KLS.Isotropic μ) (a b : EuclideanSpace ℝ n) :
    ProbabilityTheory.covarianceBilin ((μ : Measure (EuclideanSpace ℝ n)).map
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (0 : Matrix n n ℝ))) a b = 0 := by
  have h := KLS.Isotropic.covarianceBilin_map_sqrt_abs_matrix μ hμ 0 (Matrix.isSymm_zero) a b
  simp only [mul_zero, CFC.sqrt_zero, map_zero] at h
  simpa using h

/-- An actual isotropic law in dimension zero. -/
def zeroLaw : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)) := ⟨Measure.dirac 0, inferInstance⟩

theorem zeroLaw_isotropic : KLS.Isotropic zeroLaw where
  memLp_two := MemLp.of_bound continuous_id.aestronglyMeasurable 0
    (ae_of_all _ fun x => by simp [Subsingleton.elim x 0])
  mean_zero := by simp [zeroLaw]
  covariance_identity := by
    ext1 x
    exact Subsingleton.elim _ _

/-- Dimension zero: every matrix is symmetric and the theorem applies to the actual isotropic law. -/
theorem zero_dimensional (M : Matrix (Fin 0) (Fin 0) ℝ) (a b : EuclideanSpace ℝ (Fin 0)) :
    ProbabilityTheory.covarianceBilin ((zeroLaw : Measure (EuclideanSpace ℝ (Fin 0))).map
        (Matrix.toEuclideanCLM (n := Fin 0) (𝕜 := ℝ) (CFC.sqrt (CFC.sqrt (M * M))))) a b =
      inner ℝ a ((Matrix.toEuclideanCLM (n := Fin 0) (𝕜 := ℝ) (CFC.sqrt (M * M))) b) :=
  KLS.Isotropic.covarianceBilin_map_sqrt_abs_matrix zeroLaw zeroLaw_isotropic M
    (by ext i; exact Fin.elim0 i) a b

end BKLMappedCovarianceClients


section ScaleClients

open MeasureTheory
open scoped MatrixOrder RealInnerProductSpace
open FunctionalInequalities

namespace BKLMappedCovarianceClients

/-- `M = -4 • 1` is symmetric and negative definite; `|M| = 4 • 1` and `S = sqrt |M| = 2 • 1`, so the mapped law
`2 X` has covariance `4 ⟪a, b⟫` for every isotropic law, in every dimension. -/
theorem scale_neg_four {n : Type*} [Fintype n] [DecidableEq n] (μ : ProbabilityMeasure (EuclideanSpace ℝ n))
    (hμ : KLS.Isotropic μ) (a b : EuclideanSpace ℝ n) :
    ProbabilityTheory.covarianceBilin ((μ : Measure (EuclideanSpace ℝ n)).map
        (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) ((2 : ℝ) • (1 : Matrix n n ℝ)))) a b = 4 * inner ℝ a b := by
  have hsymm : ((-4 : ℝ) • (1 : Matrix n n ℝ)).IsSymm := by
    simp [Matrix.IsSymm, Matrix.transpose_smul]
  have hsq : (-4 : ℝ) • (1 : Matrix n n ℝ) * ((-4 : ℝ) • 1) = (4 : ℝ) • 1 * ((4 : ℝ) • 1) := by
    simp only [smul_mul_smul_comm, one_mul]
    norm_num
  have hpos : ∀ r : ℝ, 0 ≤ r → (0 : Matrix n n ℝ) ≤ r • 1 := fun r hr => by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.PosSemidef.one.smul hr
  have habs : CFC.sqrt ((-4 : ℝ) • (1 : Matrix n n ℝ) * ((-4 : ℝ) • 1)) = (4 : ℝ) • 1 := by
    rw [hsq]
    exact CFC.sqrt_unique rfl (hpos 4 (by norm_num))
  have hroot : CFC.sqrt ((4 : ℝ) • (1 : Matrix n n ℝ)) = (2 : ℝ) • 1 := by
    refine CFC.sqrt_unique ?_ (hpos 2 (by norm_num))
    simp only [smul_mul_smul_comm, one_mul]
    norm_num
  have h := KLS.Isotropic.covarianceBilin_map_sqrt_abs_matrix μ hμ _ hsymm a b
  simp only [habs, hroot] at h
  rw [h]
  simp [inner_smul_right]

end BKLMappedCovarianceClients

end ScaleClients

section GaussianClient

open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities

namespace BKLMappedCovarianceGaussian

abbrev E := EuclideanSpace ℝ (Fin 1)
def gaussian : ProbabilityMeasure E := (KLS.regularPotential_half_norm_sq (E := E)).law

theorem gaussian_isotropic : KLS.Isotropic gaussian := by
  apply KLS.isotropic_of_moments gaussian
    (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law.memLp_id_two
    KLS.integral_id_tilted_half_norm_sq
  intro u v
  have hs : (∫ x : E, x 0 ^ 2 ∂(gaussian : Measure E)) = 1 := by
    have h := KLS.integral_inner_sq_tilted_half_norm_sq (EuclideanSpace.basisFun (Fin 1) ℝ 0)
    have hm : (volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2) = (gaussian : Measure E) := rfl
    rw [hm] at h
    simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_pow] using h
  simp only [PiLp.inner_apply, Fin.sum_univ_one, Real.inner_apply]
  have he : (fun x : E => u 0 * x 0 * (v 0 * x 0)) = fun x => (u 0 * v 0) * x 0 ^ 2 := by
    ext x
    ring
  rw [he, integral_const_mul, hs, mul_one]


/-- The actual standard Gaussian on `EuclideanSpace ℝ (Fin 1)`: the law of `2 X` has covariance `4 ⟪a, b⟫`. -/
theorem gaussian_scale (a b : E) :
    ProbabilityTheory.covarianceBilin ((gaussian : Measure E).map
        (Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))) a b =
      4 * inner ℝ a b :=
  BKLMappedCovarianceClients.scale_neg_four gaussian gaussian_isotropic a b

end BKLMappedCovarianceGaussian

end GaussianClient

#print axioms BKLMappedCovarianceClients.general
#print axioms BKLMappedCovarianceClients.spectral
#print axioms BKLMappedCovarianceClients.signFlip_symm
#print axioms BKLMappedCovarianceClients.signFlip_mul_self
#print axioms BKLMappedCovarianceClients.signFlip_not_posSemidef
#print axioms BKLMappedCovarianceClients.indefinite
#print axioms BKLMappedCovarianceClients.singular_zero
#print axioms BKLMappedCovarianceClients.zeroLaw_isotropic
#print axioms BKLMappedCovarianceClients.zero_dimensional
#print axioms BKLMappedCovarianceClients.scale_neg_four
#print axioms BKLMappedCovarianceGaussian.gaussian_isotropic
#print axioms BKLMappedCovarianceGaussian.gaussian_scale
#print axioms FunctionalInequalities.Analysis.symmetric_matrix_sqrt_real_cfc_bridge
#print axioms FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization
#print axioms FunctionalInequalities.KLS.Isotropic.covarianceBilin_map_sqrt_abs_matrix
