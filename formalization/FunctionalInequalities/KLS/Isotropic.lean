import FunctionalInequalities.Probability.Covariance.Basic
import FunctionalInequalities.Probability.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.ConvexHessian
import FunctionalInequalities.Analysis.Matrix.Sign
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Isotropic probability laws

Source: Blueprint `def:isotropic-law`. The three fields state finite second moment,
zero barycenter, and identity centered covariance. This is a definition, with no whitening
or equivalence theorem. On a zero-dimensional space the identity operator is itself zero.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]

/-- A probability law with finite second moment, mean zero, and identity centered covariance.
The moment field prevents the totalized integral/covariance from encoding integrability. -/
structure Isotropic (μ : ProbabilityMeasure E) : Prop where
  memLp_two : MemLp id 2 (μ : Measure E)
  mean_zero : ∫ x, x ∂(μ : Measure E) = 0
  covariance_identity : Covariance.operator (μ : Measure E) = ContinuousLinearMap.id ℝ E

section Moments

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Isotropy from moments**: finite second moment, mean zero and `∫ ⟪u, x⟫⟪v, x⟫ = ⟪u, v⟫`. -/
theorem isotropic_of_moments
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) (h2 : MemLp id 2 (ν : Measure E))
    (h0 : ∫ x, x ∂(ν : Measure E) = 0)
    (hcov : ∀ u v : E, ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E) = ⟪u, v⟫) :
    Isotropic ν := by
    refine ⟨h2, h0, ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right (𝕜 := ℝ)
    intro v
    rw [Covariance.operator_inner]
    rw [ProbabilityTheory.covarianceBilin_apply h2]
    simpa [h0] using hcov u v

/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫`. -/
theorem Isotropic.integral_inner_mul_inner
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (u v : E) :
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) = ⟪u, v⟫ := by
  calc
    (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂(ν : Measure E)) =
        ∫ x, ⟪u, x - ∫ y, id y ∂(ν : Measure E)⟫ *
          ⟪v, x - ∫ y, id y ∂(ν : Measure E)⟫ ∂(ν : Measure E) := by
      simp [hν.mean_zero]
    _ = ProbabilityTheory.covarianceBilin (ν : Measure E) u v := by
      rw [ProbabilityTheory.covarianceBilin_apply hν.memLp_two]
    _ = ⟪u, v⟫ := by
      rw [← Covariance.operator_inner, hν.covariance_identity]
      simp

end Moments

section LinearIsometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **Isotropy along a linear isometry**.
The `MemLp` step uses `ContinuousLinearMap.comp_memLp'`. -/
theorem Isotropic.map_linearIsometryEquiv {ν : ProbabilityMeasure E}
    (hν : Isotropic ν) (φ : E ≃ₗᵢ[ℝ] F) :
    Isotropic (ν.map φ.continuous.measurable.aemeasurable) := by
    let μ : Measure F := Measure.map φ (ν : Measure E)
    have hmem : MemLp id 2 μ := by
      change MemLp id 2 (Measure.map φ (ν : Measure E))
      apply (memLp_map_measure_iff continuous_id.aestronglyMeasurable
        φ.continuous.measurable.aemeasurable).2
      exact φ.toContinuousLinearMap.comp_memLp' hν.memLp_two
    have hmean : (∫ x, x ∂μ) = 0 := by
      change (∫ x, id x ∂Measure.map φ (ν : Measure E)) = 0
      rw [integral_map φ.continuous.measurable.aemeasurable
        continuous_id.aestronglyMeasurable]
      have hint : Integrable id (ν : Measure E) :=
        hν.memLp_two.integrable (by norm_num)
      calc
        (∫ x, id (φ x) ∂(ν : Measure E)) =
            ∫ x, φ (id x) ∂(ν : Measure E) := by rfl
        _ = φ (∫ x, id x ∂(ν : Measure E)) :=
          φ.toContinuousLinearMap.integral_comp_comm hint
        _ = 0 := by simp [hν.mean_zero]
    refine isotropic_of_moments
      (ν.map φ.continuous.measurable.aemeasurable) hmem hmean ?_
    intro u v
    let g : F → ℝ := fun x => ⟪u, x⟫ * ⟪v, x⟫
    have hg : AEStronglyMeasurable g μ := by
      exact
        ((continuous_const.inner continuous_id).mul
          (continuous_const.inner continuous_id)).aestronglyMeasurable
    change (∫ x, g x ∂Measure.map φ (ν : Measure E)) = ⟪u, v⟫
    rw [integral_map φ.continuous.measurable.aemeasurable hg]
    have hu : ∀ x : E, ⟪u, φ x⟫ = ⟪φ.symm u, x⟫ := by
      intro x
      simpa using φ.inner_map_map (φ.symm u) x
    have hv : ∀ x : E, ⟪v, φ x⟫ = ⟪φ.symm v, x⟫ := by
      intro x
      simpa using φ.inner_map_map (φ.symm v) x
    calc
      (∫ x, g (φ x) ∂(ν : Measure E)) =
          ∫ x, ⟪φ.symm u, x⟫ * ⟪φ.symm v, x⟫ ∂(ν : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [g, hu, hv]
      _ = ⟪φ.symm u, φ.symm v⟫ :=
        hν.integral_inner_mul_inner (φ.symm u) (φ.symm v)
      _ = ⟪u, v⟫ := by
        simpa only [φ.apply_symm_apply] using
          (φ.inner_map_map (φ.symm u) (φ.symm v)).symm

end LinearIsometry

section FiniteDimensional

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Gradient second moments of an isotropic pushforward** (Letwin Lemma 2.3, step 2): if `(∇φ)_* ν` is isotropic then
`∫ (∂_u φ)(∂_v φ) dν = ⟪u, v⟫`. -/
theorem integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map
    (ν : ProbabilityMeasure E) {φ : E → ℝ} (hφ : Measurable (gradient φ))
    (hiso : Isotropic (ν.map hφ.aemeasurable)) (u v : E) :
    ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) = ⟪u, v⟫ := by
    have hderiv (x w : E) :
        fderiv ℝ φ x w = ⟪w, gradient φ x⟫ := by
      rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply, real_inner_comm]

    have hmeas :
        AEStronglyMeasurable
          (fun y : E => ⟪u, y⟫ * ⟪v, y⟫)
          ((ν : Measure E).map (gradient φ)) := by
      exact
        ((continuous_const.inner continuous_id).mul
          (continuous_const.inner continuous_id)).aestronglyMeasurable

    calc
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) =
          ∫ x, ⟪u, gradient φ x⟫ * ⟪v, gradient φ x⟫ ∂(ν : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hderiv x u, hderiv x v]
      _ = ∫ y, ⟪u, y⟫ * ⟪v, y⟫
            ∂((ν : Measure E).map (gradient φ)) := by
        exact (integral_map hφ.aemeasurable hmeas).symm
      _ = ⟪u, v⟫ := by
        have h := hiso.integral_inner_mul_inner u v
        simp only [ProbabilityMeasure.toMeasure_map] at h
        exact h

open scoped ContDiff in
/-- **Letwin Lemma 2.3 (mean Hessian of the moment-map potential is the identity)**, for any smooth
normalized `φ` with isotropic gradient law and the stated integrability (the moment map itself is not constructed). -/
theorem integral_fderiv_fderiv_tilted_eq_inner_of_isotropic_map
    (m : Measure E) [m.IsAddHaarMeasure]
    (φ : E → ℝ) (u v : E) (hφ : ContDiff ℝ ∞ φ)
    (hφexp : Integrable (fun x => Real.exp (-φ x)) m)
    (hφnorm : ∫ x, Real.exp (-φ x) ∂m = 1)
    (ν : ProbabilityMeasure E) (hν : (ν : Measure E) = m.tilted (-φ))
    (hiso : KLS.Isotropic (ν.map (Analysis.BakryEmery.continuous_gradient
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top))).measurable.aemeasurable))
    (hdd : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ φ y u) x v) (m.tilted (-φ)))
    (hdd' : Integrable (fun x => fderiv ℝ φ x u * fderiv ℝ φ x v) (m.tilted (-φ)))
    (hd : Integrable (fun x => fderiv ℝ φ x u) (m.tilted (-φ))) :
    (∫ x, fderiv ℝ (fun y => fderiv ℝ φ y u) x v ∂(m.tilted (-φ))) = ⟪u, v⟫ := by
    have hgrad : Measurable (gradient φ) :=
      (Analysis.BakryEmery.continuous_gradient (hφ.of_le (WithTop.coe_le_coe.mpr le_top))).measurable
    rw [Analysis.BakryEmery.integral_fderiv_fderiv_tilted_eq_integral_mul m φ u v hφ hφexp hφnorm hdd hdd' hd]
    rw [← hν]
    exact KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map ν hgrad hiso u v


open scoped RealInnerProductSpace in
/-- An isotropic law on `ℝⁿ` has `∫‖x‖² = n` (sum of the unit coordinate variances). -/
theorem Isotropic.integral_norm_sq {n : ℕ}
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : KLS.Isotropic ν) :
    (∫ x, ‖x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) = (n : ℝ) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hcoord (j : Fin n) : (∫ x, (x j) ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) = 1 := by
    have h := hiso.integral_inner_mul_inner (e j) (e j)
    rw [real_inner_self_eq_norm_sq, e.norm_eq_one, one_pow] at h
    simpa only [e, EuclideanSpace.basisFun_inner, ← pow_two] using h
  have hints (j : Fin n) : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x j) ^ 2)
      (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh : MemLp (fun x => ⟪e j, x⟫) 2 (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [Function.comp_def, id_eq, innerSL_apply_apply] using
        (innerSL ℝ (e j)).comp_memLp' hiso.memLp_two
    simpa only [e, EuclideanSpace.basisFun_inner] using hh.integrable_sq
  calc
    (∫ x, ‖x‖ ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) = ∫ x, ∑ j : Fin n, (x j) ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      congr 1
      funext x
      exact EuclideanSpace.real_norm_sq_eq x
    _ = ∑ j : Fin n, ∫ x, (x j) ^ 2 ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) :=
      integral_finsetSum _ (fun j _ => hints j)
    _ = (n : ℝ) := by simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]


open scoped ContDiff in
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Letwin Lemma 2.3 for a given potential**: if `φ` is smooth and convex with `e^{-φ}` a probability
density, `ν = e^{-φ} dx`, and `(∇φ)_* ν` is isotropic, then `∫ ∂_u∂_v φ dν = ⟪u, v⟫`; every integrability
input is derived. The moment map producing such a `φ` for a given law is not constructed. -/
theorem integral_hessian_eq_inner_of_isotropic_map
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : ConvexOn ℝ Set.univ φ)
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (ν : ProbabilityMeasure E) (hν : (ν : Measure E) = (volume : Measure E).tilted (-φ))
    (hiso : KLS.Isotropic (ν.map (continuous_gradient
      (hφ.of_le (WithTop.coe_le_coe.mpr le_top))).measurable.aemeasurable)) (u v : E) :
    (∫ x, bilinearIteratedFDerivTwo ℝ φ x u v ∂(ν : Measure E)) = ⟪u, v⟫ := by
  have hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hgm : Measurable (gradient φ) :=
    (continuous_gradient (hφ.of_le (WithTop.coe_le_coe.mpr le_top))).measurable
  have hgradν : MemLp (gradient φ) 2 (ν : Measure E) := by
    have hh := hiso.memLp_two
    simp only [ProbabilityMeasure.toMeasure_map] at hh
    simpa only [Function.comp_def, id_eq] using
      (memLp_map_measure_iff continuous_id.aestronglyMeasurable hgm.aemeasurable).mp hh
  have hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ)) := by
    rw [← hν]
    exact hgradν
  rw [hν, Analysis.BakryEmery.integral_hessian_tilted_eq_integral_fderiv_mul_of_convexOn φ hφ hc hexp hnorm hgrad]
  rw [← hν]
  exact integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map ν hgm hiso u v

end FiniteDimensional

end FunctionalInequalities.KLS

/-! ### Covariance of the matrix absolute-value transform (Letwin, proof of Theorem 1.2, p. 14)

For an isotropic law and a real symmetric matrix `M` (singular, indefinite and `Fin 0` included), the push-forward by
`S = sqrt(sqrt(M * M))` has covariance `|M| = sqrt(M * M)`: the covariance step `Cov Z = |M|`, `Z = |M|^{1/2} X`,
of the proof of Letwin arXiv:2607.24164v1 Theorem 1.2 (p. 14, the unnumbered display preceding (2.21); the source
first reduces to invertible `M`). Covariance/algebra prerequisite only (consumer chain:
Letwin Theorem 1.2, then Bizeul–Klartag–Lehec Lemma 4.2); not the Stein-kernel trace identity (2.21), the `H⁻¹` or
the variance-eight estimates. -/

namespace FunctionalInequalities.KLS

open scoped MatrixOrder

/-- Letwin, proof of Theorem 1.2, p. 14 (the covariance step preceding (2.21)): after `Z = |M|^{1/2} X`, the
covariance of `Z` is `|M|`, for every real symmetric `M` (singular, indefinite and `Fin 0` included).
The input law is genuinely isotropic, hence in particular centered with a finite second moment. -/
theorem Isotropic.covarianceBilin_map_sqrt_abs_matrix
    {n : Type*} [Fintype n] [DecidableEq n]
    (μ : ProbabilityMeasure (EuclideanSpace ℝ n)) (hμ : KLS.Isotropic μ)
    (M : Matrix n n ℝ) (hM : M.IsSymm) :
    let AbsM := CFC.sqrt (M * M)
    let S := CFC.sqrt AbsM
    let L := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) S
    ∀ a b : EuclideanSpace ℝ n,
      ProbabilityTheory.covarianceBilin ((μ : Measure (EuclideanSpace ℝ n)).map L) a b =
        inner ℝ a ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) AbsM) b) := by
    let AbsM : Matrix n n ℝ := CFC.sqrt (M * M)
    let S : Matrix n n ℝ := CFC.sqrt AbsM
    let L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) S
    change
      ∀ a b : EuclideanSpace ℝ n,
        ProbabilityTheory.covarianceBilin
            ((μ : Measure (EuclideanSpace ℝ n)).map L) a b =
          inner ℝ a
            ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) AbsM) b)
    intro a b
    have hSS : S * S = AbsM := by
      simpa [AbsM, S] using
        (FunctionalInequalities.Analysis.symmetric_matrix_sign_factorization M hM).1
    have hSpos : (0 : Matrix n n ℝ) ≤ S := by
      dsimp [S]
      exact CFC.sqrt_nonneg AbsM
    have hSstar : star S = S := by
      exact (IsSelfAdjoint.of_nonneg hSpos).star_eq
    have hLadj : ContinuousLinearMap.adjoint L = L := by
      have hs :=
        map_star (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) S
      have hs' : L = star L := by
        simpa [L, hSstar] using hs
      simpa only [ContinuousLinearMap.star_eq_adjoint] using hs'.symm
    have hLL :
        L (L b) =
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) AbsM) b := by
      have hm :
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (S * S) =
            Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) S *
              Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) S :=
        map_mul (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) S S
      rw [hSS] at hm
      simpa [L] using (congrArg (fun T => T b) hm).symm
    calc
      ProbabilityTheory.covarianceBilin
          ((μ : Measure (EuclideanSpace ℝ n)).map L) a b =
          ProbabilityTheory.covarianceBilin
            (μ : Measure (EuclideanSpace ℝ n))
            (ContinuousLinearMap.adjoint L a)
            (ContinuousLinearMap.adjoint L b) :=
        ProbabilityTheory.covarianceBilin_map (hμ.memLp_two) L a b
      _ = inner ℝ
            (ContinuousLinearMap.adjoint L a)
            (ContinuousLinearMap.adjoint L b) := by
        calc
          ProbabilityTheory.covarianceBilin
              (μ : Measure (EuclideanSpace ℝ n))
              (ContinuousLinearMap.adjoint L a)
              (ContinuousLinearMap.adjoint L b) =
              inner ℝ
                ((Covariance.operator (μ : Measure (EuclideanSpace ℝ n)))
                  (ContinuousLinearMap.adjoint L a))
                (ContinuousLinearMap.adjoint L b) :=
            (Covariance.operator_inner
              (μ : Measure (EuclideanSpace ℝ n))
              (ContinuousLinearMap.adjoint L a)
              (ContinuousLinearMap.adjoint L b)).symm
          _ = inner ℝ
                (ContinuousLinearMap.adjoint L a)
                (ContinuousLinearMap.adjoint L b) := by
            rw [hμ.covariance_identity]
            simp
      _ = inner ℝ (L a) (L b) := by
        rw [hLadj]
      _ = inner ℝ a
            ((ContinuousLinearMap.adjoint L) (L b)) := by
        symm
        exact ContinuousLinearMap.adjoint_inner_right L a (L b)
      _ = inner ℝ a (L (L b)) := by
        rw [hLadj]
      _ = inner ℝ a
            ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) AbsM) b) := by
        rw [hLL]

end FunctionalInequalities.KLS
