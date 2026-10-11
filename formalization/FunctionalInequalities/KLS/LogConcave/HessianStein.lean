import FunctionalInequalities.Probability.Stein.HessianKernel
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.KLS.LogConcave.Stein

/-!
# The Hessian–Stein kernel of a normalized convex potential

Letwin, arXiv:2607.24164v1, Lemma 2.7, analytic part for a given potential. Let `φ` be smooth and
convex on `ℝⁿ` with `e^{-φ}` a probability density, `ν = e^{-φ}dx`, and `(∇φ)_* ν = μ` isotropic.
Then the entries of the Hessian matrix of `φ` are `ν`-integrable, and for a measurable left inverse `Ψ`
of `∇φ` the Hessian kernel `τ = ∇²φ ∘ Ψ` is a Stein kernel of `μ` (Definition 2.6) with integrable entries, a.e. symmetry,
positive semidefiniteness and mean `Id`; gradient injectivity (an explicit geometric prerequisite)
produces such a `Ψ`. The existence of the moment-map potential for an arbitrary law, strict positive
definiteness and the Hilbert–Schmidt `L²` bound (the rest of Lemma 2.7 and Theorem 2.5) remain
open. Proof bodies: Codex route (bundle `Hessian-Stein-Kernel`, independently accepted);
statements and placement: Claude.
-/

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.KLS.LogConcave

/-- For a smooth convex normalized `φ` with `(∇φ)_* ν = μ` isotropic, the Hessian entries are `ν`-integrable. -/
theorem integrable_hessianMatrix_of_isotropic_map {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcv : ConvexOn ℝ Set.univ φ)
    (hnorm : ∫ y, Real.exp (-φ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-φ))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hiso : KLS.Isotropic μ) (i j : Fin n) :
    Integrable (fun y => Probability.Stein.hessianMatrix φ y i j) (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hexp : Integrable (fun y => Real.exp (-φ y)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hgrad := Probability.Stein.memLp_two_gradient_of_map_eq
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) ν μ hmap hiso.memLp_two
  rw [hν] at hgrad ⊢
  exact Analysis.BakryEmery.integrable_hessian_tilted_of_convexOn φ hφ hcv hexp hnorm hgrad _ _

/-- The entries `τ_{ij} = (∇²φ ∘ Ψ)_{ij}` of the Hessian kernel are `μ`-integrable. -/
theorem integrable_hessianKernel_of_isotropic_map {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcv : ConvexOn ℝ Set.univ φ)
    (hnorm : ∫ y, Real.exp (-φ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-φ))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hiso : KLS.Isotropic μ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y) (i j : Fin n) :
    Integrable (fun x => Probability.Stein.hessianKernel φ Ψ x i j) (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hg : Measurable (gradient φ) :=
    (continuous_gradient (hφ.of_le (WithTop.coe_le_coe.mpr le_top))).measurable
  have hk := Probability.Stein.hessianKernel_entries_measurable (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hΨ i j
  rw [← hmap]
  apply (integrable_map_measure hk.aestronglyMeasurable hg.aemeasurable).mpr
  have hH := integrable_hessianMatrix_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso i j
  apply hH.congr
  filter_upwards [Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hInv] with y hy
  exact (congrArg (fun T => T i j) hy).symm

/-- **Compact-test Stein identity for the Hessian kernel**: `∫ x_i f dμ = ∫ (τ ∇f)_i dμ` for `f ∈ C_c^∞`
(A.3 applied to the bounded pullback `f ∘ ∇φ`, whose compact support is not assumed). -/
theorem hessianKernel_compact_identity {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcv : ConvexOn ℝ Set.univ φ)
    (hnorm : ∫ y, Real.exp (-φ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-φ))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hiso : KLS.Isotropic μ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (i : Fin n) :
    (∫ x, x i * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ x) (gradient f x) i ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgsmooth : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hg := (continuous_gradient hφ1).measurable
  let F : EuclideanSpace ℝ (Fin n) → ℝ := f ∘ gradient φ
  have hF : ContDiff ℝ ∞ F := hf.comp hgsmooth
  obtain ⟨M0, hM0⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨M1, hM1⟩ := (continuous_gradient hf1).bounded_above_of_compact_support
    (hasCompactSupport_gradient hfc)
  have hgradν := Probability.Stein.memLp_two_gradient_of_map_eq hφ1 ν μ hmap hiso.memLp_two
  have hφi : Integrable (fun y => fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i)) (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh := hgradν.inner_const (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)
    simpa only [inner_gradient_left] using hh.integrable one_le_two
  have hFbd : ∀ y, ‖F y‖ ≤ M0 := fun y => hM0 (gradient φ y)
  have hFi : Integrable (fun y => F y * fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i)) (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
    hφi.bdd_mul hF.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hFbd)
  have hFint : Integrable F (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_const M0).mono' hF.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hFbd)
  have hdfF : Integrable (fun y => fderiv ℝ F y (EuclideanSpace.basisFun (Fin n) ℝ i)) (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hterms (j : Fin n) : Integrable (fun y => Probability.Stein.hessianMatrix φ y i j * gradient f (gradient φ y) j)
        (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hh := integrable_hessianMatrix_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso i j
      have hb : ∀ y, ‖gradient f (gradient φ y) j‖ ≤ M1 := fun y =>
        (PiLp.norm_apply_le _ j).trans (hM1 (gradient φ y))
      have hcont : Continuous (fun y => gradient f (gradient φ y) j) :=
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp ((continuous_gradient hf1).comp (continuous_gradient hφ1))
      exact hh.mul_bdd hcont.aestronglyMeasurable (Filter.Eventually.of_forall hb)
    have hh := integrable_finsetSum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hterms j)
    apply hh.congr
    exact Filter.Eventually.of_forall fun y => (Probability.Stein.chain_coordinate hφ2 hf1 y i).symm
  have hexp : Integrable (fun y => Real.exp (-φ y)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  have hdfLaw : Integrable (fun y => fderiv ℝ F y (EuclideanSpace.basisFun (Fin n) ℝ i) * (1 : ℝ))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) := by rw [← hν]; simpa only [mul_one] using hdfF
  have hprodLaw : Integrable (fun y => F y * (1 : ℝ) * fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) := by rw [← hν]; simpa only [mul_one] using hFi
  have hFLaw : Integrable (fun y => F y * (1 : ℝ)) ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) := by
    rw [← hν]; simpa only [mul_one] using hFint
  have hA3 := integral_fderiv_mul_tilted_eq (volume : Measure (EuclideanSpace ℝ (Fin n))) φ F (fun _ => 1)
    (EuclideanSpace.basisFun (Fin n) ℝ i) hφ hF contDiff_const hexp hnorm hdfLaw (by simp) hprodLaw hFLaw
  rw [← hν] at hA3
  have hDir (y : EuclideanSpace ℝ (Fin n)) : fderiv ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i) = gradient φ y i := by
    rw [← inner_gradient_left]
    exact EuclideanSpace.inner_basisFun_real (Fin n) _ i
  have hA3' : (∫ y, fderiv ℝ F y (EuclideanSpace.basisFun (Fin n) ℝ i) ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ y, gradient φ y i * f (gradient φ y) ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [mul_one, one_mul, fderiv_const_apply, zero_apply, sub_zero, F, Function.comp_def,
      hDir, mul_comm] using hA3
  have hLmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i * f x) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable.mul hf.continuous.measurable
  have hRmeas : Measurable (fun x => Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ x) (gradient f x) i) := by
    change Measurable (fun x => ∑ j, Probability.Stein.hessianKernel φ Ψ x i j * gradient f x j)
    exact Finset.measurable_sum _ (fun j _ => (Probability.Stein.hessianKernel_entries_measurable hφ2 hΨ i j).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp (continuous_gradient hf1)).measurable)
  rw [← hmap, integral_map hg.aemeasurable hLmeas.aestronglyMeasurable,
    integral_map hg.aemeasurable hRmeas.aestronglyMeasurable]
  have hR : (fun y => Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ (gradient φ y)) (gradient f (gradient φ y)) i) =ᵐ[
      (ν : Measure (EuclideanSpace ℝ (Fin n)))] fun y => fderiv ℝ F y (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    filter_upwards [Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hInv] with y hy
    rw [hy]
    exact (Probability.Stein.chain_coordinate hφ2 hf1 y i).symm
  rw [integral_congr_ae hR]
  exact hA3'.symm

/-- `τ = ∇²φ ∘ Ψ` is a Stein kernel of `μ` (Definition 2.6). -/
theorem hessianKernel_isSteinKernel {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcv : ConvexOn ℝ Set.univ φ)
    (hnorm : ∫ y, Real.exp (-φ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-φ))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hiso : KLS.Isotropic μ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y) :
    Probability.Stein.IsSteinKernel μ (Probability.Stein.hessianKernel φ Ψ) where
  integrable_id := hiso.memLp_two.integrable one_le_two
  mean_zero := hiso.mean_zero
  measurable_entries := Probability.Stein.hessianKernel_entries_measurable (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hΨ
  local_entries := fun i j => (integrable_hessianKernel_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hInv i j).locallyIntegrable
  compact_identity := hessianKernel_compact_identity φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hInv

/-- `∫ τ dμ = Id` (mean Hessian identity). -/
theorem integral_hessianKernel_eq_one {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcv : ConvexOn ℝ Set.univ φ)
    (hnorm : ∫ y, Real.exp (-φ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-φ))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hiso : KLS.Isotropic μ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y) (i j : Fin n) :
    (∫ x, Probability.Stein.hessianKernel φ Ψ x i j ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) = (1 : Probability.Stein.KernelMatrix n) i j := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg := (continuous_gradient hφ1).measurable
  have hk := Probability.Stein.hessianKernel_entries_measurable (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hΨ i j
  rw [← hmap, integral_map hg.aemeasurable hk.aestronglyMeasurable]
  have hcoup : (fun y => Probability.Stein.hessianKernel φ Ψ (gradient φ y) i j) =ᵐ[(ν : Measure (EuclideanSpace ℝ (Fin n)))]
      fun y => Probability.Stein.hessianMatrix φ y i j := by
    filter_upwards [Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hInv] with y hy
    exact congrArg (fun T => T i j) hy
  rw [integral_congr_ae hcoup]
  have hEq : ν.map hg.aemeasurable = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa only [ProbabilityMeasure.toMeasure_map] using hmap
  have hI : KLS.Isotropic (ν.map hg.aemeasurable) := by rw [hEq]; exact hiso
  have h := integral_hessian_eq_inner_of_isotropic_map φ hφ hcv hnorm ν hν hI
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
  have he : ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ j⟫ = (1 : Probability.Stein.KernelMatrix n) i j := by
    rw [EuclideanSpace.basisFun_inner]
    change (EuclideanSpace.basisFun (Fin n) ℝ j) i = (if i = j then (1 : ℝ) else 0)
    rw [EuclideanSpace.basisFun_apply]
    change (PiLp.single 2 j (1 : ℝ) : EuclideanSpace ℝ (Fin n)) i = _
    simp only [PiLp.single_apply]
  rw [he] at h
  exact h

/-- **Letwin Lemma 2.7, analytic part for a given potential**: if `φ` is smooth, convex, normalized,
`ν = e^{-φ}dx`, `(∇φ)_* ν = μ` is isotropic and `∇φ` is injective (explicit prerequisite), then with a
measurable left inverse `Ψ` the Hessian kernel `∇²φ ∘ Ψ` is a symmetric, positive semidefinite, integrable
Stein kernel of `μ` with mean `Id` and coupling `τ(∇φ y) = ∇²φ(y)`. The moment map `φ` for an arbitrary law, strict
positive definiteness and `|τ|_HS ∈ L²` are not provided. -/
theorem exists_hessianSteinKernel_of_injective_gradient {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcv : ConvexOn ℝ Set.univ φ)
    (hnorm : ∫ y, Real.exp (-φ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : (ν : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-φ))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hiso : KLS.Isotropic μ) (hInj : Function.Injective (gradient φ)) :
    ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) ∧
      Probability.Stein.IsSteinKernel μ (Probability.Stein.hessianKernel φ Ψ) ∧
      Probability.Stein.SymmetricAE μ (Probability.Stein.hessianKernel φ Ψ) ∧
      (∀ i j, Integrable (fun x => Probability.Stein.hessianKernel φ Ψ x i j) (μ : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Probability.Stein.hessianKernel φ Ψ (gradient φ y) = Probability.Stein.hessianMatrix φ y) ∧
      (∀ x v, 0 ≤ ⟪v, Probability.Stein.action (Probability.Stein.hessianKernel φ Ψ x) v⟫) ∧
      (∀ i j, (∫ x, Probability.Stein.hessianKernel φ Ψ x i j ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        (1 : Probability.Stein.KernelMatrix n) i j) := by
  obtain ⟨Ψ, hΨ, hi⟩ := Probability.Stein.exists_measurable_leftInverse_gradient_of_injective
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hInj
  have hiAE : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y := Filter.Eventually.of_forall hi
  refine ⟨Ψ, hΨ, hi, hessianKernel_isSteinKernel φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hiAE,
    Probability.Stein.hessianKernel_symmetricAE (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) Ψ μ,
    fun i j => integrable_hessianKernel_of_isotropic_map φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hiAE i j,
    Probability.Stein.hessianKernel_comp_gradient φ Ψ ν hiAE,
    fun x v => Probability.Stein.hessianKernel_quadratic_nonneg (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) hcv Ψ x v,
    fun i j => integral_hessianKernel_eq_one φ hφ hcv hnorm ν μ hν hmap hiso Ψ hΨ hiAE i j⟩

end FunctionalInequalities.KLS.LogConcave
