import FunctionalInequalities.Probability.Stein.Kernel
import FunctionalInequalities.Analysis.BakryEmery.Calculus
import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
import FunctionalInequalities.Energy.Euclidean.WeakDerivative
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The Hessian–Stein hessianKernel candidate of a potential

Letwin, arXiv:2607.24164v1, Lemma 2.7 (analytic support): for a potential `φ` on `ℝⁿ` and a map
`Ψ`, the hessianKernel candidate `τ = ∇²φ ∘ Ψ`. Generic facts: the coordinate chain rule for `f ∘ ∇φ`,
continuity and measurability of the entries, symmetry, positive semidefiniteness for convex `φ`,
the coupling `τ(∇φ y) = ∇²φ(y)` when `Ψ ∘ ∇φ = id` a.e., the second moment of `∇φ` from the
pushforward, and the measurable left inverse of an injective continuous gradient. The source
adapters (Stein identity, integrability, mean) are in `KLS/LogConcave/HessianStein.lean`. No
potential is constructed for an arbitrary law. Proof bodies: Codex route (bundle
`Hessian-Stein-Kernel`, independently accepted); statements and placement: Claude.
-/

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Probability.Stein

/-- The Hessian matrix `(∇²φ)_{ij}(y) = D²φ(y)(e_i, e_j)` of `φ` in the standard basis. -/
noncomputable def hessianMatrix {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) : Probability.Stein.KernelMatrix n :=
  fun i j => bilinearIteratedFDerivTwo ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- The coordinate Hessian matrix is the standard-basis entry matrix of the Hessian operator
`Analysis.BakryEmery.hessianOperator` (specialization bridge; the two objects keep their roles). -/
theorem hessianMatrix_eq_operatorEntry_hessianOperator {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    hessianMatrix φ y i j =
      Analysis.operatorEntry (EuclideanSpace.basisFun (Fin n) ℝ) (hessianOperator φ y) i j :=
  (operatorEntry_hessianOperator (EuclideanSpace.basisFun (Fin n) ℝ) hφ y i j).symm

/-- The Hessian–Stein hessianKernel candidate `τ = ∇²φ ∘ Ψ` for a given potential `φ` and inverse map `Ψ`
(Letwin Lemma 2.7: `Ψ = (∇φ)⁻¹`). -/
noncomputable def hessianKernel {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n := fun x => hessianMatrix φ (Ψ x)

/-- `D²φ(y)(u, v) = ⟪D(∇φ)(y) u, v⟫`. -/
theorem hessian_eq_inner_fderiv_gradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    (y u v : E) : bilinearIteratedFDerivTwo ℝ φ y u v = ⟪fderiv ℝ (gradient φ) y u, v⟫ := by
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_gradient hφ (by norm_num)
  have hfun : (fun x : E => fderiv ℝ φ x v) = fun x => ⟪gradient φ x, v⟫ := by
    funext x
    exact inner_gradient_left.symm
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hφ, hfun,
    fderiv_inner_apply ℝ (hg.differentiable one_ne_zero y) (differentiableAt_const v)]
  simp

/-- Chain rule in coordinates: `∂_i (f ∘ ∇φ)(y) = ∑_j (∇²φ)_{ij}(y) (∂_j f)(∇φ y)`. -/
theorem chain_coordinate {n : ℕ} {φ f : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hf : ContDiff ℝ 1 f) (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    fderiv ℝ (f ∘ gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ∑ j, hessianMatrix φ y i j * gradient f (gradient φ y) j := by
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_gradient hφ (by norm_num)
  rw [fderiv_comp y (hf.differentiable one_ne_zero _) (hg.differentiable one_ne_zero _)]
  change fderiv ℝ f (gradient φ y) (fderiv ℝ (gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i)) = _
  rw [← inner_gradient_left, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hcoord : fderiv ℝ (gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i) j = hessianMatrix φ y i j := by
    rw [hessianMatrix, hessian_eq_inner_fderiv_gradient hφ]
    exact (EuclideanSpace.inner_basisFun_real (Fin n) (fderiv ℝ (gradient φ) y (EuclideanSpace.basisFun (Fin n) ℝ i)) j).symm
  rw [hcoord]
  simp only [Real.inner_apply, mul_comm]

/-- Continuity of the Hessian entries. -/
theorem hessian_entry_continuous {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ) (i j : Fin n) :
    Continuous (fun y => hessianMatrix φ y i j) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  exact ((h1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const

/-- The Hessian kernel `∇²φ ∘ Ψ` (the Hessian matrix of `φ` composed with `Ψ`) is symmetric everywhere. -/
theorem hessianKernel_symmetricAE {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    Probability.Stein.SymmetricAE μ (hessianKernel φ Ψ) := by
  exact Filter.Eventually.of_forall fun x i j => bilinearIteratedFDerivTwo_symm hφ (Ψ x) _ _

/-- If `(∇φ)_* ν = μ` and `μ` has finite second moment, then `∇φ ∈ L²(ν)`. -/
theorem memLp_two_gradient_of_map_eq {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hμ2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (gradient φ) 2 (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hg : Measurable (gradient φ) := (continuous_gradient hφ).measurable
  have hh : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ((ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ)) := by
    rw [hmap]
    exact hμ2
  simpa only [Function.comp_def, id_eq] using
    (memLp_map_measure_iff continuous_id.aestronglyMeasurable hg.aemeasurable).mp hh

/-- With `Ψ ∘ ∇φ = id` a.e., the hessianKernel at `∇φ y` is the Hessian at `y`. -/
theorem hessianKernel_comp_gradient {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y) :
    ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), hessianKernel φ Ψ (gradient φ y) = hessianMatrix φ y := by
  filter_upwards [hInv] with y hy
  simp only [hessianKernel, hy]

theorem hessianKernel_entries_measurable {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hΨ : Measurable Ψ) (i j : Fin n) :
    Measurable (fun x => hessianKernel φ Ψ x i j) :=
  (hessian_entry_continuous hφ i j).measurable.comp hΨ

/-- `⟪v, (∇²φ)(y) w⟫ = D²φ(y)(v, w)`. -/
theorem inner_action_hessian {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (y v w : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Probability.Stein.action (hessianMatrix φ y) w⟫ = bilinearIteratedFDerivTwo ℝ φ y v w := by
  have hv : (∑ i, v i • EuclideanSpace.basisFun (Fin n) ℝ i) = v := by
    simpa only [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  have hw : (∑ j, w j • EuclideanSpace.basisFun (Fin n) ℝ j) = w := by
    simpa only [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w
  symm
  calc
    bilinearIteratedFDerivTwo ℝ φ y v w =
        bilinearIteratedFDerivTwo ℝ φ y (∑ i, v i • EuclideanSpace.basisFun (Fin n) ℝ i) (∑ j, w j • EuclideanSpace.basisFun (Fin n) ℝ j) := by rw [hv, hw]
    _ = ∑ i, ∑ j, v i * (hessianMatrix φ y i j * w j) := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hessianMatrix, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ⟪v, Probability.Stein.action (hessianMatrix φ y) w⟫ := by
      simp only [Probability.Stein.action, PiLp.inner_apply, Real.inner_apply,
        Matrix.mulVec, dotProduct, Finset.mul_sum]


/-- The Hessian kernel of a convex `φ` is positive semidefinite. -/
theorem hessianKernel_quadratic_nonneg {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hcv : ConvexOn ℝ Set.univ φ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪v, Probability.Stein.action (hessianKernel φ Ψ x) v⟫ := by
  rw [hessianKernel, inner_action_hessian]
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hφ hcv _ _

/-- `∇φ ∘ Ψ = id` holds `μ`-a.e. when `Ψ ∘ ∇φ = id` holds `ν`-a.e. and `(∇φ)_* ν = μ`. -/
theorem gradient_comp_inverse_ae {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient φ) = (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient φ y) = y) :
    ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), gradient φ (Ψ x) = x := by
  have hg := (continuous_gradient hφ).measurable
  rw [← hmap]
  apply (ae_map_iff (μ := (ν : Measure (EuclideanSpace ℝ (Fin n)))) (p := fun x => gradient φ (Ψ x) = x)
    hg.aemeasurable (by
      simpa only [Function.comp_def, id_eq] using measurableSet_eq_fun (hg.comp hΨ) measurable_id)).mpr
  filter_upwards [hInv] with y hy
  rw [hy]

/-- An injective continuous gradient has a measurable left inverse. -/
theorem exists_measurable_leftInverse_gradient_of_injective {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hInj : Function.Injective (gradient φ)) :
    ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Measurable Ψ ∧ Function.LeftInverse Ψ (gradient φ) := by
  have he : MeasurableEmbedding (gradient φ) := (continuous_gradient hφ).measurableEmbedding hInj
  exact ⟨he.invFun, he.measurable_invFun, he.leftInverse_invFun⟩

end FunctionalInequalities.Probability.Stein
