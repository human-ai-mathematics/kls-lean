import FunctionalInequalities.Probability.Stein.Kernel
import FunctionalInequalities.Analysis.BakryEmery.Calculus
import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
import FunctionalInequalities.Energy.Euclidean.WeakDerivative
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import FunctionalInequalities.Analysis.WeakDerivative

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


/-! Weak-route support for Letwin arXiv:2607.24164v1. Proof body: the independently
checked existing L-N11e-third-derivative-symmetry candidate; placement and acceptance: Codex closeout. -/

section WeakThirdDerivativeSymmetry

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma HasWeakDerivAlong.congr_left
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f f' g : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v) (hff' : f =ᵐ[(volume : Measure E)] f') :
    HasWeakDerivAlong f' g v := by
  refine ⟨h.1.congr hff', h.2.1, ?_⟩
  intro ψ hψ hψc
  have hp :
      (fun x => f' x * fderiv ℝ ψ x v) =ᵐ[(volume : Measure E)]
        (fun x => f x * fderiv ℝ ψ x v) := by
    filter_upwards [hff'] with x hx
    rw [hx]
  rw [integral_congr_ae hp]
  exact h.2.2 ψ hψ hψc

private lemma HasWeakDerivAlong.congr_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {f g g' : E → ℝ} {v : E}
    (h : HasWeakDerivAlong f g v) (hgg' : g =ᵐ[(volume : Measure E)] g') :
    HasWeakDerivAlong f g' v := by
  refine ⟨h.1, h.2.1.congr hgg', ?_⟩
  intro ψ hψ hψc
  have hi := h.2.2 ψ hψ hψc
  have hp :
      (fun x => g x * ψ x) =ᵐ[(volume : Measure E)]
        (fun x => g' x * ψ x) := by
    filter_upwards [hgg'] with x hx
    rw [hx]
  rw [integral_congr_ae hp] at hi
  exact hi

private lemma differentiableAt_fderiv_of_differentiableAt_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx

private lemma hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'

private lemma hessian_symm_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hu : ContDiff ℝ 1 u)
    (hx : DifferentiableAt ℝ (gradient u) x) :
    hessianMatrix u x i j = hessianMatrix u x j i := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hs :=
    second_derivative_symmetric
      (fun y => (hu.differentiable (by simp) y).hasFDerivAt)
      hfd.hasFDerivAt
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using hs

private lemma fderiv_apply_apply_symm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ φ y w) x v := by
  have hφ2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfd' : ContDiff ℝ 1 (fderiv ℝ φ) :=
    hφ2.fderiv_right (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hfd'.differentiable (by simp)).differentiableAt
  have hcv :
      DifferentiableAt ℝ (fun _ : E => v) x :=
    (differentiable_const v : Differentiable ℝ (fun _ : E => v)).differentiableAt
  have hcw :
      DifferentiableAt ℝ (fun _ : E => w) x :=
    (differentiable_const w : Differentiable ℝ (fun _ : E => w)).differentiableAt
  have hv := fderiv_clm_apply hfd hcv
  have hw := fderiv_clm_apply hfd hcw
  have hv' := congrArg (fun L : E →L[ℝ] ℝ => L w) hv
  have hw' := congrArg (fun L : E →L[ℝ] ℝ => L v) hw
  simp at hv' hw'
  have hs :=
    second_derivative_symmetric
      (fun y => (hφ2.differentiable (by norm_num) y).hasFDerivAt)
      hfd.hasFDerivAt w v
  calc
    fderiv ℝ (fun y => fderiv ℝ φ y v) x w =
        ((fderiv ℝ (fderiv ℝ φ) x) w) v := hv'
    _ = ((fderiv ℝ (fderiv ℝ φ) x) v) w := hs
    _ = fderiv ℝ (fun y => fderiv ℝ φ y w) x v := hw'.symm

private lemma contDiff_fderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (v : E) :
    ContDiff ℝ 1 (fun x => fderiv ℝ φ x v) := by
  have hφ2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfd : ContDiff ℝ 1 (fderiv ℝ φ) :=
    hφ2.fderiv_right (by norm_num)
  exact hfd.clm_apply
    (contDiff_const : ContDiff ℝ 1 (fun _ : E => v))

/-- **Symmetry of the weak third derivative** (weak Letwin route, N11, task N11e): for `u ∈ C¹` with Lipschitz gradient, if
`T · k i j` is the weak derivative of the Hessian entry `Hᵢⱼ` along `eₖ` for all indices, then a.e. `Tₖᵢⱼ = Tᵢₖⱼ` and
`Tₖᵢⱼ = Tₖⱼᵢ`. -/
theorem ae_weak_third_derivative_symm {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hT : ∀ k i j, HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i := by
  let e : Fin n → EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.basisFun (Fin n) ℝ

  have hcoord (i j : Fin n) :
      (fun x => fderiv ℝ (fun y => fderiv ℝ u y (e j)) x (e i)) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => hessianMatrix u x i j) := by
    filter_upwards [hG.ae_differentiableAt] with x hx
    exact hessian_coord_of_gradient_diff hx

  have hHsym (i j : Fin n) :
      (fun x => hessianMatrix u x i j) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => hessianMatrix u x j i) := by
    filter_upwards [hG.ae_differentiableAt] with x hx
    exact hessian_symm_of_gradient_diff hu hx

  have hgi (j : Fin n) :
      LipschitzWith (‖(innerSL ℝ) (e j)‖₊ * G)
        (fun x => fderiv ℝ u x (e j)) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) (e j)).lipschitz.comp hG)

  have hweak (i j : Fin n) :
      HasWeakDerivAlong (fun x => fderiv ℝ u x (e j))
        (fun x => hessianMatrix u x i j) (e i) := by
    exact HasWeakDerivAlong.congr_right
      (hasWeakDerivAlong_of_lipschitz (hgi j) (e i)) (hcoord i j)

  have hfirst (k i j : Fin n) :
      (fun x => T x k i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => T x k j i) := by
    have h' := HasWeakDerivAlong.congr_left (hT k j i) (hHsym j i)
    exact (hT k i j).ae_eq h'

  have hcomm (k i j : Fin n) :
      (fun x => T x k i j) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
        (fun x => T x i k j) := by
    apply ae_eq_of_integral_contDiff_smul_eq (hT k i j).2.1 (hT i k j).2.1
    intro φ hφ hφc
    have hφ1 : ContDiff ℝ 1 φ :=
      hφ.of_le (WithTop.coe_le_coe.mpr le_top)
    have hφk : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (e k)) :=
      contDiff_fderiv_apply hφ (e k)
    have hφi : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (e i)) :=
      contDiff_fderiv_apply hφ (e i)
    have hφkc : HasCompactSupport (fun x => fderiv ℝ φ x (e k)) :=
      hφc.fderiv_apply ℝ (e k)
    have hφic : HasCompactSupport (fun x => fderiv ℝ φ x (e i)) :=
      hφc.fderiv_apply ℝ (e i)
    have e₁ := (hweak i j).2.2
      (fun x => fderiv ℝ φ x (e k)) hφk hφkc
    have e₂ := (hT k i j).2.2 φ hφ1 hφc
    have e₃ := (hweak k j).2.2
      (fun x => fderiv ℝ φ x (e i)) hφi hφic
    have e₄ := (hT i k j).2.2 φ hφ1 hφc
    have hleft :
        (∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            -(∫ x, hessianMatrix u x i j *
              fderiv ℝ φ x (e k) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
                linarith [e₂]
        _ = ∫ x, fderiv ℝ u x (e j) *
              fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
                linarith [e₁]
    have hright :
        (∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            -(∫ x, hessianMatrix u x k j *
              fderiv ℝ φ x (e i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
                linarith [e₄]
        _ = ∫ x, fderiv ℝ u x (e j) *
              fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
                linarith [e₃]
    have hsecond :
        (fun x => fderiv ℝ u x (e j) *
          fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)) =
          (fun x => fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)) := by
      funext x
      rw [fderiv_apply_apply_symm hφ x (e k) (e i)]
    have hmul :
        (∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      calc
        ∫ x, T x k i j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
            ∫ x, fderiv ℝ u x (e j) *
              fderiv ℝ (fun y => fderiv ℝ φ y (e k)) x (e i)
                ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hleft
        _ = ∫ x, fderiv ℝ u x (e j) *
            fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e k)
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
            rw [hsecond]
        _ = ∫ x, T x i k j * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
          hright.symm
    simpa only [smul_eq_mul, mul_comm] using hmul

  apply ae_all_iff.2
  intro k
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro j
  filter_upwards [hcomm k i j, hfirst k i j] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

end FunctionalInequalities.Analysis

end WeakThirdDerivativeSymmetry

section GradientDerivativeIdentification

open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Probability.Stein

private lemma hessianMatrix_entry_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) (i j : Fin n) :
    hessianMatrix u x i j =
      ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [hessian_symm_of_gradient_diff hu hx,
    ← hessian_coord_of_gradient_diff hx]
  have heq :
      (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        fun y => ⟪gradient u y, EuclideanSpace.basisFun (Fin n) ℝ i⟫ := by
    funext y
    exact inner_gradient_left.symm
  rw [heq, fderiv_inner_apply ℝ hx
    (differentiableAt_const (EuclideanSpace.basisFun (Fin n) ℝ i))]
  simp [real_inner_comm]

/-- At a point where the gradient of a `C¹` potential is differentiable, its derivative
is represented by the coordinate Hessian. This pointwise bridge requires no `C²` hypothesis
and supports the weak regular moment-potential package for Letwin's Lemma 2.2. -/
theorem hessianMatrix_toEuclideanLin_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    Matrix.toEuclideanLin (hessianMatrix u x) =
      (fderiv ℝ (gradient u) x).toLinearMap := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  rw [LinearMap.toMatrix_toLin]
  ext i j
  rw [LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  exact hessianMatrix_entry_of_differentiableAt_gradient hu hx i j

/-- The coordinate Hessian of a `C¹` potential is symmetric at every differentiability
point of its gradient, including the zero-dimensional case. -/
theorem hessianMatrix_isHermitian_of_differentiableAt_gradient
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x) :
    (hessianMatrix u x).IsHermitian := by
  change (hessianMatrix u x).conjTranspose = hessianMatrix u x
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact hessian_symm_of_gradient_diff hu hx

end FunctionalInequalities.Probability.Stein

end GradientDerivativeIdentification

noncomputable section HessianEntryBounds

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Probability.Stein

private def n10_matrix {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun r s =>
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      (L (EuclideanSpace.basisFun (Fin n) ℝ r))
      (EuclideanSpace.basisFun (Fin n) ℝ s)

private lemma n10_hessian {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    hessianMatrix u x = n10_matrix (fderiv ℝ (gradient u) x) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  have he : fderiv ℝ u = T ∘ gradient u :=
    funext fun y => (T.apply_symm_apply (fderiv ℝ u y)).symm
  have hd :
      fderiv ℝ (fderiv ℝ u) x =
        T.toContinuousLinearMap.comp (fderiv ℝ (gradient u) x) :=
    (congrArg (fun f => fderiv ℝ f x) he).trans T.comp_fderiv
  ext r s
  change
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ r)
        (EuclideanSpace.basisFun (Fin n) ℝ s) =
      T (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ r))
        (EuclideanSpace.basisFun (Fin n) ℝ s)
  rw [hd]
  rfl

private lemma n11b_continuous_hessian_entry {n : ℕ} (i j : Fin n) :
    Continuous
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
        n10_matrix L i j) := by
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv
  exact
    (T.continuous.comp (continuous_id.clm_apply continuous_const)).clm_apply
      continuous_const

/-- Measurability of the total coordinate Hessian, without smoothness premises. -/
theorem measurable_hessianMatrix_entry {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (i j : Fin n) :
    Measurable (fun x => hessianMatrix u x i j) := by
  simpa only [n10_hessian, Function.comp_def] using
    (n11b_continuous_hessian_entry i j).measurable.comp
      (measurable_fderiv ℝ (gradient u))

/-- The total coordinate Hessian is bounded by the gradient Lipschitz constant;
this does not assert C2 regularity or classical differentiability everywhere. -/
theorem norm_hessianMatrix_entry_le_of_lipschitz_gradient {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ‖hessianMatrix u x i j‖ ≤ (G : ℝ) := by
  let L := fderiv ℝ (gradient u) x
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let T := InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))
  rw [n10_hessian]
  change ‖T (L (e i)) (e j)‖ ≤ (G : ℝ)
  calc
    ‖T (L (e i)) (e j)‖ ≤ ‖T (L (e i))‖ * ‖e j‖ :=
      (T (L (e i))).le_opNorm (e j)
    _ = ‖L (e i)‖ := by
      rw [T.norm_map, e.norm_eq_one j, mul_one]
    _ ≤ ‖L‖ * ‖e i‖ := L.le_opNorm (e i)
    _ = ‖L‖ := by
      rw [e.norm_eq_one i, mul_one]
    _ ≤ (G : ℝ) := norm_fderiv_le_of_lipschitz ℝ hG

end FunctionalInequalities.Probability.Stein

end HessianEntryBounds


noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
namespace FunctionalInequalities.Probability.Stein

/-- The total coordinate Hessian entry is L2 on every compact set, from the
actual Lipschitz-gradient bound. No differentiability or PDE premise is added. -/
theorem memLp_hessianMatrix_entry_of_isCompact {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) :
    MemLp (fun x => hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  exact MemLp.of_bound
    (measurable_hessianMatrix_entry u i j).aestronglyMeasurable
    (G : ℝ)
    (Filter.Eventually.of_forall fun x =>
      norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)

/-- Multiplying a total Hessian entry by a continuous compact cutoff produces
an actual global L2 function for the existing difference-quotient criterion. -/
theorem memLp_cutoff_mul_hessianMatrix_entry {n : ℕ}
    {u χ : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x * hessianMatrix u x i j) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hK : IsCompact (tsupport χ) := hχc
  have hKm : MeasurableSet (tsupport χ) :=
    (isClosed_tsupport χ).measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχ.continuousOn
  let : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hlocal : MemLp (fun x => χ x * hessianMatrix u x i j) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (tsupport χ)) := by
    apply MemLp.of_bound
      (hχ.measurable.mul
        (measurable_hessianMatrix_entry u i j)).aestronglyMeasurable
      (C * (G : ℝ))
    exact (ae_restrict_mem hKm).mono fun x hx => by
      calc
        ‖χ x * hessianMatrix u x i j‖ =
            ‖χ x‖ * ‖hessianMatrix u x i j‖ := norm_mul _ _
        _ ≤ ‖χ x‖ * (G : ℝ) :=
          mul_le_mul_of_nonneg_left
            (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
            (norm_nonneg _)
        _ ≤ C * (G : ℝ) :=
          mul_le_mul_of_nonneg_right (hC x hx) (NNReal.coe_nonneg G)
  have heq :
      (tsupport χ).indicator (fun x => χ x * hessianMatrix u x i j) =
        (fun x => χ x * hessianMatrix u x i j) := by
    funext x
    by_cases hx : x ∈ tsupport χ
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,
        image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [← heq]
  exact (memLp_indicator_iff_restrict hKm).mpr hlocal

end FunctionalInequalities.Probability.Stein
