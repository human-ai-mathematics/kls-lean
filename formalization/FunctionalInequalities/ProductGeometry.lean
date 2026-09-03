import FunctionalInequalities.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Geometry and admissible sections of a Hilbert product

The product norm is the L2 norm on `WithLp 2 (E × F)`. Integrability of sections is asserted
almost everywhere, as required by Fubini.
The coordinate inclusions preserve smoothness, and their gradients are the corresponding
components of the full Hilbert-product gradient.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Poincare

/-- The product law transported to the Hilbert product. -/
def prodMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) : Measure (WithLp 2 (E × F)) :=
  (μ.prod ν).map (WithLp.toLp 2)

instance prodMeasure_isProbabilityMeasure {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (prodMeasure μ ν) := by
  rw [prodMeasure]
  exact Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × F)).aemeasurable

section Geometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
theorem contDiff_section_left {f : WithLp 2 (E × F) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (y : F) :
    ContDiff ℝ ⊤ (fun x ↦ f (WithLp.toLp 2 (x, y))) :=
  hf.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.contDiff.comp (contDiff_prodMk_left y))

omit [CompleteSpace E] [CompleteSpace F] in
theorem contDiff_section_right {f : WithLp 2 (E × F) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (x : E) :
    ContDiff ℝ ⊤ (fun y ↦ f (WithLp.toLp 2 (x, y))) :=
  hf.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.contDiff.comp (contDiff_prodMk_right x))

theorem gradient_section_left {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    gradient (fun x ↦ f (WithLp.toLp 2 (x, y))) x =
      (gradient f (WithLp.toLp 2 (x, y))).fst := by
  set p : WithLp 2 (E × F) := WithLp.toLp 2 (x, y) with hp
  set incl : E →L[ℝ] WithLp 2 (E × F) :=
    (((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm :
        (E × F) →L[ℝ] WithLp 2 (E × F)).comp (ContinuousLinearMap.inl ℝ E F)) with hincl_def
  have hincl_apply : ∀ h : E, incl h = WithLp.toLp 2 (h, 0) := fun h ↦ rfl
  have hsec : HasFDerivAt (fun x : E ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F))) incl x := by
    have heq : (fun x : E ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F)))
        = fun x : E ↦ incl x + WithLp.toLp 2 ((0 : E), y) := by
      funext x'
      rw [hincl_apply, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
    rw [heq]
    exact incl.hasFDerivAt.add_const _
  have hcomp : HasFDerivAt (fun x : E ↦ f (WithLp.toLp 2 (x, y)))
      ((fderiv ℝ f p).comp incl) x := hf.hasFDerivAt.comp x hsec
  have hkey : (fderiv ℝ f p).comp incl
      = InnerProductSpace.toDual ℝ E ((gradient f p).fst) := by
    have hfd : fderiv ℝ f p
        = InnerProductSpace.toDual ℝ (WithLp 2 (E × F)) (gradient f p) := by
      rw [toDual_gradient]
    ext h
    rw [ContinuousLinearMap.comp_apply, hincl_apply, hfd, InnerProductSpace.toDual_apply_apply,
      InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply]
    simp
  have hgrad : HasGradientAt (fun x : E ↦ f (WithLp.toLp 2 (x, y)))
      ((gradient f p).fst) x := by
    rw [hasGradientAt_iff_hasFDerivAt, ← hkey]
    exact hcomp
  exact hgrad.gradient

theorem gradient_section_right {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    gradient (fun y ↦ f (WithLp.toLp 2 (x, y))) y =
      (gradient f (WithLp.toLp 2 (x, y))).snd := by
  set p : WithLp 2 (E × F) := WithLp.toLp 2 (x, y) with hp
  set incl : F →L[ℝ] WithLp 2 (E × F) :=
    (((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm :
        (E × F) →L[ℝ] WithLp 2 (E × F)).comp (ContinuousLinearMap.inr ℝ E F)) with hincl_def
  have hincl_apply : ∀ h : F, incl h = WithLp.toLp 2 (0, h) := fun h ↦ rfl
  have hsec : HasFDerivAt (fun y : F ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F))) incl y := by
    have heq : (fun y : F ↦ (WithLp.toLp 2 (x, y) : WithLp 2 (E × F)))
        = fun y : F ↦ incl y + WithLp.toLp 2 (x, (0 : F)) := by
      funext y'
      rw [hincl_apply, ← WithLp.toLp_add, Prod.mk_add_mk, zero_add, add_zero]
    rw [heq]
    exact incl.hasFDerivAt.add_const _
  have hcomp : HasFDerivAt (fun y : F ↦ f (WithLp.toLp 2 (x, y)))
      ((fderiv ℝ f p).comp incl) y := hf.hasFDerivAt.comp y hsec
  have hkey : (fderiv ℝ f p).comp incl
      = InnerProductSpace.toDual ℝ F ((gradient f p).snd) := by
    have hfd : fderiv ℝ f p
        = InnerProductSpace.toDual ℝ (WithLp 2 (E × F)) (gradient f p) := by
      rw [toDual_gradient]
    ext h
    rw [ContinuousLinearMap.comp_apply, hincl_apply, hfd, InnerProductSpace.toDual_apply_apply,
      InnerProductSpace.toDual_apply_apply, WithLp.prod_inner_apply]
    simp
  have hgrad : HasGradientAt (fun y : F ↦ f (WithLp.toLp 2 (x, y)))
      ((gradient f p).snd) y := by
    rw [hasGradientAt_iff_hasFDerivAt, ← hkey]
    exact hcomp
  exact hgrad.gradient

/-- The exact sum of squared partial gradients for the Hilbert product norm. -/
theorem norm_gradient_sq_prod {f : WithLp 2 (E × F) → ℝ} {x : E} {y : F}
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (x, y))) :
    ‖gradient f (WithLp.toLp 2 (x, y))‖ ^ 2 =
      ‖gradient (fun x ↦ f (WithLp.toLp 2 (x, y))) x‖ ^ 2 +
      ‖gradient (fun y ↦ f (WithLp.toLp 2 (x, y))) y‖ ^ 2 := by
  rw [gradient_section_left hf, gradient_section_right hf]
  exact WithLp.prod_norm_sq_eq_of_L2 _

end Geometry

end FunctionalInequalities.Poincare
