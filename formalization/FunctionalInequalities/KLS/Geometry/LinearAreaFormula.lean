import FunctionalInequalities.Analysis.Vector.Jacobian
import FunctionalInequalities.Analysis.Graph.Implicit
import FunctionalInequalities.KLS.Geometry.SmoothDomain.Basic

/-! # The linear area formula in the normalized convention, and affine fibres

Step one of the codimension-`m` coarea program.  Mathlib proves the **linear area formula**
`μH[n] (L '' s) = normDet L * μH[n] s` for the raw Hausdorff measure; every measure in this
repository is instead `KLS.hausdorffNormalized`, the classical `ω_d (diam/2)^d` normalization.
This module carries the formula across that normalization and draws the consequence the
codimension-`m` coarea formula needs about its fibres.

The fibres of a linear map are affine translates of its kernel, and the point of
`hausdorffNormalized_image_affine` and `hausdorffNormalized_fiber` is that the `k`-dimensional
normalized Hausdorff measure of such a translate is **exactly Lebesgue measure on the kernel**,
with no constant left over: a linear isometric embedding has unit norm determinant, translation is
an isometry, and the top-dimensional normalized Hausdorff measure of a space is its own volume.

**No coarea formula is proved here**, and no `C¹` area formula either: everything below is about
linear maps and affine subspaces.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace FunctionalInequalities.KLS

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] in
/-- **Linear area formula, normalized convention.**  Both sides pick up the same normalization
constant `ω_k / 2^k`, so it cancels and the norm determinant is the exact volume factor. -/
theorem hausdorffNormalized_image_linearMap (L : H →ₗ[ℝ] V) (s : Set H) :
    hausdorffNormalized V (Module.finrank ℝ H) (L '' s)
      = ENNReal.ofReal (LinearMap.normDet L) * hausdorffNormalized H (Module.finrank ℝ H) s := by
  rw [hausdorffNormalized, hausdorffNormalized, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, LinearMap.hausdorffMeasure_image]
  ring

section IsometricJacobians

omit [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V] [BorelSpace V]
/-- The adjoint of a linear isometric embedding is a left inverse. -/
theorem adjoint_apply_linearIsometry (ι : H →ₗᵢ[ℝ] V) (x : H) :
    LinearMap.adjoint (ι : H →ₗ[ℝ] V) (ι x) = x := by
  refine ext_inner_right ℝ fun y => ?_
  rw [LinearMap.adjoint_inner_left]
  exact ι.inner_map_map x y

/-- A linear isometric embedding has unit norm determinant: it changes no `k`-volume. -/
theorem normDet_linearIsometry (ι : H →ₗᵢ[ℝ] V) : LinearMap.normDet (ι : H →ₗ[ℝ] V) = 1 := by
  have hcomp : LinearMap.adjoint (ι : H →ₗ[ℝ] V) ∘ₗ (ι : H →ₗ[ℝ] V) = LinearMap.id := by
    ext x
    exact adjoint_apply_linearIsometry ι x
  have hsq : LinearMap.normDet (ι : H →ₗ[ℝ] V) ^ 2 = 1 := by
    have h := LinearMap.normDet_sq (ι : H →ₗ[ℝ] V)
    rw [hcomp, LinearMap.det_id] at h
    exact_mod_cast h
  have hnn := LinearMap.normDet_nonneg (ι : H →ₗ[ℝ] V)
  nlinarith

end IsometricJacobians

/-- An isometrically embedded set keeps its normalized `k`-dimensional measure. -/
theorem hausdorffNormalized_image_linearIsometry (ι : H →ₗᵢ[ℝ] V) (s : Set H) :
    hausdorffNormalized V (Module.finrank ℝ H) (ι '' s)
      = hausdorffNormalized H (Module.finrank ℝ H) s := by
  rw [show ((ι : H → V) '' s) = ((ι : H →ₗ[ℝ] V) '' s) from rfl,
    hausdorffNormalized_image_linearMap, normDet_linearIsometry, ENNReal.ofReal_one, one_mul]

/-- **Affine slices carry Lebesgue measure.**  The normalized `k`-dimensional Hausdorff measure of
an isometrically embedded, translated set is the Lebesgue measure of the parameter set, with no
residual constant.  `k = finrank ℝ H` is the dimension of the slice. -/
theorem hausdorffNormalized_image_affine (x₀ : V) (ι : H →ₗᵢ[ℝ] V) (s : Set H) :
    hausdorffNormalized V (Module.finrank ℝ H) ((fun y => x₀ + ι y) '' s)
      = (volume : Measure H) s := by
  have himg : ((fun y => x₀ + ι y) '' s) = (fun x : V => x₀ + x) '' ((ι : H → V) '' s) := by
    rw [Set.image_image]
  rw [himg, Analysis.hausdorffNormalized_image_add_left, hausdorffNormalized_image_linearIsometry,
    hausdorffNormalized_finrank_eq_volume]

/-- **The fibres of a linear map.**  A translate of the kernel, measured in the dimension of the
kernel, carries exactly Lebesgue measure on the kernel.  This is the fibre bookkeeping of the
codimension-`m` coarea formula: with `L` surjective the kernel has dimension `n - m`, and the
right-hand integral of that formula is over these fibres. -/
theorem hausdorffNormalized_fiber {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (L : V →ₗ[ℝ] W) (x₀ : V) (s : Set (LinearMap.ker L)) :
    hausdorffNormalized V (Module.finrank ℝ (LinearMap.ker L))
        ((fun y : LinearMap.ker L => x₀ + (y : V)) '' s)
      = (volume : Measure (LinearMap.ker L)) s :=
  hausdorffNormalized_image_affine x₀ (LinearMap.ker L).subtypeₗᵢ s

end FunctionalInequalities.KLS
