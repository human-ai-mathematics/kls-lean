import FunctionalInequalities.Analysis.VectorFiberIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the `m`-dimensional fibre change of variables

**What is proved.**  `lintegral_image_eq_lintegral_normDet_fderiv_mul` is the change of variables
between two inner product spaces of the **same dimension**, with `LinearMap.normDet` as the volume
factor; Mathlib proves only the self-map case, whose factor `|det f'|` does not typecheck between
different spaces.  `setLIntegral_image_vectorVerticalMap` is the codimension-`m` vertical
substitution, `setLIntegral_image_levelGraphMap` transports it to the ambient space along the
measure-preserving splitting, and `setLIntegral_coareaJacobian_levelGraphFamily` turns the ambient
coarea density into the graph area density that the proved area formula `B2` consumes.

**What is not proved.**  *No coarea formula.*  The fibre half — the **weighted** codimension-`m`
area formula, the analogue of `setLIntegral_image_graphMap` — and the Tonelli assembly and the
patching are still missing.  Nothing about the critical set, sharp Sard or the Cheeger comparisons
is touched.

**`m = 1` returns the proved scalar substitution.**  `codimension_one_verticalMap` below derives the
repository's already proved `Analysis.setLIntegral_image_verticalMap`, verbatim, from the new
codimension-`m` statement.

**The equal-dimension hypothesis is necessary**, and `equal_dimension_necessary` exhibits the
failure rather than asserting it: for `t ↦ t • e` from `ℝ` into the plane on the unit interval the
left-hand side is `0` and the right-hand side is `1`.
-/

noncomputable section

open Set MeasureTheory Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal RealInnerProductSpace ContDiff

namespace VectorFiberIntegralAudit

section Restatements

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **The change of variables, restated from scratch** for a `C¹` map, and discharged through named
arguments.  No integrability, finiteness or positivity of the weight is assumed. -/
theorem change_of_variables (h : finrank ℝ W = finrank ℝ K) {f : W → K} (hf : ContDiff ℝ 1 f)
    {s : Set W} (hs : MeasurableSet s) (hinj : InjOn f s) (g : K → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂(volume : Measure K)
      = ∫⁻ x in s, ENNReal.ofReal (LinearMap.normDet ((fderiv ℝ f x : W →ₗ[ℝ] K))) * g (f x)
          ∂(volume : Measure W) :=
  lintegral_image_eq_lintegral_normDet_fderiv_mul h hs
    (fun x _ => (hf.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt) hinj g

/-- **A linear isometry preserves measure**, as the change of variables must give. -/
theorem isometry_preserves_measure (ε : W →ₗᵢ[ℝ] K) (h : finrank ℝ W = finrank ℝ K)
    {s : Set W} (hs : MeasurableSet s) :
    (volume : Measure K) (ε '' s) = (volume : Measure W) s := by
  have hinj : InjOn (ε : W → K) s := fun x _ y _ hxy => ε.injective hxy
  have h1 := lintegral_image_eq_lintegral_normDet_fderiv_mul h hs
    (fun x _ => (ε.toContinuousLinearMap.hasFDerivAt).hasFDerivWithinAt) hinj (fun _ => 1)
  simpa [LinearIsometry.normDet_eq_one] using h1

/-- **No finiteness anywhere**: the whole parameter–level space is allowed. -/
theorem whole_space (hdim : finrank ℝ W = finrank ℝ K) {ψ : H × W → K} (hψ : ContDiff ℝ 1 ψ)
    (hi : InjOn (fun p : H × W => (p.1, ψ p)) Set.univ) {f : H × K → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q in (fun p : H × W => (p.1, ψ p)) '' Set.univ, f q ∂(volume : Measure (H × K))
      = ∫⁻ p, ENNReal.ofReal (LinearMap.normDet
            ((fderiv ℝ (fun t => ψ (p.1, t)) p.2 : W →ₗ[ℝ] K))) * f (p.1, ψ p)
          ∂(volume : Measure (H × W)) := by
  have h := setLIntegral_image_vectorVerticalMap hdim hψ MeasurableSet.univ hi hf
  simpa using h

/-- A **zero-dimensional fibre** is inside the statement: the vertical factor is `1`. -/
theorem zero_dimensional_fibre {ψ : H × EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)}
    (hψ : ContDiff ℝ 1 ψ) {A : Set (H × EuclideanSpace ℝ (Fin 0))} (hA : MeasurableSet A)
    (hi : InjOn (fun p : H × EuclideanSpace ℝ (Fin 0) => (p.1, ψ p)) A)
    {f : H × EuclideanSpace ℝ (Fin 0) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q in (fun p => (p.1, ψ p)) '' A, f q
        ∂(volume : Measure (H × EuclideanSpace ℝ (Fin 0)))
      = ∫⁻ p in A, f (p.1, ψ p) ∂(volume : Measure (H × EuclideanSpace ℝ (Fin 0))) := by
  have h := setLIntegral_image_vectorVerticalMap (rfl : finrank ℝ (EuclideanSpace ℝ (Fin 0))
    = finrank ℝ (EuclideanSpace ℝ (Fin 0))) hψ hA hi hf
  simpa [LinearMap.normDet_of_subsingleton] using h

end Restatements

/-! ### The codimension-one case is the proved scalar substitution -/

section CodimensionOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The one-dimensional volume factor is the absolute derivative. -/
theorem normDet_fderiv_eq_abs_deriv (g : ℝ → ℝ) (t : ℝ) :
    LinearMap.normDet ((fderiv ℝ g t : ℝ →ₗ[ℝ] ℝ)) = |deriv g t| := by
  rw [LinearMap.normDet_eq_abs_det, LinearMap.det_ring]
  rfl

/-- **`m = 1` is the proved scalar substitution**, reproduced verbatim from the codimension-`m`
statement.  This is `Analysis.setLIntegral_image_verticalMap`, whose own proof is the
one-dimensional Jacobian theorem; here it is a specialization. -/
theorem codimension_one_verticalMap {ψ : H × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    {A : Set (H × ℝ)} (hA : MeasurableSet A)
    (hi : InjOn (fun p : H × ℝ => (p.1, ψ p)) A)
    {f : H × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q in (fun p : H × ℝ => (p.1, ψ p)) '' A, f q ∂(volume : Measure (H × ℝ)) =
      ∫⁻ p in A, ENNReal.ofReal |deriv (fun t => ψ (p.1, t)) p.2| *
        f (p.1, ψ p) ∂(volume : Measure (H × ℝ)) := by
  have h := setLIntegral_image_vectorVerticalMap (rfl : finrank ℝ ℝ = finrank ℝ ℝ) hψ hA hi hf
  simpa only [normDet_fderiv_eq_abs_deriv] using h

end CodimensionOne

/-! ### The equal-dimension hypothesis is necessary -/

section Necessity

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- A unit vector of the plane. -/
def e₀ : Plane := EuclideanSpace.single 0 (1 : ℝ)

theorem norm_e₀ : ‖e₀‖ = 1 := by
  simp [e₀]

/-- The line through `e₀`, as a linear isometry from `ℝ`. -/
def line : ℝ →ₗᵢ[ℝ] Plane where
  toLinearMap := LinearMap.toSpanSingleton ℝ Plane e₀
  norm_map' := by
    intro t
    simp [LinearMap.toSpanSingleton_apply, norm_smul, norm_e₀]

/-- **The equal-dimension hypothesis cannot be dropped.**  For the line map from `ℝ` into the plane
on the unit interval the left-hand side of the change of variables is `0`, because the image lies in
a proper subspace, while the right-hand side is `1`, because a linear isometry has unit volume
factor. -/
theorem equal_dimension_necessary :
    (volume : Measure Plane) ((line : ℝ → Plane) '' Set.Icc (0 : ℝ) 1) = 0 ∧
      ∫⁻ _ in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (LinearMap.normDet ((line.toContinuousLinearMap : ℝ →ₗ[ℝ] Plane)))
            * (1 : ℝ≥0∞) ∂(volume : Measure ℝ) = 1 ∧
      finrank ℝ ℝ ≠ finrank ℝ Plane := by
  refine ⟨?_, ?_, ?_⟩
  · have hsub : (line : ℝ → Plane) '' Set.Icc (0 : ℝ) 1
        ⊆ (LinearMap.range (line.toLinearMap) : Submodule ℝ Plane) := by
      rintro _ ⟨t, -, rfl⟩
      exact ⟨t, rfl⟩
    refine measure_mono_null hsub ?_
    refine Measure.addHaar_submodule _ _ ?_
    intro htop
    have h1 : finrank ℝ (LinearMap.range (line.toLinearMap) : Submodule ℝ Plane) ≤ 1 := by
      simpa using LinearMap.finrank_range_le (line.toLinearMap)
    rw [htop] at h1
    simp only [finrank_top] at h1
    rw [show finrank ℝ Plane = 2 from finrank_euclideanSpace_fin] at h1
    omega
  · rw [show LinearMap.normDet ((line.toContinuousLinearMap : ℝ →ₗ[ℝ] Plane)) = 1 from
      LinearIsometry.normDet_eq_one line]
    simp
  · rw [finrank_self, show finrank ℝ Plane = 2 from finrank_euclideanSpace_fin]
    norm_num

end Necessity

end VectorFiberIntegralAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.isometryEquivOfFinrankEq
#print axioms FunctionalInequalities.Analysis.lintegral_image_eq_lintegral_normDet_fderiv_mul
#print axioms FunctionalInequalities.Analysis.fderiv_snd_eq
#print axioms FunctionalInequalities.Analysis.continuous_normDet_fderiv_snd
#print axioms FunctionalInequalities.Analysis.setLIntegral_image_vectorVerticalMap
#print axioms FunctionalInequalities.Analysis.splitVectorEquiv
#print axioms FunctionalInequalities.Analysis.splitVectorEquiv_apply
#print axioms FunctionalInequalities.Analysis.setLIntegral_image_levelGraphMap
#print axioms FunctionalInequalities.Analysis.setLIntegral_coareaJacobian_levelGraphFamily
#print axioms VectorFiberIntegralAudit.change_of_variables
#print axioms VectorFiberIntegralAudit.isometry_preserves_measure
#print axioms VectorFiberIntegralAudit.whole_space
#print axioms VectorFiberIntegralAudit.zero_dimensional_fibre
#print axioms VectorFiberIntegralAudit.normDet_fderiv_eq_abs_deriv
#print axioms VectorFiberIntegralAudit.codimension_one_verticalMap
#print axioms VectorFiberIntegralAudit.equal_dimension_necessary
