import Mathlib.Analysis.Calculus.ContDiff.Convolution
import FunctionalInequalities.Analysis.BakryEmery.Calculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Laplacian commutes with convolution against a locally integrable kernel

`laplacian_convolution_compact_C2`: for a locally integrable kernel `k` and a compactly supported
`u ∈ C²` on `EuclideanSpace ℝ (Fin n)`, `Δ(k ⋆ u) = k ⋆ Δu` pointwise, with Mathlib's actual
Laplacian and convolution. It supports the representation `u = Γ ⋆ Δu` of compactly supported `C²`
functions in Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
2001 (ISBN 3-540-41160-7), (4.15). No regularity of `k` beyond local integrability is used.
-/

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery
open scoped Convolution ContDiff
namespace FunctionalInequalities.Analysis

/-- A locally integrable kernel commutes with the actual Laplacian on a
compactly supported C² source. This supports GT2001 (4.15). -/
theorem laplacian_convolution_compact_C2 {n : ℕ}
    {k u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hk : LocallyIntegrable k volume) (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Laplacian.laplacian u) x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have huD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hcD : HasCompactSupport (fderiv ℝ u) := hc.fderiv ℝ
  have hconv : ContDiff ℝ 2 (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) :=
    hc.contDiff_convolution_right _ hk hu
  have hd : DifferentiableAt ℝ (fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)) x :=
    (hconv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have hdir : ∀ v, (fun y => fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) y v) =
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun a => fderiv ℝ u a v) := by
    intro v
    funext y
    rw [(hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hk hu1 y).fderiv,
      convolution_precompR_apply _ hk hcD huD.continuous]
  have hsecond : ∀ v w, fderiv ℝ (fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)) x v w =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun a => fderiv ℝ (fderiv ℝ u) a v w)) x := by
    intro v w
    rw [← fderiv_fderiv_apply hd v w,hdir w]
    have hw1 : ContDiff ℝ 1 (fun a => fderiv ℝ u a w) := huD.clm_apply contDiff_const
    have hwc : HasCompactSupport (fun a => fderiv ℝ u a w) := hc.fderiv_apply ℝ w
    rw [(hwc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hk hw1 x).fderiv,
      convolution_precompR_apply _ hk (hwc.fderiv ℝ) (hw1.continuous_fderiv one_ne_zero)]
    simp only [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
    rw [fderiv_fderiv_apply (huD.differentiable one_ne_zero _) v w]
  have hDD : Continuous (fderiv ℝ (fderiv ℝ u)) := huD.continuous_fderiv one_ne_zero
  have hint : ∀ i : Fin n, Integrable (fun t =>
      (ContinuousLinearMap.lsmul ℝ ℝ (k t)) (fderiv ℝ (fderiv ℝ u) (x-t) (b i) (b i))) volume := by
    intro i
    have hcc : HasCompactSupport (fun a => fderiv ℝ (fderiv ℝ u) a (b i) (b i)) :=
      ((hc.fderiv ℝ).fderiv ℝ).comp_left (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (b i) (b i)) (by simp)
    exact hcc.convolutionExists_right _ hk ((hDD.clm_apply continuous_const).clm_apply continuous_const) x
  have hlap (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
      Laplacian.laplacian f y = ∑ i : Fin n, fderiv ℝ (fderiv ℝ f) y (b i) (b i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [hlap]
  simp only [hsecond,convolution_def]
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul,hlap,Finset.mul_sum]
end FunctionalInequalities.Analysis
