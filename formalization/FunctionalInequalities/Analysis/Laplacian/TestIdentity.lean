module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Green's first identity against compactly supported tests

`integral_test_mul_laplacian`: on `EuclideanSpace ℝ (Fin n)`, for `u ∈ C²` and a compactly supported
`ψ ∈ C¹`, `∫ ψ Δu = -∑ᵢ ∫ ∂ᵢψ ∂ᵢu`, with Mathlib's actual Laplacian and no boundary term. This is
the whole-space, compact-support case of Green's first identity (Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), §2.4), used for
the representation (4.15) of compactly supported functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Analysis

/-- Green's first identity against a compact `C¹` test, with every product integrable
by continuity and compact support. The function itself needs only `C²`. -/
theorem integral_test_mul_laplacian {n : ℕ}
    {u ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, ψ x * Laplacian.laplacian u x) =
      -(∑ i : Fin n, ∫ x, fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hFi (i : Fin n) : ContDiff ℝ 1 (fun x => fderiv ℝ u x (b i)) :=
    hDu.clm_apply contDiff_const
  have hDψ (i : Fin n) : Continuous (fun x => fderiv ℝ ψ x (b i)) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDψc (i : Fin n) : HasCompactSupport (fun x => fderiv ℝ ψ x (b i)) :=
    hc.fderiv_apply ℝ (b i)
  have hsecond (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => fderiv ℝ u y (b i)) x (b i) =
        bilinearIteratedFDerivTwo ℝ u x (b i) (b i) := by
    rw [fderiv_clm_apply (hDu.differentiable one_ne_zero x) (differentiableAt_const (b i))]
    simp [bilinearIteratedFDerivTwo]
  have hi1 (i : Fin n) : Integrable (fun x => fderiv ℝ ψ x (b i) *
      fderiv ℝ u x (b i)) volume :=
    ((hDψ i).mul (hFi i).continuous).integrable_of_hasCompactSupport
      ((hDψc i).mul_right)
  have hi2 (i : Fin n) : Integrable (fun x => ψ x *
      fderiv ℝ (fun y => fderiv ℝ u y (b i)) x (b i)) volume :=
    (hψ.continuous.mul (((hFi i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport (hc.mul_right)
  have hi3 (i : Fin n) : Integrable (fun x => ψ x * fderiv ℝ u x (b i)) volume :=
    (hψ.continuous.mul (hFi i).continuous).integrable_of_hasCompactSupport
      (hc.mul_right)
  have he (i : Fin n) : (∫ x, ψ x *
      bilinearIteratedFDerivTwo ℝ u x (b i) (b i)) =
      -(∫ x, fderiv ℝ ψ x (b i) * fderiv ℝ u x (b i)) := by
    simpa only [hsecond] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi1 i) (hi2 i) (hi3 i)
        (fun x _ => hψ.differentiable one_ne_zero x)
        (fun x _ => (hFi i).differentiable one_ne_zero x)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  simp_rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => by simpa only [hsecond] using hi2 i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib]

end FunctionalInequalities.Analysis
