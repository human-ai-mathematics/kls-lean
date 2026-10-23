import FunctionalInequalities.Analysis.Laplacian.TestIdentity
import Mathlib.Tactic.NormNum

/-!
# Symmetry of the Laplacian against one compactly supported function

`integral_mul_laplacian_symm`: on `EuclideanSpace ℝ (Fin n)`, for a compactly supported `u ∈ C²` and
an arbitrary `g ∈ C²(ℝⁿ)`, `∫ g Δu = ∫ u Δg`, with Mathlib's actual Laplacian. This is the
whole-space, compact-support case of Green's second identity (Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), §2.4): both sides equal
`-∑ᵢ ∫ ∂ᵢg ∂ᵢu`, the left one by coordinatewise integration by parts and the right one by Green's first
identity (`integral_test_mul_laplacian`) with `u` as the compact test. Only `u` needs compact support
and no boundary term appears.

It is the integration-by-parts step that turns the Newtonian representation (4.15) into the
annular reproducing formula of `Harmonic/CompactReproduction`, used for the harmonic part of GT
Theorem 4.6, p. 60.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities.Analysis

/-- Move the actual Laplacian from a compact C² function to a globally C² test.
Only the first function is compact; no PDE or Green identity is assumed. -/
theorem integral_mul_laplacian_symm {n : ℕ}
    {u g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u) (hg : ContDiff ℝ 2 g) :
    (∫ y, g y * Laplacian.laplacian u y) =
      ∫ y, u y * Laplacian.laplacian g y := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hDu : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hFi (i : Fin n) : ContDiff ℝ 1 (fun y => fderiv ℝ u y (b i)) :=
    hDu.clm_apply contDiff_const
  have hDg (i : Fin n) : Continuous (fun y => fderiv ℝ g y (b i)) :=
    (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDuc (i : Fin n) : HasCompactSupport (fun y => fderiv ℝ u y (b i)) :=
    hc.fderiv_apply ℝ (b i)
  have hsecond (i : Fin n) (y : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun z => fderiv ℝ u z (b i)) y (b i) =
        bilinearIteratedFDerivTwo ℝ u y (b i) (b i) := by
    rw [fderiv_clm_apply (hDu.differentiable one_ne_zero y) (differentiableAt_const (b i))]
    simp [bilinearIteratedFDerivTwo]
  have hi1 (i : Fin n) : Integrable (fun y => fderiv ℝ g y (b i) *
      fderiv ℝ u y (b i)) volume :=
    ((hDg i).mul (hFi i).continuous).integrable_of_hasCompactSupport (hDuc i).mul_left
  have hi2 (i : Fin n) : Integrable (fun y => g y *
      fderiv ℝ (fun z => fderiv ℝ u z (b i)) y (b i)) volume :=
    (hg.continuous.mul (((hFi i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const)).integrable_of_hasCompactSupport ((hDuc i).fderiv_apply ℝ (b i)).mul_left
  have hi3 (i : Fin n) : Integrable (fun y => g y * fderiv ℝ u y (b i)) volume :=
    (hg.continuous.mul (hFi i).continuous).integrable_of_hasCompactSupport (hDuc i).mul_left
  have he (i : Fin n) : (∫ y, g y * bilinearIteratedFDerivTwo ℝ u y (b i) (b i)) =
      -(∫ y, fderiv ℝ g y (b i) * fderiv ℝ u y (b i)) := by
    simpa only [hsecond] using
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi1 i) (hi2 i) (hi3 i)
        (fun y _ => hg1.differentiable one_ne_zero y)
        (fun y _ => (hFi i).differentiable one_ne_zero y)
  have hleft : (∫ y, g y * Laplacian.laplacian u y) =
      -(∑ i : Fin n, ∫ y, fderiv ℝ g y (b i) * fderiv ℝ u y (b i)) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
    simp_rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => by simpa only [hsecond] using hi2 i)]
    simp_rw [he]
    rw [Finset.sum_neg_distrib]
  rw [hleft, integral_test_mul_laplacian hg hu1 hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
end FunctionalInequalities.Analysis
