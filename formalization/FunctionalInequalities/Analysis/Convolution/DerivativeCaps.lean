import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import FunctionalInequalities.Analysis.Convolution.UniformBound
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.NormNum

/-!
# Derivative caps for convolution with a compact C⁴ kernel

Supporting the interior derivative estimates for harmonic functions in Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 2.10 /
estimate (2.31), as used in Theorem 4.6, p. 60:

* `convolution_derivative_caps`: for a compactly supported `K ∈ C⁴(ℝⁿ)` there are positive constants
  `C1, C2, C3`, chosen before the source, such that for every locally integrable scalar `g` with
  `|g| ≤ M` everywhere (`0 ≤ M`), the first three Fréchet derivatives of `K ⋆ g` are bounded at
  every point by `C1 * M`, `C2 * M`, `C3 * M` in operator norm.

The derivatives fall on the kernel (`HasCompactSupport.hasFDerivAt_convolution_left`), and each
`Dᵏ K ⋆ g` is bounded by `Convolution/UniformBound`. The constants depend only on `K`; the source
enters only through local integrability and its value bound, never through its derivatives.
The convolution is Mathlib's bilinear convolution with `ContinuousLinearMap.lsmul ℝ ℝ`, so
`(K ⋆ g) x = ∫ K t * g (x - t) dt`.
-/
noncomputable section
open MeasureTheory
open scoped Convolution
namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

/-- A compact C⁴ kernel produces uniform D1/D2/D3 bounds. The source enters only
through local integrability and its value bound, never through its derivatives. -/
theorem convolution_derivative_caps {n : ℕ}
    {K : EuclideanSpace ℝ (Fin n) → ℝ} (hK : ContDiff ℝ 4 K)
    (hc : HasCompactSupport K) :
    ∃ C1 C2 C3 : ℝ, 0 < C1 ∧ 0 < C2 ∧ 0 < C3 ∧
      ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ), LocallyIntegrable g volume →
      ∀ (M : ℝ), 0 ≤ M → (∀ y, |g y| ≤ M) →
      ∀ x, ‖fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ C1 * M ∧
        ‖fderiv ℝ (fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x‖ ≤ C2 * M ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ
          (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g))) x‖ ≤ C3 * M := by
  let K1 := fderiv ℝ K
  let K2 := fderiv ℝ K1
  let K3 := fderiv ℝ K2
  let L0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let L1 := L0.precompL (EuclideanSpace ℝ (Fin n))
  let L2 := L1.precompL (EuclideanSpace ℝ (Fin n))
  let L3 := L2.precompL (EuclideanSpace ℝ (Fin n))
  have hK1 : ContDiff ℝ 3 K1 := hK.fderiv_right (by norm_num)
  have hK2 : ContDiff ℝ 2 K2 := hK1.fderiv_right (by norm_num)
  have hK3 : ContDiff ℝ 1 K3 := hK2.fderiv_right (by norm_num)
  have hc1 : HasCompactSupport K1 := hc.fderiv ℝ
  have hc2 : HasCompactSupport K2 := hc1.fderiv ℝ
  have hc3 : HasCompactSupport K3 := hc2.fderiv ℝ
  let A1 := ‖L1‖ * ∫ y, ‖K1 y‖
  let A2 := ‖L2‖ * ∫ y, ‖K2 y‖
  let A3 := ‖L3‖ * ∫ y, ‖K3 y‖
  refine ⟨max 1 A1, max 1 A2, max 1 A3,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro g hg M hM hbound x
  have hd0 : fderiv ℝ (K ⋆[L0, volume] g) = (K1 ⋆[L1, volume] g) := by
    funext z
    exact (hc.hasFDerivAt_convolution_left L0 (hK.of_le (by norm_num)) hg z).fderiv
  have hd1 : fderiv ℝ (K1 ⋆[L1, volume] g) = (K2 ⋆[L2, volume] g) := by
    funext z
    exact (hc1.hasFDerivAt_convolution_left L1 (hK1.of_le (by norm_num)) hg z).fderiv
  have hd2 : fderiv ℝ (K2 ⋆[L2, volume] g) = (K3 ⋆[L3, volume] g) := by
    funext z
    exact (hc2.hasFDerivAt_convolution_left L2 (hK2.of_le (by norm_num)) hg z).fderiv
  have hb1 := norm_convolution_le_of_bound L1 (hK1.continuous.integrable_of_hasCompactSupport hc1)
    hbound x
  have hb2 := norm_convolution_le_of_bound L2 (hK2.continuous.integrable_of_hasCompactSupport hc2)
    hbound x
  have hb3 := norm_convolution_le_of_bound L3 (hK3.continuous.integrable_of_hasCompactSupport hc3)
    hbound x
  change ‖fderiv ℝ (K ⋆[L0, volume] g) x‖ ≤ max 1 A1 * M ∧
    ‖fderiv ℝ (fderiv ℝ (K ⋆[L0, volume] g)) x‖ ≤ max 1 A2 * M ∧
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (K ⋆[L0, volume] g))) x‖ ≤ max 1 A3 * M
  rw [hd0, hd1, hd2]
  exact ⟨hb1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM),
    hb2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM),
    hb3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM)⟩
end FunctionalInequalities.Analysis
