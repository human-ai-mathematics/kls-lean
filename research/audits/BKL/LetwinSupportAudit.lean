import FunctionalInequalities.Analysis.Tensor.Coordinate
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: Letwin supporting identities with source-style consumers

Source: Letwin, arXiv:2607.24164v1, proof of Theorem 2.5 (equation (2.12), p. 10) and Lemma A.3
(pp. 16–17); these are dependencies of BKL Lemma 4.2 through the Letwin bound. They are supporting
identities only: neither Letwin Theorem 1.2 nor BKL Theorem 4.1 is asserted.

* `mixedContraction_le`: the source inequality `Σ b_i b_j T_{ijk}² ≤ Σ b_i² T_{ijk}²` from the finite
  identity (2.12); `signed_nonzero_client`, `positive_nonzero_client`: nonzero `Fin 2` instances.
* `directional_test_against_one`: Lemma A.3 with `g = 1`, the directional Stein pairing
  `∫ ∂_v f dν = ∫ f ∂_v φ dν`.
-/

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis.Tensor FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff BigOperators

namespace LetwinSupportAudit

theorem mixedContraction_le {ι : Type*} [Fintype ι] (b : ι → ℝ)
    (T : ι → ι → ι → ℝ) (hT : ∀ i j k, T i j k = T j i k) :
    (∑ i, ∑ j, ∑ k, b i * b j * T i j k ^ 2) ≤
      ∑ i, ∑ j, ∑ k, b i ^ 2 * T i j k ^ 2 := by
  have hn : 0 ≤ ∑ i, ∑ j, ∑ k, (b i - b j) ^ 2 * T i j k ^ 2 := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have heq := sum_weight_sq_mul_sq_sub_eq_half_sum_sq_sub_mul_sq b T hT
  linarith

theorem signed_nonzero_client :
    let b : Fin 2 → ℝ := ![-1, 1]
    (∑ i : Fin 2, ∑ _j : Fin 2, ∑ _k : Fin 2, b i ^ 2 * (1 : ℝ)^2) -
      (∑ i : Fin 2, ∑ j : Fin 2, ∑ _k : Fin 2, b i * b j * (1 : ℝ)^2) = 8 := by
  norm_num [Fin.sum_univ_two]

theorem positive_nonzero_client :
    let b : Fin 2 → ℝ := ![0, 1]
    (∑ i : Fin 2, ∑ _j : Fin 2, ∑ _k : Fin 2, b i ^ 2 * (1 : ℝ)^2) -
      (∑ i : Fin 2, ∑ j : Fin 2, ∑ _k : Fin 2, b i * b j * (1 : ℝ)^2) = 2 := by
  norm_num [Fin.sum_univ_two]

theorem directional_test_against_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]
    (φ f : E → ℝ) (v : E) (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f)
    (hφexp : Integrable (fun x => Real.exp (-φ x)) m)
    (hφnorm : ∫ x, Real.exp (-φ x) ∂m = 1)
    (hdf : Integrable (fun x => fderiv ℝ f x v) (m.tilted (-φ)))
    (hfφ : Integrable (fun x => f x * fderiv ℝ φ x v) (m.tilted (-φ)))
    (hfint : Integrable f (m.tilted (-φ))) :
    (∫ x, fderiv ℝ f x v ∂(m.tilted (-φ))) =
      ∫ x, f x * fderiv ℝ φ x v ∂(m.tilted (-φ)) := by
  have hzero : Integrable (fun x : E => f x * fderiv ℝ (fun _ : E => (1 : ℝ)) x v)
      (m.tilted (-φ)) := by simp
  simpa only [fderiv_const_apply, zero_apply, mul_one, sub_zero] using
    integral_fderiv_mul_tilted_eq m φ f (fun _ => 1) v hφ hf contDiff_const hφexp hφnorm
      (by simpa only [mul_one] using hdf) hzero
      (by simpa only [mul_one] using hfφ) (by simpa only [mul_one] using hfint)

end LetwinSupportAudit

#print axioms LetwinSupportAudit.mixedContraction_le
#print axioms LetwinSupportAudit.signed_nonzero_client
#print axioms LetwinSupportAudit.positive_nonzero_client
#print axioms LetwinSupportAudit.directional_test_against_one
#print axioms FunctionalInequalities.Analysis.Tensor.sum_weight_sq_mul_sq_sub_eq_half_sum_sq_sub_mul_sq
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_fderiv_mul_tilted_eq
