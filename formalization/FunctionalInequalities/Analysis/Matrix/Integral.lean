import FunctionalInequalities.Analysis.Matrix.Sign
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Trace energies of symmetric matrix fields under a measure

Letwin, arXiv:2607.24164v1, Theorem 2.5, the extension step from positive semidefinite to all symmetric `B`, for a
measurable field `H : Ω → Matrix ι ι ℝ` of positive semidefinite matrices under an arbitrary measure `ν` on an arbitrary
measurable space, over every finite index type (the empty one included): if every positive semidefinite `A` has
`x ↦ tr(A H(x) A H(x))` integrable with `∫ tr(A H A H) dν ≤ 2 tr(A²)`, then every symmetric `B` has the same
(`symmetric_trace_integral_extension`). The integrability for `B` is derived (pointwise Jordan domination of
`Matrix/Sign.lean` and `Matrix/Trace.lean`); no finiteness of `ν`, nonemptiness or commutation is assumed. The positive
semidefinite bound is a named hypothesis: it is not constructed here, nor is the moment map, Brascamp–Lieb or Theorem
2.5 itself. Proof body: strong-API candidate (gpt-6-astra, `api-symmetric-client-patch-v9`, 1376c19e…), verbatim.
-/

noncomputable section

open Matrix MeasureTheory

namespace FunctionalInequalities.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Supporting measure extension from the PSD integral estimate to every symmetric
real matrix. This theorem does not construct the PSD estimate or any source-law
moment-map data. -/
theorem symmetric_trace_integral_extension
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (H : Ω → Matrix ι ι ℝ)
    (hH_meas : ∀ i j, Measurable (fun x => H x i j))
    (hH_psd : ∀ x, (H x).PosSemidef)
    (hPSD : ∀ A : Matrix ι ι ℝ, A.PosSemidef →
      Integrable (fun x => (A * H x * A * H x).trace) ν ∧
        (∫ x, (A * H x * A * H x).trace ∂ν) ≤
          2 * (A * A).trace)
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) :
    Integrable (fun x => (B * H x * B * H x).trace) ν ∧
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        2 * (B * B).trace := by
  obtain ⟨P, N, hP, hN, hdec, hPN, hNP, htrace⟩ :=
    symmetric_jordan_decomposition B hB
  obtain ⟨hP_int, hP_bound⟩ := hPSD P hP
  obtain ⟨hN_int, hN_bound⟩ := hPSD N hN
  have hmeas (A : Matrix ι ι ℝ) :
      Measurable (fun x => (A * H x * A * H x).trace) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.mul ?_ (hH_meas j i)
    refine Finset.measurable_sum _ (fun k _ => ?_)
    refine Measurable.mul ?_ measurable_const
    refine Finset.measurable_sum _ (fun l _ => ?_)
    exact measurable_const.mul (hH_meas l k)
  have hP_nonneg : ∀ x,
      0 ≤ (P * H x * P * H x).trace := by
    intro x
    exact trace_energy_nonneg (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hP)) (hH_psd x)
  have hN_nonneg : ∀ x,
      0 ≤ (N * H x * N * H x).trace := by
    intro x
    exact trace_energy_nonneg (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian hN)) (hH_psd x)
  have hB_nonneg : ∀ x,
      0 ≤ (B * H x * B * H x).trace := by
    intro x
    exact trace_energy_nonneg hB (hH_psd x)
  have hdom : ∀ x,
      (B * H x * B * H x).trace ≤
        (P * H x * P * H x).trace + (N * H x * N * H x).trace := by
    intro x
    rw [hdec]
    exact jordan_trace_domination hP hN
      (Matrix.isHermitian_iff_isSymm.mp (Matrix.PosSemidef.isHermitian (hH_psd x)))
  have hsum_int :
      Integrable
        (fun x =>
          (P * H x * P * H x).trace + (N * H x * N * H x).trace) ν := by
    exact hP_int.add hN_int
  have hB_int :
      Integrable (fun x => (B * H x * B * H x).trace) ν := by
    refine hsum_int.mono (hmeas B).aestronglyMeasurable ?_
    exact ae_of_all ν (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hB_nonneg x)]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (hP_nonneg x) (hN_nonneg x))]
      exact hdom x)
  have hIntDom :
      (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        ∫ x, ((P * H x * P * H x).trace +
          (N * H x * N * H x).trace) ∂ν := by
    exact integral_mono hB_int hsum_int hdom
  refine ⟨hB_int, ?_⟩
  calc
    (∫ x, (B * H x * B * H x).trace ∂ν) ≤
        ∫ x, ((P * H x * P * H x).trace +
          (N * H x * N * H x).trace) ∂ν := hIntDom
    _ = (∫ x, (P * H x * P * H x).trace ∂ν) +
        ∫ x, (N * H x * N * H x).trace ∂ν :=
      integral_add hP_int hN_int
    _ ≤ 2 * (P * P).trace + 2 * (N * N).trace :=
      add_le_add hP_bound hN_bound
    _ = 2 * (B * B).trace := by
      calc
        2 * (P * P).trace + 2 * (N * N).trace =
            2 * ((P * P).trace + (N * N).trace) := by ring
        _ = 2 * (B * B).trace := by rw [← htrace]

end FunctionalInequalities.Analysis
