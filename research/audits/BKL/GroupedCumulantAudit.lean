import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz
import FunctionalInequalities.KLS.Isotropic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Audit clients for the grouped expansion of Bizeul–Klartag–Lehec, arXiv:2610.05474v1, (72)–(74)
(`Analysis/BakryEmery/Cumulant/Leibniz.lean`, `iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact`):
at `m = 3` the middle sum (72) is empty and the expansion is `6 κ₃`; at `m = 4` exactly three middle masks contain
`i0`, written out as the three pairings `{0,1|2,3}`, `{0,2|1,3}`, `{0,3|1,2}`; the theorem through its frozen binder
names (`mu`, `hc`, `hA`, `hm`, `h`, `i0`); and the actual compactly supported skew two-point law, whose covariance unit
is derived from its actual isotropy (never assumed), with `D³⟪v, Cov⁻¹ v⟫(0)[1,1,1] = 6 κ₃ = 9 ≠ 0` on repeated
data. Section `SkewLaw` and `law`/`law_compact` are verbatim from `RawCumulantExpansionAudit.lean` (receipt
f17f3495…), with the fixture namespace renamed to `BKLGroupedSkewLaw` so that no fixture name is shared with the other
BKL audits. -/


-- ===== reviewer module SkewLaw (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
section SkewLaw
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
open FunctionalInequalities.Analysis.BakryEmery
namespace BKLGroupedSkewLaw
/-- The two-point law `(1/5) δ₂ + (4/5) δ_{-1/2}`: centered, isotropic and skewed. -/
def twoPt : Measure ℝ := (1 / 5 : ℝ≥0∞) • Measure.dirac 2 + (4 / 5 : ℝ≥0∞) • Measure.dirac (-1 / 2)

theorem integrable_twoPt (f : ℝ → ℝ) : Integrable f twoPt := by
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))

theorem integral_twoPt (f : ℝ → ℝ) : ∫ x, f x ∂twoPt = (1 / 5) * f 2 + (4 / 5) * f (-1 / 2) := by
  rw [twoPt, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))

theorem isProbabilityMeasure_twoPt : IsProbabilityMeasure twoPt := by
  constructor
  rw [twoPt]
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem centered_twoPt (v : ℝ) : ∫ x, ⟪v, x⟫ ∂twoPt = 0 := by
  rw [integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem isotropic_twoPt (v w : ℝ) : ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂twoPt = ⟪v, w⟫ := by
  rw [integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem integrable_exp_mul_norm_twoPt (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖)) twoPt := integrable_twoPt _

theorem cumulant_three_twoPt : cumulant twoPt 3 ![1, 1, 1] = 3 / 2 := by
  have := isProbabilityMeasure_twoPt
  rw [cumulant_three_eq_integral twoPt integrable_exp_mul_norm_twoPt centered_twoPt, integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  norm_num

end BKLGroupedSkewLaw

end
end SkewLaw

section GroupedClients

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery

namespace BKLGroupedClients

/-- The length of a selected list depends only on the mask. -/
private theorem length_selected_congr {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∀ {m : ℕ} (h : Fin m → E) (h' : Fin m → F) (q : Fin m → Bool),
      (selected h q).length = (selected h' q).length
  | 0, _, _, _ => rfl
  | m + 1, h, h', q => by
    simp only [selected]
    split_ifs <;> simp [length_selected_congr (Fin.tail h) (Fin.tail h') (Fin.tail q)]

section NormedSpace

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At `m = 3` no allocation has at least two slots on both sides: (72) is empty. -/
theorem middle_three_empty (h : Fin 3 → E) (i0 : Fin 3) :
    Finset.univ.filter (fun q : Fin 3 → Bool => q i0 = true ∧ 2 ≤ (selected h q).length ∧
      2 ≤ (selected h (fun i => !(q i))).length) = ∅ := by
  simp_rw [length_selected_congr h (fun _ : Fin 3 => (0 : ℝ))]
  revert i0
  decide

/-- At `m = 4`, exactly three allocations contain `i0` and leave two slots on each side. -/
theorem middle_four_card (h : Fin 4 → E) (i0 : Fin 4) :
    (Finset.univ.filter (fun q : Fin 4 → Bool => q i0 = true ∧ 2 ≤ (selected h q).length ∧
      2 ≤ (selected h (fun i => !(q i))).length)).card = 3 := by
  simp_rw [length_selected_congr h (fun _ : Fin 4 => (0 : ℝ))]
  revert i0
  decide

/-- At `m = 4` and `i0 = 0` the three middle masks are the pairings `{0,1}`, `{0,2}`, `{0,3}` (repeated data allowed). -/
theorem middle_four_masks (h : Fin 4 → E) :
    Finset.univ.filter (fun q : Fin 4 → Bool => q 0 = true ∧ 2 ≤ (selected h q).length ∧
      2 ≤ (selected h (fun i => !(q i))).length) =
      {![true, true, false, false], ![true, false, true, false], ![true, false, false, true]} := by
  simp_rw [length_selected_congr h (fun _ : Fin 4 => (0 : ℝ))]
  decide

end NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- BKL (74) at `m = 3`: the grouped expansion is `6 κ₃`, for a compactly supported law with invertible covariance. -/
theorem grouped_three (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (hA : IsUnit (Covariance.operator (μ : Measure E))) (h : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (fun z : E =>
        ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
          Ring.inverse (Covariance.operator (μ : Measure E))
            (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫) 0 h =
      6 * cumulant (μ : Measure E) 3 h := by
  rw [iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact μ hc hA le_rfl h 0, middle_three_empty]
  norm_num

/-- BKL (74) at `m = 4`: `8 κ₄` plus twice the three representative middle terms containing `i0`. -/
theorem grouped_four (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (hA : IsUnit (Covariance.operator (μ : Measure E))) (h : Fin 4 → E) (i0 : Fin 4) :
    iteratedFDeriv ℝ 4 (fun z : E =>
        ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
          Ring.inverse (Covariance.operator (μ : Measure E))
            (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫) 0 h =
      8 * cumulant (μ : Measure E) 4 h +
        2 * ∑ q ∈ Finset.univ.filter (fun q : Fin 4 → Bool =>
          q i0 = true ∧ 2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
          ⟪cumulantVector (μ : Measure E) (selected h q),
            Ring.inverse (Covariance.operator (μ : Measure E))
              (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫ := by
  rw [iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact μ hc hA (by norm_num) h i0]
  norm_num

/-- BKL (74) at `m = 4` written out: `8 κ₄` plus twice the three pairings of the slots containing `h 0`. -/
theorem grouped_four_pairs (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (hA : IsUnit (Covariance.operator (μ : Measure E))) (h : Fin 4 → E) :
    iteratedFDeriv ℝ 4 (fun z : E =>
        ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
          Ring.inverse (Covariance.operator (μ : Measure E))
            (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫) 0 h =
      8 * cumulant (μ : Measure E) 4 h +
        2 * (⟪cumulantVector (μ : Measure E) [h 0, h 1],
              Ring.inverse (Covariance.operator (μ : Measure E)) (cumulantVector (μ : Measure E) [h 2, h 3])⟫ +
            (⟪cumulantVector (μ : Measure E) [h 0, h 2],
              Ring.inverse (Covariance.operator (μ : Measure E)) (cumulantVector (μ : Measure E) [h 1, h 3])⟫ +
             ⟪cumulantVector (μ : Measure E) [h 0, h 3],
              Ring.inverse (Covariance.operator (μ : Measure E)) (cumulantVector (μ : Measure E) [h 1, h 2])⟫)) := by
  rw [grouped_four μ hc hA h 0, middle_four_masks h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rfl

/-- The sealed interface through its frozen binder names as named arguments (`mu`, `hc`, `hA`, `hm`, `h`, `i0`). -/
theorem grouped_named (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (hA : IsUnit (Covariance.operator (μ : Measure E))) {m : ℕ} (hm : 3 ≤ m) (h : Fin m → E) (i0 : Fin m) :
    iteratedFDeriv ℝ m (fun z : E =>
        ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
          Ring.inverse (Covariance.operator (μ : Measure E))
            (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫) 0 h =
      (2 * (m : ℝ)) * cumulant (μ : Measure E) m h +
        2 * ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
          q i0 = true ∧ 2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
          ⟪cumulantVector (μ : Measure E) (selected h q),
            Ring.inverse (Covariance.operator (μ : Measure E))
              (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫ :=
  iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact (mu := μ) (hc := hc) (hA := hA) (hm := hm)
    (h := h) (i0 := i0)

end BKLGroupedClients

namespace BKLGroupedSkew
open BKLGroupedSkewLaw

def law : ProbabilityMeasure ℝ := ⟨twoPt,isProbabilityMeasure_twoPt⟩
lemma law_compact : IsCompact (law : Measure ℝ).support := by
  have hsub : (law : Measure ℝ).support ⊆ ({(2:ℝ),-1/2}:Set ℝ) := by
    apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
    rw [mem_ae_iff]
    simp [law,twoPt]
  exact (Set.toFinite ({(2:ℝ),-1/2}:Set ℝ)).isCompact.of_isClosed_subset
    (law : Measure ℝ).isClosed_support hsub

/-- The skew two-point law is isotropic (actual moments), so its covariance is the identity, a unit. -/
theorem law_isotropic : FunctionalInequalities.KLS.Isotropic law :=
  FunctionalInequalities.KLS.isotropic_of_moments law
    ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 (integrable_twoPt _))
    (by simpa [law] using centered_twoPt 1) (fun u v => isotropic_twoPt u v)

theorem law_covariance_unit : IsUnit (Covariance.operator (law : Measure ℝ)) := by
  rw [law_isotropic.covariance_identity]
  exact isUnit_one

/-- BKL (74) at `m = 3` on the actual skew law: `D³⟪v, Cov⁻¹ v⟫(0)[1,1,1] = 6 κ₃ = 9`. -/
theorem grouped_three_value :
    iteratedFDeriv ℝ 3 (fun z : ℝ =>
        ⟪gradient (logLaplace (law : Measure ℝ)) z - gradient (logLaplace (law : Measure ℝ)) 0,
          Ring.inverse (Covariance.operator (law : Measure ℝ))
            (gradient (logLaplace (law : Measure ℝ)) z - gradient (logLaplace (law : Measure ℝ)) 0)⟫) 0 ![1, 1, 1] =
      9 := by
  rw [BKLGroupedClients.grouped_three law law_compact law_covariance_unit]
  change 6 * cumulant twoPt 3 ![1, 1, 1] = 9
  rw [cumulant_three_twoPt]
  norm_num

end BKLGroupedSkew

end
end GroupedClients

#print axioms BKLGroupedClients.middle_three_empty
#print axioms BKLGroupedClients.middle_four_card
#print axioms BKLGroupedClients.middle_four_masks
#print axioms BKLGroupedClients.grouped_three
#print axioms BKLGroupedClients.grouped_four
#print axioms BKLGroupedClients.grouped_four_pairs
#print axioms BKLGroupedClients.grouped_named
#print axioms BKLGroupedSkew.law_isotropic
#print axioms BKLGroupedSkew.law_covariance_unit
#print axioms BKLGroupedSkew.grouped_three_value
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact
