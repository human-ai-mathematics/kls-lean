import FunctionalInequalities.Analysis.RieszPotential.Growth
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Layer-cake bound for bounded functions with power-tail superlevel sets

`lintegral_le_of_bounded_rpow_superlevels`: if `0 ≤ f ≤ T` almost everywhere (`T > 0`) and the
superlevel sets satisfy `μ {f > t} ≤ B t^{-s}` for all `t > 0` with `s < 1` and `B ≥ 0`, then
`∫⁻ f dμ ≤ B T^{1-s} / (1 - s)`. The layer-cake formula reduces the integral to `t ∈ (0, T]`,
where the tail bound is integrable because `-s > -1`.

This is the radial tail mechanism in the far part of the proof of Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 4.4,
pp. 57–59. It is a statement about an arbitrary measure; no kernel or Newtonian potential appears
here. The complementary case `s > 1` with a total-mass bound is handled inside
`FunctionalInequalities.Analysis.RieszPotential.Growth`, which this module imports for its
downstream consumers.
-/
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

/-- The low-threshold layer-cake estimate for a bounded nonnegative function.
This is the radial tail mechanism in the far part of GT (2001), Lemma 4.4. -/
theorem lintegral_le_of_bounded_rpow_superlevels
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : AEMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    {B s T : ℝ} (hB : 0 ≤ B) (hs : s < 1) (hT : 0 < T)
    (hcap : ∀ᵐ x ∂μ, f x ≤ T)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (B*t^(-s))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal (B*T^(1-s)/(1-s)) := by
  have hsplit : Ioi (0:ℝ) = Ioc (0:ℝ) T ∪ Ioi T := by
    ext t
    constructor
    · intro ht
      by_cases hh : t ≤ T
      · exact Or.inl ⟨ht,hh⟩
      · exact Or.inr (lt_of_not_ge hh)
    · rintro (⟨ht,-⟩ | ht)
      · exact ht
      · exact hT.trans ht
  have hd : Disjoint (Ioc (0:ℝ) T) (Ioi T) :=
    Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy
  have hz : (∫⁻ t in Ioi T, μ {x | t < f x}) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcap] with x hx
    exact not_lt_of_ge (hx.trans ht.le)
  have hi : IntegrableOn (fun t : ℝ => B*t^(-s)) (Ioc (0:ℝ) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -s)).const_mul B)
  have hn : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) T)), 0 ≤ B*t^(-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg hB (Real.rpow_nonneg ht.1.le _)
  have hp : (∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (B*t^(-s))) =
      ENNReal.ofReal (B*T^(1-s)/(1-s)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← intervalIntegral.integral_of_le hT.le,
      intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < -s))]
    rw [Real.zero_rpow (by linarith : -s+1 ≠ 0), sub_zero]
    congr 1
    have he : -s+1 = 1-s := by ring
    rw [he]
    ring
  calc
    _ = (∫⁻ t in Ioc (0:ℝ) T, μ {x | t < f x}) + ∫⁻ t in Ioi T, μ {x | t < f x} := by
      rw [lintegral_eq_lintegral_meas_lt μ hf0 hf, hsplit, lintegral_union measurableSet_Ioi hd]
    _ = ∫⁻ t in Ioc (0:ℝ) T, μ {x | t < f x} := by rw [hz,add_zero]
    _ ≤ ∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal (B*t^(-s)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact htail t ht.1
    _ = _ := hp

end FunctionalInequalities.Analysis

