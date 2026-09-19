import FunctionalInequalities.KLS.Geometry.Coarea.Regular
import FunctionalInequalities.KLS.Geometry.CriticalSlice

/-! # Weighted coarea for an arbitrary `C¹` function

Obligation `L11` of the weighted coarea route: the regular-domain identity `L9` and the null
critical slices `L10` combine into the weighted coarea formula for **any** `C¹` real function on a
finite-dimensional inner-product space, over any measurable set and any measurable `ℝ≥0∞` weight.

No Lipschitz bound on `u`, no boundedness or finiteness of `S`, no integrability of `g`, and no
nondegeneracy assumption on the derivative: the critical set is allowed to be arbitrarily large.

The two halves meet exactly, and neither alone suffices.  The critical set
`C = {x | fderiv ℝ u x = 0}` is closed, so its complement `R` is open and `L9` applies to `R`,
which gives the identity for `S ∩ R`.  On the left the critical part contributes nothing because
`gradient u` vanishes there, so the ambient integral over `S` equals the one over `S ∩ R`.  On the
right `L10` makes the critical slice null at almost every level, so the slice integral over
`S ∩ {u = t}` agrees with the one over `(S ∩ R) ∩ {u = t}` for almost every `t`; that same almost
everywhere equality transports `L9`'s `AEMeasurable` component to the full slice function.

This module assumes `u` is `C¹`. `LipschitzCoarea` uses this theorem and the proved exact C¹
decomposition L7, built from the compact Whitney extension L6, to prove L12 for globally
Lipschitz functions and the original `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
entry point. `LocallyLipschitzCoarea` further proves L13 for locally Lipschitz functions. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

section SmoothCoarea

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The regular set of a `C¹` function is open: it is the complement of the closed critical set. -/
theorem isOpen_regular {u : V → ℝ} (hu : ContDiff ℝ 1 u) :
    IsOpen {x : V | fderiv ℝ u x ≠ 0} := by
  have h : {x : V | fderiv ℝ u x ≠ 0} = {x : V | fderiv ℝ u x = 0}ᶜ := by ext x; simp
  rw [h]
  exact (isClosed_critical hu).isOpen_compl

/-- **Weighted coarea for an arbitrary `C¹` function** (obligation `L11`), including almost
everywhere measurability of the weighted slices. -/
theorem coarea_of_contDiff {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hu : ContDiff ℝ 1 u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have hCmeas : MeasurableSet {x : V | fderiv ℝ u x = 0} :=
    (isClosed_critical hu).measurableSet
  have hRmeas : MeasurableSet {x : V | fderiv ℝ u x ≠ 0} := (isOpen_regular hu).measurableSet
  -- `L9` on the open regular part.
  obtain ⟨hmeasR, heqR⟩ := coarea_of_contDiffOn_of_fderiv_ne_zero
    (O := {x : V | fderiv ℝ u x ≠ 0}) (S := S ∩ {x : V | fderiv ℝ u x ≠ 0})
    (isOpen_regular hu) hu.contDiffOn (fun _ hx => hx) (hS.inter hRmeas)
    Set.inter_subset_right hg
  -- `L10`: the two slice integrands agree at almost every level.
  have hslice : (fun t : ℝ =>
        ∫⁻ y in (S ∩ {x : V | fderiv ℝ u x ≠ 0}) ∩ ({x | u x = t} : Set V), g y
          ∂(surfaceMeasure V))
      =ᵐ[(volume : Measure ℝ)] fun t : ℝ =>
        ∫⁻ y in S ∩ ({x | u x = t} : Set V), g y ∂(surfaceMeasure V) := by
    filter_upwards [ae_surfaceMeasure_critical_inter_levelSet_eq_zero (V := V) hu] with t ht
    have hsub : (S ∩ {x : V | fderiv ℝ u x ≠ 0}) ∩ ({x | u x = t} : Set V)
        ⊆ S ∩ ({x | u x = t} : Set V) :=
      Set.inter_subset_inter_left _ Set.inter_subset_left
    have haee : (((S ∩ {x : V | fderiv ℝ u x ≠ 0}) ∩ {x | u x = t} : Set V))
        =ᵐ[surfaceMeasure V] ((S ∩ {x | u x = t} : Set V)) := by
      refine ae_eq_set.2 ⟨?_, measure_mono_null ?_ ht⟩
      · rw [Set.sdiff_eq_empty.2 hsub]
        exact measure_empty
      · intro x hx
        refine ⟨?_, hx.1.2⟩
        by_contra hne
        exact hx.2 ⟨⟨hx.1.1, hne⟩, hx.1.2⟩
    rw [Measure.restrict_congr_set haee]
  refine ⟨hmeasR.congr hslice, ?_⟩
  -- On the left the critical part contributes nothing: the gradient vanishes there.
  have hsplit : (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V))
      = ∫⁻ x in S ∩ {x : V | fderiv ℝ u x ≠ 0}, ‖gradient u x‖ₑ * g x
          ∂(volume : Measure V) := by
    have hSU : S = (S ∩ {x : V | fderiv ℝ u x ≠ 0}) ∪ (S ∩ {x : V | fderiv ℝ u x = 0}) := by
      ext x
      by_cases h : fderiv ℝ u x = 0 <;> simp [h]
    have hdisj : Disjoint (S ∩ {x : V | fderiv ℝ u x ≠ 0})
        (S ∩ {x : V | fderiv ℝ u x = 0}) :=
      Set.disjoint_left.2 fun x hx hx' => hx.2 hx'.2
    have hzero : (∫⁻ x in S ∩ {x : V | fderiv ℝ u x = 0}, ‖gradient u x‖ₑ * g x
        ∂(volume : Measure V)) = 0 := by
      have hfun : Set.EqOn (fun x : V => ‖gradient u x‖ₑ * g x) 0
          (S ∩ {x : V | fderiv ℝ u x = 0}) := by
        intro x hx
        have hfd : fderiv ℝ u x = 0 := hx.2
        have hgr : gradient u x = 0 := by rw [gradient, hfd]; simp
        simp [hgr]
      rw [setLIntegral_congr_fun (hS.inter hCmeas) hfun]
      simp
    conv_lhs => rw [hSU]
    rw [lintegral_union (hS.inter hCmeas) hdisj, hzero, add_zero]
  rw [hsplit, heqR]
  exact lintegral_congr_ae hslice

end SmoothCoarea

end FunctionalInequalities.KLS
