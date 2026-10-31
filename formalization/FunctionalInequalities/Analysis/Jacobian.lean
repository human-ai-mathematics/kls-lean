module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Haar image bounds from almost-everywhere derivatives

A genuine measurable good set and null hull let Mathlib's pointwise Jacobian
inequality use actual AE derivatives. A proved null-image property removes the
bad image. The map need not be continuous or convex, the source need not have
finite measure, and the image need not be measurable. The real normed space
has finite dimension, including zero; no inner product or Nontrivial premise.

Real consumers are residual contact gradients and generated Lipschitz-gradient
Moreau regularizers for Letwin arXiv2607.24164v1 Lemma2.2 via BB1207.6128v1
Theorem2.24(ii). The latter source generates its derivative and null-image data.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FunctionalInequalities.Analysis
/-- A Haar image bound from actual a.e. derivatives with bounded absolute
 determinant and an actual null-image property. No image measurability or
 finite volume is assumed, and no set volume is canceled. -/
theorem addHaar_image_le_mul_of_ae_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [Measure.IsAddHaarMeasure μ] {F : E → E} {Γ : Set E} (hΓ : MeasurableSet Γ) {K : ℝ}
    (hAE : ∀ᵐ x ∂(μ.restrict Γ), ∃ D : E →L[ℝ] E, HasFDerivAt F D x ∧ |D.det| ≤ K)
    (hN : ∀ N : Set E, N ⊆ Γ → μ N = 0 → μ (F '' N) = 0) :
    μ (F '' Γ) ≤ ENNReal.ofReal K * μ Γ := by
  classical
  let P : E → Prop := fun x => ∃ D : E →L[ℝ] E, HasFDerivAt F D x ∧ |D.det| ≤ K
  have hAE' : ∀ᵐ x ∂μ, x ∈ Γ → P x := (ae_restrict_iff' hΓ).mp hAE
  let B : Set E := {x | ¬(x ∈ Γ → P x)}
  have hB : μ B = 0 := ae_iff.mp hAE'
  let Z := toMeasurable μ B
  have hZ : MeasurableSet Z := measurableSet_toMeasurable μ B
  have hBZ : B ⊆ Z := subset_toMeasurable μ B
  have hZ0 : μ Z = 0 := by dsimp [Z]; rw [measure_toMeasurable]; exact hB
  let S := Γ \ Z
  have hS : MeasurableSet S := hΓ.diff hZ
  have hs : ∀ x ∈ S, P x := by
    intro x hx
    by_contra h
    exact hx.2 (hBZ (show x ∈ B from fun hh => h (hh hx.1)))
  have hd : ∀ x, ∃ D : E →L[ℝ] E, x ∈ S → HasFDerivAt F D x ∧ |D.det| ≤ K := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨D, hD⟩ := hs x hx
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => (hx h).elim⟩
  choose D hD using hd
  have hgood : μ (F '' S) ≤ ENNReal.ofReal K * μ S := by
    calc
      _ ≤ ∫⁻ x in S, ENNReal.ofReal |(D x).det| ∂μ :=
        addHaar_image_le_lintegral_abs_det_fderiv μ hS
          (fun x hx => (hD x hx).1.hasFDerivWithinAt)
      _ ≤ ∫⁻ _ in S, ENNReal.ofReal K ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hS] with x hx
        exact ENNReal.ofReal_le_ofReal (hD x hx).2
      _ = _ := by simp
  have hbad : μ (F '' (Γ ∩ Z)) = 0 :=
    hN _ inter_subset_left (measure_mono_null inter_subset_right hZ0)
  have hsplit : Γ = S ∪ (Γ ∩ Z) := by
    ext x;
    simp only [S, mem_union, Set.mem_sdiff, mem_inter_iff]; tauto
  calc
    _ = μ ((F '' S) ∪ (F '' (Γ ∩ Z))) := by conv_lhs => rw [hsplit, image_union]
    _ ≤ μ (F '' S) + μ (F '' (Γ ∩ Z)) := measure_union_le _ _
    _ = μ (F '' S) := by rw [hbad, add_zero]
    _ ≤ ENNReal.ofReal K * μ S := hgood
    _ ≤ _ := mul_le_mul le_rfl (measure_mono sdiff_subset) bot_le bot_le

end FunctionalInequalities.Analysis
