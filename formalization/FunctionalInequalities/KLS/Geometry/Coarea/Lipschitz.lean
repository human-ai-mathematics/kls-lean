import FunctionalInequalities.Analysis.Lipschitz.C1Pieces
import FunctionalInequalities.KLS.Geometry.Coarea.Smooth

/-! # Weighted coarea for Lipschitz functions

Exact C¹ pieces carry the C¹ coarea formula. Countable additivity sums the pieces;
null slicing removes their ambient-null complement from almost every level.
No boundedness, finite-volume, integrability, positive-dimension or SFinite surface-measure
assumption is imposed. The ENNReal weight may be identically infinity.

`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is the full-space specialization.
The sharp finite-regularity Sard theorem and its nonzero-derivative consequence are proved
separately in `Analysis/Sard/Sharp.lean`. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

namespace FunctionalInequalities.KLS

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **globally Lipschitz coarea**: weighted Lipschitz coarea, including almost-everywhere slice measurability. -/
theorem coarea_of_lipschitz {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞}
    (hu : LipschitzWith K u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  obtain ⟨C, v, hCm, hCd, hCnull, hv, hjet⟩ := Analysis.exists_contDiff_pieces hu
  let P : ℕ → Set V := fun n => S ∩ C n
  have hPm : ∀ n, MeasurableSet (P n) := fun n => hS.inter (hCm n)
  have hPd : Pairwise (fun i j => Disjoint (P i) (P j)) := fun i j hij =>
    (hCd hij).mono inter_subset_right inter_subset_right
  have hslices : ∀ n t, P n ∩ {x | v n x = t} = P n ∩ {x | u x = t} := by
    intro n t
    ext x
    constructor <;> rintro ⟨hx, ht⟩
    · exact ⟨hx, (hjet n x hx.2).2.1.symm.trans ht⟩
    · exact ⟨hx, (hjet n x hx.2).2.1.trans ht⟩
  have hformula : ∀ n,
      AEMeasurable (fun t : ℝ => ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) volume ∧
      (∫⁻ x in P n, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
        ∫⁻ t, ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V) := by
    intro n
    have h := coarea_of_contDiff (hv n) (hPm n) hg
    simp_rw [hslices n] at h
    refine ⟨h.1, ?_⟩
    rw [← h.2]
    apply setLIntegral_congr_fun (hPm n)
    intro x hx
    simp only [gradient, (hjet n x hx.2).2.2]
  have hset : S =ᵐ[(volume : Measure V)] (⋃ n, P n) := by
    apply ae_eq_set.2
    constructor
    · refine measure_mono_null (fun x hx => ?_) hCnull
      intro hxC
      obtain ⟨n, hn⟩ := mem_iUnion.1 hxC
      exact hx.2 (mem_iUnion.2 ⟨n, hx.1, hn⟩)
    · have hempty : (⋃ n, P n) \ S = ∅ := by
        apply sdiff_eq_empty.2
        exact iUnion_subset fun _ => inter_subset_left
      rw [hempty, measure_empty]
  have hslice : (fun t : ℝ => ∫⁻ y in (⋃ n, P n) ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      =ᵐ[(volume : Measure ℝ)] fun t : ℝ =>
        ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) := by
    filter_upwards [ae_surfaceMeasure_inter_levelSet_eq_zero
      (hu.lipschitzOnWith (s := (⋃ n, C n)ᶜ)) hCnull] with t ht
    have heq : (((⋃ n, P n) ∩ {x | u x = t} : Set V))
        =ᵐ[surfaceMeasure V] ((S ∩ {x | u x = t} : Set V)) := by
      apply ae_eq_set.2
      constructor
      · rw [sdiff_eq_empty.2 (inter_subset_inter_left _ (iUnion_subset fun _ => inter_subset_left)),
          measure_empty]
      · apply measure_mono_null _ ht
        intro x hx
        refine ⟨?_, hx.1.2⟩
        intro hxC
        obtain ⟨n, hn⟩ := mem_iUnion.1 hxC
        exact hx.2 ⟨mem_iUnion.2 ⟨n, hx.1.1, hn⟩, hx.1.2⟩
    rw [Measure.restrict_congr_set heq]
  refine ⟨aemeasurable_setLIntegral_inter_levelSet hu.continuous hu.lipschitzOnWith hS hg, ?_⟩
  calc
    _ = ∫⁻ x in ⋃ n, P n, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) := by
      rw [Measure.restrict_congr_set hset]
    _ = ∑' n, ∫⁻ x in P n, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) :=
      lintegral_iUnion hPm hPd _
    _ = ∑' n, ∫⁻ t, ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V) :=
      tsum_congr fun n => (hformula n).2
    _ = ∫⁻ t, ∑' n, ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V) :=
      (lintegral_tsum (fun n => (hformula n).1)).symm
    _ = ∫⁻ t, ∫⁻ y in (⋃ n, P n) ∩ {x | u x = t}, g y ∂(surfaceMeasure V) := by
      apply lintegral_congr
      intro t
      rw [iUnion_inter]
      exact (lintegral_iUnion (fun n => (hPm n).inter (hu.continuous.measurable (measurableSet_singleton t)))
        (fun i j hij => (hPd hij).mono inter_subset_left inter_subset_left) g).symm
    _ = _ := lintegral_congr_ae hslice

end FunctionalInequalities.KLS

namespace FunctionalInequalities

universe u

namespace Analysis

section Coarea

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

-- The section variables are kept so that the published interface is unchanged; `CompleteSpace V`
-- is what the statement's `gradient` elaborates against, and no other instance is narrowed away.
/-- **Weighted coarea formula** for a Lipschitz function on a finite-dimensional inner-product
space, with Lebesgue measure on `V` and the normalized surface measure `ℋ^{n-1}` on the level
sets: `∫ g ‖∇u‖ = ∫_ℝ (∫_{u = t} g dℋ^{n-1}) dt`.  The gradient is Mathlib's `gradient`, zero at
the points of non-differentiability (a null set by Rademacher's theorem). -/
theorem lintegral_enorm_gradient_mul_eq_lintegral_levelSet {u : V → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have h := (KLS.coarea_of_lipschitz (S := univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa only [setLIntegral_univ, univ_inter] using h

end Coarea

end Analysis

end FunctionalInequalities
