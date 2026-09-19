import FunctionalInequalities.Analysis.Lipschitz.VectorPieces
import FunctionalInequalities.Analysis.Vector.RankDeficient.Coarea
import FunctionalInequalities.Analysis.Vector.Slice.Measurable

/-! # The codimension-`m` coarea formula for Lipschitz maps

`Analysis/Vector/RankDeficient/Coarea.lean` proves the codimension-`m` coarea formula
`coarea_of_contDiff` for **`C¹`** maps with no hypothesis on the critical set.  Federer's coarea
formula holds for merely **Lipschitz** maps, and this module makes that step, exactly as
`KLS/Geometry/Coarea/Lipschitz.lean` did in codimension one:

* `ae_hausdorffNormalized_inter_levelSet_eq_zero_of_volume_eq_zero` — a Lebesgue-null set is
  `ℋ^k`-null in almost every level, the codimension-`m` null slicing in the form the assembly
  consumes;
* `coarea_of_lipschitz_of_pieces` — the assembly: on each `C¹` piece of `Analysis/Lipschitz/
  VectorPieces.lean` the `C¹` formula applies, first-order agreement identifies its density and its
  slice with those of `u`, the pieces are disjoint and measurable so both sides add up, and the
  null complement disappears from almost every level;
* `coarea_of_lipschitz` — the target, `coarea_of_contDiff` with `ContDiff ℝ 1 u` replaced by
  `LipschitzWith K u` and nothing else changed.

The density is still written `coareaJacobian (fderiv ℝ u x)`: `fderiv` is junk at the points of
non-differentiability, which form a Lebesgue-null set by Rademacher's theorem, so the integrand is
unaffected almost everywhere — the convention the scalar formula uses for `gradient`.

No finiteness, boundedness, integrability or regular-value hypothesis is used, `S` is an arbitrary
Borel set, `g` an arbitrary measurable `ℝ≥0∞` weight, and no positivity of the codimension is
required.  **It is not a Sard theorem**: nothing is claimed about the measure of the set of
critical values.  The **locally** Lipschitz statement is not proved here.
-/

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **`V2`: a Lebesgue-null set has null slices in almost every level, in codimension `m`.**  Under
`k + m = n` the hypothesis of `ae_hausdorffNormalized_inter_levelSet_eq_zero_vector` at `d = k` is
Lebesgue-nullity, through the identification of the top normalized Hausdorff measure with Lebesgue
measure.  Only a Lipschitz bound on `u` is used; no regularity. -/
theorem ae_hausdorffNormalized_inter_levelSet_eq_zero_of_volume_eq_zero {u : V → W} {N : Set V}
    {K : ℝ≥0} {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V) (hu : LipschitzWith K u)
    (hN : (volume : Measure V) N = 0) :
    ∀ᵐ t ∂(volume : Measure W), KLS.hausdorffNormalized V k (N ∩ {x : V | u x = t}) = 0 := by
  refine ae_hausdorffNormalized_inter_levelSet_eq_zero_vector (K := K) hu.lipschitzOnWith ?_
  rw [hk]
  exact hausdorffNormalized_finrank_eq_zero_of_volume_eq_zero hN

/-- **`V5`: the assembly.**  Given exact `C¹` pieces of `u` — countably many disjoint measurable
sets with conull union, each carrying a `C¹` map agreeing with `u` in value and in differential —
the codimension-`m` coarea formula for `u` follows from the `C¹` one by countable additivity.

The hypothesis is literally the conclusion of `exists_contDiff_pieces_vector`, so that the Lipschitz
formula is that theorem composed with this one. -/
theorem coarea_of_lipschitz_of_pieces {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hu : LipschitzWith K u)
    (hS : MeasurableSet S) (hg : Measurable g)
    (hpieces : ∃ (P : ℕ → Set V) (v : ℕ → V → W),
      (∀ j, MeasurableSet (P j)) ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (volume : Measure V) (⋃ j, P j)ᶜ = 0 ∧ (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ P j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
          ∂(volume : Measure W)) := by
  obtain ⟨C, v, hCm, hCd, hCnull, hv, hjet⟩ := hpieces
  set ν : Measure V := KLS.hausdorffNormalized V k
  set P : ℕ → Set V := fun n => S ∩ C n with hP
  have hPm : ∀ n, MeasurableSet (P n) := fun n => hS.inter (hCm n)
  have hPd : Pairwise (fun i j => Disjoint (P i) (P j)) := fun i j hij =>
    (hCd hij).mono inter_subset_right inter_subset_right
  have hslices : ∀ n t, P n ∩ {x : V | v n x = t} = P n ∩ {x : V | u x = t} := by
    intro n t
    ext x
    constructor <;> rintro ⟨hx, ht⟩
    · exact ⟨hx, (hjet n x hx.2).2.1.symm.trans ht⟩
    · exact ⟨hx, (hjet n x hx.2).2.1.trans ht⟩
  have hformula : ∀ n,
      AEMeasurable (fun t : W => ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν)
        (volume : Measure W) ∧
      (∫⁻ x in P n, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V))
        = ∫⁻ t, ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) := by
    intro n
    have h := coarea_of_contDiff hk (hv n) (hPm n) hg
    simp_rw [hslices n] at h
    refine ⟨h.1, ?_⟩
    rw [← h.2]
    refine setLIntegral_congr_fun (hPm n) fun x hx => ?_
    rw [(hjet n x hx.2).2.2]
  have hset : S =ᵐ[(volume : Measure V)] (⋃ n, P n) := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => ?_) hCnull, ?_⟩
    · intro hxC
      obtain ⟨n, hn⟩ := mem_iUnion.1 hxC
      exact hx.2 (mem_iUnion.2 ⟨n, hx.1, hn⟩)
    · have hempty : (⋃ n, P n) \ S = ∅ :=
        sdiff_eq_empty.2 (iUnion_subset fun _ => inter_subset_left)
      rw [hempty, measure_empty]
  have hslice : (fun t : W => ∫⁻ y in (⋃ n, P n) ∩ {x : V | u x = t}, g y ∂ν)
      =ᵐ[(volume : Measure W)] fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂ν := by
    filter_upwards [ae_hausdorffNormalized_inter_levelSet_eq_zero_of_volume_eq_zero hk hu hCnull]
      with t ht
    have heq : (((⋃ n, P n) ∩ {x : V | u x = t} : Set V))
        =ᵐ[ν] ((S ∩ {x : V | u x = t} : Set V)) := by
      refine ae_eq_set.2 ⟨?_, measure_mono_null (fun x hx => ?_) ht⟩
      · rw [sdiff_eq_empty.2 (inter_subset_inter_left _
          (iUnion_subset fun _ => inter_subset_left)), measure_empty]
      · refine ⟨?_, hx.1.2⟩
        intro hxC
        obtain ⟨n, hn⟩ := mem_iUnion.1 hxC
        exact hx.2 ⟨mem_iUnion.2 ⟨n, hx.1.1, hn⟩, hx.1.2⟩
    rw [Measure.restrict_congr_set heq]
  refine ⟨aemeasurable_setLIntegral_inter_levelSet_vector hk hu.continuous hu.lipschitzOnWith
    hS hg, ?_⟩
  calc
    _ = ∫⁻ x in ⋃ n, P n, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V) := by rw [Measure.restrict_congr_set hset]
    _ = ∑' n, ∫⁻ x in P n, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V) := lintegral_iUnion hPm hPd _
    _ = ∑' n, ∫⁻ t, ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
        tsum_congr fun n => (hformula n).2
    _ = ∫⁻ t, ∑' n, ∫⁻ y in P n ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) :=
        (lintegral_tsum fun n => (hformula n).1).symm
    _ = ∫⁻ t, ∫⁻ y in (⋃ n, P n) ∩ {x : V | u x = t}, g y ∂ν ∂(volume : Measure W) := by
        refine lintegral_congr fun t => ?_
        rw [iUnion_inter]
        exact (lintegral_iUnion (fun n => (hPm n).inter
          (hu.continuous.measurable (measurableSet_singleton t)))
          (fun i j hij => (hPd hij).mono inter_subset_left inter_subset_left) g).symm
    _ = _ := lintegral_congr_ae hslice

/-- **`L0`: the codimension-`m` coarea formula for Lipschitz maps.**  Exactly
`coarea_of_contDiff` with `ContDiff ℝ 1 u` replaced by `LipschitzWith K u`; the density
`coareaJacobian (fderiv ℝ u x)` is unchanged, `fderiv` being junk on the Lebesgue-null set of
non-differentiability.

No hypothesis on the critical set, no finiteness, boundedness, integrability or regular-value
hypothesis, and no positivity of the codimension.  **It is not a Sard theorem.** -/
theorem coarea_of_lipschitz {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hu : LipschitzWith K u)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
          ∂(volume : Measure W)) :=
  coarea_of_lipschitz_of_pieces hk hu hS hg (exists_contDiff_pieces_vector hu)

end FunctionalInequalities.Analysis
