module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The rank stratification of the differential, and the kernel lemma

The critical set is stratified into measurable exact-rank layers. Linear algebra identifies the
kernel of the differential with that of its regular component.

The coarea critical set of a map into an `m`-dimensional target is
`{x | fderiv ℝ u x` is not surjective`}`, where the rank of the differential drops below `m`.
`Analysis/Vector/Slice/Critical.lean` handles the layer where the derivative *vanishes*; the route
for the remaining layers stratifies the critical set by the exact rank.

**rank stratification** makes the stratification usable: each stratum is measurable — Mathlib's
`isOpen_setOfPred_nat_le_rank` makes `{f | r ≤ rank f}` open, so a stratum is the difference of two
open sets, pulled back along the continuous derivative — and the critical set is the union of the
finitely many strata of rank `r < m`.

**the kernel identity** is the structural heart of the route, and is pure linear algebra.  If `P ∘
L` is already
surjective onto a space of the same dimension as the range of `L`, then `P` is injective on that
range, so `P ∘ L` and `L` have the *same* kernel.  In the route `L` is the differential at a point
of the stratum and `P` the orthogonal projection onto its range, so the conclusion is that the
differential vanishes along the fibre of the regular part `P ∘ u` — which is what lets the
Eilenberg bound be applied inside a fibre, at the exponent that finally matches.

No inner product, no measure and no completeness is used for the kernel identity; rank
stratification needs only continuity of
the derivative and the Borel structure of the domain.  The target is never assumed
positive-dimensional: with `finrank ℝ W = 0` every map is surjective, the critical set is empty and
the union over `r < 0` is empty too.
-/

@[expose] public section

noncomputable section

open Module Set

namespace FunctionalInequalities.Analysis

section Kernel

variable {V W W₁ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]

/-- The corestriction of `P` to the range of `L` is surjective as soon as `P ∘ L` is: its range is
the image of the range of `L`, which is exactly the range of `P ∘ L`. -/
theorem surjective_domRestrict_range_of_comp {L : V →L[ℝ] W} {P : W →L[ℝ] W₁}
    (h : Function.Surjective (P.comp L)) :
    Function.Surjective ((P : W →ₗ[ℝ] W₁).domRestrict (LinearMap.range (L : V →ₗ[ℝ] W))) := by
  intro w₁
  obtain ⟨z, hz⟩ := h w₁
  exact ⟨⟨L z, LinearMap.mem_range_self _ z⟩, hz⟩

section FiniteDimensional

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ W₁]

/--
**the kernel identity, kernel form.**  If `P ∘ L` is surjective onto a space whose dimension equals
the rank of
`L`, then `P` is injective on the range of `L` and the two kernels coincide.

The dimension hypothesis is exactly what rules out the degenerate reading: without it `P` may
collapse part of the range of `L` while `P ∘ L` stays surjective, and then `ker (P ∘ L)` is
strictly larger. -/
theorem ker_comp_eq_ker_of_finrank_range_eq {L : V →L[ℝ] W} {P : W →L[ℝ] W₁}
    (hsurj : Function.Surjective (P.comp L))
    (hrank : finrank ℝ W₁ = finrank ℝ (LinearMap.range (L : V →ₗ[ℝ] W))) :
    LinearMap.ker ((P.comp L : V →L[ℝ] W₁) : V →ₗ[ℝ] W₁) = LinearMap.ker (L : V →ₗ[ℝ] W) := by
  have hfin : FiniteDimensional ℝ (LinearMap.range (L : V →ₗ[ℝ] W)) :=
    FiniteDimensional.of_surjective (LinearMap.rangeRestrict (L : V →ₗ[ℝ] W))
      (LinearMap.surjective_rangeRestrict _)
  have hinj :
    Function.Injective ((P : W →ₗ[ℝ] W₁).domRestrict (LinearMap.range (L : V →ₗ[ℝ] W))) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank.symm).2
      (surjective_domRestrict_range_of_comp hsurj)
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · have hz' :
      ((P : W →ₗ[ℝ] W₁).domRestrict (LinearMap.range (L : V →ₗ[ℝ] W)))
          ⟨L z, LinearMap.mem_range_self _ z⟩ =
        0 :=
      hz
    have := hinj (hz'.trans (map_zero _).symm)
    simpa using congrArg Subtype.val this
  · have hz' : L z = 0 := hz
    simp [LinearMap.mem_ker, hz']

/--
**the kernel identity, the form the route consumes**: on the stratum the differential vanishes
wherever the
regular component does, that is, along the fibre directions of `P ∘ u`. -/
theorem apply_eq_zero_of_comp_apply_eq_zero (L : V →L[ℝ] W) (P : W →L[ℝ] W₁)
    (hsurj : Function.Surjective (P.comp L))
    (hrank : finrank ℝ W₁ = finrank ℝ (LinearMap.range (L : V →ₗ[ℝ] W))) (z : V)
    (hz : P (L z) = 0) : L z = 0 := by
  have hker := ker_comp_eq_ker_of_finrank_range_eq hsurj hrank
  have hmem : z ∈ LinearMap.ker ((P.comp L : V →L[ℝ] W₁) : V →ₗ[ℝ] W₁) := hz
  rw [hker] at hmem
  exact hmem

end FiniteDimensional

end Kernel

section Stratification

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

section RankStrata

omit [FiniteDimensional ℝ W]
/-- In finite dimensions the rank of a linear map is the `finrank` of its range, as a cardinal. -/
theorem rank_toLinearMap_eq (f : V →L[ℝ] W) :
    (f : V →ₗ[ℝ] W).rank = (finrank ℝ (LinearMap.range (f : V →ₗ[ℝ] W)) : Cardinal) :=
  (finrank_eq_rank ℝ (LinearMap.range (f : V →ₗ[ℝ] W))).symm

/-- A rank stratum of continuous linear maps is the difference of two open sets: the rank is an
integer, so `rank f = r` is `r ≤ rank f` together with the failure of `r + 1 ≤ rank f`. -/
theorem setOf_rank_eq (r : ℕ) :
    {f : V →L[ℝ] W | (f : V →ₗ[ℝ] W).rank = (r : Cardinal)}
      = {f : V →L[ℝ] W | (r : Cardinal) ≤ (f : V →ₗ[ℝ] W).rank}
          \ {f : V →L[ℝ] W | ((r + 1 : ℕ) : Cardinal) ≤ (f : V →ₗ[ℝ] W).rank} := by
  ext f
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, rank_toLinearMap_eq, Nat.cast_le, Nat.cast_inj]
  omega

end RankStrata

/-- A continuous linear map into a finite-dimensional target is surjective exactly when its rank is
the dimension of the target. -/
theorem surjective_iff_rank_eq (f : V →L[ℝ] W) :
    Function.Surjective f ↔ (f : V →ₗ[ℝ] W).rank = (finrank ℝ W : Cardinal) := by
  rw [rank_toLinearMap_eq, Nat.cast_inj]
  constructor
  · intro h
    rw [LinearMap.range_eq_top.2 h]
    exact finrank_top ℝ W
  · intro h
    exact LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq h)

/--
**rank stratification, second half: the critical set is the union of the strata of rank below the
dimension of
the target.**  A finite union, and no regularity of `u` is used: this is pointwise linear algebra.
With a zero-dimensional target both sides are empty. -/
theorem setOf_not_surjective_fderiv_eq_iUnion (u : V → W) :
    {x : V | ¬Function.Surjective (fderiv ℝ u x)} =
      ⋃ r ∈ Finset.range (finrank ℝ W),
        {x : V | (fderiv ℝ u x : V →ₗ[ℝ] W).rank = (r : Cardinal)} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
    surjective_iff_rank_eq, rank_toLinearMap_eq, Nat.cast_inj]
  have hle : finrank ℝ (LinearMap.range (fderiv ℝ u x : V →ₗ[ℝ] W)) ≤ finrank ℝ W :=
    Submodule.finrank_le _
  constructor
  · exact fun h => ⟨_, by omega, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    omega

variable [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ W] in
/--
**rank stratification, first half: the rank strata of the differential of a `C¹` map are
measurable.**

Mathlib's `isOpen_setOfPred_nat_le_rank` gives the lower semicontinuity of the rank; a stratum is
the difference of two of those open sets, pulled back along the continuous derivative.  No
measurable structure on the space of operators is needed. -/
theorem measurableSet_rank_fderiv_eq {u : V → W} (hu : ContDiff ℝ 1 u) (r : ℕ) :
    MeasurableSet {x : V | (fderiv ℝ u x : V →ₗ[ℝ] W).rank = (r : Cardinal)} := by
  have hcont : Continuous fun x : V => fderiv ℝ u x := hu.continuous_fderiv one_ne_zero
  have hpre :
    {x : V | (fderiv ℝ u x : V →ₗ[ℝ] W).rank = (r : Cardinal)} =
      (fun x : V => fderiv ℝ u x) ⁻¹' {f : V →L[ℝ] W | (f : V →ₗ[ℝ] W).rank = (r : Cardinal)} :=
    rfl
  rw [hpre, setOf_rank_eq, Set.preimage_sdiff]
  exact
    ((isOpen_setOfPred_nat_le_rank r).preimage hcont).measurableSet.diff
      ((isOpen_setOfPred_nat_le_rank (r + 1)).preimage hcont).measurableSet

end Stratification

end FunctionalInequalities.Analysis
