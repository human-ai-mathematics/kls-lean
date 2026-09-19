import FunctionalInequalities.Analysis.Vector.RankDeficient.Stratification
import FunctionalInequalities.Analysis.Vector.Slice.Critical
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the rank stratification and the kernel lemma

**What is proved.**  Exactly the route obligations `R1` and `R2` of
`research/audits/RankDeficientRouteStatements.lean`, whose three propositions are restated
**verbatim** below as `route_R1_measurable`, `route_R1_decomposition` and `route_R2` and discharged.
Nothing else on that list is proved: `R0`, `R3`–`R10`, `N1` and `N2` are still open, and so is the
rank-deficient part of the codimension-`m` coarea critical set.  **No coarea formula, no slicing
statement and no Sard theorem is proved here.**

**The rank hypothesis of `R2` is necessary, and that is exhibited rather than asserted.**
`rank_hypothesis_necessary` drops only the dimension hypothesis and gives a counterexample on the
plane: the identity of the plane composed with the first coordinate functional is surjective onto
`ℝ`, but the identity does not vanish on the kernel of that composite.  Without the hypothesis the
conclusion of `R2` is false.

**`m = 1` returns the proved scalar situation.**  `codimension_one_collapse` shows that for a
one-dimensional target the critical set is exactly the vanishing-derivative set, so the
stratification adds nothing in codimension one, and `codimension_one_critical_slices` derives the
`m = 1` case of the still-open `R0` from the proved
`ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero`.  This is a consequence of what was already
proved, not new coverage of the rank-deficient part, which is empty when `m = 1`.

**Boundary cases.**  A zero-dimensional target (every map surjective, both sides of the
decomposition empty), a zero-dimensional domain (every rank zero), a stratum index at or above the
dimension of the target (empty stratum), and a zero map with a zero-dimensional projection target
in `R2` are all covered.  No finiteness, inner product, completeness or measure hypothesis is used
by `R2`, and `R1`'s measurability half needs no finite-dimensionality of the target.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched.
-/

noncomputable section

open Set MeasureTheory Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace RankStratificationAudit

/-! ### The route obligations, restated verbatim and discharged -/

/-- **Route obligation `R1`, first half**, copied from
`research/audits/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_R1_measurable :
    (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      {u : V → W}, ContDiff ℝ 1 u → ∀ r : ℕ,
      MeasurableSet {x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)}) :=
  fun hu r => measurableSet_rank_fderiv_eq hu r

/-- **Route obligation `R1`, second half**, copied verbatim and discharged. -/
theorem route_R1_decomposition :
    (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      {u : V → W},
      {x : V | ¬ Function.Surjective (fderiv ℝ u x)}
        = ⋃ r ∈ Finset.range (finrank ℝ W),
            {x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)}) :=
  fun {_ _ _ _ _ _ _ _} {u} => setOf_not_surjective_fderiv_eq_iUnion u

/-- **Route obligation `R2`**, copied verbatim and discharged. -/
theorem route_R2 :
    (∀ {V W W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
      (L : V →L[ℝ] W) (P : W →L[ℝ] W₁), Function.Surjective (P.comp L) →
      finrank ℝ W₁ = finrank ℝ (LinearMap.range L.toLinearMap) →
      ∀ z : V, P (L z) = 0 → L z = 0) :=
  fun L P hsurj hrank z hz => apply_eq_zero_of_comp_apply_eq_zero L P hsurj hrank z hz

/-! ### `R2` says the two kernels agree, which is what the route consumes -/

section Kernel

variable {V W W₁ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [FiniteDimensional ℝ W₁]

/-- The kernel form, restated: on the stratum the fibre directions of the regular component are
exactly the kernel of the differential. -/
theorem kernels_agree {L : V →L[ℝ] W} {P : W →L[ℝ] W₁}
    (hsurj : Function.Surjective (P.comp L))
    (hrank : finrank ℝ W₁ = finrank ℝ (LinearMap.range (L : V →ₗ[ℝ] W))) :
    LinearMap.ker ((P.comp L : V →L[ℝ] W₁) : V →ₗ[ℝ] W₁) = LinearMap.ker (L : V →ₗ[ℝ] W) :=
  ker_comp_eq_ker_of_finrank_range_eq hsurj hrank

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W₁] in
/-- **A degenerate instance of `R2`**: the zero map with a zero-dimensional projection target.  The
composite is surjective onto a subsingleton and both ranks are `0`, so the hypotheses hold and the
conclusion is vacuous rather than false. -/
theorem zero_map_zero_target [Subsingleton W₁] (L : V →L[ℝ] W) (P : W →L[ℝ] W₁) :
    Function.Surjective (P.comp L) ∧ ∀ z : V, P (L z) = 0 := by
  refine ⟨fun w₁ => ⟨0, Subsingleton.elim _ _⟩, fun z => Subsingleton.elim _ _⟩

end Kernel

/-! ### The dimension hypothesis of `R2` is necessary -/

section Necessity

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate functional on the plane. -/
def coord₀ : Plane →L[ℝ] ℝ := innerSL ℝ (EuclideanSpace.single 0 (1 : ℝ))

@[simp] theorem coord₀_apply (x : Plane) :
    coord₀ x = (⟪EuclideanSpace.single 0 (1 : ℝ), x⟫ : ℝ) := rfl

/-- **Dropping only the dimension hypothesis makes `R2` false.**  Take `L` the identity of the plane
and `P` the first coordinate functional.  Then `P ∘ L` is surjective onto `ℝ`, but the rank of `L`
is `2` while `finrank ℝ ℝ = 1`, and the second basis vector lies in the kernel of `P ∘ L` without
lying in the kernel of `L`.

So `R2` is not a statement about surjectivity of the composite alone: it is exactly the assertion
that `P` does not collapse any of the range of `L`. -/
theorem rank_hypothesis_necessary :
    Function.Surjective (coord₀.comp (ContinuousLinearMap.id ℝ Plane)) ∧
      finrank ℝ ℝ ≠ finrank ℝ (LinearMap.range (ContinuousLinearMap.id ℝ Plane).toLinearMap) ∧
      ∃ z : Plane, coord₀ ((ContinuousLinearMap.id ℝ Plane) z) = 0 ∧
        (ContinuousLinearMap.id ℝ Plane) z ≠ 0 := by
  refine ⟨fun c => ⟨EuclideanSpace.single 0 c, ?_⟩, ?_, EuclideanSpace.single 1 (1 : ℝ), ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, coord₀_apply,
      EuclideanSpace.inner_single_left]
    simp
  · rw [LinearMap.range_eq_top.2 (fun x => ⟨x, rfl⟩)]
    simp [finrank_self, finrank_euclideanSpace]
  · rw [ContinuousLinearMap.id_apply, coord₀_apply, EuclideanSpace.inner_single_left]
    simp
  · intro h
    have := congrFun (congrArg (fun v : Plane => (WithLp.ofLp v)) h) 1
    simp at this

end Necessity

/-! ### Boundary cases of the stratification -/

section Boundary

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- **A zero-dimensional target makes every map surjective**, so the critical set is empty and so is
the union over `r < 0`.  This is why `R0` needs no positivity of the codimension. -/
theorem zero_dimensional_target [Subsingleton W] (u : V → W) :
    {x : V | ¬ Function.Surjective (fderiv ℝ u x)} = (∅ : Set V) ∧
      finrank ℝ W = 0 := by
  constructor
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact fun w => ⟨0, Subsingleton.elim _ _⟩
  · exact finrank_zero_of_subsingleton

omit [FiniteDimensional ℝ W] in
/-- **A zero-dimensional domain puts everything in the rank-zero stratum.** -/
theorem zero_dimensional_domain [Subsingleton V] (u : V → W) :
    {x : V | (fderiv ℝ u x : V →ₗ[ℝ] W).rank = (0 : Cardinal)} = (Set.univ : Set V) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, rank_toLinearMap_eq, Nat.cast_eq_zero,
    Submodule.finrank_eq_zero]
  refine le_antisymm (fun w hw => ?_) bot_le
  obtain ⟨z, rfl⟩ := hw
  rw [Subsingleton.elim z 0]
  simp

/-- **A stratum index at or above the dimension of the target is empty**: the rank of a map into `W`
never exceeds `finrank ℝ W`. -/
theorem stratum_empty_of_le {u : V → W} {r : ℕ} (hr : finrank ℝ W < r) :
    {x : V | (fderiv ℝ u x : V →ₗ[ℝ] W).rank = (r : Cardinal)} = (∅ : Set V) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, rank_toLinearMap_eq,
    Nat.cast_inj]
  have := Submodule.finrank_le (LinearMap.range (fderiv ℝ u x : V →ₗ[ℝ] W))
  omega

/-- **The strata are measurable with no finite-dimensionality of the target.** -/
theorem stratum_measurable_without_target_finrank {V' W' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    [MeasurableSpace V'] [BorelSpace V'] [NormedAddCommGroup W'] [NormedSpace ℝ W']
    {u : V' → W'} (hu : ContDiff ℝ 1 u) (r : ℕ) :
    MeasurableSet {x : V' | (fderiv ℝ u x : V' →ₗ[ℝ] W').rank = (r : Cardinal)} :=
  measurableSet_rank_fderiv_eq hu r

end Boundary

/-! ### `m = 1` returns the proved scalar situation -/

section CodimensionOne

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

omit [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W] in
/-- **For a one-dimensional target the critical set is exactly the vanishing-derivative set**, so
the rank stratification has a single layer and adds nothing in codimension one.  This is the set
identity behind the `m = 1` collapse recorded in the previous rounds. -/
theorem codimension_one_collapse (hm : finrank ℝ W = 1) (u : V → W) :
    {x : V | ¬ Function.Surjective (fderiv ℝ u x)} = {x : V | fderiv ℝ u x = 0} := by
  rw [setOf_not_surjective_fderiv_eq_iUnion, hm]
  ext x
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop, Set.mem_ofPred_eq,
    rank_toLinearMap_eq, Nat.cast_inj]
  constructor
  · rintro ⟨r, hr, hrk⟩
    have hr0 : r = 0 := by omega
    rw [hr0, Submodule.finrank_eq_zero] at hrk
    ext z
    have : (fderiv ℝ u x) z ∈ LinearMap.range (fderiv ℝ u x : V →ₗ[ℝ] W) :=
      LinearMap.mem_range_self _ z
    rw [hrk] at this
    simpa using this
  · intro h
    refine ⟨0, by omega, ?_⟩
    rw [Submodule.finrank_eq_zero]
    rw [h]
    simp

/-- **The `m = 1` case of the still-open `R0`, derived and not asserted.**  With a one-dimensional
target the critical set coincides with the vanishing-derivative set by
`codimension_one_collapse`, so the proved
`ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero` already gives the conclusion.

This closes **no part of the rank-deficient problem**: for `m = 1` the rank-deficient part is
empty, and the open case is `m ≥ 2`. -/
theorem codimension_one_critical_slices {u : V → W} (hu : ContDiff ℝ 1 u) {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hm : finrank ℝ W = 1) :
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) = 0 := by
  rw [codimension_one_collapse hm u]
  exact ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero hu hk (by omega)

end CodimensionOne

end RankStratificationAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.surjective_domRestrict_range_of_comp
#print axioms FunctionalInequalities.Analysis.ker_comp_eq_ker_of_finrank_range_eq
#print axioms FunctionalInequalities.Analysis.apply_eq_zero_of_comp_apply_eq_zero
#print axioms FunctionalInequalities.Analysis.rank_toLinearMap_eq
#print axioms FunctionalInequalities.Analysis.setOf_rank_eq
#print axioms FunctionalInequalities.Analysis.surjective_iff_rank_eq
#print axioms FunctionalInequalities.Analysis.setOf_not_surjective_fderiv_eq_iUnion
#print axioms FunctionalInequalities.Analysis.measurableSet_rank_fderiv_eq
#print axioms RankStratificationAudit.route_R1_measurable
#print axioms RankStratificationAudit.route_R1_decomposition
#print axioms RankStratificationAudit.route_R2
#print axioms RankStratificationAudit.kernels_agree
#print axioms RankStratificationAudit.zero_map_zero_target
#print axioms RankStratificationAudit.rank_hypothesis_necessary
#print axioms RankStratificationAudit.zero_dimensional_target
#print axioms RankStratificationAudit.zero_dimensional_domain
#print axioms RankStratificationAudit.stratum_empty_of_le
#print axioms RankStratificationAudit.stratum_measurable_without_target_finrank
#print axioms RankStratificationAudit.codimension_one_collapse
#print axioms RankStratificationAudit.codimension_one_critical_slices
