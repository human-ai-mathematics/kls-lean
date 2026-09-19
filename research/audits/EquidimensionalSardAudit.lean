import FunctionalInequalities.Analysis.Sard.Equidimensional
import FunctionalInequalities.Analysis.Vector.RankDeficient.Coarea
import FunctionalInequalities.Analysis.Sard.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the equidimensional degenerate case `R10`

**What is proved.**  Route obligation `R10` of `research/audits/RankDeficientRouteStatements.lean`,
restated **verbatim** below as `route_R10` and discharged.  With `R0`–`R9` that is eleven of the
route's thirteen numbered items; the two that remain, `N1` and `N2`, are diagnostics of the
obstruction and are **not** proved here.  They are handled in
`research/audits/ExponentObstructionAudit.lean`, where `N1` is left open and `N2` is proved **false
as written**, with a repaired statement in its place; none of that is used below.

**`R10` is not a Sard theorem, and is not progress on the route.**  The route record states it
explicitly and this audit repeats it.  Two separate points:

* *Not a Sard theorem.*  Sard's theorem concerns the measure of the set of critical **values** of a
  map `ℝⁿ → ℝᵐ`.  What is proved here is the case `n = m` alone, where a singular differential is
  volume-contracting and Mathlib already supplies the statement for self-maps.  The sharp
  finite-regularity Sard theorem is the direct hole `FunctionalInequalities.Analysis.sard` in
  `KLS/WIP/AnalyticPrerequisites.lean`: real-valued `u` on a space of **any** dimension `n`, at
  regularity `C^n`.  That hole is untouched; nothing in this file imports it or weakens it, and its
  status is unchanged.  `r10_reaches_only_dimension_one` records the exact overlap: against a
  real-valued target `R10` applies only when `finrank ℝ V = 1`, and that case was already proved
  unconditionally by `Analysis.sard_of_finrank_le_one`, which uses the same Mathlib lemma.
  `sard_dimension_one_recovered` carries out the recovery, so the overlap is exhibited rather than
  asserted.  For `n ≥ 2` nothing here says anything.
* *Not a step towards `R0`.*  `R0` was proved independently in `Analysis/Vector/RankDeficient/Coarea.lean`
  by the stratification route, which never specializes to `n = m`.  `R10` is a consistency check
  run after the fact.  `Analysis/Sard/Equidimensional.lean` imports no part of that route, so the
  check is genuinely independent: `equidimensional_R0_of_R10` and `equidimensional_R10_of_R0`
  derive each statement from the other in the case `n = m`, where they are equivalent because
  `μH[0]` of a nonempty set is at least `1`.

**Boundary cases.**  `zero_dimensional` (both spaces trivial: every linear map is surjective, the
critical set is empty), `constant_map` (the differential vanishes identically, so every point is
critical and the whole image is one point), and `regular_map` (`n = m` with an everywhere
invertible differential, where the critical set is empty and the conclusion is vacuous) are all
checked.

**Untouched.**  The two Cheeger comparisons, the five Energy holes, and the dimension-free KLS
conjecture are not referred to here.
-/

noncomputable section

open MeasureTheory Set Module Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace EquidimensionalSardAudit

/-! ### The route obligation, restated verbatim and discharged -/

/-- **Route obligation `R10`**, copied verbatim from
`research/audits/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_R10 :
    (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
      {u : V → W}, ContDiff ℝ 1 u → finrank ℝ V = finrank ℝ W →
      ∀ᵐ t ∂(volume : Measure W),
        {x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t} = ∅) :=
  fun hu h => ae_critical_inter_levelSet_eq_empty hu h

/-! ### Agreement with the independently proved `R0` -/

section Agreement

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- `R10` gives the `n = m` reading of `R0`: an empty slice is `ℋ^0`-null. -/
theorem equidimensional_R0_of_R10 {u : V → W} (hu : ContDiff ℝ 1 u)
    (h : finrank ℝ V = finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W),
      μH[((0 : ℕ) : ℝ)]
        ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) = 0 := by
  filter_upwards [ae_critical_inter_levelSet_eq_empty hu h] with t ht
  rw [ht, measure_empty]

/-- Conversely the independently proved `R0` gives `R10`, because `μH[0]` of a nonempty set is at
least `1`.  In the equidimensional case the two statements are therefore equivalent, and the two
proofs — the stratification route and Mathlib's self-map lemma — agree. -/
theorem equidimensional_R10_of_R0 {u : V → W} (hu : ContDiff ℝ 1 u)
    (h : finrank ℝ V = finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W),
      {x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t} = ∅ := by
  have hk : 0 + finrank ℝ W = finrank ℝ V := by omega
  filter_upwards [ae_hausdorffMeasure_critical_inter_levelSet_eq_zero (k := 0) hu hk] with t ht
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  have h1 : (1 : ℝ≥0∞) ≤ μH[(0 : ℝ)]
      ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) :=
    Measure.one_le_hausdorffMeasure_zero_of_nonempty ⟨x, hx⟩
  rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) from Nat.cast_zero] at ht
  rw [ht] at h1
  exact absurd h1 (by simp)

end Agreement

/-! ### Where this sits relative to the sharp Sard hole -/

section SardBoundary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Against a real-valued target, a linear functional fails to be surjective exactly when it
vanishes; this is what lets the equidimensional statement be compared with `Analysis.sard`. -/
theorem not_surjective_iff_eq_zero (L : V →L[ℝ] ℝ) :
    ¬ Function.Surjective L ↔ L = 0 := by
  constructor
  · intro h
    by_contra hL
    refine h fun r => ?_
    obtain ⟨v, hv⟩ : ∃ v : V, L v ≠ 0 := by
      by_contra hall
      exact hL (by ext v; simpa using not_not.1 (not_exists.1 hall v))
    exact ⟨(r / L v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩
  · rintro rfl h
    obtain ⟨v, hv⟩ := h 1
    simp at hv

omit [FiniteDimensional ℝ V] in
/-- **The overlap with the sharp Sard hole is exactly dimension one.**  `R10` applies to a
real-valued map only when `finrank ℝ V = finrank ℝ ℝ = 1`. -/
theorem r10_reaches_only_dimension_one (h : finrank ℝ V = finrank ℝ ℝ) : finrank ℝ V = 1 := by
  simpa using h

/-- **And in dimension one it recovers what is already proved.**  `Analysis.sard_of_finrank_le_one`
proves this case unconditionally, by the same Mathlib lemma; the sharp `Analysis.sard` for
`finrank ℝ V ≥ 2` is a direct hole and is not addressed. -/
theorem sard_dimension_one_recovered [MeasurableSpace V] [BorelSpace V] {u : V → ℝ}
    (hdim : finrank ℝ V = 1) (hu : ContDiff ℝ 1 u) :
    (volume : Measure ℝ) (u '' {x : V | fderiv ℝ u x = 0}) = 0 := by
  have hset : {x : V | fderiv ℝ u x = 0}
      = {x : V | ¬ Function.Surjective (fderiv ℝ u x)} := by
    ext x
    simp [not_surjective_iff_eq_zero]
  rw [hset]
  exact measure_image_critical_eq_zero hu (by simp [hdim])

end SardBoundary

/-! ### Boundary cases -/

section Boundary

/-- **Both spaces zero-dimensional.**  Every linear map into a subsingleton is surjective, so the
critical set is empty and every level meets it in `∅`. -/
theorem zero_dimensional {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Subsingleton W]
    (u : V → W) (t : W) :
    {x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro x ⟨hx, -⟩
  exact hx fun w => ⟨0, Subsingleton.elim _ _⟩

/-- **A constant map.**  The differential vanishes identically, so with a positive-dimensional
target every point is critical; the conclusion still holds because the whole image is a single
point, which is Lebesgue-null. -/
theorem constant_map (c : ℝ) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      {x : ℝ | ¬ Function.Surjective (fderiv ℝ (fun _ : ℝ => c) x)}
        ∩ {x : ℝ | (fun _ : ℝ => c) x = t} = ∅ :=
  ae_critical_inter_levelSet_eq_empty (contDiff_const) rfl

/-- The constant map really is critical everywhere: the boundary case above is not vacuous. -/
theorem constant_map_critical_everywhere (c : ℝ) :
    {x : ℝ | ¬ Function.Surjective (fderiv ℝ (fun _ : ℝ => c) x)} = Set.univ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro h
  obtain ⟨y, hy⟩ := h 1
  simp at hy

/-- **`n = m` with an everywhere regular differential.**  The critical set is empty, so the
conclusion holds for *every* level, not merely almost every one. -/
theorem regular_map {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (t : V) :
    {x : V | ¬ Function.Surjective (fderiv ℝ (id : V → V) x)} ∩ {x : V | id x = t} = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro x ⟨hx, -⟩
  exact hx (by simpa [fderiv_id] using Function.surjective_id)

end Boundary

end EquidimensionalSardAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.det_eq_zero_of_not_surjective
#print axioms FunctionalInequalities.Analysis.measure_image_critical_eq_zero
#print axioms FunctionalInequalities.Analysis.ae_critical_inter_levelSet_eq_empty
#print axioms EquidimensionalSardAudit.route_R10
#print axioms EquidimensionalSardAudit.equidimensional_R0_of_R10
#print axioms EquidimensionalSardAudit.equidimensional_R10_of_R0
#print axioms EquidimensionalSardAudit.not_surjective_iff_eq_zero
#print axioms EquidimensionalSardAudit.r10_reaches_only_dimension_one
#print axioms EquidimensionalSardAudit.sard_dimension_one_recovered
#print axioms EquidimensionalSardAudit.zero_dimensional
#print axioms EquidimensionalSardAudit.constant_map
#print axioms EquidimensionalSardAudit.constant_map_critical_everywhere
#print axioms EquidimensionalSardAudit.regular_map
