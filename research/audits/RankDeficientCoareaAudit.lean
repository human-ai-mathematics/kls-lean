import FunctionalInequalities.Analysis.Vector.RankDeficient.Coarea
import FunctionalInequalities.Analysis.Vector.Slice.Critical
import FunctionalInequalities.Analysis.Coarea.Smooth
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the rank-deficient critical set and the codimension-`m` coarea formula

**What is proved.**  Route obligations `R8`, **`R0`** and **`R9`** of
`research/audits/RankDeficientRouteStatements.lean`, restated **verbatim** below as `route_R8`,
`route_R0` and `route_R9` and discharged.  With `R1`–`R7` that is ten of the route's thirteen
numbered items, and it closes the rank-deficient part of the codimension-`m` coarea critical set:
**the general codimension-`m` coarea formula for `C¹` maps is proved.**

**Other route items.** `R10` is the equidimensional sanity check; `N1` and `N2` diagnose the
exponent obstruction rather than supplying steps of this client. Their contracts are recorded in
`research/audits/RankDeficientRouteStatements.lean`.

**This is not a Sard theorem.**  `no_sard_claimed` records what is and is not asserted: `R0` is
about the measure of the critical set **inside a level**, and nothing whatever is claimed about the
measure of the set of critical *values*, which for a merely `C¹` map may well be positive.  The
finite-regularity Sard theorem has separate source `Analysis/Sard/Sharp.lean` and client
`research/audits/SharpSardAudit.lean`.

**Comparison with the vanishing-derivative hypothesis.** `strictly_extends_conditional` derives
`coarea_of_contDiff_of_critical_eq_zeroDeriv` from the general formula, and
`rank_deficient_witness_now_covered` shows the rank-one projection of the plane — the witness that
the old hypothesis fails at every point — is covered by `R0`.

**`m = 1` returns the proved scalar statements.**  `scalar_L10` recovers
`KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` and `scalar_L11`
`KLS.coarea_of_contDiff`, both with the extra `1 ≤ finrank V` that the codimension-`m` bookkeeping
forces, recorded rather than hidden.

**Boundary cases.**  A zero-dimensional target — where every map is surjective, the critical set is
empty and no positivity of the codimension is needed — and a constant map are covered.

The current coarea source is `Analysis/Vector/RankDeficient/Coarea.lean`. Cheeger comparisons and
energy identifications are outside this client's scope.
-/

noncomputable section

open MeasureTheory Set Module Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace RankDeficientCoareaAudit

/-! ### The route obligations, restated verbatim and discharged -/

/-- **Route obligation `R8`**, copied verbatim and discharged. -/
theorem route_R8 :
    (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
      {u : V → W} {A : Set V} {k : ℕ},
      (∀ x₀ ∈ A, ∃ U ∈ nhds x₀, ∀ᵐ t ∂(volume : Measure W),
          μH[(k : ℝ)] (A ∩ U ∩ {x : V | u x = t}) = 0) →
      ∀ᵐ t ∂(volume : Measure W), μH[(k : ℝ)] (A ∩ {x : V | u x = t}) = 0) :=
  fun h => ae_hausdorffMeasure_inter_levelSet_eq_zero_of_local h

/-- **Route obligation `R0`, the target of the whole route**, copied verbatim and discharged. -/
theorem route_R0 :
    (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
      {u : V → W} {k : ℕ}, ContDiff ℝ 1 u → k + finrank ℝ W = finrank ℝ V →
      ∀ᵐ t ∂(volume : Measure W),
        μH[(k : ℝ)] ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) = 0) :=
  fun hu hk => ae_hausdorffMeasure_critical_inter_levelSet_eq_zero hu hk

/-- **Route obligation `R9`**, copied verbatim and discharged.  The proved statement does not need
the route's `0 < finrank ℝ W`, which is therefore discharged by ignoring it. -/
theorem route_R9 :
    (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
      {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ},
      k + finrank ℝ W = finrank ℝ V → 0 < finrank ℝ W → ContDiff ℝ 1 u →
      MeasurableSet S → Measurable g →
      AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
          (volume : Measure W) ∧
        (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
              ∂(volume : Measure W))) :=
  fun hk _ hu hS hg => coarea_of_contDiff hk hu hS hg

/-! ### Comparison with the vanishing-derivative hypothesis -/

section Extends

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **The previously proved conditional formula is a corollary**: its dichotomy hypothesis is simply
dropped. -/
theorem strictly_extends_conditional {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hu : ContDiff ℝ 1 u)
    (_hcrit : ∀ x : V, coareaJacobian (fderiv ℝ u x) ≠ 0 ∨ fderiv ℝ u x = 0)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
          ∂(volume : Measure W)) :=
  coarea_of_contDiff hk hu hS hg

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
/-- **No Sard theorem is claimed.**  `R0` bounds the critical set *inside a level*; it says nothing
about the set of critical values.  This records the distinction: the conclusion is an assertion
about `μH[k]` of a slice, and the set of critical values does not appear in it. -/
theorem no_sard_claimed (u : V → W) (t : W) :
    {x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}
      ⊆ {x : V | ¬ Function.Surjective (fderiv ℝ u x)} :=
  Set.inter_subset_left

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
/-- **A zero-dimensional target needs no positivity hypothesis**: every linear map into it is
surjective, so the critical set is empty. -/
theorem zero_dimensional_target [Subsingleton W] (u : V → W) :
    {x : V | ¬ Function.Surjective (fderiv ℝ u x)} = (∅ : Set V) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact fun w => ⟨0, Subsingleton.elim _ _⟩

end Extends

/-! ### The rank-deficient witness is now covered -/

section Witness

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The rank-one orthogonal projection of the plane onto its first axis: the witness that the
previously proved conditional formula's hypothesis fails at every point. -/
def proj₀ : Plane →L[ℝ] Plane :=
  (innerSL ℝ (EuclideanSpace.single 0 (1 : ℝ))).smulRight (EuclideanSpace.single 0 (1 : ℝ))

/-- **The witness is covered.**  For the rank-one projection of the plane the derivative is nowhere
zero and nowhere surjective, so the vanishing-derivative set is empty and the critical set is
everything; the earlier conditional formula says nothing about it, and `R0` does. -/
theorem rank_deficient_witness_now_covered :
    ∀ᵐ t ∂(volume : Measure Plane),
      μH[((0 : ℕ) : ℝ)]
        ({x : Plane | ¬ Function.Surjective (fderiv ℝ (proj₀ : Plane → Plane) x)}
          ∩ {x : Plane | proj₀ x = t}) = 0 := by
  refine ae_hausdorffMeasure_critical_inter_levelSet_eq_zero proj₀.contDiff ?_
  simp [finrank_euclideanSpace]

end Witness

/-! ### `m = 1` returns the proved scalar statements -/

section CodimensionOne

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **`m = 1` is the proved scalar `L10`**, with the extra `1 ≤ finrank V` that the codimension-`m`
bookkeeping forces, recorded rather than hidden. -/
theorem scalar_L10 {u : V → ℝ} (hn : 1 ≤ finrank ℝ V) (hu : ContDiff ℝ 1 u) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      μH[((finrank ℝ V - 1 : ℕ) : ℝ)]
        ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) = 0 := by
  refine ae_hausdorffMeasure_critical_inter_levelSet_eq_zero hu ?_
  rw [finrank_self]
  omega

/-- **`m = 1` is the proved scalar `L11`**, `KLS.coarea_of_contDiff`, reproduced from the
codimension-`m` version with no hypothesis on the critical set. -/
theorem scalar_L11 {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞} (hn : 1 ≤ finrank ℝ V)
    (hu : ContDiff ℝ 1 u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ)) := by
  have hk : (finrank ℝ V - 1) + finrank ℝ ℝ = finrank ℝ V := by rw [finrank_self]; omega
  obtain ⟨hmeas, heq⟩ := coarea_of_contDiff (V := V) (W := ℝ) (S := S) (g := g) hk hu hS hg
  have hdens : ∀ x : V, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) = ‖gradient u x‖ₑ := by
    intro x
    rw [coareaJacobian_fderiv, ofReal_norm]
  simp_rw [hdens] at heq
  exact ⟨hmeas, heq⟩

end CodimensionOne

end RankDeficientCoareaAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero_of_local
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_critical_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.Analysis.ae_hausdorffNormalized_critical_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.Analysis.coarea_of_contDiff
#print axioms RankDeficientCoareaAudit.route_R8
#print axioms RankDeficientCoareaAudit.route_R0
#print axioms RankDeficientCoareaAudit.route_R9
#print axioms RankDeficientCoareaAudit.strictly_extends_conditional
#print axioms RankDeficientCoareaAudit.no_sard_claimed
#print axioms RankDeficientCoareaAudit.zero_dimensional_target
#print axioms RankDeficientCoareaAudit.rank_deficient_witness_now_covered
#print axioms RankDeficientCoareaAudit.scalar_L10
#print axioms RankDeficientCoareaAudit.scalar_L11
