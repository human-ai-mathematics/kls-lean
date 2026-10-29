import FunctionalInequalities.Energy.Euclidean.Slope.Density
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Scope audit for the density module `Energy/Euclidean/Slope/Density.lean`

This client uses `Energy/Euclidean/Slope/Density.lean` to discharge
the five propositions `C1`, `C2`, `C4`, `C5`, `C6` of the route file
`research/audits/Energy/SlopeRouteStatements.lean` from it.  The propositions are restated
**verbatim** from the route file as `route_C1`, `route_C2`, `route_C4`, `route_C5`, `route_C6`;
each is proved by a **named** application of the library lemma, so a renamed binder or a reordered
hypothesis would fail to elaborate here.

`route_C6` is the reverse inequality `SmoothGradient.relaxation ν ≤ LocalSlope.relaxation ν` for
**every** Borel probability law, singular laws included. It is the density input to
`Energy/Cheeger/Identification.lean`, without an absolute-continuity hypothesis.  The library
lemma proving `route_C2` carries one extra conclusion beyond the route statement — the uniform
bound `|F − f| ≤ 2 L + 2 α`, which is what makes the patches converge in `L²(ν)` — and `route_C2`
below projects the route's own conjunction out of it.

The sandwich section records, for a globally Lipschitz `L²(ν)` test, the chain
`LocalSlope.relaxation ≤ SmoothGradient.relaxation ≤ LocalSlope.energy ≤
AsymptoticLipschitz.energy`: the two relaxations sit below the two raw energies, the left
inequality is the unconditional comparison already in the library, the middle one is `route_C4`
and the right one is the pointwise domination of the local slope by the asymptotic Lipschitz
constant.

The boundary section records the constant test and the zero-dimensional convention (on a one-point
coordinate space the smooth-gradient relaxation vanishes identically without an absolute-continuity hypothesis).

The axiom reports at the end cover every public declaration of the density module and every theorem of
this client; each of them must list only `propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.Energy
open scoped ENNReal NNReal ContDiff

namespace EnergySlopeDensityAudit

/-! ### The local slope of a continuous function is Borel -/

/-- The local slope of a continuous function is Borel measurable. -/
theorem route_C1 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
      [BorelSpace V] {f : V → ℝ}, Continuous f → Measurable (LocalSlope.apply f) := by
  intro V _ _ _ _ f hf
  exact LocalSlope.measurable_apply (f := f) (hf := hf)

/-! ### The McShane patch -/

/-- For a globally `L`-Lipschitz `f` and `α, δ > 0`: a globally Lipschitz `F` with constant
`9 L + 8 α` (independent of `δ`), equal to `f` on a Borel set `K` of co-mass at most `δ`, whose
asymptotic Lipschitz constant on `K` is within `2 α` of the local slope of `f`. -/
theorem route_C2 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {f : V → ℝ} {L : ℝ≥0}, LipschitzWith L f →
      ∀ {α : ℝ≥0}, 0 < α → ∀ {δ : ℝ≥0∞}, 0 < δ →
      ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * α) F ∧ MeasurableSet K ∧
        (ν : Measure V) Kᶜ ≤ δ ∧ (∀ x ∈ K, F x = f x) ∧
        ∀ x ∈ K, AsymptoticLipschitz.apply F x ≤ LocalSlope.apply f x + 2 * (α : ℝ≥0∞) := by
  intro V _ _ _ _ _ _ _ ν f L hf α hα δ hδ
  obtain ⟨F, K, hFlip, hKmeas, hKmass, hFeq, _, hFslope⟩ :=
    LocalSlope.exists_patch (ν := ν) (f := f) (L := L) (hf := hf) (α := α) (hα := hα)
      (δ := δ) (hδ := hδ)
  exact ⟨F, K, hFlip, hKmeas, hKmass, hFeq, hFslope⟩

/-! ### Density for globally Lipschitz tests -/

/-- The smooth-gradient relaxation of a globally Lipschitz test is at most its raw local-slope
energy. -/
theorem route_C4 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {g : V → ℝ} {L : ℝ≥0}, LipschitzWith L g →
      ∀ (hg : MemLp g 2 (ν : Measure V)),
      SmoothGradient.relaxation ν (hg.toLp g) ≤ LocalSlope.energy ν g := by
  intro V _ _ _ _ _ _ _ ν g L hL hg
  exact SmoothGradient.relaxation_le_localSlope_of_lipschitzWith
    (ν := ν) (g := g) (L := L) (hg := hL) (hmem := hg)

/-! ### Density for every admissible local-slope test -/

/-- The smooth-gradient relaxation of an admissible local-slope test is at most its raw
local-slope energy. -/
theorem route_C5 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {g : V → ℝ} (hg : LocalSlope.Admissible ν g),
      SmoothGradient.relaxation ν (hg.memLp_two.toLp g) ≤ LocalSlope.energy ν g := by
  intro V _ _ _ _ _ _ _ ν g hg
  exact SmoothGradient.relaxation_le_localSlope_of_admissible (ν := ν) (g := g) (hg := hg)

/-! ### The reverse inequality, for every law -/

/-- The smooth-gradient relaxation is at most the local-slope relaxation, with no absolute
continuity hypothesis. -/
theorem route_C6 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
      SmoothGradient.relaxation ν f ≤ LocalSlope.relaxation ν f := by
  intro V _ _ _ _ _ _ _ ν f
  exact SmoothGradient.relaxation_le_localSlope (ν := ν) f

/-! ### The sandwich on globally Lipschitz tests -/

section Sandwich

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- On a globally Lipschitz `L²(ν)` test the two relaxations sit below the two raw energies:
`LocalSlope.relaxation ≤ SmoothGradient.relaxation ≤ LocalSlope.energy ≤
AsymptoticLipschitz.energy`. -/
theorem sandwich (ν : ProbabilityMeasure V) {g : V → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hmem : MemLp g 2 (ν : Measure V)) :
    LocalSlope.relaxation ν (hmem.toLp g) ≤ SmoothGradient.relaxation ν (hmem.toLp g) ∧
      SmoothGradient.relaxation ν (hmem.toLp g) ≤ LocalSlope.energy ν g ∧
      LocalSlope.energy ν g ≤ AsymptoticLipschitz.energy ν g := by
  refine ⟨SmoothGradient.localSlope_relaxation_le ν _, route_C4 ν hg hmem,
    LocalSlope.energy_le_asymptoticLipschitz ν g⟩

/-- The same chain read through the mollification recovery
`SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith`: the smooth-gradient
relaxation of a globally Lipschitz test is dominated by both raw energies. -/
theorem relaxation_le_both (ν : ProbabilityMeasure V) {g : V → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hmem : MemLp g 2 (ν : Measure V)) :
    SmoothGradient.relaxation ν (hmem.toLp g) ≤ LocalSlope.energy ν g ∧
      SmoothGradient.relaxation ν (hmem.toLp g) ≤ AsymptoticLipschitz.energy ν g :=
  ⟨route_C4 ν hg hmem,
    SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith ν hg hmem⟩

end Sandwich

/-! ### Boundary cases -/

section Boundary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- A constant test has zero local-slope energy. -/
theorem const_localSlope_energy (ν : ProbabilityMeasure V) (c : ℝ) :
    LocalSlope.energy ν (fun _ : V ↦ c) = 0 := by
  unfold LocalSlope.energy
  simp

/-- `route_C4` at a constant test: the smooth-gradient relaxation vanishes. -/
theorem const_relaxation (ν : ProbabilityMeasure V) (c : ℝ) :
    SmoothGradient.relaxation ν ((memLp_const c : MemLp (fun _ : V ↦ c) 2
      (ν : Measure V)).toLp (fun _ : V ↦ c)) = 0 := by
  refine le_antisymm ?_ bot_le
  have h := route_C4 ν (g := fun _ : V ↦ c) (L := 0) (LipschitzWith.const c)
    (memLp_const c : MemLp (fun _ : V ↦ c) 2 (ν : Measure V))
  rwa [const_localSlope_energy ν c] at h

/-- Dimension zero: on a one-point coordinate space the smooth-gradient relaxation vanishes
identically.  Unlike the certified absolutely continuous scope, this needs no hypothesis on the
law: it is `route_C6` composed with the zero-dimensional local-slope relaxation. -/
theorem subsingleton_relaxation [Subsingleton V] (ν : ProbabilityMeasure V)
    (f : Lp ℝ 2 (ν : Measure V)) :
    SmoothGradient.relaxation ν f = 0 := by
  refine le_antisymm ?_ bot_le
  have h := route_C6 ν f
  rwa [LocalSlope.relaxation_eq_zero_of_subsingleton ν f] at h

end Boundary

/-! ### Axiom reports

Every public declaration of `Energy/Euclidean/Slope/Density.lean`, then every theorem of this
client.  Only `propext`, `Classical.choice` and `Quot.sound` may appear. -/

#print axioms FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant
#print axioms FunctionalInequalities.Energy.LocalSlope.apply_eq_iInf_nat
#print axioms FunctionalInequalities.Energy.LocalSlope.measurable_apply
#print axioms FunctionalInequalities.Energy.exists_thickening_pairwise_disjoint
#print axioms FunctionalInequalities.Energy.LocalSlope.exists_patch_of_isCompact
#print axioms FunctionalInequalities.Energy.LocalSlope.exists_partition
#print axioms FunctionalInequalities.Energy.LocalSlope.exists_patch
#print axioms FunctionalInequalities.Energy.le_liminf_of_lowerSemicontinuous
#print axioms FunctionalInequalities.Energy.le_one_add_sq
#print axioms FunctionalInequalities.Energy.sq_add_two_mul_le
#print axioms FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_lipschitzWith
#print axioms FunctionalInequalities.Energy.real_sq_add_le
#print axioms FunctionalInequalities.Energy.sq_add_le_mul_sq_add
#print axioms FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope_of_admissible
#print axioms FunctionalInequalities.Energy.SmoothGradient.relaxation_le_localSlope

#print axioms EnergySlopeDensityAudit.route_C1
#print axioms EnergySlopeDensityAudit.route_C2
#print axioms EnergySlopeDensityAudit.route_C4
#print axioms EnergySlopeDensityAudit.route_C5
#print axioms EnergySlopeDensityAudit.route_C6
#print axioms EnergySlopeDensityAudit.sandwich
#print axioms EnergySlopeDensityAudit.relaxation_le_both
#print axioms EnergySlopeDensityAudit.const_localSlope_energy
#print axioms EnergySlopeDensityAudit.const_relaxation
#print axioms EnergySlopeDensityAudit.subsingleton_relaxation

end EnergySlopeDensityAudit
