import FunctionalInequalities.Energy.Euclidean.SlopeRecovery

/-!
# Scope audit for the smooth-recovery module `Energy/Euclidean/SlopeRecovery.lean`

This client imports **only** the new library module — no work-in-progress layer — and discharges
the five propositions `B1`–`B5` of the route file
`research/audits/EnergySlopeRouteStatements.lean` from it.  The propositions are restated
**verbatim** from the route file as `route_B1` … `route_B5`; each is proved by a **named**
application of the library lemma, so a renamed binder or a reordered hypothesis would fail to
elaborate here.

`B1` is the mollification recovery
`SmoothGradient.relaxation ν (toLp g) ≤ AsymptoticLipschitz.energy ν g` for a globally Lipschitz
`g`; `B2`–`B5` are the four reduction tools.  Nothing here is a density statement: the uniform
mollification radius is genuinely insufficient for a general locally Lipschitz test, which is the
diagnostic `D1` of the route file and is not claimed.

The boundary section records the constant test (both slopes vanish, so the recovered relaxation is
zero) and the zero-dimensional convention (on a one-point coordinate space every asymptotic
Lipschitz constant vanishes).

The axiom reports at the end cover every public declaration of the new module and every theorem of
this client; each of them must list only `propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.Energy
open scoped ENNReal NNReal ContDiff

namespace EnergySlopeRecoveryAudit

/-! ### `B1` — smooth recovery of a globally Lipschitz test -/

/-- Mollifying a globally Lipschitz test gives an approximating sequence of smooth tests whose
limiting energy is at most the asymptotic-Lipschitz energy. -/
theorem route_B1 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {g : V → ℝ} {K : ℝ≥0}, LipschitzWith K g →
      ∀ (hg : MemLp g 2 (ν : Measure V)),
      SmoothGradient.relaxation ν (hg.toLp g) ≤ AsymptoticLipschitz.energy ν g := by
  intro V _ _ _ _ _ _ _ ν g K hK hg
  exact SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith
    (ν := ν) (g := g) (K := K) (hlip := hK) (hmem := hg)

/-! ### `B2` — locally Lipschitz times bounded globally Lipschitz -/

/-- A locally Lipschitz function times a bounded globally Lipschitz one is locally Lipschitz. -/
theorem route_B2 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      {g h : V → ℝ} {N : ℝ≥0}, LocallyLipschitz g → LipschitzWith N h → (∀ x, |h x| ≤ 1) →
      LocallyLipschitz (fun x => g x * h x) := by
  intro V _ _ g h N hg hh hh1
  exact locallyLipschitz_mul (g := g) (h := h) (N := N) (hg := hg) (hh := hh) (hh1 := hh1)

/-! ### `B3` — locally Lipschitz and vanishing outside a ball -/

/-- Vanishing outside a ball upgrades local to global Lipschitz continuity. -/
theorem route_B3 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      {g : V → ℝ} {R : ℝ}, LocallyLipschitz g → (∀ x, R ≤ ‖x‖ → g x = 0) →
      ∃ K : ℝ≥0, LipschitzWith K g := by
  intro V _ _ _ g R hg hR
  exact exists_lipschitzWith_of_eq_zero_outside_ball (g := g) (R := R) (hg := hg) (hR := hR)

/-! ### `B4`, `B5` — the one-moving-point Leibniz bounds -/

/-- Leibniz bound for the asymptotic Lipschitz constant. -/
theorem route_B4 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      (g h : V → ℝ) {N : ℝ≥0}, LipschitzWith N h → (∀ y, |h y| ≤ 1) → ∀ x : V,
      AsymptoticLipschitz.apply (fun y => g y * h y) x ≤
        AsymptoticLipschitz.apply g x + ENNReal.ofReal |g x| * N := by
  intro V _ _ g h N hh hh1 x
  exact AsymptoticLipschitz.apply_mul_le g h (N := N) (hh := hh) (hh1 := hh1) x

/-- Leibniz bound for the local slope. -/
theorem route_B5 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      (g h : V → ℝ) {N : ℝ≥0}, LipschitzWith N h → (∀ y, |h y| ≤ 1) → ∀ x : V,
      LocalSlope.apply (fun y => g y * h y) x ≤
        LocalSlope.apply g x + ENNReal.ofReal |g x| * N := by
  intro V _ _ g h N hh hh1 x
  exact LocalSlope.apply_mul_le g h (N := N) (hh := hh) (hh1 := hh1) x

/-! ### Boundary cases -/

section Boundary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- A constant test has zero asymptotic-Lipschitz energy. -/
theorem const_asymptoticLipschitz_energy (ν : ProbabilityMeasure V) (c : ℝ) :
    AsymptoticLipschitz.energy ν (fun _ : V ↦ c) = 0 := by
  unfold AsymptoticLipschitz.energy
  simp

/-- `B1` at a constant test: the recovered relaxation vanishes. -/
theorem const_relaxation (ν : ProbabilityMeasure V) (c : ℝ) :
    SmoothGradient.relaxation ν ((memLp_const c : MemLp (fun _ : V ↦ c) 2
      (ν : Measure V)).toLp (fun _ : V ↦ c)) = 0 := by
  refine le_antisymm ?_ bot_le
  have h := route_B1 ν (g := fun _ : V ↦ c) (K := 0) (LipschitzWith.const c)
    (memLp_const c : MemLp (fun _ : V ↦ c) 2 (ν : Measure V))
  rwa [const_asymptoticLipschitz_energy ν c] at h

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Dimension zero: on a one-point coordinate space every asymptotic-Lipschitz energy vanishes. -/
theorem subsingleton_asymptoticLipschitz_energy [Subsingleton V] (ν : ProbabilityMeasure V)
    (f : V → ℝ) : AsymptoticLipschitz.energy ν f = 0 := by
  unfold AsymptoticLipschitz.energy
  simp [AsymptoticLipschitz.apply_eq_zero_of_subsingleton f]

/-- Dimension zero for `B1`: every globally Lipschitz test recovers zero energy. -/
theorem subsingleton_relaxation [Subsingleton V] (ν : ProbabilityMeasure V) {g : V → ℝ}
    {K : ℝ≥0} (hg : LipschitzWith K g) (hmem : MemLp g 2 (ν : Measure V)) :
    SmoothGradient.relaxation ν (hmem.toLp g) = 0 := by
  refine le_antisymm ?_ bot_le
  have h := route_B1 ν (g := g) (K := K) hg hmem
  rwa [subsingleton_asymptoticLipschitz_energy ν g] at h

end Boundary

/-! ### Axiom reports

Every public declaration of `Energy/Euclidean/SlopeRecovery.lean`, then every theorem of this
client.  Only `propext`, `Classical.choice` and `Quot.sound` may appear. -/

#print axioms FunctionalInequalities.Energy.LocalSlope.secant
#print axioms FunctionalInequalities.Energy.LocalSlope.apply_eq_iInf_secant
#print axioms FunctionalInequalities.Energy.LocalSlope.apply_le_secant
#print axioms FunctionalInequalities.Energy.LocalSlope.secant_mono
#print axioms FunctionalInequalities.Energy.LocalSlope.secant_le_of_forall
#print axioms FunctionalInequalities.Energy.LocalSlope.secant_le_ofReal
#print axioms FunctionalInequalities.Energy.LocalSlope.dist_le_of_secant_le
#print axioms FunctionalInequalities.Energy.LocalSlope.exists_secant_le
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.secant
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.apply_eq_iInf_secant
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_secant
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.secant_le_of_forall
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.secant_le_ofReal
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.exists_secant_le
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.dist_le_of_secant_le
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.apply_le_of_lipschitzOnWith
#print axioms FunctionalInequalities.Energy.locallyLipschitz_mul
#print axioms FunctionalInequalities.Energy.exists_lipschitzWith_of_eq_zero_outside_ball
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.apply_mul_le
#print axioms FunctionalInequalities.Energy.LocalSlope.apply_mul_le
#print axioms FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball
#print axioms FunctionalInequalities.Energy.norm_fderiv_mollify_le_of_lipschitzOnWith
#print axioms FunctionalInequalities.Energy.limsup_enorm_gradient_mollify_le
#print axioms
  FunctionalInequalities.Energy.SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith

#print axioms EnergySlopeRecoveryAudit.route_B1
#print axioms EnergySlopeRecoveryAudit.route_B2
#print axioms EnergySlopeRecoveryAudit.route_B3
#print axioms EnergySlopeRecoveryAudit.route_B4
#print axioms EnergySlopeRecoveryAudit.route_B5
#print axioms EnergySlopeRecoveryAudit.const_asymptoticLipschitz_energy
#print axioms EnergySlopeRecoveryAudit.const_relaxation
#print axioms EnergySlopeRecoveryAudit.subsingleton_asymptoticLipschitz_energy
#print axioms EnergySlopeRecoveryAudit.subsingleton_relaxation

end EnergySlopeRecoveryAudit
