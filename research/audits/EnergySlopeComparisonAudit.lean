import FunctionalInequalities.Energy.Euclidean.Slope.Comparison

/-!
# Scope audit for the slope sandwich `A1`–`A3`

This client imports **only** the new hole-free module
`FunctionalInequalities/Energy/Euclidean/Slope/Comparison.lean`; no work-in-progress layer is
imported, and no `#check` stands in for a proof.  It discharges the three obligations `A1`, `A2`,
`A3` of `research/audits/EnergySlopeRouteStatements.lean`, restated **verbatim** as `route_A1`,
`route_A2`, `route_A3`.

## What the sandwich gives, and what it does not

`sandwich` records the two inequalities

`    LocalSlope.relaxation ν ≤ AsymptoticLipschitz.relaxation ν ≤ SmoothGradient.relaxation ν`

for every Borel probability law on a finite-dimensional inner-product space, the first from the
repository (`LocalSlope.relaxation_le_asymptoticLipschitz`) and the second from `A2`.
`conventions_agree_on_smooth_tests` records that on the smooth test class the one-moving-point and
two-moving-point conventions agree pointwise, both being the gradient norm.

The remaining obligation `E0a`, `SmoothGradient.relaxation ν = LocalSlope.relaxation ν` for a
singular law, is **not** proved anywhere in this round: it needs density of smooth tests in the
local-slope energy.  It therefore appears below as an **explicit hypothesis** of `collapse`,
`cheeger_conventions_eq`, `two_mul_cheeger` and `intrinsic_two_mul_cheeger`, which are the
statements `E0b`, `E0c`, `E0d`, `E0e` of the route file with that hypothesis prefixed.  Nothing in
this file assumes it silently, and no placeholder axiom is introduced.
`hypothesis_of_absolutelyContinuous` shows the hypothesis is discharged on the certified
absolutely continuous scope, so the four consequences hold unconditionally there.

The boundary section records the zero-dimensional convention: on a one-point coordinate space all
three relaxations vanish identically, so `E0a` itself and the whole collapse hold there with no
hypothesis at all.

The axiom reports at the end cover every public declaration of the new module and every theorem of
this client; each of them must list only `propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.Energy
open scoped ENNReal NNReal ContDiff

namespace EnergySlopeComparisonAudit

/-! ### `A1` — a smooth test's asymptotic Lipschitz constant is its gradient norm, pointwise -/

/-- Restated verbatim from the route file. -/
theorem route_A1 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {ν : ProbabilityMeasure V} (f : SmoothGradient.Test ν) (x : V),
      AsymptoticLipschitz.apply f.toFun x = ‖gradient f.toFun x‖ₑ := by
  intro V _ _ _ _ _ _ _ ν f x
  exact SmoothGradient.Test.asymptoticLipschitz_apply f x

/-! ### `A2` — the third side of the sandwich, for every law -/

/-- Restated verbatim from the route file. -/
theorem route_A2 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
      AsymptoticLipschitz.relaxation ν f ≤ SmoothGradient.relaxation ν f := by
  intro V _ _ _ _ _ _ _ ν f
  exact SmoothGradient.asymptoticLipschitz_relaxation_le ν f

/-! ### `A3` — the collapse: `E0a` implies `E0b` -/

/-- Restated verbatim from the route file. -/
theorem route_A3 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V), SmoothGradient.relaxation ν = LocalSlope.relaxation ν →
      LocalSlope.relaxation ν = AsymptoticLipschitz.relaxation ν := by
  intro V _ _ _ _ _ _ _ ν h
  exact LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient ν h

/-! ### The sandwich, as one statement -/

/-- Both inequalities of the sandwich
`LocalSlope.relaxation ν ≤ AsymptoticLipschitz.relaxation ν ≤ SmoothGradient.relaxation ν`,
for every Borel probability law and every `L²(ν)` element.  Only the second is new. -/
theorem sandwich :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
      LocalSlope.relaxation ν f ≤ AsymptoticLipschitz.relaxation ν f ∧
        AsymptoticLipschitz.relaxation ν f ≤ SmoothGradient.relaxation ν f := by
  intro V _ _ _ _ _ _ _ ν f
  exact ⟨LocalSlope.relaxation_le_asymptoticLipschitz ν f,
    SmoothGradient.asymptoticLipschitz_relaxation_le ν f⟩

/-- On the smooth test class the two Cheeger conventions agree pointwise: the one-moving-point
local slope and the two-moving-point asymptotic Lipschitz constant are both the gradient norm.
No measure hypothesis and no absolute continuity are used. -/
theorem conventions_agree_on_smooth_tests :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {ν : ProbabilityMeasure V} (f : SmoothGradient.Test ν) (x : V),
      LocalSlope.apply f.toFun x = AsymptoticLipschitz.apply f.toFun x := by
  intro V _ _ _ _ _ _ _ ν f x
  rw [SmoothGradient.Test.asymptoticLipschitz_apply f x, ← ofReal_norm,
    LocalSlope.apply_eq_norm_gradient f.toFun x (f.contDiff.differentiable (by simp) x)]

/-! ### `E0b`–`E0e` with `E0a` as an explicit hypothesis

Each statement is the route file's proposition with
`SmoothGradient.relaxation ν = LocalSlope.relaxation ν →` prefixed; for the intrinsic identity the
hypothesis is taken at the intrinsic law on the direction space of the affine support, which is
the law the certified corollary transports along. -/

/-- `E0b` under `E0a`: the two Cheeger conventions relax to the same `L²(ν)` functional. -/
theorem collapse :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V), SmoothGradient.relaxation ν = LocalSlope.relaxation ν →
      LocalSlope.relaxation ν = AsymptoticLipschitz.relaxation ν := by
  intro V _ _ _ _ _ _ _ ν h
  exact LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient ν h

/-- `E0c` under `E0a`: the two Cheeger energies agree. -/
theorem cheeger_conventions_eq :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V), SmoothGradient.relaxation ν = LocalSlope.relaxation ν →
      Cheeger.energy ν = Cheeger.ofAsymptoticLipschitz ν := by
  intro V _ _ _ _ _ _ _ ν h
  refine Functional.ext fun f ↦ ?_
  rw [Cheeger.energy_apply, LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient ν h]
  rfl

/-- `E0d` under `E0a`: on the coordinate space the smooth-gradient relaxation is twice the
selected Cheeger energy. -/
theorem two_mul_cheeger :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
      SmoothGradient.relaxation ν = LocalSlope.relaxation ν →
      SmoothGradient.relaxation ν f = 2 * Cheeger.energy ν f := by
  intro V _ _ _ _ _ _ _ ν f h
  rw [h, Cheeger.two_mul_energy]

/-- `E0e` under `E0a` at the intrinsic law: the Blueprint identity
`thm:smooth-gradient-relaxation-two-cheeger` on the affine support, transported exactly as the
certified absolutely continuous corollary does. -/
theorem intrinsic_two_mul_cheeger :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (μ : ProbabilityMeasure E) (f : Lp ℝ 2 (μ : Measure E)),
      SmoothGradient.relaxation (Probability.intrinsicMeasure μ) =
          LocalSlope.relaxation (Probability.intrinsicMeasure μ) →
      SmoothGradient.Intrinsic.energy μ f = 2 * Cheeger.Intrinsic.energy μ f := by
  intro E _ _ _ _ _ _ _ μ f h
  rw [SmoothGradient.Intrinsic.energy_apply, Cheeger.Intrinsic.energy_apply, h]
  exact (Cheeger.two_mul_energy (Probability.intrinsicMeasure μ)
    (Energy.Euclidean.toIntrinsicL2 μ f)).symm

/-- The hypothesis of the four statements above is discharged on the certified absolutely
continuous scope, where it is the proved
`SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous`. -/
theorem hypothesis_of_absolutelyContinuous :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure], (ν : Measure V) ≪ m →
      SmoothGradient.relaxation ν = LocalSlope.relaxation ν := by
  intro V _ _ _ _ _ _ _ ν m _ hac
  exact SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous ν m hac

/-! ### Dimension zero -/

/-- Boundary case: on a one-point coordinate space every gradient is zero, every constant is a
smooth test of zero energy, and all three relaxations vanish identically.  So `E0a` itself — and
with it the whole collapse — holds there with no hypothesis. -/
theorem boundary_zero_dimensional :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      [Subsingleton V] (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
      LocalSlope.relaxation ν f = 0 ∧ AsymptoticLipschitz.relaxation ν f = 0 ∧
        SmoothGradient.relaxation ν f = 0 := by
  intro V _ _ _ _ _ _ _ _ ν f
  refine ⟨LocalSlope.relaxation_eq_zero_of_subsingleton ν f,
    AsymptoticLipschitz.relaxation_eq_zero_of_subsingleton ν f, ?_⟩
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (ν : Measure V)
  set c := f x₀ with hc
  have hconst : MemLp (fun _ : V ↦ c) 2 (ν : Measure V) := memLp_const c
  have hgrad : (fun x : V ↦ ‖gradient (fun _ : V ↦ c) x‖ ^ 2) = fun _ : V ↦ (0 : ℝ) := by
    funext x
    rw [Subsingleton.elim (gradient (fun _ : V ↦ c) x) 0]
    simp
  set t : SmoothGradient.Test ν :=
    { toFun := fun _ : V ↦ c
      contDiff := contDiff_const
      memLp_two := hconst
      gradient_sq_integrable := by rw [hgrad]; exact integrable_zero _ _ _ } with ht
  have hE : (t.energy : ℝ≥0∞) = 0 := by
    have : (t.energy : ℝ) = 0 := by
      show ∫ x, ‖gradient (fun _ : V ↦ c) x‖ ^ 2 ∂(ν : Measure V) = 0
      rw [hgrad]
      simp
    rw [show t.energy = 0 from NNReal.coe_injective this]
    simp
  have hle := (SmoothGradient.preEnergy ν).sequentialRelaxation_toAmbient_le t
  rw [SmoothGradient.preEnergy_energy, hE] at hle
  have hft : f = t.toL2 := by
    apply Lp.ext
    filter_upwards [hconst.coeFn_toLp] with x hx
    show f x = (t.memLp_two.toLp t.toFun : V → ℝ) x
    rw [hx, hc]
    exact congrArg f (Subsingleton.elim x x₀)
  rw [hft]
  exact le_antisymm hle bot_le

end EnergySlopeComparisonAudit

/-! ### Axiom reports

Every public declaration of `FunctionalInequalities/Energy/Euclidean/Slope/Comparison.lean`, then
every theorem of this client.  Only `propext`, `Classical.choice` and `Quot.sound` may appear. -/

#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.apply_eq_norm_gradient
#print axioms FunctionalInequalities.Energy.AsymptoticLipschitz.relaxation_eq_zero_of_subsingleton
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.asymptoticLipschitz_apply
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.asymptoticLipschitz_energy
#print axioms FunctionalInequalities.Energy.SmoothGradient.Test.asymptoticLipschitz_admissible
#print axioms FunctionalInequalities.Energy.SmoothGradient.asymptoticLipschitz_relaxation_le
#print axioms
  FunctionalInequalities.Energy.LocalSlope.relaxation_eq_asymptoticLipschitz_of_smoothGradient

#print axioms EnergySlopeComparisonAudit.route_A1
#print axioms EnergySlopeComparisonAudit.route_A2
#print axioms EnergySlopeComparisonAudit.route_A3
#print axioms EnergySlopeComparisonAudit.sandwich
#print axioms EnergySlopeComparisonAudit.conventions_agree_on_smooth_tests
#print axioms EnergySlopeComparisonAudit.collapse
#print axioms EnergySlopeComparisonAudit.cheeger_conventions_eq
#print axioms EnergySlopeComparisonAudit.two_mul_cheeger
#print axioms EnergySlopeComparisonAudit.intrinsic_two_mul_cheeger
#print axioms EnergySlopeComparisonAudit.hypothesis_of_absolutelyContinuous
#print axioms EnergySlopeComparisonAudit.boundary_zero_dimensional
