import FunctionalInequalities.KLS.Geometry.CheegerInequality
import FunctionalInequalities.KLS.Geometry.Median

/-!
# Scope audit for Cheeger's inequality `C_P^smooth(ν) ≤ 4 / h_M(ν)²`

Every obligation `P1`–`P6` and the consequence `D1` of
`research/audits/CheegerInequalityRouteStatements.lean` is restated here **verbatim** — the
propositions are copied character for character from that route snapshot — and discharged from
the two new hole-free modules `KLS/Geometry/Median.lean` and `KLS/Geometry/CheegerInequality.lean`.
A renamed binder, a reordered hypothesis or a weakened conclusion would fail to elaborate here.

Out of scope, deliberately absent from this file: the target `P0`
(`C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²` for log-concave laws), which needs the identification
`h_μ = h_M(ν)` supplied by another module, and the Buser half `B1`
(`Ψ_KLS(μ)² ≤ π C_P^lit(μ)`), which is not part of this route at all.

Three boundary cases are recorded after the route items: dimension zero, where the Minkowski
Cheeger infimum is `⊤` and the smooth-test constant collapses to `0`; a constant test, whose
variance and gradient energy both vanish so that `P5` there is the identity `0 ≤ 0`; and a
`1`-Lipschitz admissible test, for which `P6` gives the scale-free bound
`h_M² Var(f) ≤ 4`, the consistency check `Ψ_KLS ≥ √(Var f) / 2` in multiplied form.

The axiom reports at the end cover every public declaration of the two new modules and every
theorem of this client.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set FunctionalInequalities
  FunctionalInequalities.KLS FunctionalInequalities.KLS.Isoperimetry
open scoped ENNReal NNReal ContDiff

namespace CheegerInequalityAudit

/-! ### `P1` — Cheeger's inequality for the smooth-test constant of any Borel law -/

/-- `P1`, restated verbatim and discharged. -/
theorem route_P1 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V),
      Poincare.SmoothTest.constant (ν : Measure V) ≤ 4 / minkowskiConstant ν ^ 2 := by
  intro V _ _ _ _ _ _ _ ν
  exact Isoperimetry.smoothTest_constant_le ν

/-! ### `P2` — a median exists -/

/-- `P2`, restated verbatim and discharged. -/
theorem route_P2 :
    ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      {g : α → ℝ}, Measurable g →
      ∃ m : ℝ, μ {x | m < g x} ≤ 1 / 2 ∧ μ {x | g x < m} ≤ 1 / 2 := by
  intro α _ μ _ g hg
  exact Isoperimetry.exists_median (g := g) μ hg

/-! ### `P3` — the `L¹` Cheeger inequality for a nonnegative function of half mass -/

/-- `P3`, restated verbatim and discharged. -/
theorem route_P3 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {u : V → ℝ}, ContDiff ℝ 1 u → ∀ {K : ℝ≥0}, LipschitzWith K u →
      (∀ x, 0 ≤ u x) → (ν : Measure V) {x | 0 < u x} ≤ 1 / 2 →
      minkowskiConstant ν * ∫⁻ x, ENNReal.ofReal (u x) ∂(ν : Measure V) ≤
        ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  intro V _ _ _ _ _ _ _ ν u hu K hK hu0 hmass
  exact Isoperimetry.minkowskiConstant_mul_lintegral_le (u := u) (K := K) ν hu hK hu0 hmass

/-! ### `P4` — the positive-part square -/

/-- `P4`, restated verbatim and discharged. -/
theorem route_P4 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {g : V → ℝ}, ContDiff ℝ 1 g → ∀ {K : ℝ≥0}, LipschitzWith K g →
      ∀ {M : ℝ}, (∀ x, |g x| ≤ M) → ∀ (m : ℝ), (ν : Measure V) {x | m < g x} ≤ 1 / 2 →
      minkowskiConstant ν ^ 2 * ∫⁻ x, ENNReal.ofReal (max (g x - m) 0 ^ 2) ∂(ν : Measure V) ≤
        4 * ∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂(ν : Measure V) := by
  intro V _ _ _ _ _ _ _ ν g hg K hK M hM m hmass
  exact Isoperimetry.minkowskiConstant_sq_mul_lintegral_posPart_sq_le
    (g := g) (K := K) (M := M) ν hg hK hM m hmass

/-! ### `P5` — Cheeger's inequality for bounded `C¹` Lipschitz functions -/

/-- `P5`, restated verbatim and discharged. -/
theorem route_P5 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {g : V → ℝ}, ContDiff ℝ 1 g → ∀ {K : ℝ≥0}, LipschitzWith K g →
      ∀ {M : ℝ}, (∀ x, |g x| ≤ M) →
      minkowskiConstant ν ^ 2 * evariance g (ν : Measure V) ≤
        4 * ∫⁻ x, ‖gradient g x‖ₑ ^ 2 ∂(ν : Measure V) := by
  intro V _ _ _ _ _ _ _ ν g hg K hK M hM
  exact Isoperimetry.minkowskiConstant_sq_mul_evariance_le (g := g) (K := K) (M := M) ν hg hK hM

/-! ### `P6` — every admissible smooth test -/

/-- `P6`, restated verbatim and discharged. -/
theorem route_P6 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {f : V → ℝ}, Poincare.SmoothTest.Admissible (ν : Measure V) f →
      minkowskiConstant ν ^ 2 * evariance f (ν : Measure V) ≤
        4 * ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂(ν : Measure V) := by
  intro V _ _ _ _ _ _ _ ν f hf
  exact Isoperimetry.minkowskiConstant_sq_mul_evariance_le_of_admissible (f := f) ν hf

/-! ### `D1` — an infinite Minkowski constant forces a vanishing Poincaré constant -/

/-- `D1`, restated verbatim and discharged. -/
theorem route_D1 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V), minkowskiConstant ν = ⊤ →
      Poincare.SmoothTest.constant (ν : Measure V) = 0 := by
  intro V _ _ _ _ _ _ _ ν h
  exact Isoperimetry.smoothTest_constant_eq_zero_of_minkowskiConstant_eq_top ν h

/-! ### Boundary cases -/

/-- Dimension zero: no Borel set has intermediate mass, the Minkowski Cheeger infimum is `⊤`, and
`D1` collapses the smooth-test constant to `0`. -/
theorem boundary_subsingleton :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      [Subsingleton V] (ν : ProbabilityMeasure V),
      Poincare.SmoothTest.constant (ν : Measure V) = 0 := by
  intro V _ _ _ _ _ _ _ _ ν
  exact Isoperimetry.smoothTest_constant_eq_zero_of_minkowskiConstant_eq_top ν
    (Isoperimetry.minkowskiConstant_eq_top_of_subsingleton ν)

/-- A constant test is admissible and both sides of `P5` vanish on it, so the inequality there is
the identity `0 ≤ 0` and carries no hidden strictness. -/
theorem boundary_const_test :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (c : ℝ),
      Poincare.SmoothTest.Admissible (ν : Measure V) (fun _ => c) ∧
        evariance (fun _ : V => c) (ν : Measure V) = 0 ∧
        ∫⁻ x, ‖gradient (fun _ : V => c) x‖ₑ ^ 2 ∂(ν : Measure V) = 0 := by
  intro V _ _ _ _ _ _ _ ν c
  have hgrad : ∀ x : V, gradient (fun _ : V => c) x = 0 := fun x => by simp
  refine ⟨⟨contDiff_const, memLp_const c, ?_⟩, ?_, ?_⟩
  · simp [hgrad]
  · simpa using (evariance_eq_zero_iff (X := fun _ : V => c) aemeasurable_const).mpr
      (Eventually.of_forall fun _ => by simp)
  · simp [hgrad]

/-- A `1`-Lipschitz admissible test: `P6` gives the scale-free bound `h_M² Var(f) ≤ 4`, the
multiplied form of `Ψ_KLS(ν) ≥ √(Var f) / 2`. -/
theorem boundary_lipschitz_one :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {f : V → ℝ}, Poincare.SmoothTest.Admissible (ν : Measure V) f →
      LipschitzWith 1 f →
      minkowskiConstant ν ^ 2 * evariance f (ν : Measure V) ≤ 4 := by
  intro V _ _ _ _ _ _ _ ν f hf hlip
  have hpt : ∀ x : V, ‖gradient f x‖ₑ ^ 2 ≤ 1 := by
    intro x
    have hle : ‖gradient f x‖ₑ ≤ 1 := by
      rw [Isoperimetry.enorm_gradient_eq_enorm_fderiv, ← ofReal_norm]
      have h1 : ‖fderiv ℝ f x‖ ≤ ((1 : ℝ≥0) : ℝ) := norm_fderiv_le_of_lipschitz ℝ hlip
      calc ENNReal.ofReal ‖fderiv ℝ f x‖ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (by
            simpa using h1)
        _ = 1 := by simp
    calc ‖gradient f x‖ₑ ^ 2 ≤ (1 : ℝ≥0∞) ^ 2 := by gcongr
      _ = 1 := one_pow 2
  calc minkowskiConstant ν ^ 2 * evariance f (ν : Measure V)
      ≤ 4 * ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂(ν : Measure V) :=
        Isoperimetry.minkowskiConstant_sq_mul_evariance_le_of_admissible (f := f) ν hf
    _ ≤ 4 * ∫⁻ _ : V, (1 : ℝ≥0∞) ∂(ν : Measure V) := by
        gcongr with x
        exact hpt x
    _ = 4 := by simp

end CheegerInequalityAudit

/-! ### Axiom audit

Every public declaration of the two new modules, then every theorem of this client.  Only
`propext`, `Classical.choice` and `Quot.sound` may appear; no hole axiom is reported. -/

#print axioms FunctionalInequalities.KLS.Isoperimetry.exists_median
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_mul_lintegral_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.hasDerivAt_sq_posPart
#print axioms FunctionalInequalities.KLS.Isoperimetry.contDiff_sq_posPart
#print axioms FunctionalInequalities.KLS.Isoperimetry.enorm_gradient_eq_enorm_fderiv
#print axioms FunctionalInequalities.KLS.Isoperimetry.measurable_enorm_gradient
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_sq_mul_lintegral_posPart_sq_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.evariance_le_lintegral_ofReal_sub_sq
#print axioms FunctionalInequalities.KLS.Isoperimetry.enorm_gradient_neg
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_sq_mul_evariance_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.add_sq_le_four_mul_add_sq
#print axioms FunctionalInequalities.KLS.Isoperimetry.exists_lipschitz_bound_of_hasCompactSupport
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_sq_mul_evariance_le_of_admissible
#print axioms FunctionalInequalities.KLS.Isoperimetry.ofReal_energy_eq_lintegral
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothTest_constant_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothTest_constant_eq_zero_of_minkowskiConstant_eq_top

#print axioms CheegerInequalityAudit.route_P1
#print axioms CheegerInequalityAudit.route_P2
#print axioms CheegerInequalityAudit.route_P3
#print axioms CheegerInequalityAudit.route_P4
#print axioms CheegerInequalityAudit.route_P5
#print axioms CheegerInequalityAudit.route_P6
#print axioms CheegerInequalityAudit.route_D1
#print axioms CheegerInequalityAudit.boundary_subsingleton
#print axioms CheegerInequalityAudit.boundary_const_test
#print axioms CheegerInequalityAudit.boundary_lipschitz_one

/-! #### The target `P0`, verbatim, added at integration (2026-09-19) once
`KLS/Geometry/CheegerEquality.lean` supplied `h_μ = h_M(ν)` -/

theorem CheegerInequalityAudit.route_P0 : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * Isoperimetry.inverseScale μ ^ 2 :=
  fun hμ => FunctionalInequalities.KLS.LogConcave.literatureConstant_le_four_mul_inverseScale_sq hμ

#print axioms FunctionalInequalities.KLS.LogConcave.literatureConstant_le_four_mul_inverseScale_sq
#print axioms CheegerInequalityAudit.route_P0
