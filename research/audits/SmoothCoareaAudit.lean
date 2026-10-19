import FunctionalInequalities.Analysis.Coarea.Smooth

/-!
# Strict audit client for the `C¹` weighted coarea formula (obligation `L11`, target `T3`)

Independent client of `Analysis/Coarea/Smooth.lean`.  `target` states the route's `L11`
quantifier for quantifier and proves it; `target_of_not_completeSpace` drops the unused
`[CompleteSpace V]`.

`target_T3` preserves the route's third target, and `wip_isoperimetry_statement` preserves the
contract of `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` from
`Analysis/Coarea/Isoperimetry.lean`. Both follow from `L11` at `S = univ`; their
`LipschitzWith` hypothesis is unused because they assume `ContDiff ℝ 1 u`.

`constant_function` checks the `⊤ · 0` boundary independently of `L11`: for a constant function
every slice at the attained level is the whole space, of infinite surface measure, yet both sides
are `0` because the exceptional level set is Lebesgue-null.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff

namespace SmoothCoareaAudit

/-! ### The obligation itself -/

-- The statement text of obligation `L11` of the weighted coarea route.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    ContDiff ℝ 1 u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))

/-- `L11`, proved. -/
theorem target : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    ContDiff ℝ 1 u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ S u g hu hS hg
  exact coarea_of_contDiff hu hS hg

/-- The same conclusion without `[CompleteSpace V]`. -/
theorem target_of_not_completeSpace : ∀ {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    ContDiff ℝ 1 u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ S u g hu hS hg
  exact coarea_of_contDiff hu hS hg

/-! ### Target `T3`: the `C¹` isoperimetric coarea contract -/

/-- Target `T3` of the route, proved.  The `LipschitzWith` hypothesis is unused. -/
theorem target_T3 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    {u : V → ℝ} (_ : ContDiff ℝ 1 u)
    {K : ℝ≥0} (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ _ u hu K _ g hg
  have h := (coarea_of_contDiff (S := Set.univ) hu MeasurableSet.univ hg).2
  simpa using h

/-- Verbatim the isoperimetric coarea contract
`KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, discharged through **named**
arguments so a renamed binder or reordered hypothesis would fail to elaborate.  The
work-in-progress file itself is untouched. -/
theorem wip_isoperimetry_statement :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {u : V → ℝ}, ContDiff ℝ 1 u → ∀ {K : ℝ≥0}, LipschitzWith K u →
      ∀ {g : V → ℝ≥0∞}, Measurable g →
      ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ _ u hu K hK g hg
  have h := (coarea_of_contDiff (S := Set.univ) (u := u) (g := g) hu MeasurableSet.univ hg).2
  simpa using h

/-! ### Consumers -/

section Consumers

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- No finiteness of the weight: `g` is identically `∞`. -/
theorem top_weight {S : Set V} {u : V → ℝ} (hu : ContDiff ℝ 1 u) (hS : MeasurableSet S) :
    AEMeasurable (fun t : ℝ => ∫⁻ _y in S ∩ {x | u x = t}, (⊤ : ℝ≥0∞)
      ∂(surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * (⊤ : ℝ≥0∞) ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ _y in S ∩ {x | u x = t}, (⊤ : ℝ≥0∞) ∂(surfaceMeasure V) ∂(volume : Measure ℝ) :=
  coarea_of_contDiff hu hS measurable_const

/-- The degenerate set. -/
theorem empty_set {u : V → ℝ} {g : V → ℝ≥0∞} (hu : ContDiff ℝ 1 u) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in (∅ : Set V) ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in (∅ : Set V), ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in (∅ : Set V) ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) :=
  coarea_of_contDiff hu MeasurableSet.empty hg

/-- No nondegeneracy of the derivative: the critical set may be everything. -/
theorem everywhere_critical (c : ℝ) {S : Set V} (hS : MeasurableSet S) {g : V → ℝ≥0∞}
    (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | (fun _ : V => c) x = t}, g y
      ∂(surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient (fun _ : V => c) x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | (fun _ : V => c) x = t}, g y ∂(surfaceMeasure V)
        ∂(volume : Measure ℝ) :=
  coarea_of_contDiff contDiff_const hS hg

end Consumers

/-- The `⊤ · 0` boundary, checked independently of `L11`: for a constant function on the line the
slice at the attained level is the whole line, of infinite surface measure, and yet both sides of
the coarea identity are `0`, because the exceptional level set is Lebesgue-null. -/
theorem constant_function :
    (∫⁻ x : ℝ, ‖gradient (fun _ : ℝ => (0 : ℝ)) x‖ₑ * (⊤ : ℝ≥0∞) ∂(volume : Measure ℝ)) = 0 ∧
    (∫⁻ t, ∫⁻ _y in {x : ℝ | (fun _ : ℝ => (0 : ℝ)) x = t}, (⊤ : ℝ≥0∞) ∂(surfaceMeasure ℝ)
      ∂(volume : Measure ℝ)) = 0 := by
  refine ⟨?_, ?_⟩
  · simp [gradient]
  · have hne : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ 0 := by
      rw [ae_iff]
      simp
    have h : (fun t : ℝ => ∫⁻ _y in {x : ℝ | (fun _ : ℝ => (0 : ℝ)) x = t}, (⊤ : ℝ≥0∞)
        ∂(surfaceMeasure ℝ)) =ᵐ[(volume : Measure ℝ)] 0 := by
      filter_upwards [hne] with t ht
      have hempty : {x : ℝ | (fun _ : ℝ => (0 : ℝ)) x = t} = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => ht hx.symm
      simp [hempty]
    rw [lintegral_congr_ae h]
    simp

/-! ### The consumed statements are preserved -/

theorem preserved_coarea_of_contDiffOn_of_fderiv_ne_zero :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V] {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
      IsOpen O → ContDiffOn ℝ 1 u O → (∀ x ∈ O, fderiv ℝ u x ≠ 0) →
      MeasurableSet S → S ⊆ O → Measurable g →
      AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
        (volume : Measure ℝ) ∧
      (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
        ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ O S u g hO hu hreg hS hSO hg
  exact coarea_of_contDiffOn_of_fderiv_ne_zero (O := O) (S := S) (u := u) (g := g)
    hO hu hreg hS hSO hg

theorem preserved_ae_surfaceMeasure_critical_inter_levelSet_eq_zero :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V] {u : V → ℝ}, ContDiff ℝ 1 u →
      ∀ᵐ t ∂(volume : Measure ℝ),
        surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 := by
  intro V _ _ _ _ _ u hu
  exact ae_surfaceMeasure_critical_inter_levelSet_eq_zero (u := u) hu

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.KLS.isOpen_regular
#print axioms FunctionalInequalities.KLS.coarea_of_contDiff
#print axioms SmoothCoareaAudit.target
#print axioms SmoothCoareaAudit.target_of_not_completeSpace
#print axioms SmoothCoareaAudit.target_T3
#print axioms SmoothCoareaAudit.wip_isoperimetry_statement
#print axioms SmoothCoareaAudit.top_weight
#print axioms SmoothCoareaAudit.empty_set
#print axioms SmoothCoareaAudit.everywhere_critical
#print axioms SmoothCoareaAudit.constant_function
#print axioms SmoothCoareaAudit.preserved_coarea_of_contDiffOn_of_fderiv_ne_zero
#print axioms SmoothCoareaAudit.preserved_ae_surfaceMeasure_critical_inter_levelSet_eq_zero

end SmoothCoareaAudit
