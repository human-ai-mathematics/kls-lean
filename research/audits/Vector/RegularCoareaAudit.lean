module

public import FunctionalInequalities.Analysis.Vector.Coarea.Regular
public import FunctionalInequalities.Analysis.Coarea.Regular
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for codimension-`m` weighted slice measurability and the regular coarea formula

**What is proved.**  `measurable_setLIntegral_inter_levelSet_levelGraphFamily` is the weighted slice
measurability **on a chart**: the level function is a Tonelli section of one measurable function on
the parameter–level product.  With it,
`coarea_of_contDiffOn_of_coareaJacobian_ne_zero` is the **codimension-`m` regular coarea formula**,
the analogue of the scalar regular formula: on an open set where the differential is everywhere
surjective, for every Borel `S ⊆ O` and every measurable `ℝ≥0∞` weight, the level function is
measurable and the coarea equality holds, with the normalized Hausdorff measure of the codimension
as fibre measure.

**`m = 1` gives back the proved scalar regular formula verbatim.**  `scalar_L9` below reproduces
the statement of `KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` — gradient norm, `surfaceMeasure V`,
`AEMeasurable` — and discharges it from the codimension-`m` theorem.

**What is not proved.**  Slice measurability **without** the regularity hypothesis.  In codimension
one the repository proves it for an arbitrary Borel subset of an open `C¹` domain, through the
Eilenberg slicing inequality; the route taken here does **not** use the codimension-`m` Eilenberg
inequality but goes through the chart, so it needs the differential to be surjective.  That is
also why **nothing is claimed about the critical set**, and why the general codimension-`m` coarea
formula — the analogue of the scalar `C¹`, Lipschitz and locally Lipschitz formulas, which needs
Sard or a critical-slice argument — is not proved here.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal RealInnerProductSpace ContDiff

namespace VectorRegularCoareaAudit

section Restatements

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **The regular coarea formula, restated independently** and discharged through named arguments.
The regularity hypothesis is written as surjectivity of the differential, which is what
`coareaJacobian ≠ 0` means. -/
theorem regular_coarea {O S : Set V} {u : V → W} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hreg : ∀ x ∈ O, Function.Surjective ((fderiv ℝ u x : V →ₗ[ℝ] W)))
    (hS : MeasurableSet S) (hSO : S ⊆ O) (hg : Measurable g) :
    Measurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y
        ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y
          ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W)) ∂(volume : Measure W)) :=
  coarea_of_contDiffOn_of_coareaJacobian_ne_zero hO hu
    (fun x hx => (coareaJacobian_ne_zero_iff _).2 (hreg x hx)) hS hSO hg

/-- **No finiteness anywhere**: the whole space as domain and as Borel set. -/
theorem whole_space {u : V → W} {g : V → ℝ≥0∞} (hu : ContDiff ℝ 1 u)
    (hreg : ∀ x : V, coareaJacobian (fderiv ℝ u x) ≠ 0) (hg : Measurable g) :
    ∫⁻ x, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in {x : V | u x = t}, g y
          ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W)) ∂(volume : Measure W) := by
  have h := (coarea_of_contDiffOn_of_coareaJacobian_ne_zero isOpen_univ hu.contDiffOn
    (fun x _ => hreg x) MeasurableSet.univ (Set.subset_univ _) hg).2
  simpa using h

/-- An **identically infinite weight** is inside the statement. -/
theorem infinite_weight {O S : Set V} {u : V → W} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hreg : ∀ x ∈ O, coareaJacobian (fderiv ℝ u x) ≠ 0)
    (hS : MeasurableSet S) (hSO : S ⊆ O) :
    ∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * ⊤ ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ _ in S ∩ {x : V | u x = t}, (⊤ : ℝ≥0∞)
          ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W)) ∂(volume : Measure W) :=
  (coarea_of_contDiffOn_of_coareaJacobian_ne_zero hO hu hreg hS hSO measurable_const).2

/-- The **empty Borel set** is inside the statement. -/
theorem empty_set {O : Set V} {u : V → W} {g : V → ℝ≥0∞} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) (hreg : ∀ x ∈ O, coareaJacobian (fderiv ℝ u x) ≠ 0)
    (hg : Measurable g) :
    ∫⁻ x in (∅ : Set V), ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x
        ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in (∅ : Set V) ∩ {x : V | u x = t}, g y
          ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W)) ∂(volume : Measure W) :=
  (coarea_of_contDiffOn_of_coareaJacobian_ne_zero hO hu hreg MeasurableSet.empty
    (Set.empty_subset _) hg).2

/-- **A zero-dimensional target makes every point regular**, so the formula applies with no
regularity hypothesis at all. -/
theorem zero_dimensional_target [Subsingleton W] {O S : Set V} {u : V → W} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hg : Measurable g) :
    ∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y
          ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W)) ∂(volume : Measure W) := by
  refine (coarea_of_contDiffOn_of_coareaJacobian_ne_zero hO hu (fun x _ => ?_) hS hSO hg).2
  rw [coareaJacobian, LinearMap.normDet_of_subsingleton]
  exact one_ne_zero

end Restatements

/-! ### `m = 1` is the proved scalar regular coarea formula -/

section CodimensionOne

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- A nonzero real differential is surjective, so the scalar regularity hypothesis is the
codimension-`m` one. -/
theorem coareaJacobian_ne_zero_of_fderiv_ne_zero {u : V → ℝ} {x : V} (h : fderiv ℝ u x ≠ 0) :
    coareaJacobian (fderiv ℝ u x) ≠ 0 := by
  refine (coareaJacobian_ne_zero_iff _).2 fun c => ?_
  obtain ⟨v, hv⟩ : ∃ v : V, fderiv ℝ u x v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (ContinuousLinearMap.ext hcon)
  refine ⟨(c / fderiv ℝ u x v) • v, ?_⟩
  simp only [ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
  field_simp

/-- **`m = 1` is the proved scalar regular coarea formula**,
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`, reproduced verbatim — gradient norm,
`surfaceMeasure V`, `AEMeasurable` — and discharged from the codimension-`m` theorem. -/
theorem scalar_L9 {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) (hreg : ∀ x ∈ O, fderiv ℝ u x ≠ 0)
    (hS : MeasurableSet S) (hSO : S ⊆ O) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ)) := by
  have hsurf : KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ ℝ) = KLS.surfaceMeasure V := by
    rw [finrank_self]
    rfl
  have hdens : ∀ x : V, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) = ‖gradient u x‖ₑ := by
    intro x
    rw [coareaJacobian_fderiv, ofReal_norm]
  obtain ⟨hmeas, heq⟩ := coarea_of_contDiffOn_of_coareaJacobian_ne_zero hO hu
    (fun x hx => coareaJacobian_ne_zero_of_fderiv_ne_zero (hreg x hx)) hS hSO hg
  rw [hsurf] at hmeas heq
  simp_rw [hdens] at heq
  exact ⟨hmeas.aemeasurable, heq⟩

end CodimensionOne

end VectorRegularCoareaAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms
  FunctionalInequalities.Analysis.measurable_setLIntegral_inter_levelSet_levelGraphFamily
#print axioms FunctionalInequalities.Analysis.exists_vector_coarea_neighborhood_measurable
#print axioms FunctionalInequalities.Analysis.coarea_of_contDiffOn_of_coareaJacobian_ne_zero
#print axioms VectorRegularCoareaAudit.regular_coarea
#print axioms VectorRegularCoareaAudit.whole_space
#print axioms VectorRegularCoareaAudit.infinite_weight
#print axioms VectorRegularCoareaAudit.empty_set
#print axioms VectorRegularCoareaAudit.zero_dimensional_target
#print axioms VectorRegularCoareaAudit.coareaJacobian_ne_zero_of_fderiv_ne_zero
#print axioms VectorRegularCoareaAudit.scalar_L9

/-! The scalar regular coarea formula of the repository, for comparison; it is proved
independently. -/
#print axioms FunctionalInequalities.KLS.coarea_of_contDiffOn_of_fderiv_ne_zero
