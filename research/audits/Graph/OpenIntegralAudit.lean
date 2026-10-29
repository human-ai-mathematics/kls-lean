import FunctionalInequalities.Analysis.Graph.OpenIntegral

/-!
# Strict audit client for the weighted graph area over an open domain

Independent client of `Analysis/Graph/OpenIntegral.lean`.  `target` states obligation `L8` of
`research/audits/Coarea/WeightedRouteStatements.lean` quantifier for quantifier and proves it.

The consumers are not repetitions of the proof.  `global_case` recovers the pre-existing global
theorem from `target` by taking `O = univ`, so `target` is a genuine generalization.
`inv_on_Ioi` applies it to `x ↦ x⁻¹` on `(0, ∞)`, the standard function that is `C¹` on an open set
and admits **no** globally `C¹` extension — this is exactly what the countable interior localization
buys and what a single global extension could not.  `top_weight` uses a weight that is identically
`∞`, and `empty_parameter_set` the degenerate parameter set.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace OpenGraphAudit

/-! ### The obligation itself -/

-- The statement text of obligation `L8` of `research/audits/Coarea/WeightedRouteStatements.lean`.
#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : H →ₗᵢ[ℝ] V) {e : V}
    {O S : Set H} {v : H → ℝ} {g : V → ℝ≥0∞},
    ‖e‖ = 1 → (∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) →
    IsOpen O → ContDiffOn ℝ 1 v O → MeasurableSet S → S ⊆ O → Measurable g →
    (∫⁻ x in Analysis.graphMap ι e v '' S, g x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))) =
      ∫⁻ y in S, ENNReal.ofReal (Analysis.graphJacobian (gradient v y)) *
        g (Analysis.graphMap ι e v y) ∂(volume : Measure H))

/-- The route target, restated and proved. -/
theorem target : ∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : H →ₗᵢ[ℝ] V) {e : V}
    {O S : Set H} {v : H → ℝ} {g : V → ℝ≥0∞},
    ‖e‖ = 1 → (∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) →
    IsOpen O → ContDiffOn ℝ 1 v O → MeasurableSet S → S ⊆ O → Measurable g →
    (∫⁻ x in Analysis.graphMap ι e v '' S, g x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))) =
      ∫⁻ y in S, ENNReal.ofReal (Analysis.graphJacobian (gradient v y)) *
        g (Analysis.graphMap ι e v y) ∂(volume : Measure H) := by
  intro H V _ _ _ _ _ _ _ _ _ _ ι e O S v g he hperp hO hv hS hSO hg
  exact setLIntegral_image_graphMap_of_contDiffOn ι he hperp hO hv hS hSO hg

/-! ### Consumers -/

section Consumers

variable {H : Type*} {V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The target generalizes the pre-existing global theorem: take `O = univ`. -/
theorem global_case (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) {v : H → ℝ} (hv : ContDiff ℝ 1 v)
    {S : Set H} (hS : MeasurableSet S) {g : V → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in graphMap ι e v '' S, g x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)))
      = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * g (graphMap ι e v y)
          ∂(volume : Measure H) :=
  setLIntegral_image_graphMap_of_contDiffOn ι he hperp isOpen_univ
    (hv.contDiffOn) hS (Set.subset_univ S) hg

/-- No finiteness of the weight: `g` is identically `∞`. -/
theorem top_weight (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) {O S : Set H} {v : H → ℝ} (hO : IsOpen O)
    (hv : ContDiffOn ℝ 1 v O) (hS : MeasurableSet S) (hSO : S ⊆ O) :
    (∫⁻ _x in graphMap ι e v '' S, (∞ : ℝ≥0∞)
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)))
      = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * (∞ : ℝ≥0∞)
          ∂(volume : Measure H) :=
  setLIntegral_image_graphMap_of_contDiffOn ι he hperp hO hv hS hSO measurable_const

/-- The degenerate parameter set. -/
theorem empty_parameter_set (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) {O : Set H} {v : H → ℝ} (hO : IsOpen O)
    (hv : ContDiffOn ℝ 1 v O) {g : V → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in graphMap ι e v '' (∅ : Set H), g x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)))
      = ∫⁻ y in (∅ : Set H), ENNReal.ofReal (graphJacobian (gradient v y)) * g (graphMap ι e v y)
          ∂(volume : Measure H) :=
  setLIntegral_image_graphMap_of_contDiffOn ι he hperp hO hv MeasurableSet.empty
    (Set.empty_subset O) hg

end Consumers

/-- `x ↦ x⁻¹` on `(0, ∞)`: `C¹` on an open set with **no** globally `C¹` extension, so this
instance is out of reach of the pre-existing global theorem.  It is exactly what the countable
interior localization of the target provides. -/
theorem inv_on_Ioi {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : ℝ →ₗᵢ[ℝ] V) {e : V}
    (he : ‖e‖ = 1) (hperp : ∀ y : ℝ, ⟪ι y, e⟫ = (0 : ℝ)) {g : V → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in graphMap ι e (fun y : ℝ => y⁻¹) '' Set.Ioc (1 : ℝ) 2, g x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ ℝ)))
      = ∫⁻ y in Set.Ioc (1 : ℝ) 2,
          ENNReal.ofReal (graphJacobian (gradient (fun y : ℝ => y⁻¹) y))
            * g (graphMap ι e (fun y : ℝ => y⁻¹) y) ∂(volume : Measure ℝ) := by
  refine setLIntegral_image_graphMap_of_contDiffOn ι he hperp isOpen_Ioi
    (fun x hx => (contDiffAt_inv (𝕜 := ℝ) (ne_of_gt hx)).contDiffWithinAt)
    measurableSet_Ioc (fun x hx => lt_trans zero_lt_one hx.1) hg

/-! ### The pre-existing statement is preserved -/

theorem preserved_setLIntegral_image_graphChartMap :
    ∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
      [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V] (ι : H →ₗᵢ[ℝ] V) {e : V}, ‖e‖ = 1 →
      (∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) → ∀ (x₀ : V) {g : H → ℝ}, ContDiff ℝ 1 g →
      ∀ {s : Set H}, MeasurableSet s → ∀ {f : V → ℝ≥0∞}, Measurable f →
      ∫⁻ x in graphChartMap ι e x₀ g '' s, f x
          ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
        = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y))
            * f (graphChartMap ι e x₀ g y) ∂(volume : Measure H) := by
  intro H V _ _ _ _ _ _ _ _ _ _ ι e he hperp x₀ g hg s hs f hf
  exact setLIntegral_image_graphChartMap ι he hperp x₀ (g := g) (s := s) (f := f) hg hs hf

/-! ### Axiom audit -/

#print axioms FunctionalInequalities.Analysis.exists_contDiff_eqOn_ball
#print axioms FunctionalInequalities.Analysis.setLIntegral_image_graphMap
#print axioms FunctionalInequalities.Analysis.setLIntegral_image_graphMap_of_contDiffOn
#print axioms OpenGraphAudit.target
#print axioms OpenGraphAudit.global_case
#print axioms OpenGraphAudit.top_weight
#print axioms OpenGraphAudit.empty_parameter_set
#print axioms OpenGraphAudit.inv_on_Ioi
#print axioms OpenGraphAudit.preserved_setLIntegral_image_graphChartMap

end OpenGraphAudit
