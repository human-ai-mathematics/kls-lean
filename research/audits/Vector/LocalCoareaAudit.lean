import FunctionalInequalities.Analysis.Vector.Coarea.Local
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the weighted codimension-`m` graph area formula and the local coarea equality

**What is proved.**  `setLIntegral_image_vectorGraphMap` is the **weighted** codimension-`m` graph
area formula: the surface integral of an arbitrary measurable `ℝ≥0∞` weight over a piece of a `C¹`
graph is the Lebesgue integral of that weight against the graph area density.  Obligation `B2` of
`research/audits/Graph/AreaFormulaRouteStatements.lean` is its `f = 1` case, recovered verbatim
below.  Joining it to the ambient-side identity `setLIntegral_coareaJacobian_levelGraphFamily` by
Tonelli gives `setLIntegral_coarea_levelGraphFamily`, and hence
`exists_vector_coarea_neighborhood`: **every point where the differential is surjective has an open
neighbourhood on which the codimension-`m` coarea equality holds**, for every Borel subset and every
measurable weight, with the surface measure in dimension `finrank V - finrank W`.

**What is not proved.**  *Not the codimension-`m` regular coarea formula.*  Two things are missing:
the countable cover of a regular open set by such neighbourhoods with the disjoint patching, and the
codimension-`m` **weighted slice measurability** — the `AEMeasurable` statement for
`t ↦ ∫⁻ over S ∩ {u = t}` — which the patching needs in order to exchange a sum with the outer
integral.  The scalar analogues are the assembly in `Analysis/Coarea/Regular.lean` and
`Analysis/Hausdorff/Slice/OpenMeasurable.lean`.  Nothing about the critical set, sharp Sard or the Cheeger
comparisons is touched.

**`m = 1` returns the proved scalar statements.**  `codimension_one_graphArea` derives the
repository's already proved `Analysis.setLIntegral_image_graphMap`, and
`codimension_one_coarea_density` checks that the ambient density of the local coarea equality is
the gradient norm of the proved scalar theory.
-/

noncomputable section

open Set MeasureTheory Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal RealInnerProductSpace ContDiff

namespace VectorLocalCoareaAudit

section GraphArea

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **The weighted area formula, restated independently** and discharged through named arguments. -/
theorem weighted_graph_area (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set H} (hs : MeasurableSet s) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in (fun y => ι y + κ (γ y)) '' s, f x
        ∂(KLS.hausdorffNormalized V (finrank ℝ H))
      = ∫⁻ y in s, ENNReal.ofReal (Real.sqrt (LinearMap.det (LinearMap.id +
            LinearMap.adjoint ((fderiv ℝ γ y : H →ₗ[ℝ] K)) ∘ₗ (fderiv ℝ γ y : H →ₗ[ℝ] K))))
          * f (ι y + κ (γ y)) ∂(volume : Measure H) := by
  have h := setLIntegral_image_vectorGraphMap ι κ hperp hγ hs hf
  simp only [normDet_graphMapLinear ι κ hperp] at h
  exact h

/-- **The normalized graph area formula is the weight-one case**, recovered verbatim from the
weighted formula. -/
theorem unweighted_is_B2 (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set H} (hs : MeasurableSet s) :
    KLS.hausdorffNormalized V (finrank ℝ H) (vectorGraphMap ι κ γ '' s)
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet
          ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) ∂(volume : Measure H) := by
  have h := setLIntegral_image_vectorGraphMap ι κ hperp hγ hs (f := fun _ => 1) measurable_const
  simpa using h

/-- **No finiteness anywhere**: the whole parameter space with an arbitrary weight. -/
theorem whole_space (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in vectorGraphMap ι κ γ '' Set.univ, f x
        ∂(KLS.hausdorffNormalized V (finrank ℝ H))
      = ∫⁻ y, ENNReal.ofReal (LinearMap.normDet
            ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) * f (vectorGraphMap ι κ γ y)
          ∂(volume : Measure H) := by
  have h := setLIntegral_image_vectorGraphMap ι κ hperp hγ MeasurableSet.univ hf
  simpa using h

/-- An **identically infinite weight** is inside the statement. -/
theorem infinite_weight (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) {γ : H → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set H} (hs : MeasurableSet s) :
    ∫⁻ _ in vectorGraphMap ι κ γ '' s, (⊤ : ℝ≥0∞)
        ∂(KLS.hausdorffNormalized V (finrank ℝ H))
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet
            ((graphMapLinear ι κ (fderiv ℝ γ y) : H →ₗ[ℝ] V))) * ⊤ ∂(volume : Measure H) :=
  setLIntegral_image_vectorGraphMap ι κ hperp hγ hs measurable_const

/-- A **zero-dimensional parameter space** is inside the statement. -/
theorem zero_dimensional_parameter (ι : EuclideanSpace ℝ (Fin 0) →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : EuclideanSpace ℝ (Fin 0)) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    {γ : EuclideanSpace ℝ (Fin 0) → K} (hγ : ContDiff ℝ 1 γ)
    {s : Set (EuclideanSpace ℝ (Fin 0))} (hs : MeasurableSet s) {f : V → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x in vectorGraphMap ι κ γ '' s, f x
        ∂(KLS.hausdorffNormalized V (finrank ℝ (EuclideanSpace ℝ (Fin 0))))
      = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet
            ((graphMapLinear ι κ (fderiv ℝ γ y) : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] V)))
          * f (vectorGraphMap ι κ γ y) ∂(volume : Measure (EuclideanSpace ℝ (Fin 0))) :=
  setLIntegral_image_vectorGraphMap ι κ hperp hγ hs hf

end GraphArea

/-! ### The codimension-one case is the proved scalar area formula -/

section CodimensionOne

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **`m = 1` is the proved scalar weighted area formula**, `Analysis.setLIntegral_image_graphMap`,
recovered from the codimension-`m` statement. -/
theorem codimension_one_graphArea (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in graphMap ι e g '' s, f x ∂(KLS.hausdorffNormalized V (finrank ℝ H))
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y)) * f (graphMap ι e g y)
          ∂(volume : Measure H) :=
  setLIntegral_image_graphMap ι he hperp hg hs hf

omit [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H] [MeasurableSpace V]
  [BorelSpace V] in
/-- **The ambient density of the local coarea equality is the gradient norm when `m = 1`.**  This is
the proved `Analysis.coareaJacobian_fderiv`, restated here so the scalar reading of
`setLIntegral_coarea_levelGraphFamily` is explicit. -/
theorem codimension_one_coarea_density (u : V → ℝ) (x : V) :
    ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) = ‖gradient u x‖ₑ := by
  rw [coareaJacobian_fderiv, ofReal_norm]

end CodimensionOne

/-! ### The local coarea equality -/

section LocalCoarea

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **The local coarea equality, restated independently** and discharged through named arguments.
The hypotheses are: `u` is `C¹` on an open set and its differential is surjective at the point.
Nothing else — no finiteness, no boundedness, no integrability, no regular value. -/
theorem local_coarea {u : V → W} {O : Set V} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    {x₀ : V} (hx₀ : x₀ ∈ O) (hreg : Function.Surjective ((fderiv ℝ u x₀ : V →ₗ[ℝ] W))) :
    ∃ N : Set V, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      ∀ S : Set V, MeasurableSet S → S ⊆ N → ∀ g : V → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ x in S ∩ {x : V | u x = t}, g x
              ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))
              ∂(volume : Measure W) :=
  exists_vector_coarea_neighborhood hO hu hx₀ ((coareaJacobian_ne_zero_iff _).2 hreg)

/-- **A zero-dimensional target makes every point regular**, and the local equality degenerates
correctly: the outer integral is over a single level. -/
theorem zero_dimensional_target [Subsingleton W] {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O) :
    ∃ N : Set V, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      ∀ S : Set V, MeasurableSet S → S ⊆ N → ∀ g : V → ℝ≥0∞, Measurable g →
        ∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ x in S ∩ {x : V | u x = t}, g x
              ∂(KLS.hausdorffNormalized V (finrank ℝ V - finrank ℝ W))
              ∂(volume : Measure W) := by
  refine exists_vector_coarea_neighborhood hO hu hx₀ ?_
  rw [coareaJacobian, LinearMap.normDet_of_subsingleton]
  exact one_ne_zero

end LocalCoarea

end VectorLocalCoareaAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.map_vectorGraphMap_withDensity
#print axioms FunctionalInequalities.Analysis.setLIntegral_image_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.fderiv_fst_eq
#print axioms FunctionalInequalities.Analysis.continuous_normDet_graphMapLinear_fderiv_fst
#print axioms FunctionalInequalities.Analysis.setLIntegral_coarea_levelGraphFamily
#print axioms FunctionalInequalities.Analysis.exists_vector_coarea_neighborhood
#print axioms VectorLocalCoareaAudit.weighted_graph_area
#print axioms VectorLocalCoareaAudit.unweighted_is_B2
#print axioms VectorLocalCoareaAudit.whole_space
#print axioms VectorLocalCoareaAudit.infinite_weight
#print axioms VectorLocalCoareaAudit.zero_dimensional_parameter
#print axioms VectorLocalCoareaAudit.codimension_one_graphArea
#print axioms VectorLocalCoareaAudit.codimension_one_coarea_density
#print axioms VectorLocalCoareaAudit.local_coarea
#print axioms VectorLocalCoareaAudit.zero_dimensional_target
