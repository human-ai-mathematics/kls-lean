import FunctionalInequalities.Analysis.Coarea.Regular

noncomputable section
open MeasureTheory Filter Topology Set FunctionalInequalities
open scoped ENNReal ContDiff RealInnerProductSpace

namespace RegularCoareaAudit

/-- Verbatim full target `L9` of `Coarea/WeightedRouteStatements.lean` (regular open-domain `C¹`
coarea), including the CompleteSpace binder. -/
theorem target :
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    IsOpen O → ContDiffOn ℝ 1 u O → (∀ x ∈ O, fderiv ℝ u x ≠ 0) →
    MeasurableSet S → S ⊆ O → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ O S u g hO hu hreg hS hSO hg
  exact KLS.coarea_of_contDiffOn_of_fderiv_ne_zero hO hu hreg hS hSO hg

section FiniteDimensional

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section MeasurableSpace

variable [MeasurableSpace V] [BorelSpace V]

/-- The infinite weight remains inside both components of the target. -/
theorem top_weight
    {O S : Set V} {u : V → ℝ} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    (hreg : ∀ x ∈ O, fderiv ℝ u x ≠ 0) (hS : MeasurableSet S) (hSO : S ⊆ O) :
    AEMeasurable (fun t : ℝ => ∫⁻ _y in S ∩ {x | u x = t}, (⊤ : ℝ≥0∞)
      ∂(KLS.surfaceMeasure V)) volume ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * (⊤ : ℝ≥0∞) ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ _y in S ∩ {x | u x = t}, (⊤ : ℝ≥0∞) ∂(KLS.surfaceMeasure V) :=
  KLS.coarea_of_contDiffOn_of_fderiv_ne_zero hO hu hreg hS hSO measurable_const

/-- Empty set with an infinite weight: both integrals are zero. -/
theorem empty_set (u : V → ℝ) :
    AEMeasurable (fun t : ℝ => ∫⁻ _y in (∅ : Set V) ∩ {x | u x = t}, (⊤ : ℝ≥0∞)
      ∂(KLS.surfaceMeasure V)) volume ∧
    (∫⁻ x in (∅ : Set V), ‖gradient u x‖ₑ * (⊤ : ℝ≥0∞) ∂(volume : Measure V)) = 0 ∧
    (∫⁻ t, ∫⁻ _y in (∅ : Set V) ∩ {x | u x = t}, (⊤ : ℝ≥0∞)
      ∂(KLS.surfaceMeasure V)) = 0 := by simp

end MeasurableSpace

/-- In zero dimension every derivative is zero, so a regular domain must be empty. -/
theorem zero_dimension (hdim : Module.finrank ℝ V = 0)
    {O S : Set V} {u : V → ℝ} (hreg : ∀ x ∈ O, fderiv ℝ u x ≠ 0) (hSO : S ⊆ O) :
    O = ∅ ∧ S = ∅ := by
  let : Subsingleton V := Module.finrank_zero_iff.mp hdim
  have hO : O = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
    hreg x hx (Subsingleton.elim _ _)
  exact ⟨hO, Set.eq_empty_iff_forall_notMem.mpr fun x hx => by simpa [hO] using hSO hx⟩

/-- Infinite ambient volume is an actual instance, and the two integrals both equal infinity. -/
theorem infinite_volume :
    (volume : Measure ℝ) univ = ⊤ ∧
    AEMeasurable (fun t : ℝ => ∫⁻ _y in (univ : Set ℝ) ∩ {x | id x = t}, (1 : ℝ≥0∞)
      ∂(KLS.surfaceMeasure ℝ)) volume ∧
    (∫⁻ x : ℝ, ‖gradient id x‖ₑ * (1 : ℝ≥0∞)) = ⊤ ∧
    (∫⁻ t, ∫⁻ _y in (univ : Set ℝ) ∩ {x | id x = t}, (1 : ℝ≥0∞)
      ∂(KLS.surfaceMeasure ℝ)) = ⊤ := by
  have hr : ∀ x ∈ (univ : Set ℝ), fderiv ℝ id x ≠ 0 := by
    intro x hx hz
    have := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hz
    norm_num at this
  have h := target isOpen_univ contDiff_id.contDiffOn hr MeasurableSet.univ
    (subset_refl univ) (measurable_const (a := (1 : ℝ≥0∞)))
  have hleft : (∫⁻ x : ℝ, ‖gradient id x‖ₑ * (1 : ℝ≥0∞)) = ⊤ := by
    simp [gradient_eq_deriv']
  refine ⟨by simp, h.1, hleft, ?_⟩
  rw [← h.2]
  simpa using hleft

/-- No outside regularity: the function jumps at zero. -/
def jump (x : ℝ) : ℝ := if 0 < x then x else 1

theorem jump_eq_near {x : ℝ} (hx : 0 < x) : jump =ᶠ[𝓝 x] id := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  simp [jump, show 0 < y from hy]

theorem jump_on_Ioi :
    AEMeasurable (fun t : ℝ => ∫⁻ _y in Ioi 0 ∩ {x | jump x = t}, (⊤ : ℝ≥0∞)
      ∂(KLS.surfaceMeasure ℝ)) volume ∧
    (∫⁻ x in Ioi 0, ‖gradient jump x‖ₑ * (⊤ : ℝ≥0∞)) =
      ∫⁻ t, ∫⁻ _y in Ioi 0 ∩ {x | jump x = t}, (⊤ : ℝ≥0∞) ∂(KLS.surfaceMeasure ℝ) := by
  have hc : ContDiffOn ℝ 1 jump (Ioi 0) := by
    apply contDiffOn_id.congr
    intro x hx
    simp [jump, show 0 < x from hx]
  have hr : ∀ x ∈ Ioi (0 : ℝ), fderiv ℝ jump x ≠ 0 := by
    intro x hx
    rw [(jump_eq_near hx).fderiv_eq]
    intro hz
    have := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hz
    norm_num at this
  exact target isOpen_Ioi hc hr measurableSet_Ioi (subset_refl _) measurable_const

theorem jump_not_continuous : ¬ Continuous jump := by
  intro hc
  have hright : jump =ᶠ[𝓝[>] (0 : ℝ)] id := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [jump, show 0 < x from hx]
  have ht : Tendsto jump (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds |>.congr' hright.symm
  have hlim := tendsto_nhds_unique (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht
  norm_num [jump] at hlim

section MeasurableSpace

variable [MeasurableSpace V] [BorelSpace V]

/-- A whole affine line is an infinite-measure slice, at every level. -/
theorem infinite_surface_slices
    (ι : ℝ →ₗᵢ[ℝ] V) {e : V} (hsp : Analysis.IsGraphSplitting ι e)
    (hdim : Module.finrank ℝ V = 2) :
    (∀ t : ℝ, KLS.surfaceMeasure V {x | (⟪e, x⟫ : ℝ) = t} = ⊤) ∧
    AEMeasurable (fun t : ℝ => ∫⁻ _y in {x | (⟪e, x⟫ : ℝ) = t}, (1 : ℝ≥0∞)
      ∂(KLS.surfaceMeasure V)) volume ∧
    (∫⁻ x : V, ‖gradient (fun x => (⟪e, x⟫ : ℝ)) x‖ₑ * (1 : ℝ≥0∞)) =
      ∫⁻ t, ∫⁻ _y in {x | (⟪e, x⟫ : ℝ) = t}, (1 : ℝ≥0∞) ∂(KLS.surfaceMeasure V) := by
  have hslice : ∀ t : ℝ, {x | (⟪e, x⟫ : ℝ) = t} =
      Analysis.graphMap ι e (fun _ : ℝ => t) '' univ := by
    intro t
    ext x
    constructor
    · intro hx
      refine ⟨Analysis.graphProj ι x, mem_univ _, ?_⟩
      change ι (Analysis.graphProj ι x) + t • e = x
      rw [← hx]
      exact hsp.eq_ι_add_smul x
    · rintro ⟨y, -, rfl⟩
      exact hsp.inner_add_smul y t
  have hinf : ∀ t : ℝ, KLS.surfaceMeasure V {x | (⟪e, x⟫ : ℝ) = t} = ⊤ := by
    intro t
    rw [hslice, KLS.surfaceMeasure, hdim]
    have hdR : Module.finrank ℝ ℝ = 2 - 1 := by simp
    rw [← hdR]
    rw [Analysis.hausdorffNormalized_image_graphMap ι hsp.norm_e hsp.perp
      contDiff_const MeasurableSet.univ]
    simp [gradient_eq_deriv']
  have hr : ∀ x ∈ (univ : Set V), fderiv ℝ (fun x => (⟪e, x⟫ : ℝ)) x ≠ 0 := by
    intro x hx hz
    have heq := (innerSL ℝ e).hasFDerivAt (x := x) |>.fderiv
    have h := congrArg (fun L : V →L[ℝ] ℝ => L e) (heq.symm.trans hz)
    change (⟪e, e⟫ : ℝ) = 0 at h
    rw [hsp.inner_e_self] at h
    exact one_ne_zero h
  have h := target isOpen_univ (innerSL ℝ e).contDiff.contDiffOn hr MeasurableSet.univ
    (subset_refl univ) (measurable_const (a := (1 : ℝ≥0∞)))
  exact ⟨hinf, by simpa using h⟩

/-- The exact `target` call in dimension zero also returns both components. -/
theorem zero_dimension_target
    (hdim : Module.finrank ℝ V = 0) {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) (hreg : ∀ x ∈ O, fderiv ℝ u x ≠ 0)
    (hS : MeasurableSet S) (hSO : S ⊆ O) (hg : Measurable g) :
    S = ∅ ∧ AEMeasurable
      (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) volume ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) :=
  ⟨(zero_dimension hdim hreg hSO).2, target hO hu hreg hS hSO hg⟩

end MeasurableSpace

end FiniteDimensional

end RegularCoareaAudit

#print axioms FunctionalInequalities.Analysis.exists_contDiffOn_localInverse
#print axioms FunctionalInequalities.Analysis.exists_regularChart
#print axioms FunctionalInequalities.Analysis.levelChartDomain
#print axioms FunctionalInequalities.Analysis.levelChartHeight
#print axioms FunctionalInequalities.Analysis.isOpen_levelChartDomain
#print axioms FunctionalInequalities.Analysis.contDiffOn_levelChartHeight
#print axioms FunctionalInequalities.Analysis.levelChart_inverse
#print axioms FunctionalInequalities.Analysis.gradient_eq_smul_of_level_graph
#print axioms FunctionalInequalities.Analysis.abs_deriv_mul_norm_gradient
#print axioms FunctionalInequalities.Analysis.setLIntegral_prod_fibers
#print axioms FunctionalInequalities.Analysis.setLIntegral_prod_fibers_symm
#print axioms FunctionalInequalities.Analysis.continuous_deriv_snd
#print axioms FunctionalInequalities.Analysis.setLIntegral_image_verticalMap
#print axioms FunctionalInequalities.KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn
#print axioms FunctionalInequalities.Analysis.setLIntegral_coarea_graph_family
#print axioms FunctionalInequalities.Analysis.exists_coarea_neighborhood
#print axioms FunctionalInequalities.KLS.exists_regular_coarea_neighborhood
#print axioms FunctionalInequalities.KLS.coarea_of_contDiffOn_of_fderiv_ne_zero
#print axioms RegularCoareaAudit.target
#print axioms RegularCoareaAudit.top_weight
#print axioms RegularCoareaAudit.empty_set
#print axioms RegularCoareaAudit.zero_dimension
#print axioms RegularCoareaAudit.infinite_volume
#print axioms RegularCoareaAudit.jump
#print axioms RegularCoareaAudit.jump_eq_near
#print axioms RegularCoareaAudit.jump_on_Ioi
#print axioms RegularCoareaAudit.jump_not_continuous
#print axioms RegularCoareaAudit.infinite_surface_slices
#print axioms RegularCoareaAudit.zero_dimension_target
