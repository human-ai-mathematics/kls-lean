module

public import FunctionalInequalities.Analysis.Vector.Coarea.RegularChart
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the codimension-`m` level chart

**What is proved.**  Near a point where the differential of `u : V → W` is surjective, the fibres of
`u` are simultaneously the graphs of **one globally `C¹` map** `ψ` over a fixed parameter space,
with the level as a parameter: `exists_levelGraphFamily` and its regular-point form
`exists_levelGraphFamily_of_coareaJacobian_ne_zero`.  The graph map is a bijection of the open
parameter–level domain onto an open neighbourhood, `slice_eq_image_vectorGraphMap` identifies each
fibre with a graph, and `hausdorffNormalized_slice_of_levelGraphFamily` measures that fibre with the
proved normalized graph area formula.
`normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily` shows the chart feeds the fibre Jacobian
identity `normDet_fderiv_mul_coareaJacobian`.

**What is not proved.**  *No coarea formula.*  The ambient side still needs the fibrewise
`m`-dimensional change of variables, and the fibre side still needs the **weighted** area formula
(the analogue of `setLIntegral_image_graphMap`); `hausdorffNormalized_slice_of_levelGraphFamily`
carries weight one only.  Nothing about the critical set, sharp Sard or the Cheeger comparisons is
touched.

**`m = 1` returns the proved scalar shape.**  `codimension_one_levelGraphFamily` below produces the
family in exactly the form `u (ι y + ψ (y, t) • e) = t` that the proved scalar
`Analysis.setLIntegral_coarea_graph_family` consumes, from exactly the scalar hypotheses
`gradient u x₀ = c • e` with `c ≠ 0`.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal RealInnerProductSpace ContDiff

namespace VectorRegularChartAudit

section Restatements

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **The level-graph family, restated independently** and discharged through named arguments. -/
theorem level_graph_family (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    (hspan : ∀ x : V, ι (graphProj ι x) + κ (graphProj κ x) = x)
    {u : V → W} {O : Set V} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hker : ∀ y : H, fderiv ℝ u x₀ (ι y) = 0)
    (hQ : Function.Bijective fun z : K => fderiv ℝ u x₀ (κ z)) :
    ∃ (Ω : Set (H × W)) (ψ : H × W → K) (N : Set V),
      IsOpen Ω ∧ ContDiff ℝ 1 ψ ∧ IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      (∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2) ∧
      (fun p : H × W => ι p.1 + κ (ψ p)) '' Ω = N ∧
      Set.InjOn (fun p : H × W => ι p.1 + κ (ψ p)) Ω := by
  refine exists_levelGraphFamily ⟨hperp, hspan⟩ hO hu hx₀ (ContinuousLinearMap.ext fun y => ?_) hQ
  simpa using hker y

/-- **No finiteness anywhere**: the level family may be taken with `O` the whole space. -/
theorem whole_space {u : V → W} (hu : ContDiff ℝ 1 u) (x₀ : V)
    (hreg : coareaJacobian (fderiv ℝ u x₀) ≠ 0) :
    ∃ (P : Submodule ℝ V) (Ω : Set (P × W)) (ψ : P × W → (Pᗮ : Submodule ℝ V)) (N : Set V),
      IsVectorGraphSplitting P.subtypeₗᵢ (Pᗮ).subtypeₗᵢ ∧
      finrank ℝ (Pᗮ : Submodule ℝ V) = finrank ℝ W ∧
      IsOpen Ω ∧ ContDiff ℝ 1 ψ ∧ IsOpen N ∧ x₀ ∈ N ∧ N ⊆ Set.univ ∧
      (∀ p ∈ Ω, u (P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) = p.2) ∧
      (fun p : P × W => P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) '' Ω = N ∧
      Set.InjOn (fun p : P × W => P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) Ω :=
  exists_levelGraphFamily_of_coareaJacobian_ne_zero isOpen_univ hu.contDiffOn (mem_univ x₀) hreg

/-- A **zero-dimensional parameter space** is inside the statement: the fibres are single points. -/
theorem zero_dimensional_parameter {ι : EuclideanSpace ℝ (Fin 0) →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hs : IsVectorGraphSplitting ι κ) {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hker : fderiv ℝ u x₀ ∘L ι.toContinuousLinearMap = 0)
    (hQ : Function.Bijective (fderiv ℝ u x₀ ∘L κ.toContinuousLinearMap)) :
    ∃ (Ω : Set (EuclideanSpace ℝ (Fin 0) × W)) (ψ : EuclideanSpace ℝ (Fin 0) × W → K) (N : Set V),
      IsOpen Ω ∧ ContDiff ℝ 1 ψ ∧ IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      (∀ p ∈ Ω, u (ι p.1 + κ (ψ p)) = p.2) ∧
      (fun p => ι p.1 + κ (ψ p)) '' Ω = N ∧
      Set.InjOn (fun p => ι p.1 + κ (ψ p)) Ω :=
  exists_levelGraphFamily hs hO hu hx₀ hker hQ

/-- **A zero-dimensional target makes every point regular.**  With `W` a subsingleton the coarea
Jacobian is `1`, so the family exists at every point of `O` with no further hypothesis. -/
theorem zero_dimensional_target [Subsingleton W] {u : V → W} {O : Set V} (hO : IsOpen O)
    (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O) :
    coareaJacobian (fderiv ℝ u x₀) ≠ 0 ∧
    ∃ (P : Submodule ℝ V) (Ω : Set (P × W)) (ψ : P × W → (Pᗮ : Submodule ℝ V)) (N : Set V),
      IsVectorGraphSplitting P.subtypeₗᵢ (Pᗮ).subtypeₗᵢ ∧
      finrank ℝ (Pᗮ : Submodule ℝ V) = finrank ℝ W ∧
      IsOpen Ω ∧ ContDiff ℝ 1 ψ ∧ IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      (∀ p ∈ Ω, u (P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) = p.2) ∧
      (fun p : P × W => P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) '' Ω = N ∧
      Set.InjOn (fun p : P × W => P.subtypeₗᵢ p.1 + (Pᗮ).subtypeₗᵢ (ψ p)) Ω := by
  have hreg : coareaJacobian (fderiv ℝ u x₀) ≠ 0 := by
    rw [coareaJacobian, LinearMap.normDet_of_subsingleton]
    exact one_ne_zero
  exact ⟨hreg, exists_levelGraphFamily_of_coareaJacobian_ne_zero hO hu hx₀ hreg⟩

end Restatements

/-! ### The codimension-one case is the proved scalar shape -/

section CodimensionOne

variable {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ V] in
/-- The one-dimensional normal factor spanned by a unit vector. -/
def lineIsometry {e : V} (he : ‖e‖ = 1) : ℝ →ₗᵢ[ℝ] V where
  toLinearMap := LinearMap.toSpanSingleton ℝ V e
  norm_map' := by
    intro t
    simp [LinearMap.toSpanSingleton_apply, norm_smul, he]

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ V] in
@[simp] theorem lineIsometry_apply {e : V} (he : ‖e‖ = 1) (t : ℝ) :
    lineIsometry he t = t • e := rfl

omit [FiniteDimensional ℝ H] in
theorem graphProj_lineIsometry {e : V} (he : ‖e‖ = 1) (x : V) :
    graphProj (lineIsometry he) x = ⟪e, x⟫ := by
  refine ext_inner_right ℝ fun s => ?_
  rw [graphProj, ContinuousLinearMap.adjoint_inner_left]
  simp only [LinearIsometry.coe_toContinuousLinearMap, lineIsometry_apply,
    real_inner_smul_right, RCLike.inner_apply, conj_trivial]
  rw [real_inner_comm]

/-- **A codimension-one splitting is a vector splitting with one-dimensional normal factor.** -/
theorem isVectorGraphSplitting_of_isGraphSplitting {ι : H →ₗᵢ[ℝ] V} {e : V}
    (hsp : IsGraphSplitting ι e) : IsVectorGraphSplitting ι (lineIsometry hsp.norm_e) where
  perp := by
    intro y s
    rw [lineIsometry_apply, real_inner_smul_right, hsp.perp y, mul_zero]
  split := by
    intro x
    rw [graphProj_lineIsometry, lineIsometry_apply]
    exact hsp.split x

/-- **`m = 1` produces the proved scalar shape.**  From exactly the scalar hypotheses of
`Analysis.exists_coarea_neighborhood` — a graph splitting and `gradient u x₀ = c • e` with `c ≠ 0` —
the codimension-`m` chart yields a family `u (ι y + ψ (y, t) • e) = t` on an open joint domain,
which
is the hypothesis `hlevel` of the proved `Analysis.setLIntegral_coarea_graph_family`. -/
theorem codimension_one_levelGraphFamily {ι : H →ₗᵢ[ℝ] V} {e : V} (hsp : IsGraphSplitting ι e)
    {u : V → ℝ} {O : Set V} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    {c : ℝ} (hc : c ≠ 0) (hgrad : gradient u x₀ = c • e) :
    ∃ (Ω : Set (H × ℝ)) (ψ : H × ℝ → ℝ) (N : Set V),
      IsOpen Ω ∧
        ContDiff ℝ 1 ψ ∧
          IsOpen N ∧
            x₀ ∈ N ∧
              N ⊆ O ∧
                (∀ p ∈ Ω, u (ι p.1 + ψ p • e) = p.2) ∧
                  (fun p : H × ℝ => ι p.1 + ψ p • e) '' Ω = N ∧
                    Set.InjOn (fun p : H × ℝ => ι p.1 + ψ p • e) Ω := by
  have hd : ∀ v : V, fderiv ℝ u x₀ v = ⟪gradient u x₀, v⟫ := by
    intro v
    rw [← toDual_gradient (𝕜 := ℝ) (f := u) (x := x₀)]
    rfl
  have hker : fderiv ℝ u x₀ ∘L ι.toContinuousLinearMap = 0 := by
    refine ContinuousLinearMap.ext fun y => ?_
    simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      zero_apply]
    rw [hd, hgrad, real_inner_smul_left, hsp.perp' y, mul_zero]
  have hQ :
    Function.Bijective (fderiv ℝ u x₀ ∘L (lineIsometry hsp.norm_e).toContinuousLinearMap) := by
    have hval :
      ∀ s : ℝ, (fderiv ℝ u x₀ ∘L (lineIsometry hsp.norm_e).toContinuousLinearMap) s = c * s := by
      intro s
      simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        lineIsometry_apply]
      rw [hd, hgrad, real_inner_smul_right, real_inner_smul_left, hsp.inner_e_self, mul_one]
      ring
    constructor
    · intro s s' h
      rw [hval, hval] at h
      exact mul_left_cancel₀ hc h
    · intro w
      exact ⟨c⁻¹ * w, by rw [hval, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  obtain ⟨Ω, ψ, N, hΩ, hψ, hN, hxN, hNO, hlevel, himg, hinj⟩ :=
    exists_levelGraphFamily (isVectorGraphSplitting_of_isGraphSplitting hsp) hO hu hx₀ hker hQ
  exact ⟨Ω, ψ, N, hΩ, hψ, hN, hxN, hNO, hlevel, himg, hinj⟩

end CodimensionOne

end VectorRegularChartAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.normalEquiv
#print axioms FunctionalInequalities.Analysis.normalEquiv_apply
#print axioms FunctionalInequalities.Analysis.flattenVectorCLM
#print axioms FunctionalInequalities.Analysis.unflattenVectorCLM
#print axioms FunctionalInequalities.Analysis.flattenVectorEquiv
#print axioms FunctionalInequalities.Analysis.coe_flattenVectorEquiv
#print axioms FunctionalInequalities.Analysis.contDiffOn_flattenVectorChart
#print axioms FunctionalInequalities.Analysis.hasFDerivAt_flattenVectorChart
#print axioms FunctionalInequalities.Analysis.exists_vectorRegularChart
#print axioms FunctionalInequalities.Analysis.contDiffOn_vectorLevelHeight
#print axioms FunctionalInequalities.Analysis.vectorLevelChart_inverse
#print axioms FunctionalInequalities.Analysis.exists_levelGraphFamily
#print axioms FunctionalInequalities.Analysis.comp_ker_subtypeₗᵢ_eq_zero
#print axioms FunctionalInequalities.Analysis.bijective_comp_orthogonal_subtypeₗᵢ
#print axioms FunctionalInequalities.Analysis.exists_levelGraphFamily_of_coareaJacobian_ne_zero
#print axioms FunctionalInequalities.Analysis.slice_eq_image_vectorGraphMap
#print axioms FunctionalInequalities.Analysis.hausdorffNormalized_slice_of_levelGraphFamily
#print axioms FunctionalInequalities.Analysis.normDet_fderiv_mul_coareaJacobian_of_levelGraphFamily
#print axioms VectorRegularChartAudit.level_graph_family
#print axioms VectorRegularChartAudit.whole_space
#print axioms VectorRegularChartAudit.zero_dimensional_parameter
#print axioms VectorRegularChartAudit.zero_dimensional_target
#print axioms VectorRegularChartAudit.graphProj_lineIsometry
#print axioms VectorRegularChartAudit.isVectorGraphSplitting_of_isGraphSplitting
#print axioms VectorRegularChartAudit.codimension_one_levelGraphFamily
