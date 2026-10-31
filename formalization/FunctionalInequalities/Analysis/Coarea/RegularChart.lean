module

public import FunctionalInequalities.Analysis.LocalInverse
public import FunctionalInequalities.Analysis.Graph.Implicit

/-! # C¹ charts for a family of regular levels

Unlike a representation of one fixed level, these charts retain the level as a parameter.
The local inverse and the height are C¹ on open domains, with no global regularity assumption.
-/

@[expose] public section

noncomputable section
open Set Filter Topology
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A chart flattening every nearby level, with a C¹ inverse on its whole target. -/
theorem exists_regularChart (ι : H →ₗᵢ[ℝ] V) {e : V} (hsp : IsGraphSplitting ι e)
    {u : V → ℝ} {O : Set V} (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O)
    {x₀ : V} (hx₀ : x₀ ∈ O) {c : ℝ} (hc : c ≠ 0)
    (hgrad : gradient u x₀ = c • e) :
    ∃ D : OpenPartialHomeomorph V V,
      (∀ x, D x = graphRetract ι x + u x • e) ∧
      x₀ ∈ D.source ∧ D.source ⊆ O ∧
      ContDiffOn ℝ 1 D D.source ∧ ContDiffOn ℝ 1 D.symm D.target := by
  have hΦ : ContDiffOn ℝ 1 (fun x => graphRetract ι x + u x • e) O :=
    (graphRetract ι).contDiff.contDiffOn.add (hu.smul contDiffOn_const)
  have hd : HasFDerivAt (fun x => graphRetract ι x + u x • e)
      (flattenEquiv ι hsp hc : V →L[ℝ] V) x₀ := by
    have h := (graphRetract ι).hasFDerivAt.add
      (((hu.contDiffAt (hO.mem_nhds hx₀)).differentiableAt one_ne_zero).hasFDerivAt.smul_const e)
    rw [smulRight_fderiv_eq ι hgrad] at h
    exact h
  obtain ⟨D, hD, hxD, hDO, hDC, hIC⟩ := exists_contDiffOn_localInverse hO hΦ hx₀ hd
  exact ⟨D, fun x => congrFun hD x, hxD, hDO, hDC, hIC⟩

variable (ι : H →ₗᵢ[ℝ] V) (e : V) (D : OpenPartialHomeomorph V V)

/-- Open domain for the tangential coordinate and the level parameter. -/
def levelChartDomain : Set (H × ℝ) := {p | ι p.1 + p.2 • e ∈ D.target}

/-- Height of the inverse chart, as a function of both the tangential coordinate and the level. -/
def levelChartHeight (p : H × ℝ) : ℝ := ⟪e, D.symm (ι p.1 + p.2 • e)⟫

section LevelCharts

omit [FiniteDimensional ℝ H] [FiniteDimensional ℝ V]
theorem isOpen_levelChartDomain : IsOpen (levelChartDomain ι e D) :=
  D.open_target.preimage ((ι.continuous.comp continuous_fst).add
    (continuous_snd.smul continuous_const))

theorem contDiffOn_levelChartHeight (hD : ContDiffOn ℝ 1 D.symm D.target) :
    ContDiffOn ℝ 1 (levelChartHeight ι e D) (levelChartDomain ι e D) := by
  exact (innerSL ℝ e).contDiff.contDiffOn.comp
    (hD.comp ((ι.toContinuousLinearMap.contDiff.comp contDiff_fst).add
      (contDiff_snd.smul contDiff_const)).contDiffOn (fun _ hp => hp))
    (fun _ _ => mem_univ _)

end LevelCharts

variable {ι e D}

/-- The inverse chart is precisely a graph at each level, and that graph attains the level.
Both conclusions hold on one joint open parameter domain. -/
theorem levelChart_inverse (hsp : IsGraphSplitting ι e) {u : V → ℝ}
    (hD : ∀ x, D x = graphRetract ι x + u x • e) {p : H × ℝ}
    (hp : p ∈ levelChartDomain ι e D) :
    D.symm (ι p.1 + p.2 • e) = graphMap ι e (fun y => levelChartHeight ι e D (y, p.2)) p.1 ∧
      u (D.symm (ι p.1 + p.2 • e)) = p.2 := by
  set z := D.symm (ι p.1 + p.2 • e)
  have h := D.right_inv hp
  rw [hD] at h
  have hu : u z = p.2 := by
    have hi := congrArg (fun v : V => (⟪e, v⟫ : ℝ)) h
    simpa only [inner_add_right, hsp.inner_e_retract, real_inner_smul_right,
      hsp.inner_e_self, hsp.perp' _, zero_add, mul_one] using hi
  have hr : graphRetract ι z = ι p.1 := by
    rw [show u (D.symm (ι p.1 + p.2 • e)) = p.2 from hu] at h
    exact add_right_cancel h
  refine ⟨?_, hu⟩
  change z = ι p.1 + (⟪e, z⟫ : ℝ) • e
  rw [← hr]
  exact (hsp.split z).symm

/-- Local differential identity for a graph lying in one level. Only differentiability at
the point and a local level identity are needed. -/
theorem gradient_eq_smul_of_level_graph (hsp : IsGraphSplitting ι e) {φ : V → ℝ}
    {g : H → ℝ} {y : H} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (graphMap ι e g y)) (hg : DifferentiableAt ℝ g y)
    (hlevel : (φ ∘ graphMap ι e g) =ᶠ[𝓝 y] fun _ => t) :
    gradient φ (graphMap ι e g y) =
      (⟪gradient φ (graphMap ι e g y), e⟫ : ℝ) • (ι (-gradient g y) + e) := by
  set Ψ : H → V := graphMap ι e g with hΨ
  set a : V := gradient φ (Ψ y) with ha
  set β : ℝ := ⟪a, e⟫ with hβ
  have hΨderiv : HasFDerivAt Ψ (graphLinear ι e (gradient g y)) y :=
    hasFDerivAt_graphMap ι e hg
  have hcomp : HasFDerivAt (φ ∘ Ψ)
      ((fderiv ℝ φ (Ψ y)).comp (graphLinear ι e (gradient g y))) y :=
    hφ.hasFDerivAt.comp y hΨderiv
  have hzeroderiv : HasFDerivAt (φ ∘ Ψ) (0 : H →L[ℝ] ℝ) y :=
    (hasFDerivAt_const t y).congr_of_eventuallyEq hlevel
  have hkey : (fderiv ℝ φ (Ψ y)).comp (graphLinear ι e (gradient g y)) = 0 :=
    hcomp.unique hzeroderiv
  have hnormal : (innerSL ℝ (gradient φ (Ψ y))).comp (graphLinear ι e (gradient g y)) = 0 := by
    rw [fderiv_eq_innerSL_gradient φ (Ψ y)]
    exact hkey
  exact hsp.eq_normal_of_comp_graphLinear_eq_zero hnormal
/-- Pointwise matching of the one-dimensional inverse Jacobian and the graph area factor.
No division or finite-weight assumption occurs. -/
theorem abs_deriv_mul_norm_gradient (hsp : IsGraphSplitting ι e)
    {ψ : H × ℝ → ℝ} {Ω : Set (H × ℝ)} (hΩ : IsOpen Ω)
    (hψ : ContDiffOn ℝ 1 ψ Ω) {u : V → ℝ}
    (hlevel : ∀ p ∈ Ω, u (ι p.1 + ψ p • e) = p.2)
    {p : H × ℝ} (hp : p ∈ Ω) (hu : DifferentiableAt ℝ u (ι p.1 + ψ p • e)) :
    |deriv (fun t => ψ (p.1, t)) p.2| * ‖gradient u (ι p.1 + ψ p • e)‖ =
      graphJacobian (gradient (fun y => ψ (y, p.2)) p.1) := by
  have hψp := (hψ.contDiffAt (hΩ.mem_nhds hp)).differentiableAt one_ne_zero
  have hh : DifferentiableAt ℝ (fun y => ψ (y, p.2)) p.1 :=
    hψp.comp p.1 (differentiableAt_id.prodMk (differentiableAt_const _))
  have hv : DifferentiableAt ℝ (fun t => ψ (p.1, t)) p.2 :=
    hψp.comp p.2 ((differentiableAt_const _).prodMk differentiableAt_id)
  have hheq : (u ∘ graphMap ι e (fun y => ψ (y, p.2))) =ᶠ[𝓝 p.1] fun _ => p.2 := by
    have hn := (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hΩ.mem_nhds hp)
    filter_upwards [hn] with y hy using hlevel (y, p.2) hy
  have hgrad := gradient_eq_smul_of_level_graph hsp hu hh hheq
  let d := deriv (fun t => ψ (p.1, t)) p.2
  let β : ℝ := ⟪gradient u (ι p.1 + ψ p • e), e⟫
  have hd : d * β = 1 := by
    have hpath : HasDerivAt (fun t => ι p.1 + ψ (p.1, t) • e) (d • e) p.2 :=
      (hv.hasDerivAt.smul_const e).const_add (ι p.1)
    have hc := hu.hasFDerivAt.comp_hasDerivAt p.2 hpath
    have hveq : (fun t => u (ι p.1 + ψ (p.1, t) • e)) =ᶠ[𝓝 p.2] id := by
      have hn := (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds (hΩ.mem_nhds hp)
      filter_upwards [hn] with t ht using hlevel (p.1, t) ht
    have hd' := hc.unique ((hasDerivAt_id p.2).congr_of_eventuallyEq hveq)
    rw [← fderiv_eq_innerSL_gradient u (ι p.1 + ψ p • e)] at hd'
    simpa only [innerSL_apply_apply, real_inner_smul_right] using hd'
  have hnorm : ‖ι (-gradient (fun y => ψ (y, p.2)) p.1) + e‖ =
      graphJacobian (gradient (fun y => ψ (y, p.2)) p.1) := by
    have hs := hsp.norm_add_smul_sq (-gradient (fun y => ψ (y, p.2)) p.1) 1
    simp only [one_smul, norm_neg, one_pow] at hs
    rw [graphJacobian, ← add_comm (‖gradient (fun y => ψ (y, p.2)) p.1‖ ^ 2) 1,
      ← hs, Real.sqrt_sq (norm_nonneg _)]
  change |d| * ‖gradient u (graphMap ι e (fun y => ψ (y, p.2)) p.1)‖ = _
  rw [hgrad, norm_smul, Real.norm_eq_abs, hnorm, ← mul_assoc, ← abs_mul]
  change |d * β| * _ = _
  rw [hd, abs_one, one_mul]

end FunctionalInequalities.Analysis
