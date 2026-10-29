import FunctionalInequalities.Analysis.Coarea.RegularChart
import FunctionalInequalities.Analysis.Coarea.FiberIntegral
import FunctionalInequalities.Analysis.Graph.Divergence
import FunctionalInequalities.Analysis.Hausdorff.Slice.OpenMeasurable

/-! # Weighted coarea on regular open C¹ domains (regular-domain coarea)

`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` proves both weighted slice measurability and
coarea for arbitrary Borel `S ⊆ O`, arbitrary measurable ENNReal weights, and every dimension.
The gradient and normalized Hausdorff surface measure are the existing repository definitions.

The local calculation uses the measure-preserving orthogonal splitting from
`SubgraphDivergence`, proved via `WithLp 2`, followed by the one-dimensional specialization of
Mathlib's Jacobian theorem on each vertical fiber. Tonelli gives the ambient integral. The identity
`abs_deriv_mul_norm_gradient` matches its density with the graph area density, entirely by
multiplication, including infinite weights. Only volume measures enter the Tonelli steps.

`LocalInverse` and `RegularChart` retain the level parameter in a joint C¹ inverse. An interior
bump gives a global representative of its height on a smaller parameter ball, where the global
graph-area theorem applies. Separately, a local representative of `u` on a ball allows this
calculation with no regularity outside `O`. Neither representative is a global extension of all
of `O`. Second countability and disjoint Borel pieces assemble the final equality; weighted
slice measurability is established independently in `OpenSliceMeasurable`.

This proves only the regular-domain coarea identity. It does not use critical slicing, Sard
or Whitney extension.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Coarea on a Borel piece of a joint graph family. The joint parameterization is C¹,
and its value under `u` is the level coordinate on an open parameter domain. -/
theorem setLIntegral_coarea_graph_family (ι : H →ₗᵢ[ℝ] V) {e : V}
    (hsp : IsGraphSplitting ι e) {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    {ψ : H × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) {Ω A : Set (H × ℝ)}
    (hΩ : IsOpen Ω) (hA : MeasurableSet A) (hAΩ : A ⊆ Ω)
    (hlevel : ∀ p ∈ Ω, u (ι p.1 + ψ p • e) = p.2)
    {g : V → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in (fun p : H × ℝ => ι p.1 + ψ p • e) '' A,
      ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ x in ((fun p : H × ℝ => ι p.1 + ψ p • e) '' A) ∩ {x | u x = t},
        g x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)) := by
  let Ψ : H × ℝ → V := fun p => ι p.1 + ψ p • e
  let T : H × ℝ → H × ℝ := fun p => (p.1, ψ p)
  let E := splitHomeomorph hsp (0 : V)
  have hΨ : Continuous Ψ := (ι.continuous.comp continuous_fst).add
    (hψ.continuous.smul continuous_const)
  have hT : InjOn T A := by
    intro p hp q hq heq
    change (p.1, ψ p) = (q.1, ψ q) at heq
    have hy := (Prod.mk.inj heq).1
    have hz := (Prod.mk.inj heq).2
    have hx : Ψ p = Ψ q := by simp only [Ψ, hy, hz]
    have ht : p.2 = q.2 := by
      rw [← hlevel p (hAΩ hp), ← hlevel q (hAΩ hq)]
      exact congrArg u hx
    exact Prod.ext hy ht
  have hE : ∀ p, E (T p) = Ψ p := by intro p; simp [E, T, Ψ]
  have himage : Ψ '' A = E '' (T '' A) := by
    rw [← Set.image_comp]
    congr 1
    funext p
    exact (hE p).symm
  have hgrad : Continuous (gradient u) :=
    BakryEmery.continuous_gradient_of_contDiff hu (by simp)
  let f : V → ℝ≥0∞ := fun x => ‖gradient u x‖ₑ * g x
  have hf : Measurable f := hgrad.enorm.measurable.mul hg
  let J : H × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |deriv (fun t => ψ (p.1, t)) p.2| * f (Ψ p)
  have hJ : Measurable J :=
    (continuous_deriv_snd hψ).abs.measurable.ennreal_ofReal.mul (hf.comp hΨ.measurable)
  have hvol : (∫⁻ x in Ψ '' A, f x ∂(volume : Measure V)) =
      ∫⁻ p in A, J p ∂(volume : Measure (H × ℝ)) := by
    rw [himage, ← (measurePreserving_splitHomeomorph hsp (0 : V)).setLIntegral_comp_emb
      E.measurableEmbedding f (T '' A)]
    change (∫⁻ a in (fun p : H × ℝ => (p.1, ψ p)) '' A, (f ∘ E) a) = _
    rw [setLIntegral_image_verticalMap hψ hA hT (hf.comp E.continuous.measurable)]
    apply setLIntegral_congr_fun hA
    intro p hp
    change ENNReal.ofReal _ * f (E (T p)) = _
    rw [hE]
  have hslice : ∀ t, (Ψ '' A) ∩ {x | u x = t} =
      graphMap ι e (fun y => ψ (y, t)) '' {y | (y, t) ∈ A} := by
    intro t
    ext x
    constructor
    · rintro ⟨⟨⟨y, s⟩, hp, rfl⟩, ht⟩
      have hs : s = t := (hlevel (y, s) (hAΩ hp)).symm.trans ht
      subst s
      exact ⟨y, hp, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y, t), hy, rfl⟩, hlevel (y, t) (hAΩ hy)⟩
  change (∫⁻ x in Ψ '' A, f x ∂(volume : Measure V)) = _
  rw [hvol, Measure.volume_eq_prod, setLIntegral_prod_fibers_symm hA hJ]
  apply lintegral_congr
  intro t
  have hAt : MeasurableSet {y : H | (y, t) ∈ A} :=
    hA.preimage (measurable_id.prodMk measurable_const)
  have hψt : ContDiff ℝ 1 (fun y => ψ (y, t)) := hψ.comp (contDiff_id.prodMk contDiff_const)
  rw [hslice, setLIntegral_image_graphMap ι hsp.norm_e hsp.perp hψt hAt hg]
  apply setLIntegral_congr_fun hAt
  intro y hy
  have hpoint := abs_deriv_mul_norm_gradient hsp hΩ hψ.contDiffOn hlevel (hAΩ hy)
    (hu.differentiable one_ne_zero _)
  change ENNReal.ofReal |deriv (fun s => ψ (y, s)) t| *
    (‖gradient u (ι y + ψ (y, t) • e)‖ₑ * g (ι y + ψ (y, t) • e)) = _
  rw [← mul_assoc, ← ofReal_norm, ← ENNReal.ofReal_mul (abs_nonneg _), hpoint]
  rfl

/-- A regular point has an open neighborhood on every Borel subset of which the weighted
coarea equality holds. The neighborhood and chart are independent of the weight. -/
theorem exists_coarea_neighborhood (ι : H →ₗᵢ[ℝ] V) {e : V}
    (hsp : IsGraphSplitting ι e) {u : V → ℝ} (hu : ContDiff ℝ 1 u)
    {x₀ : V} {c : ℝ} (hc : c ≠ 0) (hgrad : gradient u x₀ = c • e) :
    ∃ N : Set V, IsOpen N ∧ x₀ ∈ N ∧
      ∀ S : Set V, MeasurableSet S → S ⊆ N → ∀ g : V → ℝ≥0∞, Measurable g →
        (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
          ∫⁻ t, ∫⁻ x in S ∩ {x | u x = t}, g x
            ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)) := by
  classical
  obtain ⟨D, hD, hxD, -, -, hIC⟩ :=
    exists_regularChart ι hsp isOpen_univ hu.contDiffOn (mem_univ x₀) hc hgrad
  let E := splitHomeomorph hsp (0 : V)
  let p₀ : H × ℝ := E.symm (D x₀)
  have hE : ∀ p, E p = ι p.1 + p.2 • e := by intro p; simp [E]
  have hp₀ : p₀ ∈ levelChartDomain ι e D := by
    change ι p₀.1 + p₀.2 • e ∈ D.target
    rw [← hE, show E p₀ = D x₀ from E.apply_symm_apply (D x₀)]
    exact D.map_source hxD
  obtain ⟨r, ψ, hr, hrΩ, hψ, hψeq⟩ := Analysis.exists_contDiff_eqOn_ball
    (isOpen_levelChartDomain ι e D) (contDiffOn_levelChartHeight ι e D hIC) hp₀
  let Ω := Metric.ball p₀ r
  have hΩ : IsOpen Ω := Metric.isOpen_ball
  let Ψ : H × ℝ → V := fun p => ι p.1 + ψ p • e
  have hΨ : Continuous Ψ := (ι.continuous.comp continuous_fst).add
    (hψ.continuous.smul continuous_const)
  have hinv : ∀ p ∈ Ω, Ψ p = D.symm (E p) := by
    intro p hp
    have h := (levelChart_inverse hsp hD (hrΩ hp)).1
    rw [← hE] at h
    change ι p.1 + ψ p • e = _
    rw [hψeq hp]
    exact h.symm
  have hlevel : ∀ p ∈ Ω, u (ι p.1 + ψ p • e) = p.2 := by
    intro p hp
    change u (Ψ p) = _
    rw [hinv p hp, hE]
    exact (levelChart_inverse hsp hD (hrΩ hp)).2
  let N : Set V := D.source ∩ D ⁻¹' (E '' Ω)
  have hN : IsOpen N := D.isOpen_inter_preimage (E.isOpenMap Ω hΩ)
  have hxN : x₀ ∈ N := ⟨hxD, p₀, Metric.mem_ball_self hr, E.apply_symm_apply (D x₀)⟩
  refine ⟨N, hN, hxN, ?_⟩
  intro S hS hSN g hg
  let A : Set (H × ℝ) := Ω ∩ Ψ ⁻¹' S
  have hA : MeasurableSet A := hΩ.measurableSet.inter (hS.preimage hΨ.measurable)
  have himg : Ψ '' A = S := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact hp.2
    · intro x hx
      obtain ⟨p, hp, he⟩ := (hSN hx).2
      have hpx : Ψ p = x := by
        rw [hinv p hp, he, D.left_inv (hSN hx).1]
      exact ⟨p, ⟨hp, by change Ψ p ∈ S; rw [hpx]; exact hx⟩, hpx⟩
  have h := setLIntegral_coarea_graph_family ι hsp hu hψ hΩ hA inter_subset_left hlevel hg
  change (∫⁻ x in Ψ '' A, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
    ∫⁻ t, ∫⁻ x in (Ψ '' A) ∩ {x | u x = t}, g x
      ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)) at h
  simpa only [himg] using h

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.KLS

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Local regular coarea, with the repository's normalized surface measure and with no
regularity outside the prescribed open domain. -/
theorem exists_regular_coarea_neighborhood {O : Set V} {u : V → ℝ}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) {x₀ : V} (hx₀ : x₀ ∈ O)
    (hreg : fderiv ℝ u x₀ ≠ 0) :
    ∃ N : Set V, IsOpen N ∧ x₀ ∈ N ∧ N ⊆ O ∧
      ∀ S : Set V, MeasurableSet S → S ⊆ N → ∀ g : V → ℝ≥0∞, Measurable g →
        (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
          ∫⁻ t, ∫⁻ x in S ∩ {x | u x = t}, g x ∂(surfaceMeasure V) := by
  classical
  obtain ⟨r, w, hr, hrO, hw, heq⟩ := Analysis.exists_contDiff_eqOn_ball hO hu hx₀
  have hevent : ∀ x ∈ Metric.ball x₀ r, w =ᶠ[𝓝 x] u := fun x hx =>
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx) heq
  have hgradne : gradient w x₀ ≠ 0 := by
    intro hz
    apply hreg
    rw [← (hevent x₀ (Metric.mem_ball_self hr)).fderiv_eq]
    rw [← toDual_gradient (𝕜 := ℝ), hz, map_zero]
  let e : V := ‖gradient w x₀‖⁻¹ • gradient w x₀
  have he : ‖e‖ = 1 := norm_smul_inv_norm hgradne
  let H := ((ℝ ∙ e)ᗮ : Submodule ℝ V)
  let ι : H →ₗᵢ[ℝ] V := H.subtypeₗᵢ
  have hsp : Analysis.IsGraphSplitting ι e := Analysis.isGraphSplitting_orthogonal he
  have hc : ‖gradient w x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hgradne
  have hgrad : gradient w x₀ = ‖gradient w x₀‖ • e := by
    simp only [e, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hdim : Module.finrank ℝ H = Module.finrank ℝ V - 1 := by
    have hne : e ≠ 0 := by intro hz; simp [hz] at he
    have h := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ e : Submodule ℝ V))
    rw [finrank_span_singleton hne] at h
    change Module.finrank ℝ ((ℝ ∙ e)ᗮ : Submodule ℝ V) = _
    omega
  obtain ⟨N, hN, hxN, hformula⟩ := Analysis.exists_coarea_neighborhood ι hsp hw hc hgrad
  refine ⟨N ∩ Metric.ball x₀ r, hN.inter Metric.isOpen_ball,
    ⟨hxN, Metric.mem_ball_self hr⟩, fun x hx => hrO hx.2, ?_⟩
  intro S hS hSN g hg
  have h := hformula S hS (fun x hx => (hSN hx).1) g hg
  have hsurf : hausdorffNormalized V (Module.finrank ℝ H) = surfaceMeasure V := by
    rw [hdim]; rfl
  rw [hsurf] at h
  have hslice : ∀ t, S ∩ {x | w x = t} = S ∩ {x | u x = t} := by
    intro t
    ext x
    constructor <;> rintro ⟨hx, ht⟩ <;>
      exact ⟨hx, by simpa [heq (hSN hx).2] using ht⟩
  simp_rw [hslice] at h
  rw [← h]
  exact setLIntegral_congr_fun hS fun x hx => by
    rw [(hevent x (hSN hx).2).gradient_eq]

/-- **regular-domain coarea: weighted coarea on a regular open C¹ domain**, including a.e. measurability
of the weighted slices. All weights in ENNReal and all dimensions are covered. -/
theorem coarea_of_contDiffOn_of_fderiv_ne_zero {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞}
    (hO : IsOpen O) (hu : ContDiffOn ℝ 1 u O) (hreg : ∀ x ∈ O, fderiv ℝ u x ≠ 0)
    (hS : MeasurableSet S) (hSO : S ⊆ O) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ) := by
  classical
  refine ⟨aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn hO hu hS hSO hg, ?_⟩
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · simp [hSe]
  choose N hN hxN hNO hformula using fun z : O =>
    exists_regular_coarea_neighborhood hO hu z.2 (hreg z z.2)
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable N hN
  have hOcov : ⋃ z : O, N z = O :=
    Set.Subset.antisymm (Set.iUnion_subset hNO) fun y hy =>
      Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxN ⟨y, hy⟩⟩
  have hTne : T.Nonempty := by
    have : z₀ ∈ ⋃ z ∈ T, N z := by rw [hTu, hOcov]; exact hSO hz₀
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  have hcov : O ⊆ ⋃ n, N (σ n) := by
    rw [← hOcov, ← hTu, hσ, Set.biUnion_range]
  set P : ℕ → Set V := disjointed fun n => S ∩ N (σ n) with hP
  have hPm : ∀ n, MeasurableSet (P n) :=
    MeasurableSet.disjointed fun n => hS.inter (hN (σ n)).measurableSet
  have hPd : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed _
  have hPn : ∀ n, P n ⊆ N (σ n) := fun n =>
    (disjointed_subset _ n).trans Set.inter_subset_right
  have hPO : ∀ n, P n ⊆ O := fun n => (hPn n).trans (hNO (σ n))
  have hPu : ⋃ n, P n = S := by
    rw [hP, iUnion_disjointed, ← Set.inter_iUnion]
    exact Set.inter_eq_self_of_subset_left (hSO.trans hcov)
  have hslicem : ∀ n t, MeasurableSet (P n ∩ {x | u x = t}) := by
    have hw : Measurable (O.piecewise u (fun _ => (0 : ℝ))) :=
      hu.continuousOn.measurable_piecewise continuous_const.continuousOn hO.measurableSet
    intro n t
    have heq : P n ∩ {x | u x = t} = P n ∩ {x | O.piecewise u (fun _ => (0 : ℝ)) x = t} := by
      ext x
      constructor <;> rintro ⟨hx, ht⟩ <;> exact ⟨hx, by simpa [hPO n hx] using ht⟩
    rw [heq]
    exact (hPm n).inter (hw (measurableSet_singleton t))
  have hmeas : ∀ n, AEMeasurable
      (fun t : ℝ => ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V)) volume :=
    fun n => aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn hO hu (hPm n) (hPO n) hg
  calc
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
        ∑' n, ∫⁻ x in P n, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) := by
      rw [← hPu]
      exact lintegral_iUnion hPm hPd _
    _ = ∑' n, ∫⁻ t, ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V) :=
      tsum_congr fun n => hformula (σ n) (P n) (hPm n) (hPn n) g hg
    _ = ∫⁻ t, ∑' n, ∫⁻ y in P n ∩ {x | u x = t}, g y ∂(surfaceMeasure V) :=
      (lintegral_tsum hmeas).symm
    _ = ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(surfaceMeasure V) := by
      apply lintegral_congr
      intro t
      rw [← hPu, Set.iUnion_inter]
      symm
      exact lintegral_iUnion (fun n => hslicem n t)
        (fun i j hij => (hPd hij).mono Set.inter_subset_left Set.inter_subset_left) g

end FunctionalInequalities.KLS
