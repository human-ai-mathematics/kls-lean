import FunctionalInequalities.Analysis.Convex.Legendre.Basic
import FunctionalInequalities.Analysis.Convex.Subgradient.Measure
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Essentially continuous convex potentials

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Definition 2: a convex
`ψ : ℝⁿ → ℝ ∪ {+∞}` is *essentially continuous* if it is lower semicontinuous and the set of points
where `ψ` is not continuous, as a map into `ℝ ∪ {+∞}`, has zero `(n − 1)`-dimensional Hausdorff
measure. Here `ψ : E → EReal` on a finite-dimensional real inner product space `E` of dimension `n`;
convexity is the separate hypothesis `ConvexPotential ψ` (no value `-∞`, convex real epigraph), and
continuity is `ContinuousAt` for the order topology of `EReal`.

* `ConvexPotential.setOf_not_continuousAt`: for a lower semicontinuous convex potential the
  discontinuity set is exactly `dom ψ \ int dom ψ`, where `dom ψ = {ψ ≠ ⊤}`; hence
  `ConvexPotential.essentiallyContinuous_iff`, the source's equivalent form `{ψ < ∞} = A ∪ B` with
  `A = int dom ψ` open convex and `H^{n−1}(B) = 0`. A finite convex potential is essentially
  continuous (`ConvexPotential.essentiallyContinuous_of_ne_top`).
* `hausdorffMeasure_frontier_pos`: a closed convex proper subset with nonempty interior has a
  frontier of positive `H^{n−1}` measure (projection along a separating direction).
* `ConvexPotential.ne_top_of_lipschitzOnWith`: an essentially continuous convex potential that is
  `R`-Lipschitz on the interior of its (nonempty-interior) domain is finite everywhere.
* `lipschitzOnWith_of_ae_norm_gradient_le`: a convex function on an open convex set whose gradient
  is a.e. bounded by `R` is `R`-Lipschitz there.
* `ConvexPotential.ne_top_of_map_gradient`: an essentially continuous convex potential whose moment
  measure `(∇ψ)_#(e^{-ψ} dx)` is nonzero and supported in `closedBall 0 R` is finite everywhere and
  `R`-Lipschitz. This is the step of the uniqueness part of CEK Theorem 2 (Letwin
  arXiv:2607.24164v1, Lemma 2.1) reducing essentially continuous potentials of bounded-support
  moment measures to finite convex potentials.

The moment-measure hypothesis is written as the explicit push-forward
`((volume).withDensity fun x => EReal.exp (-ψ x)).map (gradient fun x => (ψ x).toReal)`.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Essential continuity** (Cordero-Erausquin–Klartag, arXiv:1304.0630v1, Definition 2):
`ψ` is lower semicontinuous and the set of points where `ψ : E → EReal` is not continuous has zero
`(dim E − 1)`-dimensional Hausdorff measure. The source applies the notion to convex `ψ` with values
in `ℝ ∪ {+∞}`; convexity is not part of this predicate. -/
def EssentiallyContinuous [MeasurableSpace E] [BorelSpace E] (ψ : E → EReal) : Prop :=
  LowerSemicontinuous ψ ∧
    μH[(Module.finrank ℝ E : ℝ) - 1] {x | ¬ContinuousAt ψ x} = 0

omit [InnerProductSpace ℝ E] in
/-- Every point of the effective domain outside its interior is a discontinuity point; neither
convexity nor semicontinuity is needed. -/
theorem not_continuousAt_of_mem_domain_diff_interior {ψ : E → EReal} {x : E}
    (hx : x ∈ {y | ψ y ≠ ⊤} \ interior {y | ψ y ≠ ⊤}) : ¬ContinuousAt ψ x := by
  intro hc
  apply hx.2
  rw [mem_interior_iff_mem_nhds]
  have hmem : Iio (⊤ : EReal) ∈ 𝓝 (ψ x) := Iio_mem_nhds (lt_top_iff_ne_top.mpr hx.1)
  filter_upwards [hc hmem] with y hy
  exact ne_of_lt hy

namespace ConvexPotential

variable [FiniteDimensional ℝ E]

/-- For a lower semicontinuous convex potential the discontinuity set is the part of the effective
domain outside its interior: `ψ` is continuous at every point where it is `⊤` (lower
semicontinuity) and at every interior point of `{ψ ≠ ⊤}` (convexity). -/
theorem setOf_not_continuousAt {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) :
    {x | ¬ContinuousAt ψ x} = {x | ψ x ≠ ⊤} \ interior {x | ψ x ≠ ⊤} := by
  ext x
  constructor
  · intro hx
    change ¬ContinuousAt ψ x at hx
    refine ⟨fun htop => hx ?_, fun hint => hx ?_⟩
    · change Tendsto ψ (𝓝 x) (𝓝 (ψ x))
      rw [htop, EReal.tendsto_nhds_top_iff_real]
      intro r
      have hr : (r : EReal) < ψ x := by
        rw [htop]
        exact EReal.coe_lt_top r
      exact hlsc x (r : EReal) hr
    · have hcont : ContinuousAt (fun y => (ψ y).toReal) x :=
        hψ.convexOn_toReal.continuousOn_interior.continuousAt
          (isOpen_interior.mem_nhds hint)
      refine (continuous_coe_real_ereal.continuousAt.comp hcont).congr ?_
      filter_upwards [isOpen_interior.mem_nhds hint] with y hy
      exact EReal.coe_toReal (interior_subset hy) (hψ.1 y)
  · exact not_continuousAt_of_mem_domain_diff_interior

variable [MeasurableSpace E] [BorelSpace E]

/-- CEK's equivalent form of Definition 2 for a convex potential: lower semicontinuity and
`H^{n−1}(dom ψ \ int dom ψ) = 0`, i.e. `{ψ < ∞} = A ∪ B` with `A = int dom ψ` open and convex and
`B = dom ψ \ A` of zero `H^{n−1}` measure. -/
theorem essentiallyContinuous_iff {ψ : E → EReal} (hψ : ConvexPotential ψ) :
    EssentiallyContinuous ψ ↔ LowerSemicontinuous ψ ∧
      μH[(Module.finrank ℝ E : ℝ) - 1] ({x | ψ x ≠ ⊤} \ interior {x | ψ x ≠ ⊤}) = 0 := by
  constructor
  · rintro ⟨hlsc, h0⟩
    exact ⟨hlsc, by rwa [← hψ.setOf_not_continuousAt hlsc]⟩
  · rintro ⟨hlsc, h0⟩
    exact ⟨hlsc, by rwa [hψ.setOf_not_continuousAt hlsc]⟩

/-- A finite convex potential is continuous, hence essentially continuous (CEK, remark after
Definition 2). -/
theorem essentiallyContinuous_of_ne_top {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hfin : ∀ x, ψ x ≠ ⊤) : EssentiallyContinuous ψ := by
  have hdom : {x | ψ x ≠ ⊤} = univ := eq_univ_of_forall hfin
  have hcont : Continuous ψ := by
    have hreal : Continuous (fun x => (ψ x).toReal) := by
      have h := hψ.convexOn_toReal.continuousOn_interior
      rw [hdom, interior_univ] at h
      exact continuousOn_univ.mp h
    have heq : (fun x => ((ψ x).toReal : EReal)) = ψ :=
      funext fun x => EReal.coe_toReal (hfin x) (hψ.1 x)
    rw [← heq]
    exact continuous_coe_real_ereal.comp hreal
  refine ⟨hcont.lowerSemicontinuous, ?_⟩
  have hempty : {x | ¬ContinuousAt ψ x} = ∅ :=
    eq_empty_of_forall_notMem fun x hx => hx hcont.continuousAt
  rw [hempty, measure_empty]

end ConvexPotential

section Frontier

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **A proper closed convex set with nonempty interior has a frontier of positive
`H^{n−1}` measure.** Separate a point outside `C` by a functional `f` and let `θ` increase `f`;
every line `y + ℝθ` through `y ∈ C` leaves `C` and so meets `frontier C`. A surjective linear map
`E → ℝ^{n−1}` killing `θ` is Lipschitz, maps `frontier C` onto a superset of the open image of
`interior C`, and `H^{n−1}` is Lebesgue measure on `ℝ^{n−1}`. -/
theorem hausdorffMeasure_frontier_pos {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C)
    (hint : (interior C).Nonempty) (hne : C ≠ univ) :
    0 < μH[(Module.finrank ℝ E : ℝ) - 1] (frontier C) := by
  obtain ⟨p, hp⟩ := (ne_univ_iff_exists_notMem C).mp hne
  obtain ⟨f, u, hfC, hfp⟩ := geometric_hahn_banach_closed_point hC hCc hp
  obtain ⟨x₀, hx₀⟩ := hint
  set θ : E := p - x₀ with hθdef
  have hfθ : 0 < f θ := by
    have h := hfC x₀ (interior_subset hx₀)
    rw [hθdef, map_sub]
    linarith
  have hθ : θ ≠ 0 := by
    intro h
    rw [h, map_zero] at hfθ
    exact lt_irrefl 0 hfθ
  -- every line through a point of `C` in direction `θ` meets the frontier
  have hhit : ∀ y ∈ C, ∃ t : ℝ, y + t • θ ∈ frontier C := by
    intro y hy
    let g : ℝ → E := fun t => y + t • θ
    have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
    have hS : (g ⁻¹' C).Nonempty := ⟨0, by simpa [g] using hy⟩
    have hS' : g ⁻¹' C ≠ univ := by
      intro hall
      have hT : g ((u - f y) / f θ) ∈ C := by
        rw [← mem_preimage, hall]
        exact mem_univ _
      have h := hfC _ hT
      simp only [g, map_add, map_smul, smul_eq_mul] at h
      rw [div_mul_cancel₀ _ (ne_of_gt hfθ)] at h
      linarith
    obtain ⟨t, ht⟩ := nonempty_frontier_iff.mpr ⟨hS, hS'⟩
    exact ⟨t, hg.frontier_preimage_subset C ht⟩
  -- the quotient map along `θ`, identified with `ℝ^{n−1}`
  have hn : 1 ≤ Module.finrank ℝ E := by
    have : Nontrivial E := nontrivial_of_ne θ 0 hθ
    exact Module.finrank_pos
  set n := Module.finrank ℝ E with hndef
  let N : Submodule ℝ E := ℝ ∙ θ
  have hQ : Module.finrank ℝ (E ⧸ N) = Module.finrank ℝ (Fin (n - 1) → ℝ) := by
    have h1 := Submodule.finrank_quotient_add_finrank N
    rw [finrank_span_singleton hθ] at h1
    rw [Module.finrank_fin_fun]
    omega
  let e : (E ⧸ N) ≃ₗ[ℝ] (Fin (n - 1) → ℝ) := LinearEquiv.ofFinrankEq _ _ hQ
  let L : E →ₗ[ℝ] (Fin (n - 1) → ℝ) := e.toLinearMap ∘ₗ N.mkQ
  have hLsurj : Function.Surjective L := e.surjective.comp N.mkQ_surjective
  have hLθ : ∀ y : E, ∀ t : ℝ, L (y + t • θ) = L y := by
    intro y t
    have hmem : t • θ ∈ N := Submodule.smul_mem _ t (Submodule.mem_span_singleton_self θ)
    have h0 : L (t • θ) = 0 := by
      simp only [L, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero N).mpr hmem, map_zero]
    rw [map_add, h0, add_zero]
  let Lc : E →L[ℝ] (Fin (n - 1) → ℝ) := LinearMap.toContinuousLinearMap L
  have hLc : ∀ y, Lc y = L y := fun _ => rfl
  -- the image of the interior is open, nonempty and covered by the image of the frontier
  have hopen : IsOpen (Lc '' interior C) := by
    have h := L.isOpenMap_of_finiteDimensional hLsurj (interior C) isOpen_interior
    simpa only [hLc] using h
  have hsub : Lc '' interior C ⊆ Lc '' frontier C := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨t, ht⟩ := hhit y (interior_subset hy)
    exact ⟨y + t • θ, ht, by rw [hLc, hLc, hLθ]⟩
  have hvol : 0 < (volume : Measure (Fin (n - 1) → ℝ)) (Lc '' frontier C) :=
    (hopen.measure_pos volume ⟨Lc x₀, x₀, hx₀, rfl⟩).trans_le (measure_mono hsub)
  have hd : ((Module.finrank ℝ E : ℝ) - 1) = ((Fintype.card (Fin (n - 1)) : ℕ) : ℝ) := by
    rw [Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one]
  rw [← hausdorffMeasure_pi_real] at hvol
  have hle := Lc.lipschitz.hausdorffMeasure_image_le (d := ((Fintype.card (Fin (n - 1)) : ℕ) : ℝ))
    (Nat.cast_nonneg _) (frontier C)
  rw [hd, pos_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at hle
  exact hvol.ne' (nonpos_iff_eq_zero.mp hle)

end Frontier

namespace ConvexPotential

/-- A lower semicontinuous convex potential that is `R`-Lipschitz on the nonempty interior of its
effective domain has a closed effective domain: along the open segment from an interior point
`x₀` to `x ∈ closure (dom ψ)` the values stay below `ψ(x₀) + R‖x − x₀‖`, and the sublevel set is
closed. -/
theorem isClosed_domain_of_lipschitzOnWith {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) {R : ℝ≥0}
    (hlip : LipschitzOnWith R (fun x => (ψ x).toReal) (interior {x | ψ x ≠ ⊤}))
    (hint : (interior {x | ψ x ≠ ⊤}).Nonempty) : IsClosed {x | ψ x ≠ ⊤} := by
  refine closure_subset_iff_isClosed.mp ?_
  intro x hx
  obtain ⟨x₀, hx₀⟩ := hint
  set M : ℝ := (ψ x₀).toReal + R * dist x x₀ with hM
  have hseg : openSegment ℝ x₀ x ⊆ ψ ⁻¹' Iic (M : EReal) := by
    intro z hz
    have hzi : z ∈ interior {x | ψ x ≠ ⊤} :=
      hψ.convex_domain.openSegment_interior_closure_subset_interior hx₀ hx hz
    have hdist : dist z x₀ ≤ dist x x₀ := by
      have h := dist_add_dist_of_mem_segment (openSegment_subset_segment ℝ x₀ x hz)
      rw [dist_comm x₀ z, dist_comm x₀ x] at h
      linarith [dist_nonneg (x := z) (y := x)]
    have hl := hlip.dist_le_mul z hzi x₀ hx₀
    have hreal : (ψ z).toReal ≤ M := by
      rw [hM]
      have h1 := (le_abs_self _).trans (Real.dist_eq _ _ ▸ hl)
      nlinarith [R.coe_nonneg]
    change ψ z ≤ (M : EReal)
    rw [← EReal.coe_toReal (interior_subset hzi) (hψ.1 z)]
    exact EReal.coe_le_coe_iff.mpr hreal
  have hxcl : x ∈ closure (openSegment ℝ x₀ x) :=
    segment_subset_closure_openSegment (right_mem_segment ℝ x₀ x)
  have hle : ψ x ≤ (M : EReal) :=
    (closure_minimal hseg (hlsc.isClosed_preimage (M : EReal))) hxcl
  exact ne_top_of_le_ne_top (EReal.coe_ne_top M) hle

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Essential continuity and a Lipschitz bound force finiteness** (step of
Cordero-Erausquin–Klartag, Theorem 2, uniqueness; Letwin arXiv:2607.24164v1, Lemma 2.1): an
essentially continuous convex potential that is `R`-Lipschitz on the interior of its effective
domain, which is nonempty, is finite everywhere. The domain is closed; if it were not the whole
space, its frontier would be a set of discontinuity points of positive `H^{n−1}` measure. -/
theorem ne_top_of_lipschitzOnWith {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) {R : ℝ≥0}
    (hlip : LipschitzOnWith R (fun x => (ψ x).toReal) (interior {x | ψ x ≠ ⊤}))
    (hint : (interior {x | ψ x ≠ ⊤}).Nonempty) (x : E) : ψ x ≠ ⊤ := by
  have hclosed := hψ.isClosed_domain_of_lipschitzOnWith hess.1 hlip hint
  by_contra hx
  have hne : {y | ψ y ≠ ⊤} ≠ univ := fun h => (h ▸ mem_univ x : x ∈ {y | ψ y ≠ ⊤}) hx
  have hpos := hausdorffMeasure_frontier_pos hψ.convex_domain hclosed hint hne
  have hsub : frontier {y | ψ y ≠ ⊤} ⊆ {y | ¬ContinuousAt ψ y} := by
    intro y hy
    rw [frontier, hclosed.closure_eq] at hy
    exact not_continuousAt_of_mem_domain_diff_interior hy
  exact (ne_of_gt hpos) (measure_mono_null hsub hess.2)

end ConvexPotential

section Gradient

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **An a.e. gradient bound gives a Lipschitz bound for a convex function on an open convex
set**: if `g` is convex on the open convex set `U` and `‖∇g‖ ≤ R` at `μ`-a.e. point of `U` for an
additive Haar measure `μ`, then `g` is `R`-Lipschitz on `U`. For `x, y ∈ U` with `v = y − x`, the
continuous function `z ↦ g z − g (z + v)` is at most `R‖v‖` at every differentiability point of a
set of full measure (tangent-plane inequality), hence on the open set where it is defined. -/
theorem lipschitzOnWith_of_ae_norm_gradient_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) {g : E → ℝ} (hg : ConvexOn ℝ U g) {R : ℝ≥0}
    (hae : ∀ᵐ x ∂μ, x ∈ U → ‖gradient g x‖ ≤ R) : LipschitzOnWith R g U := by
  have hcont : ContinuousOn g U := by
    have h := hg.continuousOn_interior
    rwa [hU.interior_eq] at h
  have hgood : ∀ᵐ z ∂μ, z ∈ U → DifferentiableAt ℝ g z ∧ ‖gradient g z‖ ≤ R := by
    filter_upwards [ConvexOn.ae_differentiableAt_of_isOpen μ hU hg, hae] with z h1 h2 hz
    exact ⟨h1 hz, h2 hz⟩
  have hone : ∀ x ∈ U, ∀ y ∈ U, g x - g y ≤ R * ‖y - x‖ := by
    intro x hx y hy
    set v : E := y - x with hv
    by_contra hlt
    push Not at hlt
    let W : Set E := U ∩ (fun z => z + v) ⁻¹' U
    have hW : IsOpen W := hU.inter (hU.preimage (continuous_id.add continuous_const))
    have hcW : ContinuousOn (fun z => g z - g (z + v)) W :=
      (hcont.mono inter_subset_left).sub
        (hcont.comp (continuous_id.add continuous_const).continuousOn
          (fun z hz => hz.2))
    have hV : IsOpen (W ∩ (fun z => g z - g (z + v)) ⁻¹' Ioi (R * ‖v‖)) :=
      hcW.isOpen_inter_preimage hW isOpen_Ioi
    have hxV : x ∈ W ∩ (fun z => g z - g (z + v)) ⁻¹' Ioi (R * ‖v‖) := by
      refine ⟨⟨hx, ?_⟩, ?_⟩
      · change x + v ∈ U
        rw [hv, add_sub_cancel]
        exact hy
      · change R * ‖v‖ < g x - g (x + v)
        rw [hv, add_sub_cancel]
        exact hlt
    obtain ⟨z, hzV, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (ne_of_gt (hV.measure_pos μ ⟨x, hxV⟩)) (ae_restrict_of_ae hgood)
    obtain ⟨⟨hzU, hzvU⟩, hzgt⟩ := hzV
    change R * ‖v‖ < g z - g (z + v) at hzgt
    obtain ⟨hdiff, hnorm⟩ := hz hzU
    have hsupp := convex_support_of_hasFDerivWithinAt hg
      hdiff.hasGradientAt.hasFDerivAt.hasFDerivWithinAt hzU hzvU
    simp only [add_sub_cancel_left, InnerProductSpace.toDual_apply_apply] at hsupp
    have hinner : -(‖gradient g z‖ * ‖v‖) ≤ ⟪gradient g z, v⟫ :=
      neg_le_of_abs_le (abs_real_inner_le_norm _ _)
    have hRv : ‖gradient g z‖ * ‖v‖ ≤ R * ‖v‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
    linarith
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  have h1 := hone x hx y hy
  have h2 := hone y hy x hx
  rw [← norm_neg (y - x), neg_sub] at h1
  constructor <;> linarith

end Gradient

namespace ConvexPotential

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Bounded-support moment measures of essentially continuous potentials** (step of
Cordero-Erausquin–Klartag, arXiv:1304.0630v1, Theorem 2, uniqueness; Letwin arXiv:2607.24164v1,
Lemma 2.1): let `ψ` be a convex, essentially continuous potential whose moment measure
`μ = (∇ψ)_#(e^{-ψ} dx)` (push-forward of `exp(-ψ) dx` under the gradient of `(ψ ·).toReal`) is
nonzero and supported in `closedBall 0 R`. Then `ψ` is finite everywhere and `R`-Lipschitz.

The effective domain has positive Lebesgue measure (otherwise `e^{-ψ} = 0` a.e. and `μ = 0`), hence
nonempty interior; the gradient lies a.e. in `closedBall 0 R` on the domain, which gives the
Lipschitz bound on its interior; essential continuity then excludes a boundary. Without essential
continuity the conclusion fails (`ψ = 0` on a closed ball and `⊤` outside has moment measure a
multiple of `δ₀`). -/
theorem ne_top_of_map_gradient {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) {μ : Measure E}
    (hμ : ((volume : Measure E).withDensity fun x => EReal.exp (-ψ x)).map
      (gradient fun x => (ψ x).toReal) = μ)
    (hμ0 : μ ≠ 0) {R : ℝ≥0} (hsupp : μ (closedBall (0 : E) R)ᶜ = 0) :
    (∀ x, ψ x ≠ ⊤) ∧ LipschitzWith R (fun x => (ψ x).toReal) := by
  set D : Set E := {x | ψ x ≠ ⊤} with hD
  set ν : Measure E := (volume : Measure E).withDensity fun x => EReal.exp (-ψ x) with hν
  -- the domain has positive Lebesgue measure
  have hDvol : (volume : Measure E) D ≠ 0 := by
    intro h0
    apply hμ0
    rw [← hμ]
    have hzero : (fun x => EReal.exp (-ψ x)) =ᵐ[volume] fun _ => 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
      have htop : ψ x = ⊤ := not_not.mp hx
      rw [htop, EReal.neg_top, EReal.exp_bot]
    have hν0 : ν = 0 := by
      rw [hν, withDensity_congr_ae hzero]
      exact withDensity_zero
    rw [hν0, Measure.map_zero]
  -- hence nonempty interior
  have hint : (interior D).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    apply hDvol
    refine measure_mono_null ?_ (hψ.convex_domain.addHaar_frontier (volume : Measure E))
    intro x hx
    have hcl := subset_closure hx
    rw [closure_eq_interior_union_frontier, hempty, empty_union] at hcl
    exact hcl
  -- the gradient is bounded a.e. on the domain
  have hmeas : AEMeasurable (gradient fun x => (ψ x).toReal) ν := by
    by_contra hnot
    apply hμ0
    rw [← hμ, Measure.map_of_not_aemeasurable hnot]
  have hball : ∀ᵐ q ∂μ, q ∈ closedBall (0 : E) R := by
    rw [ae_iff]
    exact hsupp
  rw [← hμ] at hball
  have hν_ae := ae_of_ae_map hmeas hball
  have hdens : Measurable fun x => EReal.exp (-ψ x) :=
    EReal.measurable_exp.comp hess.1.measurable.neg
  rw [hν, ae_withDensity_iff hdens] at hν_ae
  have hvol_ae : ∀ᵐ x ∂(volume : Measure E), x ∈ interior D →
      ‖gradient (fun x => (ψ x).toReal) x‖ ≤ R := by
    filter_upwards [hν_ae] with x hx hxD
    have hne : EReal.exp (-ψ x) ≠ 0 := by
      rw [ne_eq, EReal.exp_eq_zero_iff, EReal.neg_eq_bot_iff]
      exact interior_subset hxD
    have h := hx hne
    rwa [mem_closedBall_zero_iff] at h
  have hlip : LipschitzOnWith R (fun x => (ψ x).toReal) (interior D) :=
    lipschitzOnWith_of_ae_norm_gradient_le volume isOpen_interior
      (hψ.convexOn_toReal.subset interior_subset hψ.convex_domain.interior) hvol_ae
  have hfin := hψ.ne_top_of_lipschitzOnWith hess hlip hint
  refine ⟨hfin, ?_⟩
  have hDu : D = univ := eq_univ_of_forall hfin
  rw [hDu, interior_univ] at hlip
  exact lipschitzOnWith_univ.mp hlip

end ConvexPotential

end FunctionalInequalities.Analysis
