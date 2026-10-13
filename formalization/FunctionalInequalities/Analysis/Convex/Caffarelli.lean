import FunctionalInequalities.Analysis.Convex.Alexandrov
import FunctionalInequalities.Analysis.Convex.Normalization
import FunctionalInequalities.Analysis.Convex.Subgradient
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Continuous
import FunctionalInequalities.Analysis.Convex.Coercivity

/-!
# Caffarelli's strict convexity argument: geometric steps

Steps of Caffarelli's exposed-point argument for Alexandrov solutions with two-sided Monge–Ampère bounds
(weak Letwin route, block T11e), built on `Analysis/Convex/Alexandrov.lean` and `Analysis/Convex/Normalization.lean`.

* `infDist_frontier_image_le_of_width` (task L-T11e5).
-/

noncomputable section

open Set Metric
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- **Width ratios control the distance to the frontier after an affine normalisation** (weak Letwin
route, Caffarelli block T11e, step (c)): if a bounded open `S ∋ x` has width at most `α` above `x` and
at least `β > 0` below `x` in the unit direction `θ`, and `e` is an affine equivalence with
`e '' S ⊆ closedBall 0 C₀`, then `infDist (e x) (frontier (e '' S)) ≤ 2 C₀ α / β`. -/
theorem infDist_frontier_image_le_of_width {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hup : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ α) (hlow : ∃ y ∈ S, ⟪y - x, θ⟫ ≤ -β)
    (e : E ≃ᵃ[ℝ] E) {C₀ : ℝ} (hC₀ : 0 < C₀) (himg : e '' S ⊆ closedBall (0 : E) C₀) :
    infDist (e x) (frontier (e '' S)) ≤ 2 * C₀ * α / β := by
  have _ := hb
  have _ := hθ
  have _ := hC₀
  let η : E := LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) θ
  obtain ⟨y₀, hy₀, hlow₀⟩ := hlow
  have hinner (y : E) : ⟪e y - e x, η⟫ = ⟪y - x, θ⟫ := by
    dsimp only [η]
    have hmap : e y - e x = e.linear (y - x) := by
      have hm := e.toAffineMap.linearMap_vsub y x
      change e.linear (y - x) = e y - e x at hm
      exact hm.symm
    calc
      ⟪e y - e x, LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) θ⟫ =
          ⟪e.linear (y - x),
            LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) θ⟫ := by
        rw [hmap]
      _ = ⟪(e.linear.symm : E →ₗ[ℝ] E) (e.linear (y - x)), θ⟫ :=
        LinearMap.adjoint_inner_right (e.linear.symm : E →ₗ[ℝ] E)
          (e.linear (y - x)) θ
      _ = ⟪y - x, θ⟫ := by
        change ⟪e.linear.symm (e.linear (y - x)), θ⟫ = ⟪y - x, θ⟫
        exact congrArg (fun w : E => ⟪w, θ⟫) (e.linear.symm_apply_apply (y - x))
  have hη : η ≠ 0 := by
    intro hzero
    have hz := hinner (x + θ)
    rw [hzero] at hz
    have hz' : ⟪θ, θ⟫ = 0 := by
      simpa only [inner_zero_right, add_sub_cancel_left] using hz.symm
    have hone : ⟪θ, θ⟫ = 1 := by
      calc
        ⟪θ, θ⟫ = ‖θ‖ ^ 2 := real_inner_self_eq_norm_sq θ
        _ = 1 := by rw [hθ]; norm_num
    linarith
  have hnormη : 0 < ‖η‖ := norm_pos_iff.mpr hη
  let θ' : E := ‖η‖⁻¹ • η
  have hθ' : ‖θ'‖ = 1 := by
    dsimp only [θ']
    calc
      ‖‖η‖⁻¹ • η‖ = ‖‖η‖⁻¹‖ * ‖η‖ := norm_smul _ _
      _ = ‖η‖⁻¹ * ‖η‖ := by
        rw [norm_inv, Real.norm_eq_abs, abs_of_pos hnormη]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hnormη)
  have hS' : IsOpen (e '' S) := by
    change IsOpen ((AffineEquiv.toContinuousAffineEquiv e).toHomeomorph '' S)
    exact (AffineEquiv.toContinuousAffineEquiv e).toHomeomorph.isOpenMap S hS
  have hb' : Bornology.IsBounded (e '' S) :=
    (Metric.isBounded_closedBall : Bornology.IsBounded (closedBall (0 : E) C₀)).subset himg
  have hx' : e x ∈ e '' S := ⟨x, hx, rfl⟩
  have himage : ∀ z ∈ e '' S, ⟪z - e x, θ'⟫ ≤ α / ‖η‖ := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    dsimp only [θ']
    calc
      ⟪e y - e x, ‖η‖⁻¹ • η⟫ =
          ‖η‖⁻¹ * ⟪e y - e x, η⟫ := by
        rw [real_inner_smul_right]
      _ = ‖η‖⁻¹ * ⟪y - x, θ⟫ := by
        rw [hinner y]
      _ ≤ ‖η‖⁻¹ * α :=
        mul_le_mul_of_nonneg_left (hup y hy) (inv_nonneg.mpr (le_of_lt hnormη))
      _ = α / ‖η‖ := by
        rw [div_eq_mul_inv]
        ring
  have hfront :
      infDist (e x) (frontier (e '' S)) ≤ α / ‖η‖ :=
    infDist_frontier_le_of_forall_inner_le hS' hb' hx' hθ' himage
  have hey : ‖e y₀‖ ≤ C₀ := by
    simpa only [mem_closedBall, dist_zero_right] using
      himg ⟨y₀, hy₀, rfl⟩
  have hex : ‖e x‖ ≤ C₀ := by
    simpa only [mem_closedBall, dist_zero_right] using
      himg ⟨x, hx, rfl⟩
  have hdiff : ‖e y₀ - e x‖ ≤ 2 * C₀ := by
    calc
      ‖e y₀ - e x‖ ≤ ‖e y₀‖ + ‖e x‖ := norm_sub_le _ _
      _ ≤ C₀ + C₀ := add_le_add hey hex
      _ ≤ 2 * C₀ := by nlinarith [hC₀]
  have habs₀ : β ≤ |⟪y₀ - x, θ⟫| := by
    have hnonpos : ⟪y₀ - x, θ⟫ ≤ 0 :=
      hlow₀.trans (neg_nonpos.mpr hβ.le)
    rw [abs_of_nonpos hnonpos]
    linarith
  have habs : β ≤ |⟪e y₀ - e x, η⟫| := by
    rw [hinner y₀]
    exact habs₀
  have hβnorm : β ≤ 2 * C₀ * ‖η‖ := by
    calc
      β ≤ |⟪e y₀ - e x, η⟫| := habs
      _ ≤ ‖e y₀ - e x‖ * ‖η‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * C₀) * ‖η‖ :=
        mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      _ = 2 * C₀ * ‖η‖ := by ring
  have hratio : α / ‖η‖ ≤ 2 * C₀ * α / β := by
    apply (div_le_iff₀ hnormη).2
    calc
      α ≤ (2 * C₀ * α) * ‖η‖ / β := by
        apply (le_div_iff₀ hβ).2
        calc
          α * β ≤ α * (2 * C₀ * ‖η‖) :=
            mul_le_mul_of_nonneg_left hβnorm hα
          _ = (2 * C₀ * α) * ‖η‖ := by ring
      _ = (2 * C₀ * α / β) * ‖η‖ := by ring
  exact hfront.trans hratio

end FunctionalInequalities.Analysis

section LT11E3SectionsShrink

open Set Metric Filter
open scoped RealInnerProductSpace Topology

/-! Compact sections nested inside the domain that shrink to the contact set (task L-T11e3). -/

namespace FunctionalInequalities.Analysis

private lemma caffarelli_gap_segment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    (p a b c : E) (ha : u a = u c + ⟪p, a - c⟫)
    (t : ℝ) (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    u (a + t • (b - a)) - (u c + ⟪p, a + t • (b - a) - c⟫) ≤
      t * (u b - (u c + ⟪p, b - c⟫)) := by
  have hv : (1 - t) • a + t • b = a + t • (b - a) := by
    module
  have hi :
      ⟪p, a + t • (b - a) - c⟫ =
        (1 - t) * ⟪p, a - c⟫ + t * ⟪p, b - c⟫ := by
    rw [show a + t • (b - a) - c =
      (1 - t) • (a - c) + t • (b - c) by module]
    simp only [inner_add_right, real_inner_smul_right]
  have hj := hc.2 (mem_univ a) (mem_univ b)
    (sub_nonneg.mpr ht₁) ht (by ring : (1 - t) + t = 1)
  rw [hv] at hj
  simp only [smul_eq_mul] at hj
  rw [hi]
  nlinarith [ha]

/-- **Sections at an exposed point of a compact contact set are bounded and shrink to the slab piece
of the contact set** (weak Letwin route, Caffarelli block T11e, steps G1–G2): with `w := u − ℓ ≥ 0`
(`ℓ` the supporting affine function at `x₀`), compact contact set `C = {w = 0}`, an exposed point
`xe ∈ C` in the unit direction `θ`, and `h > 0`, the sections
`S ε := {x | w x < ε (⟪x − xe, θ⟫ + h)}` lie in a fixed compact set for small `ε`, and for every `δ > 0`
they lie in the `δ`-thickening of `C ∩ {⟪· − xe, θ⟫ ≥ −h}` for `ε` small enough. -/
theorem exists_compact_sections_subset_and_shrink {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {x₀ p : E} (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y)
    (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫}) {xe θ : E}
    (hxe : u xe = u x₀ + ⟪p, xe - x₀⟫) (hθ : ‖θ‖ = 1)
    (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ xe → ⟪x - xe, θ⟫ < 0) {h : ℝ} (hh : 0 < h) :
    (∃ Q : Set E, IsCompact Q ∧ ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆ Q) ∧
    ∀ δ > 0, ∃ ε₁ > 0, ∀ ε, 0 < ε → ε < ε₁ →
      {x | u x - (u x₀ + ⟪p, x - x₀⟫) < ε * (⟪x - xe, θ⟫ + h)} ⊆
        cthickening δ ({x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - xe, θ⟫}) := by
  classical
  have _ := hexp
  let w : E → ℝ := fun x => u x - (u x₀ + ⟪p, x - x₀⟫)
  have hu : Continuous u :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hwn (x : E) : 0 ≤ w x := sub_nonneg.mpr (hp x)
  have hinner (x : E) : ⟪x - xe, θ⟫ ≤ dist x xe := by
    simpa only [hθ, mul_one, dist_eq_norm] using
      real_inner_le_norm (x - xe) θ

  obtain ⟨r, hrbound⟩ := hC.isBounded.subset_closedBall xe
  have hr : 0 ≤ r := by
    have hmem := hrbound hxe
    change dist xe xe ≤ r at hmem
    simpa only [dist_self] using hmem
  let R : ℝ := r + 1
  have hR : 0 < R := by
    dsimp [R]
    linarith
  have hRh : 0 < R + h := add_pos hR hh
  let Q : Set E := closedBall xe R
  have hQ : IsCompact Q := isCompact_closedBall xe R

  have hsphere_ne : (sphere xe R).Nonempty := by
    refine ⟨xe + R • θ, ?_⟩
    change dist (xe + R • θ) xe = R
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hR, hθ, mul_one]
  have hsphere_pos : ∀ x ∈ sphere xe R, 0 < w x := by
    intro x hx
    by_contra hnot
    have hwzero : w x = 0 :=
      le_antisymm (le_of_not_gt hnot) (hwn x)
    have hxC : u x = u x₀ + ⟪p, x - x₀⟫ :=
      sub_eq_zero.mp hwzero
    have hdist_le : dist x xe ≤ r := hrbound hxC
    have hdist_eq : dist x xe = R := hx
    dsimp [R] at hdist_eq
    linarith
  obtain ⟨z, hz, hzmin⟩ :=
    (isCompact_sphere xe R).exists_isMinOn hsphere_ne hw.continuousOn
  have hzpos : 0 < w z := hsphere_pos z hz
  let ε₀ : ℝ := w z / (R + h)
  have hε₀ : 0 < ε₀ := div_pos hzpos hRh

  have hbound : ∀ ε, 0 < ε → ε < ε₀ →
      {x | w x < ε * (⟪x - xe, θ⟫ + h)} ⊆ Q := by
    intro ε hε hεlt x hx
    change w x < ε * (⟪x - xe, θ⟫ + h) at hx
    change dist x xe ≤ R
    by_contra hxR
    have hd : R < dist x xe := lt_of_not_ge hxR
    have hdpos : 0 < dist x xe := hR.trans hd
    let t : ℝ := R / dist x xe
    have ht : 0 < t := div_pos hR hdpos
    have ht₁ : t ≤ 1 := (div_le_one hdpos).mpr hd.le
    have htd : t * dist x xe = R :=
      div_mul_cancel₀ R (ne_of_gt hdpos)
    let y : E := xe + t • (x - xe)
    have hy : y ∈ sphere xe R := by
      change dist (xe + t • (x - xe)) xe = R
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht]
      simpa only [dist_eq_norm] using htd
    have hwy : w y ≤ t * w x :=
      caffarelli_gap_segment hconv p xe x x₀ hxe t ht.le ht₁
    have hxupper : w x < ε * (dist x xe + h) :=
      hx.trans_le
        (mul_le_mul_of_nonneg_left (by linarith [hinner x]) hε.le)
    have hth : t * h ≤ h := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right ht₁ hh.le
    have hyupper : w y < ε * (R + h) := by
      calc
        w y ≤ t * w x := hwy
        _ < t * (ε * (dist x xe + h)) :=
          mul_lt_mul_of_pos_left hxupper ht
        _ = ε * (t * dist x xe + t * h) := by ring
        _ = ε * (R + t * h) := by rw [htd]
        _ ≤ ε * (R + h) :=
          mul_le_mul_of_nonneg_left (by linarith [hth]) hε.le
    have hεupper : ε * (R + h) < w z :=
      (lt_div_iff₀ hRh).mp hεlt
    have hmin : w z ≤ w y := hzmin hy
    exact (not_lt_of_ge hmin) (hyupper.trans hεupper)

  have hfactor : ∀ x ∈ Q, ⟪x - xe, θ⟫ + h ≤ R + h := by
    intro x hx
    have hd : dist x xe ≤ R := hx
    exact by linarith [(hinner x).trans hd]

  refine ⟨⟨Q, hQ, ε₀, hε₀, ?_⟩, ?_⟩
  · intro ε hε hεlt
    exact hbound ε hε hεlt
  · intro δ hδ
    let K : Set E :=
      {x | u x = u x₀ + ⟪p, x - x₀⟫} ∩
        {x | -h ≤ ⟪x - xe, θ⟫}
    let B : Set E :=
      (Q ∩ {x | -h ≤ ⟪x - xe, θ⟫}) \ thickening δ K
    have hslabclosed : IsClosed {x : E | -h ≤ ⟪x - xe, θ⟫} :=
      isClosed_le continuous_const
        ((continuous_id.sub continuous_const).inner continuous_const)
    have hBcompact : IsCompact B :=
      (hQ.inter_right hslabclosed).diff isOpen_thickening
    have hBpos : ∀ x ∈ B, 0 < w x := by
      intro x hx
      by_contra hnot
      have hwzero : w x = 0 :=
        le_antisymm (le_of_not_gt hnot) (hwn x)
      have hxK : x ∈ K := ⟨sub_eq_zero.mp hwzero, hx.1.2⟩
      have hxthick : x ∈ thickening δ K :=
        mem_thickening_iff.mpr
          ⟨x, hxK, by simpa only [dist_self] using hδ⟩
      exact hx.2 hxthick
    have hgap : ∃ η > 0, ∀ x ∈ B, η ≤ w x := by
      by_cases hBne : B.Nonempty
      · obtain ⟨b, hb, hbmin⟩ :=
          hBcompact.exists_isMinOn hBne hw.continuousOn
        exact ⟨w b, hBpos b hb, fun x hx => hbmin hx⟩
      · refine ⟨1, zero_lt_one, ?_⟩
        intro x hx
        exact (hBne ⟨x, hx⟩).elim
    obtain ⟨η, hηpos, hη⟩ := hgap
    refine ⟨min ε₀ (η / (R + h)),
      lt_min hε₀ (div_pos hηpos hRh), ?_⟩
    intro ε hε hεlt x hx
    change w x < ε * (⟪x - xe, θ⟫ + h) at hx
    change x ∈ cthickening δ K
    have hεlt₀ : ε < ε₀ :=
      lt_of_lt_of_le hεlt (min_le_left _ _)
    have hxQ : x ∈ Q := hbound ε hε hεlt₀ hx
    have hslab : -h ≤ ⟪x - xe, θ⟫ := by
      have hfac : 0 < ⟪x - xe, θ⟫ + h := by
        by_contra hnot
        have hmul : ε * (⟪x - xe, θ⟫ + h) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hε.le (le_of_not_gt hnot)
        have hnonneg := hwn x
        linarith
      linarith
    apply thickening_subset_cthickening δ K
    by_contra hxout
    have hxB : x ∈ B := ⟨⟨hxQ, hslab⟩, hxout⟩
    have hxlower : η ≤ w x := hη x hxB
    have hxupper : w x < ε * (R + h) :=
      hx.trans_le (mul_le_mul_of_nonneg_left (hfactor x hxQ) hε.le)
    have hεltη : ε < η / (R + h) :=
      lt_of_lt_of_le hεlt (min_le_right _ _)
    have hεupper : ε * (R + h) < η :=
      (lt_div_iff₀ hRh).mp hεltη
    exact (not_lt_of_ge hxlower) (hxupper.trans hεupper)

end FunctionalInequalities.Analysis

end LT11E3SectionsShrink

section LT11E7LocalizedContactLemma

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! Caffarelli's contact-set lemma: under local two-sided Alexandrov bounds a compact contact set is a single point, also in the localized form at exposed points (tasks L-T11e and L-T11e7). -/

namespace FunctionalInequalities.Analysis

private lemma contact_sub_affine_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    (c : ℝ) (p : E) :
    ConvexOn ℝ univ (fun x => u x - (c + ⟪p, x⟫)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hu.2 hx hy ha hb hab
  have hconst : a * c + b * c = c := by
    calc
      a * c + b * c = (a + b) * c := by ring
      _ = c := by rw [hab, one_mul]
  simp only [inner_add_right, real_inner_smul_right, smul_eq_mul] at h ⊢
  nlinarith only [h, hconst]

private lemma contact_subgradientImage_sub_affine {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) (c : ℝ) (p : E) (G : Set E) :
    subgradientImage (fun x => u x - (c + ⟪p, x⟫)) G =
      (fun q => q + -p) '' subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨q + p, ⟨x, hx, ?_⟩, by abel⟩
    intro y
    have h := hq y
    simp only [inner_add_left, inner_sub_right] at h ⊢
    linarith
  · rintro ⟨q, ⟨x, hx, hq⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    intro y
    have h := hq y
    simp only [inner_add_left, inner_neg_left, inner_sub_right] at h ⊢
    linarith

private lemma contact_volume_sub_affine {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (c : ℝ) (p : E) (G : Set E) :
    (volume : Measure E)
        (subgradientImage (fun x => u x - (c + ⟪p, x⟫)) G) =
      volume (subgradientImage u G) := by
  rw [contact_subgradientImage_sub_affine, Set.image_add_right,
    measure_preimage_add_right]

private lemma contact_affine_volume {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (e '' G) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)| * volume G := by
  have he (x : E) : e x = e.linear x + e 0 := by
    simpa only [vadd_eq_add, add_zero] using e.map_vadd (0 : E) x
  have himage :
      e '' G = (fun x => x + e 0) '' ((e.linear : E →ₗ[ℝ] E) '' G) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact he x
  rw [himage, Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_linearMap]

private lemma contact_det_pos {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (e : E ≃ᵃ[ℝ] E) :
    0 < |LinearMap.det (e.linear : E →ₗ[ℝ] E)| := by
  classical
  apply abs_pos.mpr
  have h := (e.linear.isUnit_det (Module.finBasis ℝ E)
    (Module.finBasis ℝ E)).ne_zero
  simpa only [LinearMap.det_toMatrix] using h

private lemma contact_real_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {G A : Set E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hG : μ G ≠ ∞)
    (hlo : ENNReal.ofReal a * μ G ≤ μ A)
    (hhi : μ A ≤ ENNReal.ofReal b * μ G) :
    μ A ≠ ∞ ∧
      a * (μ G).toReal ≤ (μ A).toReal ∧
      (μ A).toReal ≤ b * (μ G).toReal := by
  have hprod : ENNReal.ofReal b * μ G ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG
  have hA : μ A ≠ ∞ := ne_top_of_le_ne_top hprod hhi
  refine ⟨hA, ?_, ?_⟩
  · have h := ENNReal.toReal_mono hA hlo
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] using h
  · have h := ENNReal.toReal_mono hprod hhi
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb] using h

private lemma contact_transport_real_bounds {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) (a b : ℝ)
    (hfin : (volume : Measure E) (subgradientImage u G) ≠ ∞)
    (hlo : a * ((volume : Measure E) G).toReal ≤
      (volume (subgradientImage u G)).toReal)
    (hhi : (volume (subgradientImage u G)).toReal ≤
      b * ((volume : Measure E) G).toReal) :
    let D := |LinearMap.det (e.linear : E →ₗ[ℝ] E)|
    (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) ≠ ∞ ∧
      (a / D ^ 2) * (volume (e '' G)).toReal ≤
        (volume (subgradientImage (u ∘ e.symm) (e '' G))).toReal ∧
      (volume (subgradientImage (u ∘ e.symm) (e '' G))).toReal ≤
        (b / D ^ 2) * (volume (e '' G)).toReal := by
  let D := |LinearMap.det (e.linear : E →ₗ[ℝ] E)|
  have hD : 0 < D := contact_det_pos e
  have hvol :
      ((volume : Measure E) (e '' G)).toReal =
        D * (volume G).toReal := by
    have h := congrArg ENNReal.toReal (contact_affine_volume e G)
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _)] using h
  have hgrad :
      ((volume : Measure E)
          (subgradientImage (u ∘ e.symm) (e '' G))).toReal =
        D⁻¹ * (volume (subgradientImage u G)).toReal := by
    have h := congrArg ENNReal.toReal
      (volume_subgradientImage_comp_affineEquiv_symm u e G)
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))] using h
  have hid (r V : ℝ) :
      r / D ^ 2 * (D * V) = D⁻¹ * (r * V) := by
    field_simp [ne_of_gt hD]
  refine ⟨?_, ?_, ?_⟩
  · rw [volume_subgradientImage_comp_affineEquiv_symm]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  · change a / D ^ 2 * _ ≤ _
    rw [hvol, hgrad, hid]
    exact mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hD.le)
  · change _ ≤ b / D ^ 2 * _
    rw [hvol, hgrad, hid]
    exact mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hD.le)

/- Step A bounds subgradients on the half unit ball. The resulting
   dimensional constant is 8 rather than the quadratic comparison's 4. -/
private lemma contact_stepA {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {S : Set E} {A t : ℝ} (ht : 0 < t)
    (hball : ball (0 : E) 1 ⊆ S)
    (hlo : ∀ x ∈ S, -2 * t ≤ v x)
    (hhi : ∀ x ∈ S, v x ≤ 0)
    (hA : A * ((volume : Measure E) (ball (0 : E) (1 / 2))).toReal ≤
      (volume (subgradientImage v (ball (0 : E) (1 / 2)))).toReal) :
    A ≤ (8 * t) ^ Module.finrank ℝ E := by
  let n := Module.finrank ℝ E
  have hsub :
      subgradientImage v (ball (0 : E) (1 / 2)) ⊆
        closedBall (0 : E) (4 * t) := by
    rintro p ⟨z, hz, hp⟩
    have hzNorm : ‖z‖ < 1 / 2 := by
      simpa only [mem_ball, dist_zero_right] using hz
    have hzS : z ∈ S :=
      hball ((ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)) hz)
    have hpNorm : ‖p‖ ≤ 4 * t := by
      by_cases hp0 : p = 0
      · simp only [hp0, norm_zero]
        positivity
      have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      let q : E := ‖p‖⁻¹ • p
      have hq : ‖q‖ = 1 := by
        dsimp only [q]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpn)]
        exact inv_mul_cancel₀ hpn.ne'
      let y : E := z + (1 / 2 : ℝ) • q
      have hyNorm : ‖y‖ < 1 := by
        calc
          ‖y‖ ≤ ‖z‖ + ‖(1 / 2 : ℝ) • q‖ := norm_add_le _ _
          _ = ‖z‖ + 1 / 2 := by
            rw [norm_smul, hq]
            norm_num
          _ < 1 := by linarith
      have hyS : y ∈ S := hball (by
        simpa only [mem_ball, dist_zero_right] using hyNorm)
      have hpair : ⟪p, y - z⟫ = ‖p‖ / 2 := by
        dsimp only [y, q]
        simp only [add_sub_cancel_left, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp [hpn.ne']
      have hs := hp y
      rw [hpair] at hs
      have hzlo := hlo z hzS
      have hyhi := hhi y hyS
      linarith
    simpa only [mem_closedBall, dist_zero_right] using hpNorm
  have hballfin :
      (volume : Measure E) (closedBall (0 : E) (4 * t)) ≠ ∞ :=
    Metric.isBounded_closedBall.measure_lt_top.ne
  have hmeasure := ENNReal.toReal_mono hballfin (measure_mono hsub)
  let V := ((volume : Measure E) (ball (0 : E) 1)).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩).ne'
    Metric.isBounded_ball.measure_lt_top.ne
  have hhalf :
      ((volume : Measure E) (ball (0 : E) (1 / 2))).toReal =
        (1 / 2 : ℝ) ^ n * V := by
    rw [Measure.addHaar_ball volume (0 : E) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hfour :
      ((volume : Measure E) (closedBall (0 : E) (4 * t))).toReal =
        (4 * t) ^ n * V := by
    rw [Measure.addHaar_closedBall volume (0 : E)
      (show 0 ≤ 4 * t by positivity)]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have h := hA.trans hmeasure
  rw [hhalf, hfour] at h
  have hcancel : A * (1 / 2 : ℝ) ^ n ≤ (4 * t) ^ n := by
    apply le_of_mul_le_mul_right (a := V) _ hV
    simpa only [mul_assoc] using h
  have hpow :
      (8 * t) ^ n * (1 / 2 : ℝ) ^ n = (4 * t) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  apply le_of_mul_le_mul_right (a := (1 / 2 : ℝ) ^ n) _ (by positivity)
  rw [hpow]
  exact hcancel

private lemma contact_stepB {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {S : Set E} {x : E} {c t C A B R : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hC : 0 < C) (hR : 0 ≤ R)
    (himage : S ⊆ closedBall (0 : E) C)
    (hfinite : (volume : Measure E) (subgradientImage v S) ≠ ∞)
    (hmaximum :
      ENNReal.ofReal (c * t ^ Module.finrank ℝ E) ≤
        (volume : Measure E) (subgradientImage v S) *
          ENNReal.ofReal
            (diam S ^ (Module.finrank ℝ E - 1) * infDist x (frontier S)))
    (hupper : ((volume : Measure E) (subgradientImage v S)).toReal ≤
      B * (volume (closedBall (0 : E) C)).toReal)
    (hA : A ≤ (8 * t) ^ Module.finrank ℝ E)
    (hBA : B ≤ R * A) :
    c ≤
      (R * 8 ^ Module.finrank ℝ E *
          ((volume : Measure E) (closedBall (0 : E) C)).toReal *
          (2 * C) ^ (Module.finrank ℝ E - 1)) *
        infDist x (frontier S) := by
  let n := Module.finrank ℝ E
  let V := ((volume : Measure E) (closedBall (0 : E) C)).toReal
  let d := infDist x (frontier S)
  have hd : 0 ≤ d := infDist_nonneg
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfinite ENNReal.ofReal_ne_top) hmaximum
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ c * t ^ Module.finrank ℝ E),
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg diam_nonneg _) infDist_nonneg)] at hreal
  have hB : B ≤ R * (8 * t) ^ n :=
    hBA.trans (mul_le_mul_of_nonneg_left hA hR)
  have hJ :
      ((volume : Measure E) (subgradientImage v S)).toReal ≤
        (R * (8 * t) ^ n) * V :=
    hupper.trans (mul_le_mul_of_nonneg_right hB hV)
  have hdiam : diam S ^ (n - 1) ≤ (2 * C) ^ (n - 1) :=
    pow_le_pow_left₀ diam_nonneg (diam_le_of_subset_closedBall hC.le himage) _
  have hfinal :
      c * t ^ n ≤
        (R * 8 ^ n * V * (2 * C) ^ (n - 1) * d) * t ^ n := by
    calc
      c * t ^ n ≤
          ((volume : Measure E) (subgradientImage v S)).toReal *
            (diam S ^ (n - 1) * d) := hreal
      _ ≤ ((R * (8 * t) ^ n) * V) * ((2 * C) ^ (n - 1) * d) :=
        mul_le_mul hJ (mul_le_mul_of_nonneg_right hdiam hd)
          (mul_nonneg (pow_nonneg diam_nonneg _) hd) (by positivity)
      _ = (R * 8 ^ n * V * (2 * C) ^ (n - 1) * d) * t ^ n := by
        rw [mul_pow]
        ring
  exact le_of_mul_le_mul_right hfinal (pow_pos ht n)

private lemma contact_stepC_choose {c C h K : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hh : 0 < h) (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ h ∧ K * (2 * C * δ / (h / 2)) < c := by
  let L : ℝ := K * (2 * C / (h / 2))
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hL1 : 0 < L + 1 := by linarith
  let δ : ℝ := min h (c / (L + 1)) / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact half_pos (lt_min hh (div_pos hc hL1))
  have hδh : δ ≤ h := by
    have hm := min_le_left h (c / (L + 1))
    dsimp only [δ]
    linarith
  have hδc : δ < c / (L + 1) := by
    have hm := min_le_right h (c / (L + 1))
    have hp := div_pos hc hL1
    dsimp only [δ]
    linarith
  have hmul := (lt_div_iff₀ hL1).mp hδc
  refine ⟨δ, hδ, hδh, ?_⟩
  have hid : K * (2 * C * δ / (h / 2)) = L * δ := by
    dsimp only [L]
    ring
  rw [hid]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Caffarelli's contact-set lemma, localised form** (weak Letwin route, N6, task T11e7): let `C` be the
compact contact set of a supporting affine function of the convex `u`, `z ∈ C` strictly exposed in the unit
direction `θ`, `h > 0`, and suppose the two-sided Alexandrov bounds hold only on compact subsets of an open `U`
containing the slab piece `C ∩ {⟪· − z, θ⟫ ≥ −h}`. Then `C = {z}`. -/
theorem contactSet_eq_singleton_of_exposed_of_local_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫})
    {z θ : E} (hz : u z = u x₀ + ⟪p, z - x₀⟫) (hθ : ‖θ‖ = 1)
    (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ z → ⟪x - z, θ⟫ < 0) {h : ℝ} (hh : 0 < h)
    {U : Set E} (hU : IsOpen U)
    (hCU : {x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U)
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ U → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G →
      closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
      (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G) :
    {x | u x = u x₀ + ⟪p, x - x₀⟫} = {z} := by
  classical
  by_contra hnot
  let C : Set E := {x | u x = u x₀ + ⟪p, x - x₀⟫}
  let xe : E := z
  have hxe : xe ∈ C := hz
  obtain ⟨x₁, hx₁, hx₁ne⟩ : ∃ x₁ ∈ C, x₁ ≠ xe := by
    by_contra hn
    apply hnot
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨hz, ?_⟩
    intro x hx
    by_contra hne
    exact hn ⟨x, hx, hne⟩
  have hx₁pair : ⟪x₁ - xe, θ⟫ < 0 := hexp x₁ hx₁ hx₁ne
  have hcontactWidth (x : E) (hx : x ∈ C) : ⟪x - xe, θ⟫ ≤ 0 := by
    by_cases he : x = xe
    · simp only [he, sub_self, inner_zero_left, le_refl]
    · exact (hexp x hx he).le
  let c₀ : ℝ := u x₀ - ⟪p, x₀⟫
  let w : E → ℝ := fun x => u x - (c₀ + ⟪p, x⟫)
  have hw_eq (x : E) :
      w x = u x - (u x₀ + ⟪p, x - x₀⟫) := by
    dsimp only [w, c₀]
    rw [inner_sub_right]
    ring
  have hw_nonneg (x : E) : 0 ≤ w x := by
    rw [hw_eq]
    exact sub_nonneg.mpr (hp x)
  have hw_zero_iff (x : E) : w x = 0 ↔ x ∈ C := by
    rw [hw_eq]
    exact sub_eq_zero
  have hwxe : w xe = 0 := (hw_zero_iff xe).mpr hxe
  have hwx₁ : w x₁ = 0 := (hw_zero_iff x₁).mpr hx₁
  have hwconv : ConvexOn ℝ univ w := contact_sub_affine_convex hconv c₀ p
  let s : ℝ := min (1 / 2) (h / (2 * |⟪x₁ - xe, θ⟫|))
  have habs : 0 < |⟪x₁ - xe, θ⟫| := abs_pos.mpr hx₁pair.ne
  have hs : 0 < s := by
    dsimp only [s]
    exact lt_min (by norm_num) (div_pos hh (mul_pos (by norm_num) habs))
  have hsone : s ≤ 1 := by
    have hs' : s ≤ 1 / 2 := min_le_left _ _
    linarith
  have hswidth : s * (2 * |⟪x₁ - xe, θ⟫|) ≤ h :=
    (le_div_iff₀ (mul_pos (by norm_num) habs)).mp (min_le_right _ _)
  let y : E := xe + s • (x₁ - xe)
  have hyC : y ∈ C := by
    have hyform : (1 - s) • xe + s • x₁ = y := by
      dsimp only [y]
      module
    have hc := hwconv.2 (mem_univ xe) (mem_univ x₁)
      (sub_nonneg.mpr hsone) hs.le (by ring : (1 - s) + s = 1)
    rw [hyform, hwxe, hwx₁] at hc
    simp only [smul_zero, add_zero] at hc
    exact (hw_zero_iff y).mp (le_antisymm hc (hw_nonneg y))
  have hypair_raw : ⟪y - xe, θ⟫ = s * ⟪x₁ - xe, θ⟫ := by
    dsimp only [y]
    rw [add_sub_cancel_left, real_inner_smul_left]
  let β : ℝ := -⟪y - xe, θ⟫
  have hβeq : β = s * |⟪x₁ - xe, θ⟫| := by
    dsimp only [β]
    rw [hypair_raw, abs_of_neg hx₁pair]
    ring
  have hβ : 0 < β := by
    rw [hβeq]
    exact mul_pos hs habs
  have hβhalf : β ≤ h / 2 := by
    rw [hβeq]
    nlinarith only [hswidth]
  have hypair : ⟪y - xe, θ⟫ = -β := by
    dsimp only [β]
    ring
  let P : Set E := C ∩ {x | -h ≤ ⟪x - xe, θ⟫}
  have hPcompact : IsCompact P :=
    hC.inter_right (isClosed_le continuous_const (by fun_prop))
  have hPne : P.Nonempty := by
    refine ⟨xe, hxe, ?_⟩
    change -h ≤ ⟪xe - xe, θ⟫
    simp only [sub_self, inner_zero_left]
    linarith
  obtain ⟨δ', hδ', hQU⟩ :=
    hPcompact.exists_cthickening_subset_open hU hCU
  let Q : Set E := cthickening δ' P
  have hQ : IsCompact Q := hPcompact.cthickening
  obtain ⟨⟨Q₀, hQ₀, ε₀, hε₀, hQ₀sub⟩, hshrink⟩ :=
    exists_compact_sections_subset_and_shrink hconv hp hC hxe hθ hexp hh
  obtain ⟨a, b₀, ha, hbounds⟩ := hB Q hQ hQU
  let b : ℝ := max b₀ 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right b₀ 1)
  obtain ⟨C₀, hC₀, hnormalize⟩ := exists_affine_normalization (E := E)
  obtain ⟨c, hc, hmaximum⟩ := exists_pos_alexandrov_maximum_principle (E := E)
  let n := Module.finrank ℝ E
  let R : ℝ := b / a
  have hR : 0 ≤ R := (div_pos hb ha).le
  let K : ℝ :=
    R * 8 ^ n * ((volume : Measure E) (closedBall (0 : E) C₀)).toReal *
      (2 * C₀) ^ (n - 1)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  obtain ⟨δ, hδ, hδβ, hδsmall⟩ :=
    contact_stepC_choose hc hC₀ (show 0 < 2 * β by positivity) hK
  have hδh : δ ≤ h := by linarith
  have htwoβ : 2 * β / 2 = β := by ring
  rw [htwoβ] at hδsmall
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := hshrink (min δ δ') (lt_min hδ hδ')
  let ε : ℝ := min ε₀ ε₁ / 2
  have hε : 0 < ε := half_pos (lt_min hε₀ hε₁)
  have hεsmall₀ : ε < ε₀ := by
    have hm := min_le_left ε₀ ε₁
    dsimp only [ε]
    linarith
  have hεsmall₁ : ε < ε₁ := by
    have hm := min_le_right ε₀ ε₁
    dsimp only [ε]
    linarith
  let q : E := ε • θ
  let c₁ : ℝ := ε * (h - ⟪θ, xe⟫)
  let v : E → ℝ := fun x => w x - (c₁ + ⟪q, x⟫)
  have hv_eq (x : E) :
      v x = w x - ε * (⟪x - xe, θ⟫ + h) := by
    have hqx : ⟪q, x⟫ = ε * ⟪θ, x⟫ := by
      change ⟪ε • θ, x⟫ = ε * ⟪θ, x⟫
      rw [real_inner_smul_left]
    have hinner : ⟪x - xe, θ⟫ = ⟪θ, x⟫ - ⟪θ, xe⟫ := by
      rw [← real_inner_comm (x - xe) θ, inner_sub_right]
    change w x - (c₁ + ⟪q, x⟫) = _
    rw [hqx, hinner]
    dsimp only [c₁]
    ring
  have hvconv : ConvexOn ℝ univ v := contact_sub_affine_convex hwconv c₁ q
  have hvc : Continuous v :=
    continuousOn_univ.mp (hvconv.continuousOn isOpen_univ)
  let S : Set E := {x | v x < 0}
  have hSo : IsOpen S := isOpen_lt hvc continuous_const
  have hSc : Convex ℝ S := by
    simpa only [mem_univ, true_and] using hvconv.convex_lt 0
  have hSQ₀ : S ⊆ Q₀ := by
    intro x hx
    apply hQ₀sub ε hε hεsmall₀
    change u x - (u x₀ + ⟪p, x - x₀⟫) <
      ε * (⟪x - xe, θ⟫ + h)
    rw [← hw_eq]
    have hx' : v x < 0 := hx
    rw [hv_eq] at hx'
    linarith
  have hSb : Bornology.IsBounded S := hQ₀.isBounded.subset hSQ₀
  have hSthickMin : S ⊆ cthickening (min δ δ') P := by
    intro x hx
    apply hε₁sub ε hε hεsmall₁
    change u x - (u x₀ + ⟪p, x - x₀⟫) <
      ε * (⟪x - xe, θ⟫ + h)
    rw [← hw_eq]
    have hx' : v x < 0 := hx
    rw [hv_eq] at hx'
    linarith
  have hSQ : S ⊆ Q :=
    hSthickMin.trans (cthickening_mono (min_le_right δ δ') P)
  have hSclQ : closure S ⊆ Q := closure_minimal hSQ hQ.isClosed
  have hSthick : S ⊆ cthickening δ P :=
    hSthickMin.trans (cthickening_mono (min_le_left δ δ') P)
  have hvxe : v xe = -(ε * h) := by
    rw [hv_eq, hwxe]
    simp only [sub_self, inner_zero_left, zero_add, zero_sub]
  have hxeS : xe ∈ S := by
    change v xe < 0
    rw [hvxe]
    exact neg_neg_of_pos (mul_pos hε hh)
  have hyS : y ∈ S := by
    change v y < 0
    rw [hv_eq, (hw_zero_iff y).mpr hyC, hypair]
    have hgap : 0 < -β + h := by linarith
    exact sub_neg.mpr (mul_pos hε hgap)
  have hup (x : E) (hx : x ∈ S) : ⟪x - xe, θ⟫ ≤ δ := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (mem_cthickening_iff.mp (hSthick hx))
    have hdist : infDist x P ≤ δ := by
      simpa only [Metric.infDist, ENNReal.toReal_ofReal hδ.le] using ht
    obtain ⟨r, hr, heq⟩ := hPcompact.exists_infDist_eq_dist hPne x
    have hrdist : ‖x - r‖ ≤ δ := by
      rw [heq, dist_eq_norm] at hdist
      exact hdist
    have hrwidth := hcontactWidth r hr.1
    have hinner : ⟪x - r, θ⟫ ≤ ‖x - r‖ := by
      calc
        ⟪x - r, θ⟫ ≤ |⟪x - r, θ⟫| := le_abs_self _
        _ ≤ ‖x - r‖ * ‖θ‖ := abs_real_inner_le_norm _ _
        _ = ‖x - r‖ := by rw [hθ, mul_one]
    rw [show x - xe = (x - r) + (r - xe) by abel, inner_add_left]
    linarith
  have hvfront : ∀ x ∈ frontier S, v x = 0 := by
    have hsub : S ⊆ {x | v x ≤ 0} := by
      intro z hz
      exact le_of_lt (show v z < 0 from hz)
    have hcl : closure S ⊆ {x | v x ≤ 0} :=
      closure_minimal hsub (isClosed_le hvc continuous_const)
    intro x hx
    have hlo : v x ≤ 0 := hcl (frontier_subset_closure hx)
    have hnotS : x ∉ S := (hSo.frontier_eq ▸ hx).2
    have hhi : 0 ≤ v x := le_of_not_gt hnotS
    exact le_antisymm hlo hhi
  have hSne : S.Nonempty := ⟨xe, hxeS⟩
  have hreg : interior (closure S) = S := by
    rw [hSc.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hSo.interior_eq]; exact hSne), hSo.interior_eq]
  have hclosureCompact : IsCompact (closure S) :=
    hQ.of_isClosed_subset isClosed_closure hSclQ
  obtain ⟨e, heball, heouter⟩ := hnormalize (closure S) hclosureCompact hSc.closure
    (by rw [hreg]; exact hSne)
  let eh := (AffineEquiv.toContinuousAffineEquiv e).toHomeomorph
  let S' : Set E := e '' S
  let v' : E → ℝ := v ∘ e.symm
  let D : ℝ := |LinearMap.det (e.linear : E →ₗ[ℝ] E)|
  have hD : 0 < D := contact_det_pos e
  have hS'o : IsOpen S' := eh.isOpenMap S hSo
  have hS'c : Convex ℝ S' := hSc.affine_image e.toAffineMap
  have hS'outer : S' ⊆ closedBall (0 : E) C₀ :=
    (Set.image_mono subset_closure).trans heouter
  have hS'b : Bornology.IsBounded S' :=
    Metric.isBounded_closedBall.subset hS'outer
  have hS'ball : ball (0 : E) 1 ⊆ S' := by
    intro x hx
    have hi : x ∈ interior (e '' closure S) :=
      interior_mono heball (ball_subset_interior_closedBall hx)
    have him : eh '' interior (closure S) = interior (e '' closure S) :=
      eh.image_interior (closure S)
    rw [← him, hreg] at hi
    exact hi
  have hv'conv : ConvexOn ℝ univ v' := by
    simpa [v', Function.comp_def] using hvconv.comp_affineMap e.symm.toAffineMap
  have hv'front : ∀ x ∈ frontier S', v' x = 0 := by
    intro x hx
    have him : eh '' frontier S = frontier S' := eh.image_frontier S
    rw [← him] at hx
    rcases hx with ⟨z, hz, rfl⟩
    change v (e.symm (e z)) = 0
    rw [e.symm_apply_apply]
    exact hvfront z hz
  have hloc :
      ∀ G' : Set E, IsOpen G' → G' ⊆ S' →
        (volume : Measure E) (subgradientImage v' G') ≠ ∞ ∧
          (a / D ^ 2) * (volume G').toReal ≤
            (volume (subgradientImage v' G')).toReal ∧
          (volume (subgradientImage v' G')).toReal ≤
            (b / D ^ 2) * (volume G').toReal := by
    intro G' hG'o hG'S
    let G : Set E := e.symm '' G'
    have hGo : IsOpen G := eh.symm.isOpenMap G' hG'o
    have hGS : G ⊆ S := by
      rintro x ⟨z, hz, rfl⟩
      rcases hG'S hz with ⟨y, hy, he⟩
      rw [← he, e.symm_apply_apply]
      exact hy
    have hGcl : closure G ⊆ Q := (closure_mono hGS).trans hSclQ
    obtain ⟨hlo, hhi⟩ := hbounds G hGo hGcl
    have hhi' :
        (volume : Measure E) (subgradientImage u G) ≤
          ENNReal.ofReal b * volume G :=
      hhi.trans (mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (le_max_left b₀ 1)) _)
    have hvvolume :
        (volume : Measure E) (subgradientImage v G) =
          volume (subgradientImage u G) := by
      rw [contact_volume_sub_affine w c₁ q G,
        contact_volume_sub_affine u c₀ p G]
    have hGfin : (volume : Measure E) G ≠ ∞ :=
      (hSb.subset hGS).measure_lt_top.ne
    obtain ⟨hfin, hrealLo, hrealHi⟩ :=
      contact_real_bounds (volume : Measure E) ha.le hb.le hGfin hlo hhi'
    rw [← hvvolume] at hfin hrealLo hrealHi
    have himage : e '' G = G' := e.toEquiv.image_symm_image G'
    have ht := contact_transport_real_bounds v e G a b hfin hrealLo hrealHi
    simpa only [himage] using ht
  let t : ℝ := ε * h
  have ht : 0 < t := mul_pos hε hh
  have hv'lo : ∀ x ∈ S', -2 * t ≤ v' x := by
    rintro x ⟨z, hz, rfl⟩
    change -2 * t ≤ v (e.symm (e z))
    rw [e.symm_apply_apply, hv_eq]
    have hzlo := hw_nonneg z
    have hzup := hup z hz
    have hi : ⟪z - xe, θ⟫ + h ≤ 2 * h := by linarith
    have hm := mul_le_mul_of_nonneg_left hi hε.le
    dsimp only [t]
    nlinarith
  have hv'hi : ∀ x ∈ S', v' x ≤ 0 := by
    rintro x ⟨z, hz, rfl⟩
    change v (e.symm (e z)) ≤ 0
    rw [e.symm_apply_apply]
    exact le_of_lt hz
  have hhalfS : ball (0 : E) (1 / 2) ⊆ S' :=
    (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans hS'ball
  have hA :
      a / D ^ 2 ≤ (8 * t) ^ n :=
    contact_stepA ht hS'ball hv'lo hv'hi
      (hloc (ball (0 : E) (1 / 2)) isOpen_ball hhalfS).2.1
  obtain ⟨hfinite, _, hupper⟩ := hloc S' hS'o (Subset.refl S')
  have hupper' :
      ((volume : Measure E) (subgradientImage v' S')).toReal ≤
        (b / D ^ 2) * (volume (closedBall (0 : E) C₀)).toReal := by
    apply hupper.trans
    apply mul_le_mul_of_nonneg_left
    · exact ENNReal.toReal_mono Metric.isBounded_closedBall.measure_lt_top.ne
        (measure_mono hS'outer)
    · positivity
  have hxeS' : e xe ∈ S' := ⟨xe, hxeS, rfl⟩
  have hv'xe : v' (e xe) = -t := by
    change v (e.symm (e xe)) = -(ε * h)
    rw [e.symm_apply_apply]
    exact hvxe
  have hAMP := hmaximum v' hv'conv S' hS'o hS'c hS'b
    (fun x hx => (hv'front x hx).symm.le)
    (e xe) hxeS' (by rw [hv'xe]; exact neg_neg_of_pos ht)
  rw [hv'xe, neg_neg] at hAMP
  have hBA : b / D ^ 2 ≤ R * (a / D ^ 2) := by
    apply le_of_eq
    dsimp only [R]
    field_simp [ha.ne', hD.ne']
  have haway : c ≤ K * infDist (e xe) (frontier S') :=
    contact_stepB hc ht hC₀ hR hS'outer hfinite hAMP hupper' hA hBA
  have hnear :
      infDist (e xe) (frontier S') ≤ 2 * C₀ * δ / β :=
    infDist_frontier_image_le_of_width hSo hSb hxeS hθ hδ.le hβ
      hup ⟨y, hyS, hypair.le⟩ e hC₀ hS'outer
  have hstrict : K * infDist (e xe) (frontier S') < c :=
    (mul_le_mul_of_nonneg_left hnear hK).trans_lt hδsmall
  exact (not_lt_of_ge haway) hstrict

/-- **Caffarelli's contact-set lemma** (global bounds, compact contact set; same statement as task L-T11e,
re-derived here from the localised form so that only this file needs integrating). -/
theorem contactSet_eq_singleton_of_local_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hB : ∀ Q : Set E, IsCompact Q → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
      (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G)
    {x₀ p : E} (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y)
    (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫}) :
    {x | u x = u x₀ + ⟪p, x - x₀⟫} = {x₀} := by
  classical
  by_contra hnot
  let C : Set E := {x | u x = u x₀ + ⟪p, x - x₀⟫}
  have hx₀ : x₀ ∈ C := by simp [C]
  obtain ⟨xe, hxe, hmax, hexposed⟩ :=
    exists_farthest_point_exposed hC ⟨x₀, hx₀⟩ x₀
  have hxe_ne : xe ≠ x₀ := by
    intro he
    apply hnot
    ext x
    constructor
    · intro hx
      have hh := hmax x hx
      rw [he, sub_self, norm_zero] at hh
      have hzero : x - x₀ = 0 :=
        norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
      exact Set.mem_singleton_iff.mpr (sub_eq_zero.mp hzero)
    · intro hx
      have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact hx₀
  let d : ℝ := ‖xe - x₀‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxe_ne)
  let θ : E := d⁻¹ • (xe - x₀)
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    change d⁻¹ * d = 1
    exact inv_mul_cancel₀ hd.ne'
  have hexp :
      ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ xe → ⟪x - xe, θ⟫ < 0 := by
    intro x hx hne
    dsimp only [θ]
    rw [real_inner_smul_right]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hd) (hexposed x hx hne)
  have hsing : C = {xe} :=
    contactSet_eq_singleton_of_exposed_of_local_bounds hconv hp hC hxe hθ hexp
      (h := 1) (by norm_num) (U := univ) isOpen_univ (subset_univ _)
      (fun Q hQ _ => hB Q hQ)
  have he : x₀ = xe := Set.mem_singleton_iff.mp (hsing ▸ hx₀)
  exact hxe_ne he.symm

end FunctionalInequalities.Analysis

end LT11E7LocalizedContactLemma

section LT11F1StrictConvexityElementary

open Set
open scoped RealInnerProductSpace

/-! Elementary steps from singleton contact sets to strict convexity (task L-T11f1). -/

namespace FunctionalInequalities.Analysis

private theorem strict_supporting_inequality {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} (hstrict : StrictConvexOn ℝ univ u)
    {x p y : E} (hp : ∀ t, u x + ⟪p, t - x⟫ ≤ u t) (hy : y ≠ x) :
    u x + ⟪p, y - x⟫ < u y := by
  by_contra hn
  have heq : u y = u x + ⟪p, y - x⟫ :=
    le_antisymm (le_of_not_gt hn) (hp y)
  have hm :
      u ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) <
        (1 / 2 : ℝ) • u x + (1 / 2 : ℝ) • u y :=
    hstrict.2 (mem_univ x) (mem_univ y) hy.symm
      (by norm_num) (by norm_num) (by norm_num)
  have hs := hp ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  simp only [smul_eq_mul] at hm
  simp only [inner_sub_right, inner_add_right, real_inner_smul_right] at hs heq
  linarith

/-- **Singleton contact sets give strict convexity** (weak Letwin route, N6, task T11f1): if every
supporting affine function of the convex `u` touches its graph at exactly one point, `u` is strictly
convex. -/
theorem strictConvexOn_of_contact_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hcontact : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
      ∀ y, u y = u x + ⟪p, y - x⟫ → y = x) :
    StrictConvexOn ℝ univ u := by
  refine ⟨hconv.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hle := hconv.2 hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hle ⊢
  by_contra hn
  let z := a • x + b • y
  have heq : u z = a * u x + b * u y :=
    le_antisymm hle (le_of_not_gt hn)
  obtain ⟨p, hp, _⟩ := exists_subgradient_slope_le_inner_add hconv z (0 : E)
  have hzinner : ⟪p, z⟫ = a * ⟪p, x⟫ + b * ⟪p, y⟫ := by
    simp only [z, inner_add_right, real_inner_smul_right]
  have hlinear : a * ⟪p, x - z⟫ + b * ⟪p, y - z⟫ = 0 := by
    simp only [inner_sub_right]
    calc
      a * (⟪p, x⟫ - ⟪p, z⟫) + b * (⟪p, y⟫ - ⟪p, z⟫) =
          (a * ⟪p, x⟫ + b * ⟪p, y⟫) - (a + b) * ⟪p, z⟫ := by ring
      _ = 0 := by rw [← hzinner, hab, one_mul, sub_self]
  let A := u x - u z - ⟪p, x - z⟫
  let B := u y - u z - ⟪p, y - z⟫
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [hp x]
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [hp y]
  have hsum : a * A + b * B = 0 := by
    dsimp [A, B]
    calc
      a * (u x - u z - ⟪p, x - z⟫) +
          b * (u y - u z - ⟪p, y - z⟫) =
          (a * u x + b * u y) - (a + b) * u z -
            (a * ⟪p, x - z⟫ + b * ⟪p, y - z⟫) := by ring
      _ = 0 := by rw [← heq, hab, hlinear, one_mul, sub_self, sub_zero]
  have haA : 0 ≤ a * A := mul_nonneg ha.le hA
  have hbB : 0 ≤ b * B := mul_nonneg hb.le hB
  have hAz : A = 0 := by
    have h : a * A = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt ha)
  have hBz : B = 0 := by
    have h : b * B = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_left (ne_of_gt hb)
  have hxz : x = z := hcontact z p hp x (by dsimp [A] at hAz; linarith)
  have hyz : y = z := hcontact z p hp y (by dsimp [B] at hBz; linarith)
  exact hxy (hxz.trans hyz.symm)

/-- **Slopes of a strictly convex function lie in the interior of a convex slope range** (weak Letwin
route, N7, task T11f1): if all subgradients of the strictly convex `u` lie in a convex `K` with nonempty
interior, they lie in `interior K`. -/
theorem subgradient_mem_interior_of_strictConvexOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {K : Set E} (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (hK : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ interior K := by
  by_contra hn
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hKc.interior isOpen_interior hn
  have hbound : ∀ q ∈ K, f q ≤ f p := by
    have hcl : closure (interior K) ⊆ {q | f q ≤ f p} :=
      closure_minimal (fun q hq => (hf q hq).le)
        (isClosed_le f.continuous continuous_const)
    intro q hq
    apply hcl
    rw [hKc.closure_interior_eq_closure_of_nonempty_interior hKint]
    exact subset_closure hq
  let v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hvf : ∀ q : E, ⟪v, q⟫ = f q := by
    intro q
    exact InnerProductSpace.toDual_symm_apply
  have hv : v ≠ 0 := by
    intro hvzero
    obtain ⟨q, hq⟩ := hKint
    have hqp := hf q hq
    rw [← hvf q, ← hvf p, hvzero, inner_zero_left, inner_zero_left] at hqp
    exact (lt_irrefl (0 : ℝ)) hqp
  have hxv : x + v ≠ x := add_ne_left.mpr hv
  have hlt := strict_supporting_inequality hstrict hp hxv
  rw [add_sub_cancel_left] at hlt
  obtain ⟨q, hq, _⟩ :=
    exists_subgradient_slope_le_inner_add hstrict.convexOn (x + v) (0 : E)
  have hback := hq x
  have hsub : x - (x + v) = -v := by abel
  rw [hsub, inner_neg_right] at hback
  have hqp := hbound q (hK (x + v) q hq)
  have hpv : ⟪p, v⟫ = f p := (real_inner_comm v p).trans (hvf p)
  have hqv : ⟪q, v⟫ = f q := (real_inner_comm v q).trans (hvf q)
  rw [hpv] at hlt
  rw [hqv] at hback
  linarith

/-- **A strictly exposed contact point below a level** (weak Letwin route, N6, task T11f1; KLS500
`exists_strict_exposed_contact_in_sublevel`): if `{u ≤ R}` is compact and `u x < R`, the contact set of a
supporting affine function at `x` has a point `z` with `u z < R` that is strictly exposed in the direction
`θ` among the contact points with `u ≤ R`. -/
theorem exists_exposed_contact_of_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {R : ℝ} (hR : u x < R) (hK : IsCompact {y | u y ≤ R}) :
    ∃ z θ : E, u z = u x + ⟪p, z - x⟫ ∧ u z < R ∧
      ∀ y, u y = u x + ⟪p, y - x⟫ → u y ≤ R → y ≠ z → ⟪y - z, θ⟫ < 0 := by
  have hu : Continuous u := continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  let C : Set E := {y | u y = u x + ⟪p, y - x⟫} ∩ {y | u y ≤ R}
  have hclosed : IsClosed {y | u y = u x + ⟪p, y - x⟫} :=
    isClosed_eq hu (continuous_const.add
      (continuous_const.inner (continuous_id.sub continuous_const)))
  have hC : IsCompact C := hK.inter_left hclosed
  have hxC : x ∈ C := by
    refine ⟨?_, hR.le⟩
    change u x = u x + ⟪p, x - x⟫
    exact le_antisymm (by simp) (hp x)
  obtain ⟨M, hM, hbound⟩ := hC.isBounded.exists_pos_norm_le
  let ε : ℝ := (R - u x) / (2 * (M ^ 2 + 1))
  have hden : 0 < 2 * (M ^ 2 + 1) := by positivity
  have hε : 0 < ε := div_pos (sub_pos.mpr hR) hden
  have hεeq : ε * (2 * (M ^ 2 + 1)) = R - u x :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hεM : ε * M ^ 2 < R - u x := by
    nlinarith [mul_nonneg hε.le (sq_nonneg M)]
  let F : E → ℝ := fun y => ε * ‖y‖ ^ 2 - ⟪p, y⟫
  have hF : Continuous F :=
    (continuous_const.mul (continuous_norm.pow 2)).sub
      (continuous_const.inner continuous_id)
  obtain ⟨z, hzC, hzmax⟩ := hC.exists_isMaxOn ⟨x, hxC⟩ hF.continuousOn
  have hmax : ∀ y ∈ C, F y ≤ F z := isMaxOn_iff.mp hzmax
  have hzcontact : u z = u x + ⟪p, z - x⟫ := hzC.1
  have hzsq : ‖z‖ ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) hM.le).mpr (hbound z hzC)
  have hzquad : ε * ‖z‖ ^ 2 ≤ ε * M ^ 2 := mul_le_mul_of_nonneg_left hzsq hε.le
  have hxquad : 0 ≤ ε * ‖x‖ ^ 2 := mul_nonneg hε.le (sq_nonneg ‖x‖)
  have hzR : u z < R := by
    have hxmax := hmax x hxC
    dsimp [F] at hxmax
    have hzcontact' := hzcontact
    rw [inner_sub_right] at hzcontact'
    linarith
  let θ : E := (2 * ε) • z - p
  refine ⟨z, θ, hzcontact, hzR, ?_⟩
  intro y hy hyR hyz
  have hymax := hmax y ⟨hy, hyR⟩
  have hnorm : 0 < ‖y - z‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz))
  have hpos : 0 < ε * ‖y - z‖ ^ 2 := mul_pos hε hnorm
  have hid : ⟪y - z, θ⟫ = F y - F z - ε * ‖y - z‖ ^ 2 := by
    rw [real_inner_comm θ (y - z)]
    dsimp [θ, F]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, norm_sub_sq_real]
    rw [real_inner_comm z y]
    ring
  rw [hid]
  linarith

end FunctionalInequalities.Analysis

end LT11F1StrictConvexityElementary

section LT11F2TruncatedConjugate

open Set Metric
open scoped RealInnerProductSpace

/-! The truncated conjugate used to localize the contact-set argument (task L-T11f2). -/

namespace FunctionalInequalities.Analysis

/-- The **ball-truncated conjugate** `p ↦ sup_{‖x‖ ≤ M} (⟪p, x⟫ − u x)` (weak Letwin route, N7, task T11f2;
KLS500 `truncatedLegendrePotential`): a globally finite convex function that agrees with the Legendre
transform of `u` wherever the supremum is attained inside the ball. -/
def truncatedConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : E → ℝ)
    (M : ℝ) (p : E) : ℝ :=
  sSup ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M)

/-- The supremum is attained and dominates every value on the ball. -/
theorem exists_truncatedConjugate_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (p : E) :
    (∃ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x) ∧
      ∀ x ∈ closedBall (0 : E) M, ⟪p, x⟫ - u x ≤ truncatedConjugate u M p := by
  have hc :
      IsCompact ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M) :=
    (isCompact_closedBall (0 : E) M).image
      ((continuous_const.inner continuous_id).sub hu)
  have hn :
      ((fun x => ⟪p, x⟫ - u x) '' closedBall (0 : E) M).Nonempty :=
    ⟨⟪p, 0⟫ - u 0, ⟨0, mem_closedBall_self hM, rfl⟩⟩
  constructor
  · obtain ⟨x, hx, heq⟩ := hc.sSup_mem hn
    exact ⟨x, hx, heq.symm⟩
  · intro x hx
    exact le_csSup hc.bddAbove ⟨x, hx, rfl⟩

/-- The truncated conjugate is convex. -/
theorem convexOn_truncatedConjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
    ConvexOn ℝ univ (truncatedConjugate u M) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  obtain ⟨x, hx, heq⟩ :=
    (exists_truncatedConjugate_eq hu hM (a • p + b • q)).1
  have hpx := (exists_truncatedConjugate_eq hu hM p).2 x hx
  have hqx := (exists_truncatedConjugate_eq hu hM q).2 x hx
  change truncatedConjugate u M (a • p + b • q) ≤
    a * truncatedConjugate u M p + b * truncatedConjugate u M q
  rw [heq]
  calc
    ⟪a • p + b • q, x⟫ - u x =
        a * (⟪p, x⟫ - u x) + b * (⟪q, x⟫ - u x) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith [congrArg (fun t : ℝ => t * u x) hab]
    _ ≤ a * truncatedConjugate u M p + b * truncatedConjugate u M q :=
      add_le_add (mul_le_mul_of_nonneg_left hpx ha)
        (mul_le_mul_of_nonneg_left hqx hb)

/-- **Zeros of the centred truncated conjugate are the subgradients** (task T11f2): for convex `u` and
`‖xc‖ < M`, `f p := truncatedConjugate u M p − ⟪p, xc⟫ + u xc` is nonnegative, vanishes exactly at the
subgradients of `u` at `xc`, and has compact sublevel sets. -/
theorem truncatedConjugate_centered_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {M : ℝ} {xc : E}
    (hxc : ‖xc‖ < M) :
    (∀ p, 0 ≤ truncatedConjugate u M p - ⟪p, xc⟫ + u xc) ∧
    (∀ p, truncatedConjugate u M p - ⟪p, xc⟫ + u xc = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y) ∧
    ∀ R : ℝ, IsCompact {p | truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R} := by
  have hu : Continuous u :=
    continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  have hM : 0 ≤ M := (norm_nonneg xc).trans hxc.le
  have hxc_mem : xc ∈ closedBall (0 : E) M :=
    mem_closedBall_zero_iff.mpr hxc.le
  have hnonneg (p : E) :
      0 ≤ truncatedConjugate u M p - ⟪p, xc⟫ + u xc := by
    have h := (exists_truncatedConjugate_eq hu hM p).2 xc hxc_mem
    linarith
  refine ⟨hnonneg, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      have htilt : ConvexOn ℝ univ (fun x => u x - ⟪p, x⟫) := by
        refine ⟨convex_univ, ?_⟩
        intro x hx y hy a b ha hb hab
        have hc := hconv.2 hx hy ha hb hab
        change u (a • x + b • y) - ⟪p, a • x + b • y⟫ ≤
          a * (u x - ⟪p, x⟫) + b * (u y - ⟪p, y⟫)
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        change u (a • x + b • y) ≤ a * u x + b * u y at hc
        linarith
      have hmin :
          IsMinOn (fun x => u x - ⟪p, x⟫) (closedBall (0 : E) M) xc := by
        intro x hx
        have h := (exists_truncatedConjugate_eq hu hM p).2 x hx
        change u xc - ⟪p, xc⟫ ≤ u x - ⟪p, x⟫
        linarith
      have hnbhd : closedBall (0 : E) M ∈ nhds xc :=
        Filter.mem_of_superset
          (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxc))
          ball_subset_closedBall
      have hglobal :=
        IsMinOn.of_isLocalMin_of_convex_univ (hmin.isLocalMin hnbhd) htilt
      intro y
      have hy := hglobal y
      rw [inner_sub_right]
      linarith
    · intro hp
      obtain ⟨x, hx, heq⟩ := (exists_truncatedConjugate_eq hu hM p).1
      have hs := hp x
      rw [inner_sub_right] at hs
      have hn := hnonneg p
      rw [heq] at hn ⊢
      linarith
  · intro R
    have htc : Continuous (truncatedConjugate u M) :=
      continuousOn_univ.mp
        (ConvexOn.continuousOn isOpen_univ (convexOn_truncatedConjugate hu hM))
    have hf : Continuous (fun p => truncatedConjugate u M p - ⟪p, xc⟫ + u xc) :=
      (htc.sub (continuous_id.inner continuous_const)).add continuous_const
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hu.continuousOn
    have hd : 0 < M - ‖xc‖ := sub_pos.mpr hxc
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hf continuous_const)
    apply (Metric.isBounded_iff_subset_closedBall (0 : E)).2
    refine ⟨max 0 ((R + C - u xc) / (M - ‖xc‖)), ?_⟩
    intro p hp
    change truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R at hp
    apply mem_closedBall_zero_iff.mpr
    by_cases hp0 : p = 0
    · subst p
      rw [norm_zero]
      exact le_max_left _ _
    · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
      let x : E := xc + ((M - ‖xc‖) / ‖p‖) • p
      have hnorm : ‖((M - ‖xc‖) / ‖p‖) • p‖ = M - ‖xc‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hd.le (norm_nonneg p)), div_mul_cancel₀ _ hn]
      have hx : x ∈ closedBall (0 : E) M := by
        apply mem_closedBall_zero_iff.mpr
        calc
          ‖x‖ ≤ ‖xc‖ + ‖((M - ‖xc‖) / ‖p‖) • p‖ := norm_add_le _ _
          _ = M := by rw [hnorm]; ring
      have hinner : ⟪p, x⟫ = ⟪p, xc⟫ + (M - ‖xc‖) * ‖p‖ := by
        dsimp only [x]
        rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        congr 1
        field_simp
      have hux : u x ≤ C := by
        have hc := hC x hx
        rw [Real.norm_eq_abs] at hc
        exact (le_abs_self (u x)).trans hc
      have hdom := (exists_truncatedConjugate_eq hu hM p).2 x hx
      rw [hinner] at hdom
      calc
        ‖p‖ ≤ (R + C - u xc) / (M - ‖xc‖) := by
          apply (le_div_iff₀ hd).2
          nlinarith
        _ ≤ max 0 ((R + C - u xc) / (M - ‖xc‖)) := le_max_right _ _

end FunctionalInequalities.Analysis

end LT11F2TruncatedConjugate

section LT11F3TruncatedConjugateSubgradients

open Set Metric
open scoped RealInnerProductSpace Topology

/-! Subgradients and subgradient images of the truncated conjugate (task L-T11f3). -/

namespace FunctionalInequalities.Analysis

private lemma n7_isClosed_bad_maximizers {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) {C : Set E} (hC : IsClosed C) :
    IsClosed {p : E | ∃ x ∈ closedBall (0 : E) M,
      x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
  let B := closedBall (0 : E) M
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 M)
  have hT : Continuous (truncatedConjugate u M) :=
    continuousOn_univ.mp ((convexOn_truncatedConjugate hu hM).continuousOn isOpen_univ)
  let D : Set (B × E) :=
    {q | (q.1 : E) ∈ C ∧ truncatedConjugate u M q.2 = ⟪q.2, (q.1 : E)⟫ - u q.1}
  have hD : IsClosed D :=
    (hC.preimage (continuous_subtype_val.comp continuous_fst)).inter
      (isClosed_eq (hT.comp continuous_snd)
        ((continuous_snd.inner (continuous_subtype_val.comp continuous_fst)).sub
          (hu.comp (continuous_subtype_val.comp continuous_fst))))
  have he : Prod.snd '' D =
      {p : E | ∃ x ∈ closedBall (0 : E) M,
        x ∈ C ∧ truncatedConjugate u M p = ⟪p, x⟫ - u x} := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hx, rfl⟩
      exact ⟨x, x.property, hx⟩
    · rintro ⟨x, hx, hc, he⟩
      exact ⟨(⟨x, hx⟩, p), ⟨hc, he⟩, rfl⟩
  rw [← he]
  exact isClosedMap_snd_of_compactSpace D hD

private lemma n7_support_min {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    IsMinOn (fun y => u y - ⟪p, y⟫) univ x := by
  intro y _
  have h := hp y
  rw [inner_sub_right] at h
  dsimp
  linarith

private lemma n7_support_unique {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {x z p : E}
    (hx : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (hz : ∀ y, u z + ⟪p, y - z⟫ ≤ u y) : x = z := by
  exact (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
    (n7_support_min hx) (n7_support_min hz) (mem_univ x) (mem_univ z)

private lemma n7_conjugate_eq_of_support {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u : E → ℝ} {M : ℝ} {x p : E}
    (hx : x ∈ closedBall (0 : E) M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    truncatedConjugate u M p = ⟪p, x⟫ - u x := by
  have hb : ∀ y, ⟪p, y⟫ - u y ≤ ⟪p, x⟫ - u x := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h
    linarith
  apply le_antisymm
  · exact csSup_le ⟨_, ⟨x, hx, rfl⟩⟩ (by
      rintro _ ⟨y, _, rfl⟩
      exact hb y)
  · exact le_csSup ⟨_, by
      rintro _ ⟨y, _, rfl⟩
      exact hb y⟩ ⟨x, hx, rfl⟩

private lemma n7_support_of_interior_max {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Continuous u) (hconv : ConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M)
    {x p : E} (hx : ‖x‖ < M)
    (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x) :
    ∀ y, u x + ⟪p, y - x⟫ ≤ u y := by
  let f : E → ℝ := fun z => u z - ⟪p, z⟫
  have hf : ConvexOn ℝ univ f :=
    hconv.sub ((innerₗ E p).concaveOn convex_univ)
  have hmin : ∀ z ∈ ball (0 : E) M, f x ≤ f z := by
    intro z hz
    have h := (exists_truncatedConjugate_eq hu hM p).2 z
      (closedBall_subset_closedBall (le_refl M)
        (ball_subset_closedBall hz))
    rw [heq] at h
    dsimp [f]
    linarith
  intro y
  have hpre : (AffineMap.lineMap x y) ⁻¹' ball (0 : E) M ∈ 𝓝 (0 : ℝ) :=
    (AffineMap.lineMap_continuous (p := x) (q := y)).continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (by
        rw [AffineMap.lineMap_apply_zero]
        exact mem_ball_zero_iff.mpr hx))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hz : AffineMap.lineMap x y t ∈ ball (0 : E) M := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htε
  have hxz := hmin _ hz
  have hzy := hf.le_right_of_left_le (mem_univ x) (mem_univ y)
    (lineMap_mem_openSegment ℝ x y ⟨ht, ht1⟩) hxz
  have hxy : f x ≤ f y := hxz.trans hzy
  dsimp [f] at hxy
  rw [inner_sub_right]
  linarith

/-- The set of slopes whose ball maximisers all lie in the open ball is open (weak Letwin route, N7,
task T11f3). -/
theorem isOpen_setOf_truncatedConjugate_maximizer_lt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hu : Continuous u) {M : ℝ}
    (hM : 0 ≤ M) :
    IsOpen {p : E | ∀ x ∈ closedBall (0 : E) M,
      truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} := by
  classical
  have hc : IsClosed {x : E | M ≤ ‖x‖} :=
    isClosed_le continuous_const continuous_norm
  have he :
      {p : E | ∀ x ∈ closedBall (0 : E) M,
        truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} =
      {p : E | ∃ x ∈ closedBall (0 : E) M,
        x ∈ {x : E | M ≤ ‖x‖} ∧
          truncatedConjugate u M p = ⟪p, x⟫ - u x}ᶜ := by
    ext p
    constructor
    · intro hp
      rintro ⟨x, hx, hn, heq⟩
      exact (not_lt_of_ge hn) (hp x hx heq)
    · intro hp x hx heq
      by_contra hn
      exact hp ⟨x, hx, le_of_not_gt hn, heq⟩
  rw [he]
  exact (n7_isClosed_bad_maximizers hu hM hc).isOpen_compl

/-- For strictly convex `u`, a subgradient `p` at a point `x` of the open ball has `x` as its only ball
maximiser (task T11f3). -/
theorem eq_of_truncatedConjugate_eq_of_subgradient {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} {x p : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {x' : E} (hx' : x' ∈ closedBall (0 : E) M)
    (heq : truncatedConjugate u M p = ⟪p, x'⟫ - u x') : x' = x := by
  have hxeq := n7_conjugate_eq_of_support (mem_closedBall_zero_iff.mpr hx.le) hp
  have hp' : ∀ y, u x' + ⟪p, y - x'⟫ ≤ u y := by
    intro y
    have h := hp y
    rw [inner_sub_right] at h ⊢
    linarith [heq, hxeq]
  exact (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
    (n7_support_min hp') (n7_support_min hp)
    ((subset_univ (closedBall (0 : E) M)) hx') (mem_univ x)

private lemma n7_subgradient_eq_maximizer {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hu : Continuous u) (hstrict : StrictConvexOn ℝ univ u)
    {M : ℝ} (hM : 0 ≤ M) {p x g : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x)
    (hg : ∀ q, truncatedConjugate u M p + ⟪g, q - p⟫ ≤ truncatedConjugate u M q) :
    g = x := by
  classical
  by_contra hne
  let v := g - x
  have hv : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  have hgap : ⟪v, x⟫ < ⟪v, g⟫ := by
    have hh : ⟪v, v⟫ = ⟪v, g⟫ - ⟪v, x⟫ := by
      dsimp [v]
      rw [inner_sub_right]
    linarith
  let c : ℝ := (⟪v, x⟫ + ⟪v, g⟫) / 2
  have hxc : ⟪v, x⟫ < c := by dsimp [c]; linarith
  have hcg : c < ⟪v, g⟫ := by dsimp [c]; linarith
  let C : Set E := {z | c ≤ ⟪v, z⟫}
  let A : Set E := {q | ∃ z ∈ closedBall (0 : E) M,
    z ∈ C ∧ truncatedConjugate u M q = ⟪q, z⟫ - u z}
  have hA : IsClosed A :=
    n7_isClosed_bad_maximizers hu hM
      (isClosed_le continuous_const (continuous_const.inner continuous_id))
  have hpA : p ∈ Aᶜ := by
    rintro ⟨z, hz, hc, hzmax⟩
    have hzx := eq_of_truncatedConjugate_eq_of_subgradient hstrict hx hp hz hzmax
    subst z
    exact (not_le_of_gt hxc) hc
  have hpath : Continuous (fun t : ℝ => p + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun t : ℝ => p + t • v) ⁻¹' Aᶜ ∈ 𝓝 (0 : ℝ) :=
    hpath.continuousAt.preimage_mem_nhds
      (hA.isOpen_compl.mem_nhds (by simpa only [zero_smul, add_zero] using hpA))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := ε / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htε : t < ε := by dsimp [t]; linarith
  have hqA : p + t • v ∈ Aᶜ := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htε
  obtain ⟨z, hz, hzmax⟩ := (exists_truncatedConjugate_eq hu hM (p + t • v)).1
  have hzc : ⟪v, z⟫ < c := by
    by_contra hn
    exact hqA ⟨z, hz, le_of_not_gt hn, hzmax⟩
  have hbase := (exists_truncatedConjugate_eq hu hM p).2 z hz
  have hsub := hg (p + t • v)
  rw [hzmax, add_sub_cancel_left, inner_smul_right] at hsub
  rw [inner_add_left, real_inner_smul_left] at hsub
  have hgv : ⟪g, v⟫ = ⟪v, g⟫ := real_inner_comm v g
  have hle : t * ⟪v, g⟫ ≤ t * ⟪v, z⟫ := by
    rw [heq] at hbase hsub
    rw [hgv] at hsub
    linarith
  have hgz : ⟪v, g⟫ ≤ ⟪v, z⟫ := (mul_le_mul_iff_right₀ ht).mp hle
  linarith

/-- **Danskin identification of subgradient images** (weak Letwin route, N7, task T11f3; KLS500
`convexSubgradientImage_truncatedLegendrePotential_eq_relative`): for strictly convex continuous `u`, on a set
`S` of slopes whose ball maximisers lie in the open ball, the subgradient image of the truncated conjugate is the
inverse subgradient image `{x | ∃ p ∈ S, p ∈ ∂u(x)}`. -/
theorem subgradientImage_truncatedConjugate_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hu : Continuous u)
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M) {S : Set E}
    (hS : ∀ p ∈ S, ∀ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M) :
    subgradientImage (truncatedConjugate u M) S = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
  ext g
  constructor
  · rintro ⟨p, hpS, hg⟩
    obtain ⟨x, hxB, heq⟩ := (exists_truncatedConjugate_eq hu hM p).1
    have hx := hS p hpS x hxB heq
    have hp := n7_support_of_interior_max hu hstrict.convexOn hM hx heq
    have hgx := n7_subgradient_eq_maximizer hu hstrict hM hx hp heq hg
    subst g
    exact ⟨p, hpS, hp⟩
  · rintro ⟨p, hpS, hp⟩
    obtain ⟨x, hxB, heq⟩ := (exists_truncatedConjugate_eq hu hM p).1
    have hx := hS p hpS x hxB heq
    have hpx := n7_support_of_interior_max hu hstrict.convexOn hM hx heq
    have hxg : x = g := n7_support_unique hstrict hpx hp
    subst g
    refine ⟨p, hpS, ?_⟩
    intro q
    have hq := (exists_truncatedConjugate_eq hu hM q).2 x hxB
    rw [heq, inner_sub_right]
    have hcomm : ⟪x, q⟫ = ⟪q, x⟫ := real_inner_comm q x
    have hcomm' : ⟪x, p⟫ = ⟪p, x⟫ := real_inner_comm p x
    rw [hcomm, hcomm']
    linarith

end FunctionalInequalities.Analysis

end LT11F3TruncatedConjugateSubgradients

section LT11F5SublevelContactLemma

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

/-! The contact lemma on sublevel sets (task L-T11f5). -/

namespace FunctionalInequalities.Analysis

private lemma supporting_affine_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c : ℝ) (p x : E) :
    ConvexOn ℝ univ (fun w => c + ⟪p, w - x⟫) := by
  refine (((innerSL ℝ p).toLinearMap.convexOn
    (convex_univ : Convex ℝ (univ : Set E))).add_const (c - ⟪p, x⟫)).congr ?_
  intro w _
  change ⟪p, w⟫ + (c - ⟪p, x⟫) = c + ⟪p, w - x⟫
  rw [inner_sub_right]
  ring

private lemma subgradient_of_local_agreement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {u v : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {U : Set E} (hU : IsOpen U) {x q : E} (hx : x ∈ U)
    (heq : ∀ ⦃w⦄, w ∈ U → v w = u w)
    (hq : ∀ w, v x + ⟪q, w - x⟫ ≤ v w) :
    ∀ w, u x + ⟪q, w - x⟫ ≤ u w := by
  have hloc : IsLocalMin (fun w => u w - ⟪q, w⟫) x := by
    filter_upwards [hU.eventually_mem hx] with w hw
    change u x - ⟪q, x⟫ ≤ u w - ⟪q, w⟫
    have hh := hq w
    rw [heq hx, heq hw, inner_sub_right] at hh
    linarith
  have hg := IsMinOn.of_isLocalMin_of_convex_univ hloc
    (hconv.sub ((innerSL ℝ q).toLinearMap.concaveOn convex_univ))
  intro w
  have hh := hg w
  change u x - ⟪q, x⟫ ≤ u w - ⟪q, w⟫ at hh
  rw [inner_sub_right]
  linarith

private lemma subgradientImage_of_local_agreement {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (huv : ∀ x, u x ≤ v x)
    {U : Set E} (hU : IsOpen U) (heq : ∀ ⦃x⦄, x ∈ U → v x = u x)
    {G : Set E} (hGU : G ⊆ U) :
    subgradientImage v G = subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, hx, subgradient_of_local_agreement hconv hU (hGU hx) heq hq⟩
  · rintro ⟨x, hx, hq⟩
    refine ⟨x, hx, ?_⟩
    intro w
    rw [heq (hGU hx)]
    exact (hq w).trans (huv w)

private lemma eq_of_two_contacts_below {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ x, u x₀ + ⟪p, x - x₀⟫ ≤ u x) {R : ℝ}
    (hK : IsCompact {x | u x ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {x | u x < R} →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (subgradientImage u G) ∧
        (volume : Measure E) (subgradientImage u G) ≤
          ENNReal.ofReal b * (volume : Measure E) G)
    (hxR : u x₀ < R) {y : E} (hyR : u y < R)
    (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by
  classical
  by_contra hne
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨r, hr, hrR⟩ := exists_between (max_lt hxR hyR)
  have hx_r : u x₀ < r := (le_max_left _ _).trans_lt hr
  have hy_r : u y < r := (le_max_right _ _).trans_lt hr
  have hKr : IsCompact {x | u x ≤ r} :=
    hK.of_isClosed_subset (isClosed_le hu continuous_const)
      (fun _ hx => hx.trans hrR.le)
  obtain ⟨z, θ₀, hz, hzr, hexp₀⟩ :=
    exists_exposed_contact_of_lt hconv hp hx_r hKr
  have hθ₀ : θ₀ ≠ 0 := by
    intro hzero
    by_cases hxz : x₀ = z
    · have hyz : y ≠ z := by
        intro hyz
        exact hne (hyz.trans hxz.symm)
      have hh := hexp₀ y hy hy_r.le hyz
      simp [hzero] at hh
    · have hxcontact : u x₀ = u x₀ + ⟪p, x₀ - x₀⟫ := by simp
      have hh := hexp₀ x₀ hxcontact hx_r.le hxz
      simp [hzero] at hh
  have hn : 0 < ‖θ₀‖ := norm_pos_iff.mpr hθ₀
  let θ : E := ‖θ₀‖⁻¹ • θ₀
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ (ne_of_gt hn)]
  let ℓ : E → ℝ := fun x => u x₀ + ⟪p, x - x₀⟫
  have hℓ : ConvexOn ℝ univ ℓ := supporting_affine_convex (u x₀) p x₀
  have hℓcont : Continuous ℓ := by
    exact continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const))
  have hℓ0 : ℓ x₀ = u x₀ := by simp [ℓ]
  have hℓu (x : E) : ℓ x ≤ u x := hp x
  let v : E → ℝ := fun x => max (u x) (ℓ x + 2 * (ℓ x - r))
  have hvconv : ConvexOn ℝ univ v := by
    exact hconv.sup
      (hℓ.add (ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 2)
        (hℓ.sub (concaveOn_const r convex_univ))))
  have hvcont : Continuous v :=
    continuousOn_univ.mp (hvconv.continuousOn isOpen_univ)
  have huv (x : E) : u x ≤ v x := le_max_left _ _
  have hv0 : v x₀ = u x₀ := by
    change max (u x₀) (ℓ x₀ + 2 * (ℓ x₀ - r)) = u x₀
    rw [hℓ0]
    apply max_eq_left
    linarith
  have hvp : ∀ x, v x₀ + ⟪p, x - x₀⟫ ≤ v x := by
    intro x
    rw [hv0]
    exact (hp x).trans (huv x)
  have hcontact (x : E) :
      v x = v x₀ + ⟪p, x - x₀⟫ ↔ u x = ℓ x ∧ ℓ x ≤ r := by
    rw [hv0]
    change max (u x) (ℓ x + 2 * (ℓ x - r)) = ℓ x ↔
      u x = ℓ x ∧ ℓ x ≤ r
    constructor
    · intro hx
      have hfirst : u x ≤ ℓ x :=
        (le_max_left (u x) (ℓ x + 2 * (ℓ x - r))).trans_eq hx
      have hsecond : ℓ x + 2 * (ℓ x - r) ≤ ℓ x :=
        (le_max_right (u x) (ℓ x + 2 * (ℓ x - r))).trans_eq hx
      exact ⟨le_antisymm hfirst (hℓu x), by linarith⟩
    · rintro ⟨hx, hxr⟩
      rw [hx]
      apply max_eq_left
      linarith
  let C : Set E := {x | v x = v x₀ + ⟪p, x - x₀⟫}
  have hC : IsCompact C := by
    apply hKr.of_isClosed_subset
    · exact isClosed_eq hvcont
        (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const)))
    · intro x hx
      obtain ⟨hxu, hxr⟩ := (hcontact x).mp hx
      exact hxu.trans_le hxr
  have hzC : z ∈ C := (hcontact z).mpr ⟨hz, hz.symm.trans_le hzr.le⟩
  have hxC : x₀ ∈ C := by
    apply (hcontact x₀).mpr
    exact ⟨hℓ0.symm, hℓ0.trans_le hx_r.le⟩
  have hyC : y ∈ C := (hcontact y).mpr ⟨hy, hy.symm.trans_le hy_r.le⟩
  have hexp : ∀ x ∈ C, x ≠ z → ⟪x - z, θ⟫ < 0 := by
    intro x hx hxz
    obtain ⟨hxu, hxr⟩ := (hcontact x).mp hx
    have hh := hexp₀ x hxu (hxu.trans_le hxr) hxz
    change ⟪x - z, ‖θ₀‖⁻¹ • θ₀⟫ < 0
    rw [inner_smul_right]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hn) hh
  let U : Set E := {x | ℓ x < r} ∩ {x | u x < R}
  have hU : IsOpen U :=
    (isOpen_lt hℓcont continuous_const).inter (isOpen_lt hu continuous_const)
  have hzU : z ∈ U := by
    exact ⟨hz.symm.trans_lt hzr, hzr.trans hrR⟩
  have hvU : ∀ ⦃x⦄, x ∈ U → v x = u x := by
    intro x hx
    change max (u x) (ℓ x + 2 * (ℓ x - r)) = u x
    apply max_eq_left
    have hlt : ℓ x < r := hx.1
    have hle := hℓu x
    linarith
  have hwidth : ∃ h : ℝ, 0 < h ∧ C ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U := by
    let D : Set E := C ∩ Uᶜ
    have hD : IsCompact D := hC.inter_right hU.isClosed_compl
    have hf : Continuous (fun x : E => ⟪x - z, θ⟫) :=
      (continuous_id.sub continuous_const).inner continuous_const
    by_cases hDne : D.Nonempty
    · obtain ⟨d, hd, hmax⟩ := hD.exists_isMaxOn hDne hf.continuousOn
      have hdz : d ≠ z := by
        intro hdZ
        exact hd.2 (hdZ.symm ▸ hzU)
      have hdneg := hexp d hd.1 hdz
      refine ⟨-⟪d - z, θ⟫ / 2, by linarith, ?_⟩
      intro x hx
      by_contra hxU
      have hxd : x ∈ D := ⟨hx.1, hxU⟩
      have hh : ⟪x - z, θ⟫ ≤ ⟪d - z, θ⟫ := hmax hxd
      have hcap := hx.2
      change -(-⟪d - z, θ⟫ / 2) ≤ ⟪x - z, θ⟫ at hcap
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      by_contra hxU
      exact hDne ⟨x, hx.1, hxU⟩
  obtain ⟨h, hh, hCU⟩ := hwidth
  have hvB : ∀ Q : Set E, IsCompact Q → Q ⊆ U →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (subgradientImage v G) ∧
        (volume : Measure E) (subgradientImage v G) ≤
          ENNReal.ofReal b * (volume : Measure E) G := by
    intro Q hQ hQU
    obtain ⟨a, b, ha, hab⟩ := hB Q hQ (fun x hx => (hQU hx).2)
    refine ⟨a, b, ha, ?_⟩
    intro G hG hGQ
    have hGU : G ⊆ U := fun _ hx => hQU (hGQ (subset_closure hx))
    rw [subgradientImage_of_local_agreement hconv huv hU hvU hGU]
    exact hab G hG hGQ
  have hsingle : C = {z} :=
    contactSet_eq_singleton_of_exposed_of_local_bounds hvconv hvp hC hzC
      hθ hexp hh hU hCU hvB
  have hxz : x₀ = z := mem_singleton_iff.mp (hsingle ▸ hxC)
  have hyz : y = z := mem_singleton_iff.mp (hsingle ▸ hyC)
  exact hne (hyz.trans hxz.symm)

/-- **Caffarelli's contact-set lemma below a level** (weak Letwin route, N6, task T11f5; KLS500
`supportContactSet_subsingleton_of_local_subgradient_bounds`): if `{u ≤ R}` is compact and the convex `u` has
two-sided Alexandrov bounds on compact subsets of `{u < R}`, then a supporting affine function at `x₀`
(`u x₀ < R`) touches the graph of `u` at no other point of `{u < R}`. No compactness of the full contact set
is assumed. -/
theorem eq_of_contact_of_sublevel_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) {R : ℝ} (hK : IsCompact {y | u y ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {y | u y < R} → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E,
      IsOpen G → closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
      (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G)
    {y : E} (hyR : u y < R) (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by
  classical
  by_contra hne
  have hpy : ∀ w, u y + ⟪p, w - y⟫ ≤ u w := by
    intro w
    have hh := hp w
    have hy' := hy
    simp only [inner_sub_right] at hh hy' ⊢
    linarith
  have hxcontact : u x₀ = u y + ⟪p, x₀ - y⟫ := by
    have hy' := hy
    simp only [inner_sub_right] at hy' ⊢
    linarith
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let f : ℝ → E := AffineMap.lineMap y x₀
  have hf : Continuous f := AffineMap.lineMap_continuous
  have hf0 : f 0 = y := AffineMap.lineMap_apply_zero y x₀
  have htend : Tendsto (fun t => u (f t)) (𝓝 0) (𝓝 (u y)) := by
    have hh : Tendsto (fun t => u (f t)) (𝓝 0) (𝓝 (u (f 0))) :=
      (hu.comp hf).tendsto 0
    rw [hf0] at hh
    exact hh
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), u (f t) < R :=
    htend.eventually (eventually_lt_nhds hyR)
  obtain ⟨t, ht, htR, ht1⟩ :=
    (hnear.and (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one))).exists_gt
  have htcontact : u (f t) = u y + ⟪p, f t - y⟫ := by
    have hh := hconv.2 (mem_univ y) (mem_univ x₀)
      (sub_nonneg.mpr ht1.le) ht.le (by ring : 1 - t + t = 1)
    have hl := hpy (f t)
    have hx' := hxcontact
    have hft : f t = (1 - t) • y + t • x₀ :=
      AffineMap.lineMap_apply_module y x₀ t
    rw [hft] at hl ⊢
    simp only [smul_eq_mul] at hh
    simp only [inner_sub_right, inner_add_right, inner_smul_right] at hl hx' ⊢
    nlinarith
  have he : f t = y :=
    eq_of_two_contacts_below hconv hpy hK hB hyR htR htcontact
  have htzero : t = 0 :=
    (AffineMap.lineMap_injective ℝ hne) (he.trans hf0.symm)
  exact (ne_of_gt ht) htzero

end FunctionalInequalities.Analysis

end LT11F5SublevelContactLemma

section LT11F6MomentStrictConvexity

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-! **Caffarelli's strict convexity** for moment-map potentials: a convex potential whose gradient pushes a measure with bounded density forward to one with density bounded above and below on a convex body is strictly convex (task L-T11f6). -/

namespace FunctionalInequalities.Analysis

/-- **The moment potential is strictly convex** (weak Letwin route, N6, task T11f6; KLS500
`moment_strictConvexOn`): a convex Lipschitz `u` with `∫ e^{-u} = 1` whose gradient pushes `e^{-u} dx` forward
to `1_K e^{-V} dx` (`K` compact convex nonempty, `V` continuous) is strictly convex. -/
theorem strictConvexOn_of_map_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    StrictConvexOn ℝ univ u := by
  classical
  let ρ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x))
  let f : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))
  have hρ : Measurable ρ := hu.continuous.measurable.neg.exp.ennreal_ofReal
  have hf : Measurable f :=
    hV.measurable.neg.exp.ennreal_ofReal.indicator hK.measurableSet
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have htilt : (volume : Measure E).tilted (-u) = volume.withDensity ρ := by
    change (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (-u x) / ∫ y, Real.exp (-u y) ∂(volume : Measure E))) =
      volume.withDensity ρ
    simp only [hnorm, div_one, ρ]
  have hmap' :
      ((volume : Measure E).withDensity ρ).map (gradient u) =
        volume.withDensity f := by
    rw [← htilt]
    exact hmap
  have hμK : ∀ᵐ p ∂(volume : Measure E).withDensity f, p ∈ K := by
    apply (ae_withDensity_iff hf).2
    exact Filter.Eventually.of_forall fun p hp => by
      by_contra h
      exact hp (Set.indicator_of_notMem h _)
  have hνK :
      ∀ᵐ x ∂(volume : Measure E).withDensity ρ, gradient u x ∈ K := by
    apply ae_of_ae_map hgrad.aemeasurable
    rw [hmap']
    exact hμK
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K := by
    have h := (ae_withDensity_iff hρ).1 hνK
    filter_upwards [h] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-u x))))
  have hint : Integrable (fun x => Real.exp (-u x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  have hsub : ∀ R : ℝ, IsCompact {x | u x ≤ R} :=
    (exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      volume hconv hint).2
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hV.continuousOn
  obtain ⟨q, hq⟩ := hKne
  have hDnonneg : 0 ≤ D := (norm_nonneg (V q)).trans (hD q hq)
  apply strictConvexOn_of_contact_eq hconv
  intro x p hp y hy
  let R : ℝ := max (u x) (u y) + 1
  have hyR : u y < R := by
    dsimp only [R]
    linarith [le_max_right (u x) (u y)]
  refine eq_of_contact_of_sublevel_bounds hconv hp (hsub R) ?_ hyR hy
  intro Q hQ _
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hu.continuous.continuousOn
  refine ⟨Real.exp (-C - D), Real.exp (C + D), Real.exp_pos _, ?_⟩
  intro G hG hGQ
  have hbounds :
      ∀ᵐ z ∂(volume : Measure E).restrict G,
        ENNReal.ofReal (Real.exp (-C - D)) ≤
            ENNReal.ofReal (Real.exp (-u z + V (gradient u z))) ∧
          ENNReal.ofReal (Real.exp (-u z + V (gradient u z))) ≤
            ENNReal.ofReal (Real.exp (C + D)) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hG.measurableSet]
      with z hzK hzG
    have hzQ : z ∈ Q := hGQ (subset_closure hzG)
    have huz : -C ≤ u z ∧ u z ≤ C := by
      apply abs_le.mp
      simpa only [Real.norm_eq_abs] using hC z hzQ
    have hvz : -D ≤ V (gradient u z) ∧ V (gradient u z) ≤ D := by
      apply abs_le.mp
      simpa only [Real.norm_eq_abs] using hD (gradient u z) hzK
    constructor
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith [huz.2, hvz.1]
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      linarith [huz.1, hvz.2, hDnonneg]
  rw [volume_subgradientImage_eq_lintegral_of_isOpen
    hu hconv hnorm hK.isClosed hKc hV.measurable hmap hG]
  constructor
  · calc
      ENNReal.ofReal (Real.exp (-C - D)) * (volume : Measure E) G =
          ∫⁻ z in G, ENNReal.ofReal (Real.exp (-C - D)) ∂(volume : Measure E) :=
        (setLIntegral_const G _).symm
      _ ≤ ∫⁻ z in G, ENNReal.ofReal (Real.exp (-u z + V (gradient u z)))
          ∂(volume : Measure E) :=
        lintegral_mono_ae (hbounds.mono fun _ hz => hz.1)
  · calc
      (∫⁻ z in G, ENNReal.ofReal (Real.exp (-u z + V (gradient u z)))
          ∂(volume : Measure E)) ≤
          ∫⁻ z in G, ENNReal.ofReal (Real.exp (C + D)) ∂(volume : Measure E) :=
        lintegral_mono_ae (hbounds.mono fun _ hz => hz.2)
      _ = ENNReal.ofReal (Real.exp (C + D)) * (volume : Measure E) G :=
        setLIntegral_const G _

end FunctionalInequalities.Analysis

end LT11F6MomentStrictConvexity
