import FunctionalInequalities.Analysis.Convex.Alexandrov

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
