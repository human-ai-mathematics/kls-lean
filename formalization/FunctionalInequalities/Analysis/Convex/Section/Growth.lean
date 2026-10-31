module

public import FunctionalInequalities.Analysis.Convex.Boundary
public import FunctionalInequalities.Analysis.Convex.Section.Affine
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Transport
public import FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import FunctionalInequalities.Analysis.Convex.Alexandrov.MaximumPrinciple
public import FunctionalInequalities.Analysis.Convex.Normalization
public import FunctionalInequalities.Analysis.BakryEmery.Calculus

/-!
# Quantitative supports for Caffarelli's interior `C^{1,α}` (Berman–Berndtsson Theorem 2.24(i))

Supporting results for Letwin arXiv:2607.24164v1, Lemma 2.2 in the literal convex source class,
whose
interior regularity is Berman–Berndtsson arXiv:1207.6128v1, Theorem 2.24(i) (Caffarelli: a strictly
convex Alexandrov
solution of `λ ≤ det D²u ≤ Λ` is `C^{1,α}_loc`). Three reusable quantitative pieces, none of which
assumes a Hessian,
a Hölder modulus, `C²` or the target estimate:

* `norm_gradient_sub_le_of_growth`, `exists_holder_gradient_of_growth`: a differentiable convex
  function whose
  one-sided growth above its tangent planes is `≤ C ‖z − x‖^{1+α}` on balls has an `α`-Hölder
  gradient, locally with
  the explicit constant `2^{1+α} C` and on every compact set with a finite constant. This is the
  final step of
  Caffarelli's `C^{1,α}` proof; it converts section geometry into gradient regularity.
* `growth_of_closedBall_subset_section`: if every section `S_h(x) = {u ≤ ℓ_x + h}`, `0 < h ≤ h₀`,
  contains the ball
  of radius `c h^θ`, the tangent-plane growth at `x` is `≤ (‖z − x‖/c)^{1/θ}`; with `θ = 1/(1+α)`
  this is exactly the
  hypothesis of the previous item. It states the interface that Caffarelli's section iteration must
  deliver.
* `exists_section_alexandrov_estimate` (and its density-bound forms): the Alexandrov estimate for
  sections,
  `c h^n ≤ |∂u(S_h(x))| · diam(S_h(x))^{n−1} · dist(x, ∂S_h(x))`, from the library's Alexandrov
  maximum principle and
  the translation invariance of subgradient images; with the two-sided density bound `|∂u(G)| ≤ b
  |G|` it reads
  `c h^n ≤ b |S_h| diam(S_h)^{n−1} dist(x, ∂S_h)`. This is the quantitative "sections are not thin"
  input of the
  engulfing/decay argument.

The positive lower-density estimate also yields the upper section-volume bound
`|S_h| ≤ C(n) sqrt(h^n/a)`, by affine normalization and quadratic comparison. For a positive
continuous Alexandrov density, each compact Q has a common floor a before the section centre,
slope and height. No section-volume or higher-regularity conclusion is assumed.

Everything is stated for a real inner product space (finite-dimensional where volumes appear); `n =
finrank`.
Compact-uniform small-section localization and two-sided density bounds are also supplied.
The closed literal-source C¹,α and section-power gain is in
`Analysis/Convex/Section/Engulfing.lean`;
this module provides its quantitative prerequisites.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FunctionalInequalities.Analysis

section Growth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
**Gradient Hölder bound from one-sided growth (local form).** If a differentiable convex `u`
satisfies
`u z ≤ u x + ⟪∇u x, z − x⟫ + C ‖z − x‖^{1+α}` for `‖z − x‖ ≤ r₀`, then for `‖y − x‖ ≤ r₀/2`
`‖∇u y − ∇u x‖ ≤ 2^{1+α} C ‖y − x‖^α`. Only convexity at `y` (the supporting plane) and the growth
at `x` are used. -/
theorem norm_gradient_sub_le_of_growth {u : E → ℝ} (hconv : ConvexOn ℝ Set.univ u)
    (hdiff : Differentiable ℝ u) {x : E} {C α r₀ : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hgrowth : ∀ z, ‖z - x‖ ≤ r₀ → u z ≤ u x + ⟪gradient u x, z - x⟫ + C * ‖z - x‖ ^ (1 + α))
    {y : E} (hy : ‖y - x‖ ≤ r₀ / 2) :
    ‖gradient u y - gradient u x‖ ≤ 2 ^ (1 + α) * C * ‖y - x‖ ^ α := by
  set v : E := gradient u y - gradient u x with hvdef
  set r : ℝ := ‖y - x‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  have hRHS : 0 ≤ 2 ^ (1 + α) * C * r ^ α := by positivity
  by_cases hv : v = 0
  · rw [hv, norm_zero]; exact hRHS
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hrpos : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exfalso
      have : y = x := by rwa [hrdef, eq_comm, norm_eq_zero, sub_eq_zero] at h
      exact
        hv
          (by rw [hvdef, this, sub_self])
  -- the test point `z = y + w` with `w = (r/‖v‖) • v`, `‖w‖ = r`

  set w : E := (r / ‖v‖) • v with hwdef
  have hwnorm : ‖w‖ = r := by
    rw [hwdef, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrpos hvpos),
      div_mul_cancel₀ _ hvpos.ne']
  have hzx : ‖y + w - x‖ ≤ 2 * r := by
    calc
      ‖y + w - x‖ = ‖(y - x) + w‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖w‖ := norm_add_le _ _
      _ = 2 * r := by rw [← hrdef, hwnorm]; ring
  have hzr₀ : ‖y + w - x‖ ≤ r₀ :=
    hzx.trans
      (by linarith)
  -- supporting plane at `y`, supporting plane at `x`, growth at `x`

  have h1 : ⟪gradient u y, w⟫ ≤ u (y + w) - u y := gradient_le_increment hconv y w (hdiff y)
  have h2 : ⟪gradient u x, y - x⟫ ≤ u y - u x := by
    simpa only [add_sub_cancel] using gradient_le_increment hconv x (y - x) (hdiff x)
  have h3 := hgrowth (y + w) hzr₀
  have hsplit : ⟪gradient u x, y + w - x⟫ = ⟪gradient u x, y - x⟫ + ⟪gradient u x, w⟫ := by
    rw [show y + w - x = (y - x) + w by abel, inner_add_right]
  have hpow : ‖y + w - x‖ ^ (1 + α) ≤ (2 * r) ^ (1 + α) :=
    Real.rpow_le_rpow (norm_nonneg _) hzx (by linarith)
  have hkey : ⟪v, w⟫ ≤ C * (2 * r) ^ (1 + α) := by
    have : ⟪v, w⟫ = ⟪gradient u y, w⟫ - ⟪gradient u x, w⟫ := by rw [hvdef, inner_sub_left]
    rw [this]
    have hC' : C * ‖y + w - x‖ ^ (1 + α) ≤ C * (2 * r) ^ (1 + α) :=
      mul_le_mul_of_nonneg_left hpow hC
    linarith
  have hvw : ⟪v, w⟫ = r * ‖v‖ := by
    rw [hwdef, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h2r : (2 * r) ^ (1 + α) = 2 ^ (1 + α) * (r * r ^ α) := by
    rw [Real.mul_rpow (by norm_num) hr0, Real.rpow_add hrpos, Real.rpow_one]
  rw [hvw,
    h2r] at hkey
  -- divide by `r > 0`

  have : r * ‖v‖ ≤ r * (2 ^ (1 + α) * C * r ^ α) := by
    calc
      r * ‖v‖ ≤ C * (2 ^ (1 + α) * (r * r ^ α)) := hkey
      _ = r * (2 ^ (1 + α) * C * r ^ α) := by ring
  exact le_of_mul_le_mul_left this hrpos

/--
**Gradient Hölder bound on a compact set from one-sided growth.** For a `C¹` convex `u` with the
growth bound
at every point of a compact `K` (constants `C, α, r₀` fixed before the points), the gradient is
`α`-Hölder on `K`
with a finite constant. The far pairs use only the boundedness of the continuous gradient on `K`. -/
theorem exists_holder_gradient_of_growth {u : E → ℝ} (hconv : ConvexOn ℝ Set.univ u)
    (hC1 : ContDiff ℝ 1 u) {K : Set E} (hK : IsCompact K) {C α r₀ : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hr₀ : 0 < r₀)
    (hgrowth :
      ∀ x ∈ K, ∀ z, ‖z - x‖ ≤ r₀ → u z ≤ u x + ⟪gradient u x, z - x⟫ + C * ‖z - x‖ ^ (1 + α)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x ∈ K, ∀ y ∈ K, ‖gradient u y - gradient u x‖ ≤ C' * ‖y - x‖ ^ α := by
  have hdiff : Differentiable ℝ u := hC1.differentiable one_ne_zero
  obtain ⟨M, hM⟩ :=
    hK.exists_bound_of_continuousOn
      (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient hC1).continuousOn
  set Mp : ℝ := max M 0 with hMp
  have hMp0 : 0 ≤ Mp := le_max_right _ _
  have hMb : ∀ x ∈ K, ‖gradient u x‖ ≤ Mp := fun x hx => (hM x hx).trans (le_max_left _ _)
  refine ⟨2 ^ (1 + α) * C + 2 * Mp * (2 / r₀) ^ α, by positivity, fun x hx y hy => ?_⟩
  have hr0 : 0 ≤ ‖y - x‖ := norm_nonneg _
  have hpow0 : 0 ≤ ‖y - x‖ ^ α := Real.rpow_nonneg hr0 _
  by_cases hnear : ‖y - x‖ ≤ r₀ / 2
  · have h := norm_gradient_sub_le_of_growth hconv hdiff hC hα (hgrowth x hx) hnear
    calc
      ‖gradient u y - gradient u x‖ ≤ 2 ^ (1 + α) * C * ‖y - x‖ ^ α := h
      _ ≤ (2 ^ (1 + α) * C + 2 * Mp * (2 / r₀) ^ α) * ‖y - x‖ ^ α := by
        apply mul_le_mul_of_nonneg_right _ hpow0
        have : 0 ≤ 2 * Mp * (2 / r₀) ^ α := by positivity
        linarith
  · have hfar : r₀ / 2 < ‖y - x‖ :=
      not_le.mp
        hnear
    -- `(2/r₀)^α ‖y−x‖^α = (2‖y−x‖/r₀)^α ≥ 1`

    have hone : 1 ≤ (2 / r₀) ^ α * ‖y - x‖ ^ α := by
      rw [← Real.mul_rpow (by positivity) hr0]
      apply Real.one_le_rpow _ hα
      rw [div_mul_eq_mul_div, le_div_iff₀ hr₀]
      linarith
    have hbound : ‖gradient u y - gradient u x‖ ≤ 2 * Mp := by
      calc
        ‖gradient u y - gradient u x‖ ≤ ‖gradient u y‖ + ‖gradient u x‖ := norm_sub_le _ _
        _ ≤ Mp + Mp := add_le_add (hMb y hy) (hMb x hx)
        _ = 2 * Mp := by ring
    calc
      ‖gradient u y - gradient u x‖ ≤ 2 * Mp := hbound
      _ = 2 * Mp * 1 := (mul_one _).symm
      _ ≤ 2 * Mp * ((2 / r₀) ^ α * ‖y - x‖ ^ α) := by gcongr
      _ = 2 * Mp * (2 / r₀) ^ α * ‖y - x‖ ^ α := by ring
      _ ≤ (2 ^ (1 + α) * C + 2 * Mp * (2 / r₀) ^ α) * ‖y - x‖ ^ α := by
        apply mul_le_mul_of_nonneg_right _ hpow0
        have : 0 ≤ 2 ^ (1 + α) * C := by positivity
        linarith

/--
**Sections containing balls give tangent-plane growth.** If for every `0 < h ≤ h₀` the closed ball
of radius
`c h^θ` about `x` lies in the section `{z | u z ≤ u x + ⟪∇u x, z − x⟫ + h}`, then for `‖z − x‖ ≤ c
h₀^θ`
`u z ≤ u x + ⟪∇u x, z − x⟫ + (‖z − x‖/c)^{θ⁻¹}`. With `θ = (1+α)⁻¹` this is the growth hypothesis of
`norm_gradient_sub_le_of_growth` with `C = c^{−(1+α)}`. -/
theorem growth_of_closedBall_subset_section {u : E → ℝ} {x : E} {c θ h₀ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hh₀ : 0 < h₀)
    (hsec :
      ∀ h : ℝ,
        0 < h →
          h ≤ h₀ → closedBall x (c * h ^ θ) ⊆ {z | u z ≤ u x + ⟪gradient u x, z - x⟫ + h}) :
    ∀ z, ‖z - x‖ ≤ c * h₀ ^ θ → u z ≤ u x + ⟪gradient u x, z - x⟫ + (‖z - x‖ / c) ^ θ⁻¹ := by
  intro z hz
  set r : ℝ := ‖z - x‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  rcases hr0.lt_or_eq with hrpos | hrzero
  · set h : ℝ := (r / c) ^ θ⁻¹ with hhdef
    have hhpos : 0 < h := Real.rpow_pos_of_pos (div_pos hrpos hc) _
    have hhle : h ≤ h₀ := by
      have h1 : r / c ≤ h₀ ^ θ := by rwa [div_le_iff₀ hc, mul_comm]
      calc
        h = (r / c) ^ θ⁻¹ := rfl
        _ ≤ (h₀ ^ θ) ^ θ⁻¹ := Real.rpow_le_rpow (div_nonneg hr0 hc.le) h1 (inv_nonneg.mpr hθ.le)
        _ = h₀ := Real.rpow_rpow_inv hh₀.le hθ.ne'
    have hradius : c * h ^ θ = r := by
      rw [hhdef, Real.rpow_inv_rpow (div_nonneg hr0 hc.le) hθ.ne', mul_div_cancel₀ _ hc.ne']
    have hzmem : z ∈ closedBall x (c * h ^ θ) := by rw [mem_closedBall, dist_eq_norm, hradius]
    exact hsec h hhpos hhle hzmem
  · have hzx : z = x := by rwa [hrdef, eq_comm, norm_eq_zero, sub_eq_zero] at hrzero
    have hθinv : θ⁻¹ ≠ 0 := inv_ne_zero hθ.ne'
    rw [← hrzero, zero_div, Real.zero_rpow hθinv, hzx, sub_self, inner_zero_right, add_zero,
      add_zero]

end Growth

section SectionAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end SectionAlgebra

section SectionEstimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/--
**Alexandrov estimate for sections.** There is `c = c(E) > 0` such that for every convex continuous
`u`,
every affine slope `p` through `x`, every `h > 0` with a bounded section `S = {u < ℓ_x + h}`,
`c h^n ≤ |∂u(S)| · diam(S)^{n−1} · dist(x, ∂S)` (`n = finrank`). The section is the domain of the
library's
Alexandrov maximum principle applied to `u − ℓ_x − h`; the subgradient image is translation
invariant. -/
theorem exists_section_alexandrov_estimate :
    ∃ c : ℝ,
      0 < c ∧
        ∀ (u : E → ℝ),
          ConvexOn ℝ Set.univ u →
            Continuous u →
              ∀ (x p : E) (h : ℝ),
                0 < h →
                  Bornology.IsBounded {y | u y < u x + ⟪p, y - x⟫ + h} →
                    ENNReal.ofReal (c * h ^ Module.finrank ℝ E) ≤
                      (volume : Measure E)
                          (subgradientImage u {y | u y < u x + ⟪p, y - x⟫ + h}) *
                        ENNReal.ofReal
                          (diam {y | u y < u x + ⟪p, y - x⟫ + h} ^ (Module.finrank ℝ E - 1) *
                            infDist x (frontier {y | u y < u x + ⟪p, y - x⟫ + h})) := by
  obtain ⟨c, hc, hmax⟩ := exists_pos_alexandrov_maximum_principle (E := E)
  refine ⟨c, hc, fun u hconv hcont x p h hh hbdd => ?_⟩
  set S : Set E := {y | u y < u x + ⟪p, y - x⟫ + h} with hSdef
  set v : E → ℝ := fun y => u y - (⟪p, y⟫ + (u x - ⟪p, x⟫ + h)) with hvdef
  have hSv : S = {y | v y < 0} := section_eq_sublevel u x p h
  have hvconv : ConvexOn ℝ Set.univ v := convexOn_sub_inner_add_const hconv p _
  have hSo : IsOpen S := by
    apply isOpen_lt hcont
    fun_prop
  have hSc : Convex ℝ S := by
    rw [hSv]
    simpa only [Set.mem_univ, true_and] using hvconv.convex_lt 0
  have hfr : ∀ y ∈ frontier S, 0 ≤ v y := by
    intro y hy
    rw [hSo.frontier_eq] at hy
    have hyS : y ∉ S := hy.2
    rw [hSv] at hyS
    change ¬(v y < 0) at hyS
    exact not_lt.mp hyS
  have hvx : v x = -h := by simp only [hvdef]; ring
  have hxS : x ∈ S := by
    rw [hSv]
    change v x < 0
    rw [hvx]
    linarith
  have hmain := hmax v hvconv S hSo hSc hbdd hfr x hxS (by rw [hvx]; linarith)
  rw [hvx, neg_neg] at hmain
  have hvol :
    (volume : Measure E) (subgradientImage v S) = (volume : Measure E) (subgradientImage u S) :=
    volume_subgradientImage_sub_inner_add_const u p (u x - ⟪p, x⟫ + h) S
  rw [hvol] at hmain
  exact hmain

/-- The section estimate with a density upper bound `|∂u(S)| ≤ b |S|` on the section:
`c h^n ≤ b |S| diam(S)^{n−1} dist(x, ∂S)`, in `ℝ≥0∞`. -/
theorem exists_section_alexandrov_estimate_of_density_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : E → ℝ), ConvexOn ℝ Set.univ u → Continuous u →
      ∀ (x p : E) (h : ℝ), 0 < h →
      Bornology.IsBounded {y | u y < u x + ⟪p, y - x⟫ + h} →
      ∀ b : ℝ, (volume : Measure E) (subgradientImage u {y | u y < u x + ⟪p, y - x⟫ + h}) ≤
        ENNReal.ofReal b * (volume : Measure E) {y | u y < u x + ⟪p, y - x⟫ + h} →
      ENNReal.ofReal (c * h ^ Module.finrank ℝ E) ≤
        ENNReal.ofReal b * (volume : Measure E) {y | u y < u x + ⟪p, y - x⟫ + h} *
          ENNReal.ofReal (diam {y | u y < u x + ⟪p, y - x⟫ + h} ^ (Module.finrank ℝ E - 1) *
            infDist x (frontier {y | u y < u x + ⟪p, y - x⟫ + h})) := by
  obtain ⟨c, hc, hest⟩ := exists_section_alexandrov_estimate (E := E)
  refine ⟨c, hc, fun u hconv hcont x p h hh hbdd b hb => ?_⟩
  refine (hest u hconv hcont x p h hh hbdd).trans ?_
  gcongr

/-- The real form of the previous estimate: `c h^n ≤ b · vol(S) · diam(S)^{n−1} · dist(x, ∂S)`. -/
theorem exists_section_alexandrov_estimate_real :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : E → ℝ), ConvexOn ℝ Set.univ u → Continuous u →
      ∀ (x p : E) (h : ℝ), 0 < h →
      Bornology.IsBounded {y | u y < u x + ⟪p, y - x⟫ + h} →
      ∀ b : ℝ, 0 ≤ b → (volume : Measure E) (subgradientImage u {y | u y < u x + ⟪p, y - x⟫ + h}) ≤
        ENNReal.ofReal b * (volume : Measure E) {y | u y < u x + ⟪p, y - x⟫ + h} →
      c * h ^ Module.finrank ℝ E ≤
        b * ((volume : Measure E) {y | u y < u x + ⟪p, y - x⟫ + h}).toReal *
          (diam {y | u y < u x + ⟪p, y - x⟫ + h} ^ (Module.finrank ℝ E - 1) *
            infDist x (frontier {y | u y < u x + ⟪p, y - x⟫ + h})) := by
  obtain ⟨c, hc, hest⟩ := exists_section_alexandrov_estimate_of_density_bound (E := E)
  refine ⟨c, hc, fun u hconv hcont x p h hh hbdd b hb0 hb => ?_⟩
  have hmain := hest u hconv hcont x p h hh hbdd b hb
  set S : Set E := {y | u y < u x + ⟪p, y - x⟫ + h}
  have hfin : (volume : Measure E) S ≠ ⊤ := hbdd.measure_lt_top.ne
  have hd0 : 0 ≤ diam S ^ (Module.finrank ℝ E - 1) * infDist x (frontier S) :=
    mul_nonneg (pow_nonneg diam_nonneg _) infDist_nonneg
  have hbt : 0 ≤ b * ((volume : Measure E) S).toReal := mul_nonneg hb0 ENNReal.toReal_nonneg
  have hvolS : (volume : Measure E) S = ENNReal.ofReal (((volume : Measure E) S).toReal) :=
    (ENNReal.ofReal_toReal hfin).symm
  rw [hvolS, ← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_mul hbt] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hbt hd0)).mp hmain

/-- A continuous Alexandrov density gives one section estimate constant on each compact Q.
The constant is chosen before the section centre, affine slope and height. This is a
quantitative support for interior section geometry, not the normalized section iteration. -/
theorem exists_section_estimate_of_continuous_density :
    ∃ c : ℝ, 0 < c ∧ ∀ (u f : E → ℝ), ConvexOn ℝ univ u → Continuous u →
      Continuous f →
      (∀ G : Set E, IsOpen G → (volume : Measure E) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x)) →
      ∀ Q : Set E, IsCompact Q → ∃ b : ℝ, 0 < b ∧
        ∀ (x p : E) (h : ℝ), 0 < h →
          {y | u y < u x + ⟪p, y - x⟫ + h} ⊆ Q →
          c * h ^ Module.finrank ℝ E ≤
            b * ((volume : Measure E) {y | u y < u x + ⟪p, y - x⟫ + h}).toReal *
              (diam {y | u y < u x + ⟪p, y - x⟫ + h} ^ (Module.finrank ℝ E - 1) *
                infDist x (frontier {y | u y < u x + ⟪p, y - x⟫ + h})) := by
  obtain ⟨c, hc, hest⟩ := exists_section_alexandrov_estimate_real (E := E)
  refine ⟨c, hc, fun u f hu huc hf hMA Q hQ => ?_⟩
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
  let b : ℝ := max M 1
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨b, hb, fun x p h hh hSQ => ?_⟩
  let S : Set E := {y | u y < u x + ⟪p, y - x⟫ + h}
  have hSo : IsOpen S := by
    apply isOpen_lt huc
    fun_prop
  have hbound : (volume : Measure E) (subgradientImage u S) ≤
      ENNReal.ofReal b * (volume : Measure E) S := by
    rw [hMA S hSo]
    calc
      ∫⁻ y in S, ENNReal.ofReal (f y) ≤ ∫⁻ _y in S, ENNReal.ofReal b := by
        apply setLIntegral_mono' hSo.measurableSet
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        exact (le_abs_self (f y)).trans ((hM y (hSQ hy)).trans (le_max_left _ _))
      _ = ENNReal.ofReal b * (volume : Measure E) S := setLIntegral_const S _
  exact hest u hu huc x p h hh (hQ.isBounded.subset hSQ) b hb.le hbound

end SectionEstimate


section AffineDet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end AffineDet

section Main

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/--
**Upper section-volume bound from a lower density bound.** For every `n > 0` there is `C(n) > 0`
such that for
every convex continuous `u`, supporting slope `p` at `x`, `h > 0` with bounded section `S = {u < ℓ_x
+ h}` and
`a > 0` with `a |G| ≤ |∂u(G)|` for all open `G ⊆ S`: `|S| ≤ C(n) √(h^n / a)`. -/
theorem exists_section_volume_upper_bound (hn : 0 < n) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (u : 𝔼 → ℝ),
          ConvexOn ℝ Set.univ u →
            Continuous u →
              ∀ (x p : 𝔼) (h : ℝ),
                0 < h →
                  (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
                    Bornology.IsBounded {y | u y < u x + ⟪p, y - x⟫ + h} →
                      ∀ a : ℝ,
                        0 < a →
                          (∀ G : Set 𝔼,
                              IsOpen G →
                                G ⊆ {y | u y < u x + ⟪p, y - x⟫ + h} →
                                  ENNReal.ofReal a * (volume : Measure 𝔼) G ≤
                                    (volume : Measure 𝔼) (subgradientImage u G)) →
                            (volume : Measure 𝔼) {y | u y < u x + ⟪p, y - x⟫ + h} ≤
                              ENNReal.ofReal (C * Real.sqrt (h ^ n / a)) := by
  obtain ⟨C₀, hC₀, hnorm⟩ := exists_affine_normalization (E := 𝔼)
  set ω : ℝ := ((volume : Measure 𝔼) (ball (0 : 𝔼) 1)).toReal with hωdef
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : 𝔼) one_pos).ne' measure_ball_lt_top.ne
  refine ⟨Real.sqrt (2 * 2 ^ n) * (2 * C₀) ^ n * ω, by positivity, ?_⟩
  intro u hconv hcont x p h hh hp hbdd a ha
    hA
  -- the section and the shifted function `v = u − ℓ_x − h`

  set S : Set 𝔼 := {y | u y < u x + ⟪p, y - x⟫ + h} with hSdef
  set v : 𝔼 → ℝ := fun y => u y - (⟪p, y⟫ + (u x - ⟪p, x⟫ + h)) with hvdef
  have hSv : S = {y | v y < 0} := section_eq_sublevel u x p h
  have hvcont : Continuous v := by rw [hvdef]; fun_prop
  have hvconv : ConvexOn ℝ Set.univ v := convexOn_sub_inner_add_const hconv p (u x - ⟪p, x⟫ + h)
  have hSo : IsOpen S := by
    apply isOpen_lt hcont
    fun_prop
  have hSc : Convex ℝ S := by
    rw [hSv]
    simpa only [Set.mem_univ, true_and] using hvconv.convex_lt 0
  have hvx : v x = -h := by simp only [hvdef]; ring
  have hxS : x ∈ S := by
    rw [hSv]
    change v x < 0
    rw [hvx]
    linarith
  have hvge : ∀ y, -h ≤ v y := by
    intro y
    have := hp y
    simp only [hvdef]
    rw [inner_sub_right] at this
    linarith
  have hvcl : ∀ y ∈ closure S, v y ≤ 0 := by
    have hsub : closure S ⊆ {y | v y ≤ 0} := by
      apply closure_minimal
      · intro y hy
        rw [hSv] at hy
        change v y < 0 at hy
        exact le_of_lt hy
      · exact isClosed_le hvcont continuous_const
    exact fun y hy =>
      hsub
        hy
  -- normalization of `closure S` and the dilation by `2`

  have hKc : IsCompact (closure S) := hbdd.isCompact_closure
  have hKconv : Convex ℝ (closure S) := hSc.closure
  have hintS : interior S = S := hSo.interior_eq
  have hKint : (interior (closure S)).Nonempty := by
    rw [hSc.interior_closure_eq_interior_of_nonempty_interior ⟨x, by rw [hintS]; exact hxS⟩,
      hintS]
    exact ⟨x, hxS⟩
  obtain ⟨e, he1, he2⟩ := hnorm (closure S) hKc hKconv hKint
  let d : 𝔼 ≃ᵃ[ℝ] 𝔼 := (LinearEquiv.smulOfNeZero ℝ 𝔼 (2 : ℝ) two_ne_zero).toAffineEquiv
  have hd : ∀ y : 𝔼, d y = (2 : ℝ) • y := fun y => rfl
  let f : 𝔼 ≃ᵃ[ℝ] 𝔼 := e.trans d
  have hf : ∀ y : 𝔼, f y = (2 : ℝ) • e y := fun y => by
    rw [show f y = d (e y) from AffineEquiv.trans_apply e d y, hd]
  set D : ℝ := |LinearMap.det (f.linear : 𝔼 →ₗ[ℝ] 𝔼)| with hDdef
  have hD : 0 < D := abs_pos.mpr (LinearEquiv.isUnit_det' f.linear).ne_zero
  have hball : closedBall (0 : 𝔼) 2 ⊆ f '' closure S := by
    intro y hy
    rw [mem_closedBall, dist_zero_right] at hy
    have hy' : (1 / 2 : ℝ) • y ∈ closedBall (0 : 𝔼) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    obtain ⟨z, hz, hez⟩ := he1 hy'
    refine ⟨z, hz, ?_⟩
    rw [hf, hez, smul_smul]
    norm_num
  have hcap : f '' closure S ⊆ closedBall (0 : 𝔼) (2 * C₀) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := he2 ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hz' ⊢
    rw [hf, norm_smul, Real.norm_eq_abs, abs_two]
    linarith
  -- the normalized section `T = f '' S`

  let H : 𝔼 ≃ₜ 𝔼 :=
    { toEquiv := f.toEquiv
      continuous_toFun := f.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := f.symm.toAffineMap.continuous_of_finiteDimensional }
  have hH : ⇑H = ⇑f := rfl
  have hHs : ⇑H.symm = ⇑f.symm := rfl
  have hTo : IsOpen (f '' S) := by
    rw [← hH]
    exact H.isOpenMap S hSo
  have hTcl : closure (f '' S) = f '' closure S := by rw [← hH, H.image_closure]
  have hTc : Convex ℝ (f '' S) := by
    have := hSc.affine_image f.toAffineMap
    simpa only [AffineEquiv.coe_toAffineMap] using this
  have hTsub : f '' S ⊆ closedBall (0 : 𝔼) (2 * C₀) := subset_closure.trans (hTcl ▸ hcap)
  have hTb : Bornology.IsBounded (f '' S) := isBounded_closedBall.subset hTsub
  have hTball : closedBall (0 : 𝔼) 1 ⊆ f '' S := by
    apply closedBall_subset_of_ball_subset_closure (R := 2) hTo hTc ⟨f x, x, hxS, rfl⟩ (by norm_num)
    rw [hTcl]
    exact ball_subset_closedBall.trans hball
  -- the transported function `w = v ∘ f.symm`

  have hwconv : ConvexOn ℝ Set.univ (v ∘ f.symm) := by
    have := hvconv.comp_affineMap f.symm.toAffineMap
    simpa only [Set.preimage_univ, AffineEquiv.coe_toAffineMap] using this
  have hwfr : ∀ y ∈ frontier (f '' S), (v ∘ f.symm) y ≤ 0 := by
    intro y hy
    have hycl : y ∈ closure (f '' S) := frontier_subset_closure hy
    rw [hTcl] at hycl
    obtain ⟨z, hz, rfl⟩ := hycl
    show v (f.symm (f z)) ≤ 0
    rw [f.symm_apply_apply]
    exact hvcl z hz
  have hwA :
    ∀ G : Set 𝔼,
      IsOpen G →
        G ⊆ f '' S →
          ENNReal.ofReal (a * D⁻¹ * D⁻¹) * (volume : Measure 𝔼) G ≤
            (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) G) := by
    intro G hG hGT
    have hG'o : IsOpen (f.symm '' G) := by
      rw [← hHs]
      exact H.symm.isOpenMap G hG
    have hG'S : f.symm '' G ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hzS, rfl⟩ := hGT hy
      rw [f.symm_apply_apply]
      exact hzS
    have hGG' : f '' (f.symm '' G) = G := by
      rw [Set.image_image]
      simp only [AffineEquiv.apply_symm_apply, Set.image_id']
    have hvolG' : (volume : Measure 𝔼) (f.symm '' G) = ENNReal.ofReal D⁻¹ * volume G := by
      rw [volume_image_affineEquiv f.symm G, abs_det_linear_symm]
    have hsub :
      (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) G) =
        ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) (subgradientImage v (f.symm '' G)) := by
      conv_lhs => rw [← hGG']
      exact volume_subgradientImage_comp_affineEquiv_symm v f (f.symm '' G)
    have hvA :
      ENNReal.ofReal a * (volume : Measure 𝔼) (f.symm '' G) ≤
        (volume : Measure 𝔼) (subgradientImage v (f.symm '' G)) := by
      rw [hvdef, volume_subgradientImage_sub_inner_add_const]
      exact hA _ hG'o hG'S
    have hDinv0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hD.le
    calc
      ENNReal.ofReal (a * D⁻¹ * D⁻¹) * (volume : Measure 𝔼) G =
          ENNReal.ofReal D⁻¹ *
            (ENNReal.ofReal a * (ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) G)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha.le]
        ring
      _ = ENNReal.ofReal D⁻¹ * (ENNReal.ofReal a * (volume : Measure 𝔼) (f.symm '' G)) := by
        rw [hvolG']
      _ ≤ ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) (subgradientImage v (f.symm '' G)) := by
        gcongr
      _ = (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) G) :=
        hsub.symm
  -- the normalized minimum estimate and `min v = −h`

  have ha' : 0 < a * D⁻¹ * D⁻¹ := by positivity
  have hmin := le_neg_of_lower_alexandrov_bound hn hwconv hTo hTb hTball hwfr ha' hwA
  have hw0 : -h ≤ (v ∘ f.symm) 0 := hvge (f.symm 0)
  have hkey : (a * D⁻¹ * D⁻¹ / 2) ^ (1 / (n : ℝ)) ≤ 2 * h := by linarith
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hkey2 : a * D⁻¹ * D⁻¹ / 2 ≤ (2 * h) ^ n := by
    have hbase : 0 ≤ a * D⁻¹ * D⁻¹ / 2 := by positivity
    have := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hkey (Nat.cast_nonneg n)
    rw [← Real.rpow_mul hbase, one_div, inv_mul_cancel₀ hn', Real.rpow_one,
      Real.rpow_natCast] at this
    exact this
  have hDinv : D⁻¹ ≤ Real.sqrt (2 * (2 * h) ^ n / a) := by
    rw [Real.le_sqrt (inv_nonneg.mpr hD.le) (by positivity), le_div_iff₀ ha]
    nlinarith [hkey2]
  -- volumes: `|S| = D⁻¹ |f '' S|` and `|f '' S| ≤ |closedBall 0 (2 C₀)|`

  have hvolS : (volume : Measure 𝔼) S = ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) (f '' S) := by
    rw [volume_image_affineEquiv f S, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hD.le),
      inv_mul_cancel₀ hD.ne', ENNReal.ofReal_one, one_mul]
  have hvolT : (volume : Measure 𝔼) (f '' S) ≤ ENNReal.ofReal ((2 * C₀) ^ n * ω) := by
    calc
      (volume : Measure 𝔼) (f '' S) ≤ (volume : Measure 𝔼) (closedBall (0 : 𝔼) (2 * C₀)) :=
        measure_mono hTsub
      _ = ENNReal.ofReal ((2 * C₀) ^ Module.finrank ℝ 𝔼) * (volume : Measure 𝔼) (ball 0 1) :=
        Measure.addHaar_closedBall volume (0 : 𝔼) (by positivity : (0 : ℝ) ≤ 2 * C₀)
      _ = ENNReal.ofReal ((2 * C₀) ^ n * ω) := by
        rw [finrank_euclideanSpace_fin, ← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ←
          ENNReal.ofReal_mul (by positivity), hωdef]
  have hsqrt :
    Real.sqrt (2 * (2 * h) ^ n / a) = Real.sqrt (2 * 2 ^ n) * Real.sqrt (h ^ n / a) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    rw [mul_pow]
    ring
  calc
    (volume : Measure 𝔼) S = ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) (f '' S) := hvolS
    _ ≤ ENNReal.ofReal D⁻¹ * ENNReal.ofReal ((2 * C₀) ^ n * ω) := by gcongr
    _ = ENNReal.ofReal (D⁻¹ * ((2 * C₀) ^ n * ω)) :=
      (ENNReal.ofReal_mul (inv_nonneg.mpr hD.le)).symm
    _ ≤ ENNReal.ofReal (Real.sqrt (2 * (2 * h) ^ n / a) * ((2 * C₀) ^ n * ω)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDinv (by positivity))
    _ = ENNReal.ofReal (Real.sqrt (2 * 2 ^ n) * (2 * C₀) ^ n * ω * Real.sqrt (h ^ n / a)) := by
      rw [hsqrt]
      ring_nf

/-- The open-set lower bound used above follows from the compact-set form
`a |S'| ≤ |∂u(S')|` for compact `S' ⊆ Q` (the library's
`exists_local_subgradientImage_volume_bounds` output) on any
open `G ⊆ Q`, by inner regularity of Lebesgue measure and monotonicity of subgradient images. -/
theorem subgradient_volume_lower_bound_of_compact {u : 𝔼 → ℝ} {Q : Set 𝔼} {a : ℝ}
    (hQ :
      ∀ S' : Set 𝔼,
        IsCompact S' →
          S' ⊆ Q →
            ENNReal.ofReal a * (volume : Measure 𝔼) S' ≤
              (volume : Measure 𝔼) (subgradientImage u S'))
    {G : Set 𝔼} (hG : IsOpen G) (hGQ : G ⊆ Q) :
    ENNReal.ofReal a * (volume : Measure 𝔼) G ≤ (volume : Measure 𝔼) (subgradientImage u G) := by
  rw [hG.measure_eq_iSup_isCompact]
  simp_rw [ENNReal.mul_iSup]
  refine iSup₂_le fun K hKG => iSup_le fun hK => ?_
  have hmono : subgradientImage u K ⊆ subgradientImage u G := by
    rintro q ⟨y, hy, hq⟩
    exact ⟨y, hKG hy, hq⟩
  calc
    ENNReal.ofReal a * (volume : Measure 𝔼) K ≤ (volume : Measure 𝔼) (subgradientImage u K) :=
      hQ K hK (hKG.trans hGQ)
    _ ≤ (volume : Measure 𝔼) (subgradientImage u G) := measure_mono hmono

end Main



/-- Continuous positive Alexandrov density gives a compact-uniform upper section-volume bound.
The dimensional constant precedes u and f; the density floor on Q precedes the centre, slope
and height. This does not prove the normalized section iteration or Holder regularity. -/
theorem exists_section_volume_bound_of_continuous_density {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ),
      ConvexOn ℝ univ u → Continuous u → Continuous f → (∀ x, 0 < f x) →
      (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
        volume (subgradientImage u G) = ∫⁻ x in G, ENNReal.ofReal (f x)) →
      ∀ Q : Set (EuclideanSpace ℝ (Fin n)), IsCompact Q → ∃ a : ℝ, 0 < a ∧ (∀ y ∈ Q, a ≤ f y) ∧
        ∀ (x p : EuclideanSpace ℝ (Fin n)) (h : ℝ), 0 < h →
          (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
          {y | u y < u x + ⟪p, y - x⟫ + h} ⊆ Q →
          volume {y | u y < u x + ⟪p, y - x⟫ + h} ≤
            ENNReal.ofReal (C * Real.sqrt (h ^ n / a)) := by
  obtain ⟨C, hC, hbound⟩ := exists_section_volume_upper_bound hn
  refine ⟨C, hC, fun u f hu huc hf hfpos hMA Q hQ => ?_⟩
  rcases Q.eq_empty_or_nonempty with hEmpty | hNonempty
  · refine ⟨1, one_pos, (by simp only [hEmpty, mem_empty_iff_false, false_implies, implies_true]),
      fun x p h hh _hp hSQ => ?_⟩
    have hxS : x ∈ {y | u y < u x + ⟪p, y - x⟫ + h} := by
      simp only [mem_ofPred_eq, sub_self, inner_zero_right, add_zero]
      linarith
    have hxQ := hSQ hxS
    simp only [hEmpty, mem_empty_iff_false] at hxQ
  · obtain ⟨z, hz, hmin⟩ := hQ.exists_isMinOn hNonempty hf.continuousOn
    refine ⟨f z, hfpos z, fun y hy => hmin hy, fun x p h hh hp hSQ => ?_⟩
    apply hbound u hu huc x p h hh hp (hQ.isBounded.subset hSQ) (f z) (hfpos z)
    intro G hG hGS
    rw [hMA G hG, ← setLIntegral_const G]
    apply setLIntegral_mono' hG.measurableSet
    intro y hy
    exact ENNReal.ofReal_le_ofReal (hmin (hSQ (hGS hy)))

section Localization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The tangent plane of a differentiable strictly convex function has a strict
gap at every distinct point, in any finite dimension. -/
theorem gradient_tangent_gap_pos {u : E → ℝ} (hu : Differentiable ℝ u)
    (hs : StrictConvexOn ℝ univ u) {x y : E} (hxy : x ≠ y) :
    0 < u y - u x - ⟪gradient u x, y - x⟫ := by
  exact gradient_tangent_gap_pos_of_strictConvexOn hs (mem_univ x) (mem_univ y) hxy (hu x)

variable [Nontrivial E]

/-- Strict convexity gives one small section height for all centres in a compact set.
The conclusion localizes the entire sections, including their possible distant points. -/
theorem exists_uniform_section_subset_ball {u : E → ℝ} (hs : StrictConvexOn ℝ univ u)
    (hC1 : ContDiff ℝ 1 u) {K : Set E} (hK : IsCompact K) {R : ℝ} (hR : 0 < R) :
    ∃ h₀ : ℝ,
      0 < h₀ ∧
        ∀ x ∈ K, ∀ h : ℝ, h ≤ h₀ → {y | u y < u x + ⟪gradient u x, y - x⟫ + h} ⊆ ball x R := by
  classical
  by_cases hKe : K.Nonempty
  · let A : Set (E × E) := K ×ˢ sphere (0 : E) R
    let F : E × E → ℝ := fun p => u (p.1 + p.2) - u p.1 - ⟪gradient u p.1, p.2⟫
    have hAc : IsCompact A := hK.prod (isCompact_sphere (0 : E) R)
    have hAn : A.Nonempty := hKe.prod (NormedSpace.sphere_nonempty.mpr hR.le)
    have hFc : Continuous F := by
      dsimp [F]
      exact
        ((hC1.continuous.comp (continuous_fst.add continuous_snd)).sub
              (hC1.continuous.comp continuous_fst)).sub
          ((BakryEmery.continuous_gradient hC1).comp continuous_fst |>.inner continuous_snd)
    have hFp : ∀ p ∈ A, 0 < F p := by
      rintro ⟨x, v⟩ ⟨_, hv⟩
      have hvn : ‖v‖ = R := by simpa only [mem_sphere, dist_zero_right] using hv
      have hv0 : v ≠ 0 := by intro hh; simp only [hh, norm_zero] at hvn; linarith
      simpa only [F, add_sub_cancel_left] using
        gradient_tangent_gap_pos (hC1.differentiable one_ne_zero) hs (x := x) (y := x + v)
          (by intro he; exact hv0 (add_left_cancel (he.symm.trans (add_zero x).symm)))
    obtain ⟨p, hp, hmin⟩ := hAc.exists_isMinOn hAn hFc.continuousOn
    refine ⟨F p, hFp p hp, fun x hx h hh y hy => ?_⟩
    change dist y x < R
    by_contra hn
    have hd : R ≤ ‖y - x‖ := by simpa only [dist_eq_norm] using le_of_not_gt hn
    have hdpos : 0 < ‖y - x‖ := hR.trans_le hd
    let t : ℝ := R / ‖y - x‖
    have ht : 0 < t := div_pos hR hdpos
    have ht1 : t ≤ 1 := (div_le_one hdpos).mpr hd
    let v : E := t • (y - x)
    have hv : v ∈ sphere (0 : E) R := by
      change dist (t • (y - x)) 0 = R
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact div_mul_cancel₀ R hdpos.ne'
    have hlower : F p ≤ F (x, v) := hmin ⟨hx, hv⟩
    have hconv :=
      hs.convexOn.2 (mem_univ x) (mem_univ y) (by linarith : 0 ≤ 1 - t) ht.le
        (by ring : 1 - t + t = 1)
    have heq : (1 - t) • x + t • y = x + v := by dsimp [v]; module
    rw [heq] at hconv
    simp only [smul_eq_mul] at hconv
    have hgap : F (x, v) ≤ t * (u y - u x - ⟪gradient u x, y - x⟫) := by
      dsimp [F, v]
      rw [inner_smul_right]
      nlinarith [hconv]
    have hhy : u y - u x - ⟪gradient u x, y - x⟫ < h := by
      change u y < u x + ⟪gradient u x, y - x⟫ + h at hy
      linarith
    have htp : t * (u y - u x - ⟪gradient u x, y - x⟫) < t * F p :=
      mul_lt_mul_of_pos_left (hhy.trans_le hh) ht
    have htle : t * F p ≤ F p := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht1 (hFp p hp).le
    linarith
  · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
    exact (hKe ⟨x, hx⟩).elim
end Localization

section LocalDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- A strictly convex C¹ Alexandrov solution with a continuous positive density has
common density bounds on every sufficiently small section centred in a compact set.
The height, floor and ceiling are chosen before all centres and all scales. -/
theorem exists_uniform_section_density_bounds {u f : E → ℝ}
    (hs : StrictConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA : ∀ G : Set E, IsOpen G → volume (subgradientImage u G) =
      ∫⁻ y in G, ENNReal.ofReal (f y))
    {K : Set E} (hK : IsCompact K) :
    ∃ a b h₀ : ℝ, 0 < a ∧ 0 < b ∧ 0 < h₀ ∧
      ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ h₀ →
        Bornology.IsBounded {y | u y < u x + ⟪gradient u x, y - x⟫ + h} ∧
        ∀ G : Set E, IsOpen G → G ⊆ {y | u y < u x + ⟪gradient u x, y - x⟫ + h} →
          ENNReal.ofReal a * (volume : Measure E) G ≤ volume (subgradientImage u G) ∧
          volume (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let Q : Set E := closedBall (0 : E) (R + 1)
  have hQc : IsCompact Q := isCompact_closedBall _ _
  have hQn : Q.Nonempty := ⟨0, by simp only [Q, mem_closedBall, dist_self]; linarith⟩
  obtain ⟨z, hz, hmin⟩ := hQc.exists_isMinOn hQn hf.continuousOn
  obtain ⟨M, hM⟩ := hQc.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨h₀, hh₀, hloc⟩ := exists_uniform_section_subset_ball hs hC1 hK (R := 1) zero_lt_one
  refine ⟨f z, max M 1, h₀, hfpos z, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hh₀, ?_⟩
  intro x hx h _ hh
  have hSQ : {y | u y < u x + ⟪gradient u x, y - x⟫ + h} ⊆ Q := by
    intro y hy
    have hyb := hloc x hx h hh hy
    change dist y 0 ≤ R + 1
    have hxy : dist y x < 1 := hyb
    have hxp : ‖x‖ ≤ R := hKR x hx
    calc dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
      _ ≤ R + 1 := by rw [dist_zero_right]; linarith
  refine ⟨hQc.isBounded.subset hSQ, ?_⟩
  intro G hG hGS
  rw [hMA G hG]
  constructor
  · rw [← setLIntegral_const G]
    apply setLIntegral_mono' hG.measurableSet
    intro y hy
    exact ENNReal.ofReal_le_ofReal (hmin (hSQ (hGS hy)))
  · rw [← setLIntegral_const G]
    apply setLIntegral_mono' hG.measurableSet
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self (f y)).trans ((hM y (hSQ (hGS hy))).trans (le_max_left _ _))
end LocalDensity

section Dilation

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The geometric inclusion behind the section-volume estimate.

The affine map is written as `y ↦ A • y + (1 - A) • x`, which is the
homothety of centre `x` and ratio `A`. No continuity or measurability
assumption on the section is needed for this inclusion. -/
private theorem convex_section_subset_dilation_image
    {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    (x p : E) (h A : ℝ) (hA : 1 ≤ A) :
    {z : E | u z < u x + ⟪p, z - x⟫ + A * h} ⊆
      (fun y : E => A • y + (1 - A) • x) ''
        {y : E | u y < u x + ⟪p, y - x⟫ + h} := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let t : ℝ := A⁻¹
  have htpos : 0 < t := by
    dsimp [t]
    exact inv_pos.mpr hApos
  have htA : t * A = 1 := by
    dsimp [t]
    exact inv_mul_cancel₀ hApos.ne'
  have hAt : A * t = 1 := by
    simpa only [mul_comm] using htA
  have ht1 : t ≤ 1 := by
    have hprod : 0 ≤ (A - 1) * t :=
      mul_nonneg (sub_nonneg.mpr hA) htpos.le
    nlinarith [htA]
  have hcancel : t * (A * h) = h := by
    rw [← mul_assoc, htA, one_mul]
  intro z hz
  let w : E := (1 - t) • x + t • z
  have huw : u w ≤ (1 - t) * u x + t * u z := by
    simpa only [w, smul_eq_mul] using
      hu.2 (mem_univ x) (mem_univ z)
        (sub_nonneg.mpr ht1) htpos.le
        (by ring : (1 - t) + t = 1)
  have hwsub : w - x = t • (z - x) := by
    dsimp [w]
    simp only [sub_smul, one_smul, smul_sub]
    abel
  have hip : ⟪p, w - x⟫ = t * ⟪p, z - x⟫ := by
    rw [hwsub, real_inner_smul_right]
  have hz' : u z < u x + ⟪p, z - x⟫ + A * h := hz
  have hwmem : w ∈ {y : E | u y < u x + ⟪p, y - x⟫ + h} := by
    change u w < u x + ⟪p, w - x⟫ + h
    calc
      u w ≤ (1 - t) * u x + t * u z := huw
      _ < (1 - t) * u x +
          t * (u x + ⟪p, z - x⟫ + A * h) :=
        add_lt_add_right (mul_lt_mul_of_pos_left hz' htpos) _
      _ = u x + t * ⟪p, z - x⟫ + t * (A * h) := by ring
      _ = u x + ⟪p, w - x⟫ + h := by
        rw [hip, hcancel]
  have hcoeff : A * (1 - t) + (1 - A) = 0 := by
    nlinarith [hAt]
  refine ⟨w, hwmem, ?_⟩
  calc
    A • w + (1 - A) • x =
        (A * (1 - t) + (1 - A)) • x + (A * t) • z := by
      simp only [w, smul_add, smul_smul, add_smul]
      abel
    _ = z := by
      rw [hcoeff, hAt]
      simp

/-- Haar scaling and translation invariance for the particular affine
homothety used above. This identity applies to arbitrary sets, including
sets of infinite volume. -/
private theorem volume_dilation_image
    (x : E) (A : ℝ) (hA : 0 ≤ A) (S : Set E) :
    (volume : Measure E)
        ((fun y : E => A • y + (1 - A) • x) '' S) =
      ENNReal.ofReal (A ^ n) * (volume : Measure E) S := by
  let L : E →ₗ[ℝ] E := A • LinearMap.id
  have hdim : Module.finrank ℝ E = n := by
    simp
  have hdet : LinearMap.det L = A ^ n := by
    simp [L, LinearMap.det_smul, hdim]
  have himage :
      (fun y : E => A • y + (1 - A) • x) '' S =
        (fun y : E => y + (1 - A) • x) '' (L '' S) := by
    rw [Set.image_image]
    rfl
  rw [himage, Set.image_add_right, measure_preimage_add_right,
    Measure.addHaar_image_linearMap, hdet,
    abs_of_nonneg (pow_nonneg hA n)]

/-- **Convex-section dilation volume bound.**

For a globally real-valued convex function, increasing a section height
by a factor `A ≥ 1` increases its volume by at most `A ^ n`.

The slope `p` is arbitrary: it need not be a gradient or a subgradient.
The statement includes `n = 0`, permits infinite section volume, and uses
no Monge–Ampère, Hessian, or engulfing estimate. This is a geometric
supporting lemma, not a completion of the quantitative regularity theorem. -/
theorem section_volume_mul_le
    {u : E → ℝ} (hu : ConvexOn ℝ univ u)
    (x p : E) {h A : ℝ} (hA : 1 ≤ A) :
    (volume : Measure E)
        {z : E | u z < u x + ⟪p, z - x⟫ + A * h} ≤
      ENNReal.ofReal (A ^ n) *
        (volume : Measure E)
          {z : E | u z < u x + ⟪p, z - x⟫ + h} := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  calc
    (volume : Measure E)
        {z : E | u z < u x + ⟪p, z - x⟫ + A * h} ≤
        (volume : Measure E)
          ((fun y : E => A • y + (1 - A) • x) ''
            {y : E | u y < u x + ⟪p, y - x⟫ + h}) :=
      measure_mono (convex_section_subset_dilation_image hu x p h A hA)
    _ = ENNReal.ofReal (A ^ n) *
        (volume : Measure E)
          {y : E | u y < u x + ⟪p, y - x⟫ + h} :=
      volume_dilation_image x A hA0 _

end Dilation

end FunctionalInequalities.Analysis
