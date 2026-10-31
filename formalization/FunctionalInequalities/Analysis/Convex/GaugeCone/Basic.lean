module

public import FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import FunctionalInequalities.Analysis.Convex.Subgradient.Image
public import Mathlib.Analysis.Convex.Gauge

/-!
# Gauge cones and their real one-sided polars

The actual positive-height gauge cone of an open convex neighborhood of zero
is globally convex and continuous, vanishes on the entire frontier, and has
an explicit vertex supporting image. All nonvertex supporting slopes lie on
that image's frontier. These are Dirichlet construction prerequisites for
Letwin arXiv:2607.24164v1, Lemma 2.2 / BB arXiv:1207.6128v1, Theorem 2.24(ii).
The real ONE-SIDED polar here differs from Mathlib's absolute locally-convex
polar: no symmetry of the domain is assumed. Pure geometry needs neither
finite dimension nor completeness, boundedness or measure. Compactness of
actual vertex images is a separate finite-dimensional property.
-/

@[expose] public section

noncomputable section
open Set Metric
open scoped RealInnerProductSpace Pointwise Topology
namespace FunctionalInequalities.Analysis.GaugeCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The explicit gauge potential of height `h`, centered at zero. -/
def potential (D : Set E) (h : ℝ) (x : E) : ℝ :=
  h * (gauge D x - 1)

/-- The real one-sided polar at height `h`; absolute values and symmetry
are deliberately absent. -/
def polar (D : Set E) (h : ℝ) : Set E :=
  {p | ∀ y ∈ D, ⟪p, y⟫ ≤ h}

/-- One-sided polars are closed, without domain or dimension hypotheses. -/
theorem isClosed_polar (D : Set E) (h : ℝ) : IsClosed (polar D h) := by
  have heq : polar D h = ⋂ y ∈ D, {p : E | ⟪p, y⟫ ≤ h} := by
    ext p
    simp only [polar, mem_iInter, mem_ofPred_eq]
  rw [heq]
  exact
    isClosed_iInter
      (fun y =>
        isClosed_iInter
          (fun _hy => isClosed_le (continuous_id.inner continuous_const) continuous_const))

/-- One-sided polars are convex, with no domain regularity hypothesis. -/
theorem convex_polar (D : Set E) (h : ℝ) : Convex ℝ (polar D h) := by
  intro p hp q hq a b ha hb hab y hy
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    _ ≤ a * h + b * h :=
      add_le_add (mul_le_mul_of_nonneg_left (hp y hy) ha)
        (mul_le_mul_of_nonneg_left (hq y hy) hb)
    _ = h := by rw [← add_mul, hab, one_mul]

/-- Actual cone convexity, continuity, vertex value, whole-frontier zero
boundary data and vertex supporting image, all produced from source geometry. -/
theorem geometry {D : Set E} (hD : IsOpen D) (hDc : Convex ℝ D) (h0 : (0 : E) ∈ D) {h : ℝ}
    (hh : 0 < h) :
    ConvexOn ℝ univ (potential D h) ∧
      Continuous (potential D h) ∧
        potential D h 0 = -h ∧
          (∀ z ∈ frontier D, potential D h z = 0) ∧
            subgradientImageOn (potential D h) D {0} = polar D h := by
  unfold potential polar
  have hn : D ∈ 𝓝 (0 : E) := hD.mem_nhds h0
  have ha : Absorbent ℝ D := absorbent_nhds_zero hn
  have hconv : ConvexOn ℝ univ (gauge D) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha0 hb0 _hab
    calc
      gauge D (a • x + b • y) ≤ gauge D (a • x) + gauge D (b • y) := gauge_add_le hDc ha _ _
      _ = a • gauge D x + b • gauge D y := by
        rw [gauge_smul_of_nonneg ha0, gauge_smul_of_nonneg hb0]
  have hc : ConvexOn ℝ univ (fun x => h * (gauge D x - 1)) := by
    have hs := hconv.sub (concaveOn_const (1 : ℝ) convex_univ)
    have hm := hs.smul hh.le
    change ConvexOn ℝ univ (fun x => h * (gauge D x - 1)) at hm
    exact hm
  refine ⟨hc, ((continuous_gauge hDc hn).sub continuous_const).const_mul h, ?_, ?_, ?_⟩
  · simp
  · intro z hz
    rw [(gauge_eq_one_iff_mem_frontier hDc hn).2 hz]
    ring
  · ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      have hx0 : x = 0 := mem_singleton_iff.mp hx
      subst x
      intro y hy
      have hs := hp y hy
      simp only [gauge_zero, sub_zero, zero_sub, mul_neg, mul_one] at hs
      have hg := gauge_le_one_of_mem hy
      nlinarith [mul_le_mul_of_nonneg_left hg hh.le]
    · intro hp
      refine ⟨0, mem_singleton _, ?_⟩
      intro y _hy
      have hlin : ⟪p, y⟫ / h ≤ gauge D y := by
        rw [gauge_def]
        apply le_csInf ha.gauge_set_nonempty
        rintro r ⟨hr, hy⟩
        obtain ⟨z, hz, rfl⟩ := hy
        rw [real_inner_smul_right]
        apply (div_le_iff₀ hh).2
        have hs := mul_le_mul_of_nonneg_left (hp z hz) hr.le
        nlinarith
      have hs := (div_le_iff₀ hh).1 hlin
      simp only [gauge_zero, sub_zero, zero_sub, mul_neg, mul_one]
      nlinarith

/-- Actual nonvertex supporting slopes lie on the one-sided polar frontier.
The contact equality is derived at zero and at twice the contact point. -/
theorem image_nonvertex_subset_frontier {D : Set E} (hD : IsOpen D) (hDc : Convex ℝ D)
    (h0 : (0 : E) ∈ D) {h : ℝ} (hh : 0 < h) :
    subgradientImageOn (potential D h) D (D \ {0}) ⊆ frontier (polar D h) := by
  let u : E → ℝ := potential D h
  let P : Set E := polar D h
  have ht := geometry hD hDc h0 hh
  change
    ConvexOn ℝ univ u ∧
      Continuous u ∧
        u 0 = -h ∧ (∀ z ∈ frontier D, u z = 0) ∧ subgradientImageOn u D {0} = P at ht
  have hPc : IsClosed P := isClosed_polar D h
  rintro p ⟨x, hx, hp⟩
  have hxne : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
  have hg : ∀ y, u x + ⟪p, y - x⟫ ≤ u y := fun y =>
    subgradient_le_on_of_isOpen ht.1 hD (subset_univ _) hx.1 hp y (mem_univ y)
  have hs0 := hg 0
  rw [ht.2.2.1, zero_sub, inner_neg_right] at hs0
  have hs2 := hg ((2 : ℝ) • x)
  rw [show (2 : ℝ) • x - x = x by module] at hs2
  have hscale : gauge D ((2 : ℝ) • x) = 2 * gauge D x := by
    simpa only [smul_eq_mul] using gauge_smul_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) x
  dsimp [u, potential] at hs0 hs2
  rw [hscale] at hs2
  have hEq : ⟪p, x⟫ = h * gauge D x := by nlinarith
  have hpP : p ∈ P := by
    intro y hy
    have hs := hg y
    rw [inner_sub_right] at hs
    dsimp [u, potential] at hs
    have hb := mul_le_mul_of_nonneg_left (gauge_le_one_of_mem hy) hh.le
    nlinarith
  rw [frontier, hPc.closure_eq]
  refine ⟨hpP, ?_⟩
  intro hip
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hip)
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  let t : ℝ := r / (2 * ‖x‖)
  have htpos : 0 < t := by dsimp [t]; positivity
  let q : E := p + t • x
  have hqdist : dist q p < r := by
    rw [dist_eq_norm]
    change ‖(p + t • x) - p‖ < r
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]
    dsimp [t]
    have heq : r / (2 * ‖x‖) * ‖x‖ = r / 2 := by field_simp
    rw [heq]
    linarith
  have hqP : q ∈ P := hball (mem_ball.mpr hqdist)
  have hqImage : q ∈ subgradientImageOn u D {0} := by rw [ht.2.2.2.2]; exact hqP
  rcases hqImage with ⟨z, hz, hq⟩
  have hz0 : z = 0 := mem_singleton_iff.mp hz
  subst z
  have hm := hq x hx.1
  rw [ht.2.2.1, sub_zero] at hm
  have hi : ⟪q, x⟫ = ⟪p, x⟫ + t * ‖x‖ ^ 2 := by
    simp only [q, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hi] at hm
  dsimp [u, potential] at hm
  have hpos := mul_pos htpos (sq_pos_of_pos hnorm)
  nlinarith

/-- Finite-dimensional compactness of the actual vertex image. The slope cap
and closed image are generated by the C0 convex domain producer. -/
theorem isCompact_polar [FiniteDimensional ℝ E] {D : Set E} (hD : IsOpen D) (hDc : Convex ℝ D)
    (h0 : (0 : E) ∈ D) {h : ℝ} (hh : 0 < h) : IsCompact (polar D h) := by
  have ht := geometry hD hDc h0 hh
  rw [← ht.2.2.2.2]
  exact
    isCompact_subgradientImageOn_of_isCompact hD (ht.1.subset (subset_univ _) hDc)
      ht.2.1.continuousOn isCompact_singleton (singleton_subset_iff.mpr h0)

end FunctionalInequalities.Analysis.GaugeCone
