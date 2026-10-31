module

public import FunctionalInequalities.Analysis.Convex.GaugeCone.Basic
public import Mathlib.Analysis.Convex.Measure

/-!
# Atomic supporting-image mass of an actual gauge cone

The explicit gauge potential has all its Monge–Ampere mass at the vertex:
its nonvertex image lies on the genuinely Haar-null one-sided polar frontier.
The vertex coefficient is generated and finite in every finite dimension,
including zero. This is actual raw atomic data for Dirichlet construction,
not prescribed atom weight, a unit-density reference or Sobolev regularity.
-/

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace Pointwise Topology ENNReal
namespace FunctionalInequalities.Analysis.GaugeCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual vertex coefficient is finite, without a source mass cap. -/
theorem volume_polar_lt_top
    {D : Set E} (hD : IsOpen D) (hDc : Convex ℝ D) (h0 : (0:E)∈D)
    {h : ℝ} (hh : 0<h) : (volume : Measure E) (polar D h)<⊤ :=
  (isCompact_polar hD hDc h0 hh).measure_lt_top

/-- Boundedness alone generates a positive-volume ball of one-sided polar
slopes. This positivity needs no openness, convexity or interior-point premise;
finiteness is supplied separately by the actual compact-polar producer. -/
theorem volume_polar_pos {D : Set E} (hb : Bornology.IsBounded D) {h : ℝ} (hh : 0 < h) :
    0 < (volume : Measure E) (polar D h) := by
  obtain ⟨R, hR, hbound⟩ := hb.exists_pos_norm_le
  have hr : 0 < h / R := div_pos hh hR
  have hball : ball (0 : E) (h / R) ⊆ polar D h := by
    intro p hp y hy
    have hpn : ‖p‖ ≤ h / R :=
      (by simpa only [mem_ball, dist_zero_right] using hp : ‖p‖ < h / R).le
    calc
      ⟪p, y⟫ ≤ ‖p‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ (h / R) * ‖y‖ := mul_le_mul_of_nonneg_right hpn (norm_nonneg _)
      _ ≤ (h / R) * R := mul_le_mul_of_nonneg_left (hbound y hy) hr.le
      _ = h := div_mul_cancel₀ _ hR.ne'
  have hpos : 0 < (volume : Measure E) (ball (0 : E) (h / R)) :=
    isOpen_ball.measure_pos volume ⟨0, by simpa only [mem_ball, dist_self] using hr⟩
  exact hpos.trans_le (measure_mono hball)

section AtomicImage
open Classical

/-- The genuine raw atomic DOMAIN MA equation on every subset of the domain.
No measurability of the subset/image, nullity or desired mass is assumed. -/
theorem volume_image {D : Set E} (hD : IsOpen D) (hDc : Convex ℝ D) (h0 : (0 : E) ∈ D) {h : ℝ}
    (hh : 0 < h) :
    ∀ G : Set E,
      G ⊆ D →
        (volume : Measure E) (subgradientImageOn (potential D h) D G) =
          if (0 : E) ∈ G then volume (polar D h) else 0 := by
  classical
  let u : E → ℝ := potential D h
  let P : Set E := polar D h
  have ht := geometry hD hDc h0 hh
  change
    ConvexOn ℝ univ u ∧
      Continuous u ∧
        u 0 = -h ∧ (∀ z ∈ frontier D, u z = 0) ∧ subgradientImageOn u D {0} = P at ht
  have hPclosed : IsClosed P := isClosed_polar D h
  have hPb : (volume : Measure E) (frontier P) = 0 := (convex_polar D h).addHaar_frontier volume
  have hnon := image_nonvertex_subset_frontier hD hDc h0 hh
  change subgradientImageOn u D (D \ {0}) ⊆ frontier P at hnon
  change
    ∀ G : Set E,
      G ⊆ D →
        (volume : Measure E) (subgradientImageOn u D G) = if (0 : E) ∈ G then volume P else 0
  intro G hG
  by_cases hG0 : (0 : E) ∈ G
  · rw [ite_eq_left hG0]
    apply le_antisymm
    · apply MeasureTheory.measure_mono
      rintro p ⟨x, hx, hp⟩
      by_cases hx0 : x = 0
      · apply ht.2.2.2.2.subset
        exact ⟨x, by simp [hx0], hp⟩
      · rw [← hPclosed.closure_eq]
        exact
          frontier_subset_closure
            (hnon ⟨x, ⟨hG hx, by simpa only [mem_singleton_iff] using hx0⟩, hp⟩)
    · apply MeasureTheory.measure_mono
      rw [← ht.2.2.2.2]
      exact subgradientImageOn_mono u D (singleton_subset_iff.mpr hG0)
  · rw [ite_eq_right hG0]
    apply MeasureTheory.measure_mono_null (t := frontier P) _ hPb
    rintro p ⟨x, hx, hp⟩
    apply hnon
    refine ⟨x, ⟨hG hx, ?_⟩, hp⟩
    intro hx0
    have hx0' : x = 0 := mem_singleton_iff.mp hx0
    exact hG0 (hx0' ▸ hx)

end AtomicImage
end FunctionalInequalities.Analysis.GaugeCone
