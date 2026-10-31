module

public import FunctionalInequalities.Analysis.Convex.Caffarelli.Sublevel
public import FunctionalInequalities.Analysis.Convex.CompactTilt

/-! # DomainContact in convex Monge--Ampere analysis

Caffarelli contact geometry supporting Letwin arXiv:2607.24164v1
Lemma 2.2 through BB arXiv:1207.6128v1 Theorem 2.24(ii).
The declarations retain their given-source hypotheses; domain contact
rigidity and moment-source regularity have separate consumers.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- The generated proper patch transfers the SAME contact and actual UNIT
bounds to the existing Caffarelli compact-sublevel theorem. -/
theorem eq_of_domain_unit_contact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}
    {Ω : Set E} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    (hu : ConvexOn ℝ (closure Ω) u) (hC : ContinuousOn u (closure Ω))
    (hz : ∀ z ∈ frontier Ω, u z = 0) (hneg : ∀ x ∈ Ω, u x < 0)
    (hMA : ∀ G : Set E, IsOpen G → G ⊆ Ω → volume (subgradientImageOn u Ω G) = volume G)
    {x y p : E} (hx : x ∈ Ω) (hy : y ∈ Ω) (hp : ∀ z ∈ Ω, u x + ⟪p, z - x⟫ ≤ u z)
    (hxy : u y = u x + ⟪p, y - x⟫) : y = x := by
  let r : ℝ := max (u x) (u y) / 2
  have hm : max (u x) (u y) < 0 := max_lt (hneg x hx) (hneg y hy)
  have hr : r < 0 := by dsimp [r]; linarith
  have hxr : u x < r := by dsimp [r]; linarith [le_max_left (u x) (u y)]
  have hyr : u y < r := by dsimp [r]; linarith [le_max_right (u x) (u y)]
  obtain ⟨hK, _hKn, _hKΩ, V, _L, hV, _hL, heq, hweak, hstrict, himage⟩ :=
    exists_negative_sublevel_patch hΩ hcΩ hb hu hC hz hr hx hxr
  have hxK : x ∈ {z ∈ closure Ω | u z ≤ r} := ⟨subset_closure hx, hxr.le⟩
  have hyK : y ∈ {z ∈ closure Ω | u z ≤ r} := ⟨subset_closure hy, hyr.le⟩
  have hpx : p ∈ subgradientImage V { x } := by
    rw [himage { x } (singleton_subset_iff.mpr ⟨hx, hxr⟩)]
    exact ⟨x, mem_singleton x, hp⟩
  obtain ⟨z, hzX, hpV⟩ := hpx
  have hzx : z = x := mem_singleton_iff.mp hzX
  subst z
  have hKV : IsCompact {z | V z ≤ r} := by rwa [hweak]
  have hBV :
    ∀ Q : Set E,
      IsCompact Q →
        Q ⊆ {z | V z < r} →
          ∃ a b : ℝ,
            0 < a ∧
              ∀ G : Set E,
                IsOpen G →
                  closure G ⊆ Q →
                    ENNReal.ofReal a * volume G ≤ volume (subgradientImage V G) ∧
                      volume (subgradientImage V G) ≤ ENNReal.ofReal b * volume G := by
    intro Q _hQc hQV
    refine ⟨1, 1, zero_lt_one, ?_⟩
    intro G hG hGQ
    have hGstrict : G ⊆ {z ∈ Ω | u z < r} := by
      rw [← hstrict]
      exact subset_closure.trans (hGQ.trans hQV)
    have hGΩ : G ⊆ Ω := fun z hzG => (hGstrict hzG).1
    rw [himage G hGstrict, hMA G hG hGΩ]
    simp
  apply eq_of_contact_of_sublevel_bounds hV hpV hKV hBV
  · rw [heq y hyK]
    exact hyr
  · rw [heq y hyK, heq x hxK]
    exact hxy


end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

private lemma support_eq_of_contained_dual_section {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u ψ : E → ℝ} {K D : Set E} (P : E → E)
    (hP :
      ∀ p,
        P p ∈ K ∧
          (∀ y ∈ K, u (P p) + ⟪p, y - P p⟫ ≤ u y) ∧
            ∀ x ∈ K, (∀ y ∈ K, u x + ⟪p, y - x⟫ ≤ u y) → x = P p)
    (hKD : K ⊆ D) (hcvψ : ConvexOn ℝ univ ψ) (hv : ∀ p, ψ p = ⟪p, P p⟫ - u (P p))
    (hMA :
      ∀ G : Set E, IsOpen G → G ⊆ P ⁻¹' interior K → volume (subgradientImage ψ G) = volume G)
    {x p q : E} (hx : x ∈ interior K) {R : ℝ} (hR : -u x < R)
    (hcomp : IsCompact {p | ψ p - ⟪p, x⟫ ≤ R})
    (hsection : {p | ψ p - ⟪p, x⟫ ≤ R} ⊆ P ⁻¹' interior K)
    (hp : ∀ y ∈ D, u x + ⟪p, y - x⟫ ≤ u y) (hq : ∀ y ∈ D, u x + ⟪q, y - x⟫ ≤ u y) : p = q := by
  classical
  rcases subsingleton_or_nontrivial E with hsub | hnt
  · exact hsub.elim _ _
  let : Nontrivial E := hnt
  have hxK : x ∈ K := interior_subset hx
  have hPp : P p = x := ((hP p).2.2 x hxK (fun y hy => hp y (hKD hy))).symm
  have hPq : P q = x := ((hP q).2.2 x hxK (fun y hy => hq y (hKD hy))).symm
  let F : E → ℝ := fun z => ψ z - ⟪z, x⟫
  have hefun : (fun z : E => ⟪z, x⟫) = fun z : E => (innerSL ℝ x) z := by
    funext z
    change ⟪z, x⟫ = ⟪x, z⟫
    exact (real_inner_comm z x).symm
  have hlin : ConcaveOn ℝ (univ : Set E) (fun z => ⟪z, x⟫) := by
    rw [hefun]
    exact (innerSL ℝ x).toLinearMap.concaveOn convex_univ
  have hconvF : ConvexOn ℝ univ F := hcvψ.sub hlin
  have hpval : F p = -u x := by dsimp [F]; rw [hv p, hPp]; ring
  have hqval : F q = -u x := by dsimp [F]; rw [hv q, hPq]; ring
  have hmin (z : E) : F p ≤ F z := by
    rw [hpval]
    have hh := (hP z).2.1 x hxK
    dsimp [F]
    rw [hv z]
    rw [inner_sub_right] at hh
    linarith
  have hsupport (z : E) : F p + ⟪(0 : E), z - p⟫ ≤ F z := by
    simpa only [inner_zero_left, add_zero] using hmin z
  have hbounds :
    ∀ Q : Set E,
      IsCompact Q →
        Q ⊆ {z | F z < R} →
          ∃ a b : ℝ,
            0 < a ∧
              ∀ G : Set E,
                IsOpen G →
                  closure G ⊆ Q →
                    ENNReal.ofReal a * volume G ≤ volume (subgradientImage F G) ∧
                      volume (subgradientImage F G) ≤ ENNReal.ofReal b * volume G := by
    intro Q _hQ hQR
    refine ⟨1, 1, zero_lt_one, ?_⟩
    intro G hG hGQ
    have hGD : G ⊆ P ⁻¹' interior K := by
      intro z hz
      apply hsection
      have hzR : F z < R := hQR (hGQ (subset_closure hz))
      exact hzR.le
    have hvF : volume (subgradientImage F G) = volume (subgradientImage ψ G) := by
      have heF : (fun z : E => ψ z - (⟪x, z⟫ + 0)) = F := by
        funext z
        dsimp [F]
        rw [add_zero, real_inner_comm x z]
      rw [← heF]
      exact volume_subgradientImage_sub_inner_add_const ψ x 0 G
    rw [hvF, hMA G hG hGD]
    simp
  have hqR : F q < R := by rw [hqval]; exact hR
  have he : F q = F p + ⟪(0 : E), q - p⟫ := by rw [hpval, hqval, inner_zero_left, add_zero]
  exact (eq_of_contact_of_sublevel_bounds hconvF hsupport hcomp hbounds hqR he).symm

/-- Actual C0 compact conjugate and OPEN dual MA generate uniqueness of
primal support slopes, using a generated full section and existing contact/Haar. -/
theorem eq_of_primal_supports_of_open_dual_mass {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u ψ : E → ℝ} {K D : Set E} (hD : IsOpen D) (hu : ConvexOn ℝ D u) (hC : ContinuousOn u D)
    (hK : IsCompact K) (hKD : K ⊆ D) (P : E → E) (hPC : Continuous P)
    (hP :
      ∀ p,
        P p ∈ K ∧
          (∀ y ∈ K, u (P p) + ⟪p, y - P p⟫ ≤ u y) ∧
            ∀ x ∈ K, (∀ y ∈ K, u x + ⟪p, y - x⟫ ≤ u y) → x = P p)
    (hψ : Continuous ψ) (hcvψ : ConvexOn ℝ univ ψ)
    (hs : ∀ p, ψ p = sSup ((fun y => ⟪p, y⟫ - u y) '' K)) (hv : ∀ p, ψ p = ⟪p, P p⟫ - u (P p))
    (hMA :
      ∀ G : Set E, IsOpen G → G ⊆ P ⁻¹' interior K → volume (subgradientImage ψ G) = volume G)
    {x p q : E} (hx : x ∈ interior K) (hp : ∀ y ∈ D, u x + ⟪p, y - x⟫ ≤ u y)
    (hq : ∀ y ∈ D, u x + ⟪q, y - x⟫ ≤ u y) : p = q := by
  obtain ⟨_p₀, R, _hP₀, _hvalue, hR, hcomp, hsection⟩ :=
    exists_contained_dual_section hD hu hC hK hKD P hPC hP hψ hs hv hx
  exact support_eq_of_contained_dual_section P hP hKD hcvψ hv hMA hx hR hcomp hsection hp hq

/-- One actual section and one actual contact implementation produce both
the full contained section and uniqueness of ALL support slopes at SAME point. -/
theorem exists_contained_section_unique_supports {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u ψ : E → ℝ} {K D : Set E} (hD : IsOpen D) (hu : ConvexOn ℝ D u) (hC : ContinuousOn u D)
    (hK : IsCompact K) (hKD : K ⊆ D) (P : E → E) (hPC : Continuous P)
    (hP :
      ∀ p,
        P p ∈ K ∧
          (∀ y ∈ K, u (P p) + ⟪p, y - P p⟫ ≤ u y) ∧
            ∀ x ∈ K, (∀ y ∈ K, u x + ⟪p, y - x⟫ ≤ u y) → x = P p)
    (hψ : Continuous ψ) (hcvψ : ConvexOn ℝ univ ψ)
    (hs : ∀ p, ψ p = sSup ((fun y => ⟪p, y⟫ - u y) '' K)) (hv : ∀ p, ψ p = ⟪p, P p⟫ - u (P p))
    (hMA :
      ∀ G : Set E, IsOpen G → G ⊆ P ⁻¹' interior K → volume (subgradientImage ψ G) = volume G)
    {x : E} (hx : x ∈ interior K) :
    ∃ (p₀ : E) (R : ℝ),
      P p₀ = x ∧
        ψ p₀ - ⟪p₀, x⟫ = -u x ∧
          -u x < R ∧
            IsCompact {p | ψ p - ⟪p, x⟫ ≤ R} ∧
              {p | ψ p - ⟪p, x⟫ ≤ R} ⊆ P ⁻¹' interior K ∧
                ∀ p q : E,
                  (∀ y ∈ D, u x + ⟪p, y - x⟫ ≤ u y) →
                    (∀ y ∈ D, u x + ⟪q, y - x⟫ ≤ u y) → p = q := by
  obtain ⟨p₀, R, hP₀, hvalue, hR, hcomp, hsection⟩ :=
    exists_contained_dual_section hD hu hC hK hKD P hPC hP hψ hs hv hx
  exact
    ⟨p₀, R, hP₀, hvalue, hR, hcomp, hsection, fun p q hp hq =>
      support_eq_of_contained_dual_section P hP hKD hcvψ hv hMA hx hR hcomp hsection hp hq⟩

end FunctionalInequalities.Analysis
