module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import FunctionalInequalities.Analysis.Convex.Section.Growth
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Strict Alexandrov comparison and positive scaling

Supports for Letwin arXiv:2607.24164v1 Lemma 2.2 through the nonlinear interior
W²,p estimate of Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii)
(Caffarelli, Annals of Mathematics 131 (1990), 135–150, DOI 10.2307/1971510).
The comparison step uses subgradient-image monotonicity (Gutiérrez 2001, Lemma 1.4.1).

This file supplies:
* strict comparison from open-set Alexandrov measure inequalities;
* positive scaling of subgradient images and their volumes.

It uses the existing `subgradientImage_subset_of_le`.

Multiplicative Dirichlet bracketing and perturbation stability follow by positive
scaling and removal of strict density gaps. The actual unit-density comparison
solution is given. No existence theorem, Hessian bound or W²,p integrability
is asserted. Uniform C⁰ perturbations of a strictly convex C¹ reference also
produce genuine interior supporting contacts, with a compact-uniform tolerance
chosen before the perturbation. The perturbation need not be convex. Combining
this contact producer with actual density comparison realizes scaled reference
slopes as gradients at supporting contacts of the residual `u - (1 - δ) v`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Pointwise RealInnerProductSpace ENNReal

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positive multiplication of a function positively scales its subgradient
image. Neither convexity nor measurability is needed for this set identity. -/
theorem subgradientImage_mul_pos
    (u : E → ℝ) {c : ℝ} (hc : 0 < c) (G : Set E) :
    subgradientImage (fun x => c * u x) G =
      (fun p : E => c • p) '' subgradientImage u G := by
  simpa only [subgradientImageOn_univ] using subgradientImageOn_mul_pos u hc univ G

variable [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Positive scaling of a genuine domain supporting image has the actual Haar factor,
without assuming measurability or finite volume of the image. -/
theorem volume_subgradientImageOn_mul_pos (u : E → ℝ) {c : ℝ} (hc : 0 < c) (D G : Set E) :
    (volume : Measure E) (subgradientImageOn (fun x => c * u x) D G) =
      ENNReal.ofReal (c ^ Module.finrank ℝ E) *
        (volume : Measure E) (subgradientImageOn u D G) := by
  rw [subgradientImageOn_mul_pos u hc D G]
  change (volume : Measure E) (c • subgradientImageOn u D G) = _
  calc
    (volume : Measure E) (c • subgradientImageOn u D G) = _ := by apply Measure.addHaar_smul
    _ = _ := by simp [abs_of_pos hc, ENNReal.ofReal_pow, hc.le]

/-- Positive scalar covariance for a domain-relative supporting image. -/
theorem volume_subgradientImageOn_mul_pos_comp_affineEquiv_symm (u : E → ℝ) (e : E ≃ᵃ[ℝ] E)
    {a : ℝ} (ha : 0 < a) (D G : Set E) :
    (volume : Measure E) (subgradientImageOn (fun x => a * (u ∘ e.symm) x) (e '' D) (e '' G)) =
      ENNReal.ofReal (a ^ Module.finrank ℝ E * |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹) *
        (volume : Measure E) (subgradientImageOn u D G) := by
  rw [volume_subgradientImageOn_mul_pos _ ha, volume_subgradientImageOn_comp_affineEquiv_symm]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg ha.le _)]

/-- The genuine domain-relative constant-density covariance. -/
theorem volume_subgradientImageOn_affine_scalar_covariance (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) {a c : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (D : Set E)
    (hMA :
      ∀ H : Set E,
        IsOpen H →
          H ⊆ D →
            (volume : Measure E) (subgradientImageOn u D H) =
              ENNReal.ofReal c * (volume : Measure E) H) :
    ∀ U : Set E,
      IsOpen U →
        U ⊆ e '' D →
          (volume : Measure E) (subgradientImageOn (fun x => a * (u ∘ e.symm) x) (e '' D) U) =
            ENNReal.ofReal
                (a ^ Module.finrank ℝ E * |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
                    |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
                  c) *
              (volume : Measure E) U := by
  intro U hU hUD
  let H : Set E := e.symm '' U
  have hHopen : IsOpen H := by
    dsimp [H]
    exact e.symm.toContinuousAffineEquiv.toHomeomorph.isOpenMap U hU
  have hHD : H ⊆ D := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hUD hy with ⟨z, hz, hzeq⟩
    have : z = e.symm y := by
      apply e.injective
      simp [hzeq]
    simpa [this] using hz
  have heH : e '' H = U := by
    dsimp [H]
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨e.symm y, ⟨y, hy, rfl⟩, by simp⟩
  have hcov :
    (volume : Measure E) (subgradientImageOn (fun x => a * (u ∘ e.symm) x) (e '' D) (e '' H)) =
      ENNReal.ofReal (a ^ Module.finrank ℝ E * |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹) *
        (volume : Measure E) (subgradientImageOn u D H) :=
    volume_subgradientImageOn_mul_pos_comp_affineEquiv_symm u e ha D H
  rw [heH] at hcov
  rw [hcov, hMA H hHopen hHD]
  have hvol :
    (volume : Measure E) H =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ * volume U := by
    rw [volume_image_affineEquiv e.symm U, abs_det_linear_symm]
  rw [hvol]
  have hA : 0 ≤ a ^ Module.finrank ℝ E * |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ :=
    mul_nonneg (pow_nonneg ha.le _) (inv_nonneg.mpr (abs_nonneg _))
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hA, ←
    ENNReal.ofReal_mul (mul_nonneg hA hc)]
  congr 2
  ring


/-- Positive scaling multiplies subgradient-image volume by `c ^ finrank ℝ E`.

The identity concerns outer measure, so no measurability assumption on `G` or
on its subgradient image is imposed. -/
theorem volume_subgradientImage_mul_pos
    (u : E → ℝ) {c : ℝ} (hc : 0 < c) (G : Set E) :
    (volume : Measure E) (subgradientImage (fun x => c * u x) G) =
      ENNReal.ofReal (c ^ Module.finrank ℝ E) *
        (volume : Measure E) (subgradientImage u G) := by
  simpa only [subgradientImageOn_univ] using volume_subgradientImageOn_mul_pos u hc univ G

private theorem le_of_strict_bounds_on_support_domain {u v : E → ℝ} {D Ω : Set E}
    (hu : ConvexOn ℝ D u) (hv : ConvexOn ℝ D v) (huc : ContinuousOn u (closure Ω))
    (hvc : ContinuousOn v (closure Ω)) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hD : closure Ω ⊆ D) (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) {a b : ℝ} (hba : b < a)
    (hb : 0 ≤ b)
    (hMAu :
      ∀ G : Set E,
        IsOpen G →
          G ⊆ Ω → ENNReal.ofReal a * (volume : Measure E) G ≤ volume (subgradientImageOn u D G))
    (hMAv :
      ∀ G : Set E,
        IsOpen G →
          G ⊆ Ω →
            volume (subgradientImageOn v D G) ≤ ENNReal.ofReal b * (volume : Measure E) G) :
    ∀ x ∈ Ω, u x ≤ v x := by
  let G : Set E := Ω ∩ {x | v x < u x}
  have hGopen : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hΩD : Ω ⊆ D := subset_closure.trans hD
    have hi : x ∈ interior D := interior_maximal hΩD hΩ hx.1
    have hux := hu.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hi)
    have hvx := hvc.continuousAt (mem_of_superset (hΩ.mem_nhds hx.1) subset_closure)
    exact inter_mem (hΩ.mem_nhds hx.1) (hvx.eventually_lt hux hx.2)
  have hGsub : G ⊆ Ω := fun _ hx => hx.1
  have hGb := hΩb.subset hGsub
  have hGeq : ∀ x ∈ frontier G, v x = u x := by
    intro x hx
    have hxclG := frontier_subset_closure hx
    have hxclΩ := closure_mono hGsub hxclG
    have hvu : v x ≤ u x :=
      ContinuousWithinAt.closure_le hxclG ((hvc x hxclΩ).mono (hGsub.trans subset_closure))
        ((huc x hxclΩ).mono (hGsub.trans subset_closure)) (fun y hy => le_of_lt hy.2)
    apply le_antisymm hvu
    by_cases hxΩ : x ∈ Ω
    · have hnot : x ∉ G := by rw [hGopen.frontier_eq] at hx; exact hx.2
      exact le_of_not_gt (fun hlt => hnot ⟨hxΩ, hlt⟩)
    · exact hboundary x (by rw [hΩ.frontier_eq]; exact ⟨hxclΩ, hxΩ⟩)
  have himage : subgradientImageOn u D G ⊆ subgradientImageOn v D G :=
    subgradientImageOn_subset_of_le hv (hvc.mono (closure_mono hGsub))
      (huc.mono (closure_mono hGsub)) hGopen hGb ((closure_mono hGsub).trans hD)
      (fun y hy => le_of_lt hy.2) hGeq
  intro x hxΩ
  by_contra hnot
  have hxG : x ∈ G := ⟨hxΩ, lt_of_not_ge hnot⟩
  have hGpos : 0 < (volume : Measure E) G := IsOpen.measure_pos volume hGopen ⟨x, hxG⟩
  have hGfinite : (volume : Measure E) G < ∞ := hGb.measure_lt_top
  have hmul :
    ENNReal.ofReal a * (volume : Measure E) G ≤ ENNReal.ofReal b * (volume : Measure E) G := by
    calc
      _ ≤ volume (subgradientImageOn u D G) := hMAu G hGopen hGsub
      _ ≤ volume (subgradientImageOn v D G) := measure_mono himage
      _ ≤ _ := hMAv G hGopen hGsub
  have hc : ENNReal.ofReal a ≤ ENNReal.ofReal b :=
    (ENNReal.mul_le_mul_iff_right (a := (volume : Measure E) G) (ne_of_gt hGpos)
          (ne_of_lt hGfinite)).mp
      (by simpa [mul_comm] using hmul)
  exact (not_le_of_gt hba) ((ENNReal.ofReal_le_ofReal_iff hb).mp hc)

/-- Strict Alexandrov comparison from genuine open-set measure bounds.

If `u ≤ v` on the frontier of a bounded open set, the lower density bound for
`u` is strictly larger than the upper density bound for `v`, and both functions
are globally finite and convex, then `u ≤ v` throughout the set.

The domain is not assumed convex. Continuity follows from global convexity
in finite dimension. -/
theorem le_of_strict_alexandrov_bounds
    {u v : E → ℝ}
    (hu : ConvexOn ℝ univ u)
    (hv : ConvexOn ℝ univ v)
    {Ω : Set E}
    (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x)
    {a b : ℝ}
    (hba : b < a)
    (hb : 0 ≤ b)
    (hMAu :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (subgradientImage u G))
    (hMAv :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        (volume : Measure E) (subgradientImage v G) ≤
          ENNReal.ofReal b * (volume : Measure E) G) :
    ∀ x ∈ Ω, u x ≤ v x := by
  have huc : Continuous u := continuousOn_univ.mp (hu.continuousOn isOpen_univ)
  have hvc : Continuous v := continuousOn_univ.mp (hv.continuousOn isOpen_univ)
  apply le_of_strict_bounds_on_support_domain hu hv huc.continuousOn hvc.continuousOn
    hΩ hΩb (subset_univ _) hboundary hba hb
  · intro G hG hGO
    simpa only [subgradientImageOn_univ] using hMAu G hG hGO
  · intro G hG hGO
    simpa only [subgradientImageOn_univ] using hMAv G hG hGO

/-- Strict Alexandrov comparison for actual DOMAIN-relative MA data. The functions
are only convex and continuous on the closure of the bounded open convex domain.
No global extension, desired support-image inclusion or comparison is assumed. -/
theorem le_of_strict_domain_alexandrov_bounds {u v : E → ℝ} {Ω : Set E} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) (hΩb : Bornology.IsBounded Ω) (hu : ConvexOn ℝ (closure Ω) u)
    (hv : ConvexOn ℝ (closure Ω) v) (huc : ContinuousOn u (closure Ω))
    (hvc : ContinuousOn v (closure Ω)) (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) {a b : ℝ}
    (hba : b < a) (hb : 0 ≤ b)
    (hMAu :
      ∀ G : Set E,
        IsOpen G →
          G ⊆ Ω → ENNReal.ofReal a * (volume : Measure E) G ≤ volume (subgradientImageOn u Ω G))
    (hMAv :
      ∀ G : Set E,
        IsOpen G →
          G ⊆ Ω →
            volume (subgradientImageOn v Ω G) ≤ ENNReal.ofReal b * (volume : Measure E) G) :
    ∀ x ∈ Ω, u x ≤ v x := by
  apply
    le_of_strict_bounds_on_support_domain ⟨hΩc.closure, hu.2⟩ hv huc hvc hΩo hΩb (Subset.rfl)
      hboundary hba hb
  · intro G hG hGO
    rw [subgradientImageOn_closure huc G]
    exact hMAu G hG hGO
  · intro G hG hGO
    rw [subgradientImageOn_closure hvc G]
    exact hMAv G hG hGO

end InnerProduct

section Dirichlet
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem bounds_of_scaled_comparisons {u v : E → ℝ} {Ω : Set E} {c d : ℝ} (hc : 0 < c)
    (hlow : ∀ e : ℝ, d < e → ∀ x ∈ Ω, e * v x ≤ u x)
    (hupp : ∀ e : ℝ, 0 < e → e < c → ∀ x ∈ Ω, u x ≤ e * v x) :
    ∀ x ∈ Ω, d * v x ≤ u x ∧ u x ≤ c * v x := by
  intro x hx
  have hden : 0 < |v x| + 1 := by positivity
  constructor
  · apply le_of_forall_pos_le_add
    intro ε hε
    let η : ℝ := ε / (|v x| + 1)
    have hη : 0 < η := div_pos hε hden
    have hcomp := hlow (d + η) (by linarith) x hx
    have hηε : η * (|v x| + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith [neg_abs_le (v x)]
  · apply le_of_forall_pos_le_add
    intro ε hε
    let η : ℝ := min (c / 2) (ε / (|v x| + 1))
    have hη : 0 < η := lt_min (half_pos hc) (div_pos hε hden)
    have hηc : η ≤ c / 2 := min_le_left _ _
    have hηε : η * (|v x| + 1) ≤ ε := (le_div_iff₀ hden).mp (min_le_right _ _)
    have hcomp := hupp (c - η) (by linarith) (by linarith) x hx
    nlinarith [neg_abs_le (v x)]

/-- Multiplicative stability relative to an actual unit-density Dirichlet solution.
The comparison function is given; no existence or Hessian regularity is asserted. -/
theorem bounds_of_alexandrov_density_bounds (hn : 0 < n) {u v : E → ℝ} (hu : ConvexOn ℝ univ u)
    (hv : ConvexOn ℝ univ v) {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu0 : ∀ x ∈ frontier Ω, u x = 0) (hv0 : ∀ x ∈ frontier Ω, v x = 0) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d)
    (hMAu :
      ∀ G : Set E,
        IsOpen G →
          G ⊆ Ω →
            ENNReal.ofReal (c ^ n) * (volume : Measure E) G ≤ volume (subgradientImage u G) ∧
              volume (subgradientImage u G) ≤ ENNReal.ofReal (d ^ n) * (volume : Measure E) G)
    (hMAv : ∀ G : Set E, IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = volume G) :
    ∀ x ∈ Ω, d * v x ≤ u x ∧ u x ≤ c * v x := by
  have hvscale (e : ℝ) (he : 0 < e) : ConvexOn ℝ univ (fun y => e * v y) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hv.smul he.le
  have hscale (e : ℝ) (he : 0 < e) (G : Set E) (hG : IsOpen G) (hGO : G ⊆ Ω) :
    volume (subgradientImage (fun y => e * v y) G) = ENNReal.ofReal (e ^ n) * volume G := by
    rw [volume_subgradientImage_mul_pos v he G, finrank_euclideanSpace_fin, hMAv G hG hGO]
  apply bounds_of_scaled_comparisons hc
  · intro e he
    have he0 : 0 < e := hd.trans he
    exact
      le_of_strict_alexandrov_bounds (hvscale e he0) hu hΩ hΩb
        (fun z hz => by rw [hv0 z hz, hu0 z hz, mul_zero]) (pow_lt_pow_left₀ he hd.le hn.ne')
        (pow_nonneg hd.le _) (fun G hG hGO => by rw [hscale e he0 G hG hGO])
        (fun G hG hGO => (hMAu G hG hGO).2)
  · intro e he hec
    exact
      le_of_strict_alexandrov_bounds hu (hvscale e he) hΩ hΩb
        (fun z hz => by rw [hu0 z hz, hv0 z hz, mul_zero]) (pow_lt_pow_left₀ hec he.le hn.ne')
        (pow_nonneg he.le _) (fun G hG hGO => (hMAu G hG hGO).1)
        (fun G hG hGO => by rw [hscale e he G hG hGO])

/-- Given DOMAIN unit-MA reference: true multiplicative Dirichlet brackets,
with convexity/continuity required only on the closure. No existence is asserted. -/
theorem bounds_of_domain_alexandrov_density_bounds (hn : 0 < n) {u v : E → ℝ} {Ω : Set E}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩb : Bornology.IsBounded Ω)
    (hu : ConvexOn ℝ (closure Ω) u) (hv : ConvexOn ℝ (closure Ω) v)
    (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v (closure Ω))
    (hu0 : ∀ x ∈ frontier Ω, u x = 0) (hv0 : ∀ x ∈ frontier Ω, v x = 0) {c d : ℝ} (hc : 0 < c)
    (hd : 0 < d)
    (hMAu :
      ∀ G : Set E,
        IsOpen G →
          G ⊆ Ω →
            ENNReal.ofReal (c ^ n) * (volume : Measure E) G ≤
                (volume : Measure E) (subgradientImageOn u Ω G) ∧
              (volume : Measure E) (subgradientImageOn u Ω G) ≤
                ENNReal.ofReal (d ^ n) * (volume : Measure E) G)
    (hMAv :
      ∀ G : Set E,
        IsOpen G →
          G ⊆ Ω → (volume : Measure E) (subgradientImageOn v Ω G) = (volume : Measure E) G) :
    ∀ x ∈ Ω, d * v x ≤ u x ∧ u x ≤ c * v x := by
  have hvscale (e : ℝ) (he : 0 < e) : ConvexOn ℝ (closure Ω) (fun y => e * v y) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hv.smul he.le
  have hscale (e : ℝ) (he : 0 < e) (G : Set E) (hG : IsOpen G) (hGO : G ⊆ Ω) :
    volume (subgradientImageOn (fun y => e * v y) Ω G) = ENNReal.ofReal (e ^ n) * volume G := by
    rw [volume_subgradientImageOn_mul_pos v he Ω G, finrank_euclideanSpace_fin, hMAv G hG hGO]
  apply bounds_of_scaled_comparisons hc
  · intro e he
    have he0 : 0 < e := hd.trans he
    exact
      le_of_strict_domain_alexandrov_bounds hΩo hΩc hΩb (hvscale e he0) hu
        (continuousOn_const.mul hvc) huc (fun z hz => by rw [hv0 z hz, hu0 z hz, mul_zero])
        (pow_lt_pow_left₀ he hd.le hn.ne') (pow_nonneg hd.le _)
        (fun G hG hGO => by rw [hscale e he0 G hG hGO]) (fun G hG hGO => (hMAu G hG hGO).2)
  · intro e he hec
    exact
      le_of_strict_domain_alexandrov_bounds hΩo hΩc hΩb hu (hvscale e he) huc
        (continuousOn_const.mul hvc) (fun z hz => by rw [hu0 z hz, hv0 z hz, mul_zero])
        (pow_lt_pow_left₀ hec he.le hn.ne') (pow_nonneg he.le _)
        (fun G hG hGO => (hMAu G hG hGO).1) (fun G hG hGO => by rw [hscale e he G hG hGO])

end Dirichlet

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
private theorem abs_sub_le_of_multiplicative_bounds {a b ε : ℝ} (hε : 0 ≤ ε)
    (hbounds : (1 + ε) * b ≤ a ∧ a ≤ (1 - ε) * b) : |a - b| ≤ ε * |b| := by
  apply abs_le.mpr
  constructor
  · nlinarith [neg_abs_le b]
  · nlinarith [le_abs_self b, neg_abs_le b]

/-- Constant-density perturbation stability from actual Alexandrov measure bounds.
No Sobolev estimate or existence of a comparison solution is asserted. -/
theorem abs_sub_le_of_alexandrov_density_close (hn : 0 < n) {u v : E → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu0 : ∀ x ∈ frontier Ω, u x = 0) (hv0 : ∀ x ∈ frontier Ω, v x = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hMAu : ∀ G : Set E, IsOpen G → G ⊆ Ω →
      ENNReal.ofReal ((1 - ε) ^ n) * (volume : Measure E) G ≤ volume (subgradientImage u G) ∧
      volume (subgradientImage u G) ≤ ENNReal.ofReal ((1 + ε) ^ n) * (volume : Measure E) G)
    (hMAv : ∀ G : Set E, IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = volume G) :
    ∀ x ∈ Ω, |u x - v x| ≤ ε * |v x| := by
  intro x hx
  exact abs_sub_le_of_multiplicative_bounds hε
    (bounds_of_alexandrov_density_bounds hn hu hv hΩ hΩb hu0 hv0
      (by linarith) (by linarith) hMAu hMAv x hx)

/-- Actual DOMAIN-relative MA closeness gives C0 stability. The reference is
only closure-convex/continuous with zero frontier; no outside extension or
requested comparison/regularity is supplied. -/
theorem abs_sub_le_of_domain_alexandrov_density_close
    (hn : 0 < n) {u v : E → ℝ}
    {Ω : Set E}
    (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hu : ConvexOn ℝ (closure Ω) u)
    (hv : ConvexOn ℝ (closure Ω) v)
    (huc : ContinuousOn u (closure Ω))
    (hvc : ContinuousOn v (closure Ω))
    (hu0 : ∀ x ∈ frontier Ω, u x = 0)
    (hv0 : ∀ x ∈ frontier Ω, v x = 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hMAu :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        ENNReal.ofReal ((1 - ε) ^ n) * (volume : Measure E) G ≤
            (volume : Measure E) (subgradientImageOn u Ω G) ∧
        (volume : Measure E) (subgradientImageOn u Ω G) ≤
            ENNReal.ofReal ((1 + ε) ^ n) * (volume : Measure E) G)
    (hMAv :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        (volume : Measure E) (subgradientImageOn v Ω G) =
          (volume : Measure E) G) :
    ∀ x ∈ Ω, |u x - v x| ≤ ε * |v x| := by
  intro x hx
  exact abs_sub_le_of_multiplicative_bounds hε
    (bounds_of_domain_alexandrov_density_bounds hn hΩo hΩc hΩb hu hv huc hvc hu0 hv0
      (by linarith) (by linarith) hMAu hMAv x hx)

section ContactPerturbation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/- Interior strictness and closure convexity give the boundary gap. This
single-use geometric assembly is private; the strict tangent proof is shared
with the actual SectionGrowth consumer in Subgradient. -/
private theorem strict_tangent_gap_of_local {u : V → ℝ} {Ω : Set V} (hΩo : IsOpen Ω)
    (hΩc : Convex ℝ Ω) (hu : ConvexOn ℝ (closure Ω) u) (hus : StrictConvexOn ℝ Ω u) {x y : V}
    (hx : x ∈ Ω) (hy : y ∈ closure Ω) (hxy : x ≠ y) (hdx : DifferentiableAt ℝ u x) :
    0 < u y - u x - ⟪gradient u x, y - x⟫ := by
  let m : V := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hxint : x ∈ interior Ω := by simpa only [hΩo.interior_eq] using hx
  have hmseg : m ∈ openSegment ℝ x y := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    rfl
  have hm : m ∈ Ω := by
    have hm' : m ∈ interior Ω := hΩc.openSegment_interior_closure_subset_interior hxint hy hmseg
    exact by simpa only [hΩo.interior_eq] using hm'
  have hmx : m - x = (1 / 2 : ℝ) • (y - x) := by
    dsimp [m]
    module
  have hxm : x ≠ m := by
    intro h
    have hz : (1 / 2 : ℝ) • (y - x) = 0 := by rw [← hmx, sub_eq_zero.mpr h.symm]
    rcases smul_eq_zero.mp hz with hz | hz
    · norm_num at hz
    · exact hxy (sub_eq_zero.mp hz).symm
  have hmid : 0 < u m - u x - ⟪gradient u x, m - x⟫ :=
    gradient_tangent_gap_pos_of_strictConvexOn hus hx hm hxm hdx
  have hconv : u m ≤ (1 / 2 : ℝ) * u x + (1 / 2 : ℝ) * u y := by
    have h :=
      hu.2 (subset_closure hx) hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    simpa [m] using h
  have hmid' : 0 < u m - u x - (1 / 2 : ℝ) * ⟪gradient u x, y - x⟫ := by simpa [hmx] using hmid
  linarith

/- The two public reference classes below produce this helper's actual gap;
no public source interface assumes the desired contact or tangent gap. -/
private theorem exists_contact_of_uniform_close_of_tangent_gap {v : V → ℝ} {Ω K : Set V}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hvc : ContinuousOn v (closure Ω))
    (hvg : ContinuousOn (gradient v) K)
    (hgap_pos : ∀ z ∈ K, ∀ y ∈ frontier Ω, 0 < v y - v z - ⟪gradient v z, y - z⟫)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ (w : V → ℝ),
          ContinuousOn w (closure Ω) →
            DifferentiableOn ℝ w Ω →
              (∀ y ∈ closure Ω, |w y - v y| ≤ ε) →
                ∀ z ∈ K,
                  ∃ x ∈ Ω,
                    gradient w x = gradient v z ∧
                      ∀ y ∈ closure Ω, w x + ⟪gradient v z, y - x⟫ ≤ w y := by
  classical
  let A : Set (V × V) := K ×ˢ frontier Ω
  let F : V × V → ℝ := fun p => v p.2 - v p.1 - ⟪gradient v p.1, p.2 - p.1⟫
  have hcl : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hfront : IsCompact (frontier Ω) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hAc : IsCompact A := hK.prod hfront
  have hF : ContinuousOn F A := by
    have hsecond : ContinuousOn (fun p : V × V => v p.2) A :=
      hvc.comp continuousOn_snd (fun p hp => frontier_subset_closure hp.2)
    have hfirst : ContinuousOn (fun p : V × V => v p.1) A :=
      hvc.comp continuousOn_fst (fun p hp => subset_closure (hKΩ hp.1))
    have hgradient : ContinuousOn (fun p : V × V => gradient v p.1) A :=
      hvg.comp continuousOn_fst (fun _p hp => hp.1)
    have hdiff : ContinuousOn (fun p : V × V => p.2 - p.1) A :=
      continuousOn_snd.sub continuousOn_fst
    have hinner : ContinuousOn (fun p : V × V => ⟪gradient v p.1, p.2 - p.1⟫) A :=
      hgradient.inner hdiff
    exact (hsecond.sub hfirst).sub hinner
  have hFp : ∀ p ∈ A, 0 < F p := by
    rintro ⟨z, y⟩ ⟨hz, hy⟩
    exact hgap_pos z hz y hy
  obtain ⟨ρ, hρ, hgap⟩ := hAc.exists_forall_le' hF hFp
  refine ⟨ρ / 4, by positivity, ?_⟩
  intro w hwc hwD hw z hz
  let p : V := gradient v z
  let Ψ : V → ℝ := fun y => w y - ⟪p, y⟫
  have hΨc : ContinuousOn Ψ (closure Ω) := by
    dsimp [Ψ]
    exact hwc.sub (continuousOn_const.inner continuousOn_id)
  have hzcl : z ∈ closure Ω := subset_closure (hKΩ hz)
  have hstrict : ∀ y ∈ frontier Ω, Ψ z < Ψ y := by
    intro y hy
    have hycl : y ∈ closure Ω := frontier_subset_closure hy
    have hwy := abs_le.mp (hw y hycl)
    have hwz := abs_le.mp (hw z hzcl)
    have hg := hgap (z, y) ⟨hz, hy⟩
    dsimp only [F] at hg
    dsimp [Ψ, p] at *
    rw [inner_sub_right] at hg
    linarith
  obtain ⟨x, hxΩ, hmin⟩ :=
    hcl.exists_isMinOn_mem_subset (s := Ω) hΨc hzcl
      (fun y hy => hstrict y (by rw [hΩo.frontier_eq]; exact hy))
  have hxcl : x ∈ closure Ω := subset_closure hxΩ
  have hlocal : IsLocalMin Ψ x :=
    hmin.isLocalMin (Filter.mem_of_superset (hΩo.mem_nhds hxΩ) subset_closure)
  have hwd : DifferentiableAt ℝ w x := (hwD x hxΩ).differentiableAt (hΩo.mem_nhds hxΩ)
  have hlin : HasFDerivAt (fun y : V => ⟪p, y⟫) (InnerProductSpace.toDual ℝ V p) x :=
    (InnerProductSpace.toDual ℝ V p).hasFDerivAt
  have hzero := hlocal.hasFDerivAt_eq_zero (hwd.hasGradientAt.hasFDerivAt.sub hlin)
  have hgrad : gradient w x = p := by
    have hh := DFunLike.congr_fun hzero (gradient w x - p)
    change ⟪gradient w x, gradient w x - p⟫ - ⟪p, gradient w x - p⟫ = 0 at hh
    have hh' : ⟪gradient w x - p, gradient w x - p⟫ = 0 := by
      rw [inner_sub_left]
      exact hh
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hh')
  refine ⟨x, hxΩ, hgrad, ?_⟩
  intro y hy
  have hminxy := hmin hy
  change w x - ⟪gradient v z, x⟫ ≤ w y - ⟪gradient v z, y⟫ at hminxy
  rw [inner_sub_right]
  linarith

/-- Local reference regularity and interior strictness produce real supporting
contacts for uniformly close perturbations. Strictness is required only on the
open domain, convexity and continuity on its closure. The perturbation need not
be convex and needs differentiability only on the open domain; epsilon precedes
it. No global extension or contact/gap conclusion is an input. -/
theorem exists_contact_of_uniform_close_on_open
    {v : V → ℝ}
    {Ω K : Set V}
    (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hv : ConvexOn ℝ (closure Ω) v)
    (hvs : StrictConvexOn ℝ Ω v)
    (hvc : ContinuousOn v (closure Ω))
    (hvC1 : ContDiffOn ℝ 1 v Ω)
    (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (w : V → ℝ), ContinuousOn w (closure Ω) →
        DifferentiableOn ℝ w Ω →
        (∀ y ∈ closure Ω, |w y - v y| ≤ ε) →
        ∀ z ∈ K,
          ∃ x ∈ Ω, gradient w x = gradient v z ∧
            ∀ y ∈ closure Ω,
              w x + ⟪gradient v z, y - x⟫ ≤ w y := by
  have hgrad : ContinuousOn (gradient v) Ω :=
    (BakryEmery.contDiffOn_gradient hΩo hvC1
      (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  apply exists_contact_of_uniform_close_of_tangent_gap hΩo hΩb hvc
    (hgrad.mono hKΩ) _ hK hKΩ
  intro z hz y hy
  have hzy : z ≠ y := by
    intro hzy
    rw [hΩo.frontier_eq] at hy
    exact hy.2 (hzy ▸ hKΩ hz)
  have hdz : DifferentiableAt ℝ v z :=
    ((hvC1.differentiableOn one_ne_zero) z (hKΩ hz)).differentiableAt
      (hΩo.mem_nhds (hKΩ hz))
  exact strict_tangent_gap_of_local hΩo hvs.1 hv hvs (hKΩ hz)
    (frontier_subset_closure hy) hzy hdz

/-- Uniformly close global-C1 perturbations realize actual supporting contacts
on any bounded open working domain, including nonconvex domains. This original
interface shares the local compact-gap/minimum proof while global reference
strictness supplies its actual gap independently of the domain geometry. -/
private theorem exists_contact_of_uniform_close_of_global_reference {v : V → ℝ}
    (hv : StrictConvexOn ℝ univ v) (hC1 : ContDiff ℝ 1 v)
    {Ω K : Set V} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (w : V → ℝ), ContinuousOn w (closure Ω) →
      DifferentiableOn ℝ w Ω →
      (∀ y ∈ closure Ω, |w y - v y| ≤ ε) → ∀ z ∈ K,
        ∃ x ∈ Ω, gradient w x = gradient v z ∧
          ∀ y ∈ closure Ω, w x + ⟪gradient v z, y - x⟫ ≤ w y := by
  exact exists_contact_of_uniform_close_of_tangent_gap hΩo hΩb
    hC1.continuous.continuousOn (BakryEmery.continuous_gradient hC1).continuousOn
    (by
      intro z hz y hy
      have hzy : z ≠ y := by
        intro hzy
        rw [hΩo.frontier_eq] at hy
        exact hy.2 (hzy ▸ hKΩ hz)
      exact gradient_tangent_gap_pos (hC1.differentiable one_ne_zero) hv hzy)
    hK hKΩ

/-- Uniformly close global-C1 perturbations have actual supporting contacts on
any bounded open working domain, including nonconvex domains. -/
theorem exists_contact_of_uniform_close {v : V → ℝ}
    (hv : StrictConvexOn ℝ univ v) (hC1 : ContDiff ℝ 1 v)
    {Ω K : Set V} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (w : V → ℝ), ContDiff ℝ 1 w →
      (∀ y ∈ closure Ω, |w y - v y| ≤ ε) → ∀ z ∈ K,
        ∃ x ∈ Ω, gradient w x = gradient v z ∧
          ∀ y ∈ closure Ω, w x + ⟪gradient v z, y - x⟫ ≤ w y := by
  obtain ⟨ε, hε, hcontact⟩ := exists_contact_of_uniform_close_of_global_reference
    hv hC1 hΩo hΩb hK hKΩ
  refine ⟨ε, hε, ?_⟩
  intro w hwC1 hw
  exact hcontact w hwC1.continuous.continuousOn
    (hwC1.differentiable one_ne_zero).differentiableOn hw

end ContactPerturbation


private theorem strictConvex_mul_pos {V : Type*} [AddCommGroup V] [Module ℝ V]
    {v : V → ℝ} {S : Set V} (hv : StrictConvexOn ℝ S v) {δ : ℝ} (hδ : 0 < δ) :
    StrictConvexOn ℝ S (fun x => δ * v x) := by
  refine ⟨hv.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h := hv.2 hx hy hxy ha hb hab
  change δ * v (a • x + b • y) < a * (δ * v x) + b * (δ * v y)
  calc
    _ < δ * (a * v x + b * v y) := mul_lt_mul_of_pos_left h hδ
    _ = _ := by ring

private theorem gradient_mul_scalar {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {v : V → ℝ}
    (c : ℝ) (x : V) (hv : DifferentiableAt ℝ v x) :
    gradient (fun y => c * v y) x = c • gradient v x := by
  simpa only [gradient_fun_const, smul_zero, add_zero] using
    (BakryEmery.gradient_mul (differentiableAt_const c) hv)

private theorem exists_residual_contact_from_comparison {n : ℕ}
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {Ω K : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hvc : ContinuousOn v (closure Ω))
    (hvD : DifferentiableOn ℝ v Ω) (hv0 : ∀ x ∈ frontier Ω, v x = 0) (hKΩ : K ⊆ Ω) {δ τ : ℝ}
    (hτ : 0 < τ)
    (hcontact :
      ∀ w : EuclideanSpace ℝ (Fin n) → ℝ,
        ContinuousOn w (closure Ω) →
          DifferentiableOn ℝ w Ω →
            (∀ y ∈ closure Ω, |w y - δ * v y| ≤ τ) →
              ∀ z ∈ K,
                ∃ x ∈ Ω,
                  gradient w x = gradient (fun y => δ * v y) z ∧
                    ∀ y ∈ closure Ω, w x + ⟪gradient (fun y => δ * v y) z, y - x⟫ ≤ w y)
    (hcompare :
      ∀ ε : ℝ,
        0 < ε →
          ε < 1 →
            ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
              ConvexOn ℝ univ u →
                ContDiff ℝ 1 u →
                  (∀ x ∈ frontier Ω, u x = 0) →
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G →
                          G ⊆ Ω →
                            ENNReal.ofReal ((1 - ε) ^ n) * volume G ≤
                                volume (subgradientImage u G) ∧
                              volume (subgradientImage u G) ≤
                                ENNReal.ofReal ((1 + ε) ^ n) * volume G) →
                      ∀ y ∈ Ω, |u y - v y| ≤ ε * |v y|) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < 1 ∧
          ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ),
            ConvexOn ℝ univ u →
              ContDiff ℝ 1 u →
                (∀ x ∈ frontier Ω, u x = 0) →
                  (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                      IsOpen G →
                        G ⊆ Ω →
                          ENNReal.ofReal ((1 - ε) ^ n) * volume G ≤
                              volume (subgradientImage u G) ∧
                            volume (subgradientImage u G) ≤
                              ENNReal.ofReal ((1 + ε) ^ n) * volume G) →
                    ∀ z ∈ K,
                      ∃ x ∈ Ω,
                        gradient u x - (1 - δ) • gradient v x = δ • gradient v z ∧
                          ∀ y ∈ closure Ω,
                            u x - (1 - δ) * v x + ⟪δ • gradient v z, y - x⟫ ≤
                              u y - (1 - δ) * v y := by
  obtain ⟨B, hB⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn hvc
  let M : ℝ := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hvM : ∀ x ∈ closure Ω, |v x| ≤ M := by
    intro x hx
    exact
      (show |v x| ≤ B by simpa only [Real.norm_eq_abs] using hB x hx).trans (le_max_left _ _)
  have hMpos : 0 < M + 1 := by positivity
  let ε : ℝ := min (1 / 2) (τ / (M + 1))
  have hε : 0 < ε := by exact lt_min (by norm_num) (div_pos hτ hMpos)
  have hε1 : ε < 1 := by exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hετ : ε * (M + 1) ≤ τ := by exact (le_div_iff₀ hMpos).mp (min_le_right _ _)
  refine ⟨ε, hε, hε1, ?_⟩
  intro u hu huC1 hu0 hMAu z hz
  have huc : ContinuousOn u (closure Ω) := huC1.continuous.continuousOn
  have hclose := hcompare ε hε hε1 u hu huC1 hu0 hMAu
  have hbound : ∀ y ∈ closure Ω, |u y - v y| ≤ τ := by
    intro y hy
    have hsmall : |u y - v y| ≤ ε * |v y| := by
      by_cases hyΩ : y ∈ Ω
      · exact hclose y hyΩ
      · have hyf : y ∈ frontier Ω := by
          rw [hΩo.frontier_eq]
          exact ⟨hy, hyΩ⟩
        rw [hu0 y hyf, hv0 y hyf]
        simp
    calc
      |u y - v y| ≤ ε * |v y| := hsmall
      _ ≤ ε * M := mul_le_mul_of_nonneg_left (hvM y hy) hε.le
      _ ≤ ε * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ ≤ τ := hετ
  have hresC : ContinuousOn (fun y => u y - (1 - δ) * v y) (closure Ω) := by
    exact huc.sub (continuousOn_const.mul hvc)
  have hresD : DifferentiableOn ℝ (fun y => u y - (1 - δ) * v y) Ω := by
    intro x hx
    have hux : DifferentiableAt ℝ u x := huC1.differentiable one_ne_zero x
    have hvx : DifferentiableAt ℝ v x := (hvD x hx).differentiableAt (hΩo.mem_nhds hx)
    exact (hux.sub (hvx.const_mul (1 - δ))).differentiableWithinAt
  obtain ⟨x, hx, hgrad, hsupport⟩ :=
    hcontact (fun y => u y - (1 - δ) * v y) hresC hresD
      (by
        intro y hy
        have heq : u y - (1 - δ) * v y - δ * v y = u y - v y := by ring
        rw [heq]
        exact hbound y hy)
      z hz
  have huvx : DifferentiableAt ℝ u x := huC1.differentiable one_ne_zero x
  have hvx : DifferentiableAt ℝ v x := (hvD x hx).differentiableAt (hΩo.mem_nhds hx)
  have hvz : DifferentiableAt ℝ v z := (hvD z (hKΩ hz)).differentiableAt (hΩo.mem_nhds (hKΩ hz))
  have hmulx := gradient_mul_scalar (1 - δ) x hvx
  have hmulz := gradient_mul_scalar δ z hvz
  refine ⟨x, hx, ?_, ?_⟩
  · have h := hgrad
    rw [BakryEmery.gradient_sub huvx (hvx.const_mul (1 - δ)), hmulx, hmulz] at h
    exact h
  · simpa only [hmulz] using hsupport


/-- Actual density comparison yields interior supporting contacts for the
residual `u - (1 - δ) v`, uniformly on a fixed compact set of reference slopes.
The unit-density Dirichlet reference is given with its actual Alexandrov equation.
This theorem does not assert its existence, a contact-measure gain, Hessian
bounds, or Sobolev regularity. -/
theorem exists_residual_contact_of_alexandrov_density_close {n : ℕ} (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv : StrictConvexOn ℝ univ v)
    (hvC1 : ContDiff ℝ 1 v) {Ω K : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hv0 : ∀ x ∈ frontier Ω, v x = 0)
    (hMAv : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      volume (subgradientImage v G) = volume G)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ), ConvexOn ℝ univ u → ContDiff ℝ 1 u →
        (∀ x ∈ frontier Ω, u x = 0) →
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
          ENNReal.ofReal ((1 - ε) ^ n) * volume G ≤ volume (subgradientImage u G) ∧
          volume (subgradientImage u G) ≤ ENNReal.ofReal ((1 + ε) ^ n) * volume G) →
        ∀ z ∈ K, ∃ x ∈ Ω,
          gradient u x - (1 - δ) • gradient v x = δ • gradient v z ∧
          ∀ y ∈ closure Ω,
            u x - (1 - δ) * v x + ⟪δ • gradient v z, y - x⟫ ≤
              u y - (1 - δ) * v y := by
  obtain ⟨τ, hτ, hcontact⟩ := exists_contact_of_uniform_close_of_global_reference
    (strictConvex_mul_pos hv hδ) (contDiff_const.mul hvC1) hΩo hΩb hK hKΩ
  apply exists_residual_contact_from_comparison hΩo hΩb hvC1.continuous.continuousOn
    (hvC1.differentiable one_ne_zero).differentiableOn hv0 hKΩ hτ hcontact
  intro ε hε hε1 u hu _huC1 hu0 hMAu
  exact abs_sub_le_of_alexandrov_density_close hn hu hv.convexOn hΩo hΩb hu0 hv0
    hε.le hε1 hMAu hMAv

/-- Actual domain-relative MA comparison and a locally C1, interior-strict
zero-boundary reference produce residual supporting contacts on the entire
closure. The tolerance precedes every unknown solution. The reference need not
extend convexly or smoothly outside the domain; delta need only be positive.
This given-reference result does not construct a Dirichlet solution or W2p. -/
theorem exists_residual_contact_of_domain_alexandrov_density_close
    {n : ℕ} (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {Ω K : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (hv : ConvexOn ℝ (closure Ω) v)
    (hvs : StrictConvexOn ℝ Ω v)
    (hvc : ContinuousOn v (closure Ω))
    (hvC1 : ContDiffOn ℝ 1 v Ω)
    (hv0 : ∀ x ∈ frontier Ω, v x = 0)
    (hMAv :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (subgradientImageOn v Ω G) =
          (volume : Measure (EuclideanSpace ℝ (Fin n))) G)
    (hK : IsCompact K)
    (hKΩ : K ⊆ Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ),
        ConvexOn ℝ univ u →
        ContDiff ℝ 1 u →
        (∀ x ∈ frontier Ω, u x = 0) →
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
          ENNReal.ofReal ((1 - ε) ^ n) *
              (volume : Measure (EuclideanSpace ℝ (Fin n))) G ≤
            (volume : Measure (EuclideanSpace ℝ (Fin n)))
              (subgradientImage u G) ∧
          (volume : Measure (EuclideanSpace ℝ (Fin n)))
              (subgradientImage u G) ≤
            ENNReal.ofReal ((1 + ε) ^ n) *
              (volume : Measure (EuclideanSpace ℝ (Fin n))) G) →
        ∀ z ∈ K, ∃ x ∈ Ω,
          gradient u x - (1 - δ) • gradient v x =
              δ • gradient v z ∧
          ∀ y ∈ closure Ω,
            u x - (1 - δ) * v x +
                ⟪δ • gradient v z, y - x⟫ ≤
              u y - (1 - δ) * v y := by
  obtain ⟨τ, hτ, hcontact⟩ := exists_contact_of_uniform_close_on_open
    hΩo hΩb (by simpa only [Pi.smul_apply, smul_eq_mul] using hv.smul hδ.le)
    (strictConvex_mul_pos hvs hδ) (continuousOn_const.mul hvc)
    (contDiffOn_const.mul hvC1) hK hKΩ
  apply exists_residual_contact_from_comparison hΩo hΩb hvc
    (hvC1.differentiableOn one_ne_zero) hv0 hKΩ hτ hcontact
  intro ε hε hε1 u hu huC1 hu0 hMAu
  apply abs_sub_le_of_domain_alexandrov_density_close hn hΩo hvs.1 hΩb
    (hu.subset (subset_univ _) hvs.1.closure) hv huC1.continuous.continuousOn hvc
    hu0 hv0 hε.le hε1 _ hMAv
  intro G hG hGΩ
  rw [subgradientImageOn_eq_subgradientImage hu hΩo
    (huC1.differentiable one_ne_zero).differentiableOn hGΩ]
  exact hMAu G hG hGΩ


section DomainBoundaryComparison

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [MeasurableSpace F] [BorelSpace F]

/-- A constant reference has genuinely zero domain MA on every subset of an
open domain. Its supporting image is contained in a Haar-null singleton. -/
theorem volume_subgradientImageOn_const (c : ℝ) {Ω G : Set F}
    (hΩ : IsOpen Ω) (hG : G ⊆ Ω) :
    (volume : Measure F) (subgradientImageOn (fun _ : F => c) Ω G) = 0 := by
  apply le_antisymm _ (zero_le)
  calc
    (volume : Measure F) (subgradientImageOn (fun _ : F => c) Ω G)
        ≤ volume ({0} : Set F) :=
      measure_mono (subgradientImageOn_const_subset_singleton c hΩ hG)
    _ = 0 := measure_singleton 0

/-- Positive actual domain MA lower density and nonpositive boundary data
force nonpositivity inside the domain. No differentiability or global extension
of the unknown function is used. -/
theorem nonpos_of_pos_domain_alexandrov_lower
    {u : F → ℝ} {Ω : Set F} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ConvexOn ℝ (closure Ω) u)
    (huc : ContinuousOn u (closure Ω))
    (hfr : ∀ x ∈ frontier Ω, u x ≤ 0)
    {a : ℝ} (ha : 0 < a)
    (hMA : ∀ H : Set F, IsOpen H → H ⊆ Ω →
      ENNReal.ofReal a * (volume : Measure F) H ≤
        volume (subgradientImageOn u Ω H)) :
    ∀ x ∈ Ω, u x ≤ 0 := by
  apply le_of_strict_domain_alexandrov_bounds hΩ hΩconv hb hu
    (convexOn_const 0 hΩconv.closure) huc continuousOn_const hfr ha (le_refl 0) hMA
  intro H _hH hH
  rw [volume_subgradientImageOn_const 0 hΩ hH]
  simp

/-- A common absolute boundary modulus for zero-boundary domain MA solutions.
The radius precedes every unknown function. The upper side follows from genuine
positive-density comparison with a constant reference; the lower side follows
from the domain maximum principle and the actual density upper bound. -/
theorem exists_common_boundary_modulus_domain
    {Ω : Set F} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {a Λ : ℝ} (ha : 0 < a) (hΛ : 0 ≤ Λ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : F → ℝ,
      ConvexOn ℝ (closure Ω) u → ContinuousOn u (closure Ω) →
      (∀ x ∈ frontier Ω, u x = 0) →
      (∀ H : Set F, IsOpen H → H ⊆ Ω →
        ENNReal.ofReal a * (volume : Measure F) H ≤
          volume (subgradientImageOn u Ω H)) →
      (∀ H : Set F, IsOpen H → H ⊆ Ω →
        volume (subgradientImageOn u Ω H) ≤
          ENNReal.ofReal Λ * (volume : Measure F) H) →
      ∀ x ∈ Ω, Metric.infDist x (frontier Ω) < ρ → |u x| ≤ ε := by
  obtain ⟨ρ, hρ, hlower⟩ :=
    exists_common_lower_boundary_modulus_domain hΩ hΩconv hb hΛ hε
  refine ⟨ρ, hρ, ?_⟩
  intro u hu huc hfr hMAl hMAu x hx hdist
  have hn := nonpos_of_pos_domain_alexandrov_lower hΩ hΩconv hb hu huc
    (fun y hy => (hfr y hy).le) ha hMAl x hx
  have hl := hlower u hu huc (fun y hy => (hfr y hy).ge) hMAu x hx hdist
  rw [abs_of_nonpos hn]
  linarith

end DomainBoundaryComparison

end FunctionalInequalities.Analysis
