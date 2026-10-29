import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The frontier of a convex set as a local Lipschitz graph

Let `K` be a convex set in a real inner product space with a ball `ball c r ⊆ interior K`, and let
`x₀ ∈ K \ interior K`. With `τ = ‖x₀ − c‖` and the unit vector `θ = (x₀ − c)/τ`, every point
`x ∉ interior K` with `‖x − x₀‖ < r` sees `K` only behind it: `x + tθ ∉ K` for `t > 0`
(`add_smul_notMem_of_sub_smul_mem_interior`), and on `ball x₀ (r/2)` the set `K \ interior K`
is a Lipschitz graph over `θ^⊥`: `‖x − y‖ ≤ (1 + 2τ/r) ‖P(x − y)‖` with `P v = v − ⟪v, θ⟫θ`
(`norm_sub_le_mul_transversal`). These are properties (23) and (24) in the proof of
Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Proposition 10.

`hausdorffMeasure_mul_le_of_graph` is the volume count (32) of that proof: if `B` is a
`C`-Lipschitz graph over `θ^⊥` and a measurable `T` contains all segments `x + (0, ε]θ`, `x ∈ B`,
then `H^{n−1}(B) · ε ≤ M · dx(T)` for a Haar measure `dx` and a constant `M` depending only on `θ`,
`C` and `dx` (Fubini along `θ`, and the Lipschitz inverse of the projection of `B`).
`exists_convex_frontier_chart` packages both facts around a point of `K \ interior K`.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

open MeasureTheory Set Metric Filter Module
open scoped ENNReal NNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Points beyond a non-interior point leave a convex set** (CEK arXiv:1304.0630v1, (23)):
if `x ∉ interior K` and `x − τθ ∈ interior K` with `τ > 0`, then `x + tθ ∉ K` for every `t > 0`,
since otherwise `x` lies on the open segment from an interior point to a point of `K`. -/
theorem add_smul_notMem_of_sub_smul_mem_interior {K : Set E} (hK : Convex ℝ K)
    {x θ : E} {τ t : ℝ} (hx : x ∉ interior K) (hτ : 0 < τ) (hin : x - τ • θ ∈ interior K)
    (ht : 0 < t) : x + t • θ ∉ K := by
  intro hmem
  apply hx
  apply hK.openSegment_interior_self_subset_interior hin hmem
  have hτt : τ + t ≠ 0 := by positivity
  refine ⟨t / (τ + t), τ / (τ + t), by positivity, by positivity, by field_simp; ring, ?_⟩
  match_scalars <;> field_simp <;> ring

/-- One-sided slope bound behind (24) in CEK arXiv:1304.0630v1: if `y ∈ K` lies above
`x ∉ interior K` in direction `θ` (`a = ⟪y − x, θ⟫ > 0`) near `x₀`, the transversal part of
`y − x` is at least `r a / (2τ)`. -/
private theorem slope_bound {K : Set E} (hK : Convex ℝ K) {θ x₀ x y : E} {τ r : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (hball : ball (x₀ - τ • θ) r ⊆ interior K)
    (hx : x ∉ interior K) (hy : y ∈ K) (hxb : ‖x - x₀‖ < r / 2) (ha : 0 < ⟪y - x, θ⟫) :
    r / (2 * τ) * ⟪y - x, θ⟫ ≤ ‖(y - x) - ⟪y - x, θ⟫ • θ‖ := by
  set a := ⟪y - x, θ⟫ with hadef
  set w := (y - x) - a • θ with hwdef
  by_contra hlt
  push Not at hlt
  apply hx
  set q := x - (τ / a) • (y - x) with hqdef
  have hq : q ∈ interior K := by
    apply hball
    rw [mem_ball, dist_eq_norm]
    have hqe : q - (x₀ - τ • θ) = (x - x₀) - (τ / a) • w := by
      rw [hqdef, hwdef]
      match_scalars <;> field_simp
    rw [hqe]
    calc ‖(x - x₀) - (τ / a) • w‖ ≤ ‖x - x₀‖ + ‖(τ / a) • w‖ := norm_sub_le _ _
      _ = ‖x - x₀‖ + τ / a * ‖w‖ := by
          rw [norm_smul, Real.norm_of_nonneg (div_nonneg hτ.le ha.le)]
      _ < r / 2 + τ / a * (r / (2 * τ) * a) := by
          gcongr
      _ = r := by field_simp; ring
  apply hK.openSegment_interior_self_subset_interior hq hy
  have hτa : τ + a ≠ 0 := by positivity
  refine ⟨a / (τ + a), τ / (τ + a), by positivity, by positivity, by field_simp; ring, ?_⟩
  rw [hqdef]
  match_scalars <;> field_simp <;> ring

/-- **The frontier of a convex set is a local Lipschitz graph** (CEK arXiv:1304.0630v1, (24)): if
`ball (x₀ − τθ) r ⊆ interior K` with `‖θ‖ = 1`, `τ, r > 0`, then for `x, y ∈ K \ interior K` in
`ball x₀ (r/2)`, `‖x − y‖ ≤ (1 + 2τ/r) ‖(x − y) − ⟪x − y, θ⟫θ‖`. -/
theorem norm_sub_le_mul_transversal {K : Set E} (hK : Convex ℝ K) {θ x₀ x y : E}
    {τ r : ℝ} (hθ : ‖θ‖ = 1) (hτ : 0 < τ) (hr : 0 < r)
    (hball : ball (x₀ - τ • θ) r ⊆ interior K) (hx : x ∈ K \ interior K)
    (hy : y ∈ K \ interior K) (hxb : ‖x - x₀‖ < r / 2) (hyb : ‖y - x₀‖ < r / 2) :
    ‖x - y‖ ≤ (1 + 2 * τ / r) * ‖(x - y) - ⟪x - y, θ⟫ • θ‖ := by
  set a := ⟪x - y, θ⟫ with hadef
  set w := (x - y) - a • θ with hwdef
  have hk : 0 < r / (2 * τ) := by positivity
  -- `r/(2τ) |a| ≤ ‖w‖`
  have habs : r / (2 * τ) * |a| ≤ ‖w‖ := by
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · have hyx : ⟪y - x, θ⟫ = -a := by rw [hadef, ← inner_neg_left, neg_sub]
      have h := slope_bound hK hτ hr hball hx.2 hy.1 hxb (by rw [hyx]; linarith)
      have hw : (y - x) - ⟪y - x, θ⟫ • θ = -w := by
        rw [hyx, hwdef, neg_smul, sub_neg_eq_add, neg_sub, ← neg_sub x y]
        abel
      rw [hw, norm_neg, hyx] at h
      rwa [abs_of_neg hneg]
    · rw [hzero, abs_zero, mul_zero]
      exact norm_nonneg _
    · have h := slope_bound hK hτ hr hball hy.2 hx.1 hyb hpos
      rwa [abs_of_pos hpos]
  have hdecomp : x - y = a • θ + w := by rw [hwdef]; abel
  calc ‖x - y‖ = ‖a • θ + w‖ := by rw [hdecomp]
    _ ≤ |a| + ‖w‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, hθ, mul_one, Real.norm_eq_abs]
    _ ≤ 2 * τ / r * ‖w‖ + ‖w‖ := by
        gcongr
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        have := mul_le_mul_of_nonneg_left habs (by positivity : (0 : ℝ) ≤ 2 * τ)
        rw [← mul_assoc, show 2 * τ * (r / (2 * τ)) = r by field_simp] at this
        linarith
    _ = (1 + 2 * τ / r) * ‖w‖ := by ring

section Measure

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Volume of the segments above a Lipschitz graph** (CEK arXiv:1304.0630v1, (32)): fix a unit
vector `θ`, a constant `C` and an additive Haar measure `dx`. There is `M < ∞` such that, whenever
`B` is a `C`-Lipschitz graph over `θ^⊥`, i.e. `‖x − y‖ ≤ C ‖(x − y) − ⟪x − y, θ⟫θ‖` on `B`, and a
measurable `T` contains every segment `{x + tθ : 0 < t ≤ ε}` with `x ∈ B`, then
`H^{n−1}(B) · ε ≤ M · dx(T)`, where `n = dim E`. Proof: in linear coordinates `E ≅ ℝ^{n−1} × ℝ`
with second coordinate `⟪θ, ·⟫`, Fubini gives `dx(T) ≥ s ε λ^{n−1}(Φ B)` for the first coordinate
`Φ`, and `Φ` has a Lipschitz inverse on `B`, so `H^{n−1}(B) ≤ K^{n−1} λ^{n−1}(Φ B)`. -/
theorem hausdorffMeasure_mul_le_of_graph (dx : Measure E) [dx.IsAddHaarMeasure] {θ : E}
    (hθ : ‖θ‖ = 1) (C : ℝ≥0) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ B : Set E,
      (∀ x ∈ B, ∀ y ∈ B, ‖x - y‖ ≤ C * ‖(x - y) - ⟪x - y, θ⟫ • θ‖) →
      ∀ ε : ℝ, 0 < ε → ∀ T : Set E, MeasurableSet T →
        (∀ x ∈ B, ∀ t ∈ Ioc (0 : ℝ) ε, x + t • θ ∈ T) →
        μH[(finrank ℝ E : ℝ) - 1] B * ENNReal.ofReal ε ≤ M * dx T := by
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hθ
    exact zero_ne_one hθ
  have hn : 1 ≤ finrank ℝ E := by
    have : Nontrivial E := nontrivial_of_ne θ 0 hθ0
    exact Module.finrank_pos
  set n := finrank ℝ E with hndef
  set m := n - 1 with hmdef
  let N : Submodule ℝ E := ℝ ∙ θ
  have hQ : finrank ℝ (E ⧸ N) = finrank ℝ (Fin m → ℝ) := by
    have h1 := Submodule.finrank_quotient_add_finrank N
    rw [finrank_span_singleton hθ0] at h1
    rw [Module.finrank_fin_fun]
    omega
  let e : (E ⧸ N) ≃ₗ[ℝ] (Fin m → ℝ) := LinearEquiv.ofFinrankEq _ _ hQ
  let Φ : E →ₗ[ℝ] (Fin m → ℝ) := e.toLinearMap ∘ₗ N.mkQ
  have hΦθ : Φ θ = 0 := by
    simp only [Φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.mem_span_singleton_self θ), map_zero]
  have hθθ : ⟪θ, θ⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hθ, one_pow]
  let L : E →ₗ[ℝ] (Fin m → ℝ) × ℝ := Φ.prod (innerₛₗ ℝ θ)
  have hL : ∀ x, L x = (Φ x, ⟪θ, x⟫) := fun x => rfl
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr fun x hx => ?_
    rw [hL, Prod.mk_eq_zero] at hx
    have hmem : x ∈ N := by
      have h0 : N.mkQ x = 0 := e.injective (by rw [map_zero]; exact hx.1)
      exact (Submodule.Quotient.mk_eq_zero N).mp h0
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    have h2 := hx.2
    rw [inner_smul_right, hθθ, mul_one] at h2
    rw [h2, zero_smul]
  have hdim : finrank ℝ E = finrank ℝ ((Fin m → ℝ) × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
    omega
  let Lc : E ≃L[ℝ] (Fin m → ℝ) × ℝ := (L.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hLc : ∀ x, Lc x = (Φ x, ⟪θ, x⟫) := fun x => rfl
  have hseg : ∀ x : E, ∀ t : ℝ, Lc (x + t • θ) = (Φ x, ⟪θ, x⟫ + t) := by
    intro x t
    rw [hLc, map_add, map_smul, hΦθ, smul_zero, add_zero, inner_add_right, inner_smul_right, hθθ,
      mul_one]
  have hproj : ∀ v : E, Lc (v - ⟪v, θ⟫ • θ) = (Φ v, 0) := by
    intro v
    rw [hLc, map_sub, map_smul, hΦθ, smul_zero, sub_zero, inner_sub_right, inner_smul_right, hθθ,
      mul_one, real_inner_comm, sub_self]
  -- the transversal part is controlled by the first coordinate
  set Ks : ℝ≥0 := ‖(Lc.symm : (Fin m → ℝ) × ℝ →L[ℝ] E)‖₊ with hKs
  have hPΦ : ∀ v : E, ‖v - ⟪v, θ⟫ • θ‖ ≤ Ks * ‖Φ v‖ := by
    intro v
    have h1 : v - ⟪v, θ⟫ • θ = (Lc.symm : (Fin m → ℝ) × ℝ →L[ℝ] E) (Φ v, 0) := by
      rw [← hproj]
      simp
    rw [h1]
    refine ((Lc.symm : (Fin m → ℝ) × ℝ →L[ℝ] E).le_opNorm _).trans_eq ?_
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _), hKs, coe_nnnorm]
  -- the Haar measure in the new coordinates
  set ν : Measure ((Fin m → ℝ) × ℝ) := dx.map Lc with hν
  set leb : Measure ((Fin m → ℝ) × ℝ) := (volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)
    with hleb
  set s : ℝ≥0 := Measure.addHaarScalarFactor ν leb with hs
  have hs0 : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν leb
  have hνeq : ν = s • leb := Measure.isAddLeftInvariant_eq_smul ν leb
  set K' : ℝ≥0 := C * Ks with hK'
  set d : ℝ := (Fintype.card (Fin m) : ℝ) with hd
  have hd' : (finrank ℝ E : ℝ) - 1 = d := by
    rw [hd, Fintype.card_fin, hmdef, Nat.cast_sub hn, Nat.cast_one]
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  refine ⟨((K' : ℝ≥0∞) ^ d) * (s : ℝ≥0∞)⁻¹,
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hd0 ENNReal.coe_ne_top)
      (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr hs0.ne')), ?_⟩
  intro B hgraph ε hε T hT hsegT
  rw [hd']
  -- Hausdorff measure of `B` against Lebesgue measure of its projection
  set g : (Fin m → ℝ) → E := Function.invFunOn Φ B with hg
  have hgB : ∀ u ∈ Φ '' B, g u ∈ B ∧ Φ (g u) = u := by
    intro u hu
    exact ⟨Function.invFunOn_mem hu, Function.invFunOn_eq hu⟩
  have hdist : ∀ x ∈ B, ∀ y ∈ B, ‖x - y‖ ≤ K' * ‖Φ x - Φ y‖ := by
    intro x hx y hy
    refine (hgraph x hx y hy).trans ?_
    rw [hK', NNReal.coe_mul, mul_assoc, ← map_sub]
    exact mul_le_mul_of_nonneg_left (hPΦ (x - y)) C.coe_nonneg
  have hglip : LipschitzOnWith K' g (Φ '' B) := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    obtain ⟨hu1, hu2⟩ := hgB u hu
    obtain ⟨hv1, hv2⟩ := hgB v hv
    rw [dist_eq_norm, dist_eq_norm]
    have h := hdist _ hu1 _ hv1
    rwa [hu2, hv2] at h
  have hBsub : B ⊆ g '' (Φ '' B) := by
    intro x hx
    refine ⟨Φ x, mem_image_of_mem Φ hx, ?_⟩
    obtain ⟨h1, h2⟩ := hgB (Φ x) (mem_image_of_mem Φ hx)
    have h := hdist _ h1 _ hx
    rw [h2, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hH : μH[d] B ≤ (K' : ℝ≥0∞) ^ d * (volume : Measure (Fin m → ℝ)) (Φ '' B) := by
    rw [hd, hausdorffMeasure_pi_real.symm]
    exact (measure_mono hBsub).trans (hglip.hausdorffMeasure_image_le (Nat.cast_nonneg _))
  -- Fubini along `θ`
  set T' : Set ((Fin m → ℝ) × ℝ) := Lc.symm ⁻¹' T with hT'
  have hT'm : MeasurableSet T' := Lc.symm.continuous.measurable hT
  have hdxT : dx T = s * (volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ) T' := by
    have h1 : dx T = ν T' := by
      rw [hν, Measure.map_apply Lc.continuous.measurable hT'm, hT']
      congr 1
      ext x
      simp
    rw [h1, hνeq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  set f : (Fin m → ℝ) → ℝ≥0∞ := fun u => (volume : Measure ℝ) (Prod.mk u ⁻¹' T') with hf
  have hfm : Measurable f := measurable_measure_prodMk_left hT'm
  have hfB : Φ '' B ⊆ {u | ENNReal.ofReal ε ≤ f u} := by
    rintro _ ⟨x, hx, rfl⟩
    change ENNReal.ofReal ε ≤ (volume : Measure ℝ) (Prod.mk (Φ x) ⁻¹' T')
    have hsub : Ioc (⟪θ, x⟫) (⟪θ, x⟫ + ε) ⊆ Prod.mk (Φ x) ⁻¹' T' := by
      intro r hr
      change Lc.symm (Φ x, r) ∈ T
      have h := hsegT x hx (r - ⟪θ, x⟫) ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have heq : Lc.symm (Φ x, r) = x + (r - ⟪θ, x⟫) • θ := by
        rw [ContinuousLinearEquiv.symm_apply_eq, hseg, add_sub_cancel]
      rwa [heq]
    calc ENNReal.ofReal ε = (volume : Measure ℝ) (Ioc (⟪θ, x⟫) (⟪θ, x⟫ + ε)) := by
          rw [Real.volume_Ioc, add_sub_cancel_left]
      _ ≤ _ := measure_mono hsub
  have hmarkov : ENNReal.ofReal ε * (volume : Measure (Fin m → ℝ)) (Φ '' B) ≤
      (volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ) T' := by
    rw [Measure.prod_apply hT'm]
    calc ENNReal.ofReal ε * (volume : Measure (Fin m → ℝ)) (Φ '' B)
        ≤ ENNReal.ofReal ε * (volume : Measure (Fin m → ℝ)) {u | ENNReal.ofReal ε ≤ f u} := by
          gcongr
      _ ≤ ∫⁻ u, f u := mul_meas_ge_le_lintegral hfm _
  have hprod : (volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ) T' =
      (s : ℝ≥0∞)⁻¹ * dx T := by
    rw [hdxT, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hs0.ne')
      ENNReal.coe_ne_top, one_mul]
  calc μH[d] B * ENNReal.ofReal ε
      ≤ (K' : ℝ≥0∞) ^ d * (volume : Measure (Fin m → ℝ)) (Φ '' B) * ENNReal.ofReal ε :=
        by gcongr
    _ = (K' : ℝ≥0∞) ^ d * (ENNReal.ofReal ε * (volume : Measure (Fin m → ℝ)) (Φ '' B)) := by
        ring
    _ ≤ (K' : ℝ≥0∞) ^ d * ((s : ℝ≥0∞)⁻¹ * dx T) := by
        rw [← hprod]
        gcongr
    _ = (K' : ℝ≥0∞) ^ d * (s : ℝ≥0∞)⁻¹ * dx T := by ring

/-- **A local chart of the frontier of a convex set** (CEK arXiv:1304.0630v1, (23), (24), (32)):
let `K` be convex with nonempty interior, `dx` an additive Haar measure and `x₀ ∉ interior K`.
There are a unit vector `θ`, a neighbourhood `U` of `x₀` and `M < ∞` such that every
`x ∈ U \ interior K` satisfies `x + tθ ∉ K` for all `t > 0`, and for every `B ⊆ U ∩ (K \ interior K)`,
`ε > 0` and measurable `T` containing the segments `{x + tθ : 0 < t ≤ ε}`, `x ∈ B`,
`H^{n−1}(B) · ε ≤ M · dx(T)`. -/
theorem exists_convex_frontier_chart (dx : Measure E) [dx.IsAddHaarMeasure] {K : Set E}
    (hK : Convex ℝ K) (hint : (interior K).Nonempty) {x₀ : E} (hx₀ : x₀ ∉ interior K) :
    ∃ θ : E, ‖θ‖ = 1 ∧ ∃ U ∈ 𝓝 x₀, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      (∀ x ∈ U, x ∉ interior K → ∀ t : ℝ, 0 < t → x + t • θ ∉ K) ∧
      ∀ B ⊆ U ∩ (K \ interior K), ∀ ε : ℝ, 0 < ε → ∀ T : Set E, MeasurableSet T →
        (∀ x ∈ B, ∀ t ∈ Ioc (0 : ℝ) ε, x + t • θ ∈ T) →
        μH[(finrank ℝ E : ℝ) - 1] B * ENNReal.ofReal ε ≤ M * dx T := by
  obtain ⟨c, hc⟩ := hint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  have hne : x₀ ≠ c := fun h => hx₀ (h ▸ hc)
  set τ := ‖x₀ - c‖ with hτdef
  have hτ : 0 < τ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set θ := τ⁻¹ • (x₀ - c) with hθdef
  have hθ : ‖θ‖ = 1 := by
    rw [hθdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hτ.ne']
  have hc' : x₀ - τ • θ = c := by
    rw [hθdef, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, sub_sub_cancel]
  have hball' : ball (x₀ - τ • θ) r ⊆ interior K := by rw [hc']; exact hball
  set C : ℝ≥0 := ⟨1 + 2 * τ / r, by positivity⟩ with hC
  obtain ⟨M, hM, hvol⟩ := hausdorffMeasure_mul_le_of_graph dx hθ C
  refine ⟨θ, hθ, ball x₀ (r / 2), ball_mem_nhds x₀ (by positivity), M, hM, ?_, ?_⟩
  · intro x hx hxi t ht
    refine add_smul_notMem_of_sub_smul_mem_interior hK hxi hτ (hball' ?_) ht
    rw [mem_ball, dist_eq_norm, sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact (mem_ball.mp hx).trans (by linarith)
  · intro B hB ε hε T hT hseg
    refine hvol B (fun x hx y hy => ?_) ε hε T hT hseg
    have hxb : ‖x - x₀‖ < r / 2 := by rw [← dist_eq_norm]; exact mem_ball.mp (hB hx).1
    have hyb : ‖y - x₀‖ < r / 2 := by rw [← dist_eq_norm]; exact mem_ball.mp (hB hy).1
    exact norm_sub_le_mul_transversal hK hθ hτ hr hball' (hB hx).2 (hB hy).2 hxb hyb

end Measure

end FunctionalInequalities.Analysis
