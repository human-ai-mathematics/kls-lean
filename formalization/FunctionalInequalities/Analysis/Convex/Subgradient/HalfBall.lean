module

public import FunctionalInequalities.Analysis.EuclideanCoordinates
public import FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Generated tangential support of a convex flat trace

CNS1984 Lemma 5.1, pp. 385–387, (5.3) and (5.3)′.

On the closed half-ball `K = {‖x‖ ≤ R, 0 ≤ xₙ}` in `ℝ^{m+1}`, let `v` be `C¹` within `K`, convex on
the flat part
`{‖x‖ < R, xₙ = 0}`, normalized by `v 0 = 0` and vanishing tangential derivative within `K` at `0`,
with the
paper bound `|∂_ξ v| ≤ C ‖ξ‖` on tangential `ξ`. At a flat point `z̄` the tangential gradient `g`
(the
coordinates of `d = fderivWithin ℝ v K z̄`, with normal coordinate `0`) and `α = ‖g‖` are generated
first; then
`α ≤ C`, the flat trace is nonnegative, and either `α = 0` or the unit tangent `ζ = g / α` and the
intercept
`β = ⟨ζ, z̄⟩ - v z̄ / α` satisfy `0 ≤ β ≤ ‖z̄‖` and the flat support `α · max(⟨ζ, y⟩ - β, 0) ≤ v y`.

Proof: `C¹` within `K` gives `HasFDerivWithinAt v (fderivWithin ℝ v K z) K z`, restricted to the
flat set (no
`UniqueDiffOn` of the flat set, no ambient derivative). The generic
`convex_support_of_hasFDerivWithinAt` is called
at `0` (nonnegativity) and at `z̄` (the support plane); the tangential coordinate identity is
shared.
For `m = 0` there are no tangential coordinates: `g = 0` and the `α = 0` branch holds.
-/

@[expose] public section

open Set

namespace FunctionalInequalities.Analysis

/--
**Tangential coordinates.** On vectors with vanishing last coordinate, a linear functional is the
dot product
with its coordinates on the other basis vectors (last coordinate set to `0`). -/
private lemma apply_eq_sum_tangential_coordinates {m : ℕ}
    (d : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ) (ξ : EuclideanSpace ℝ (Fin (m + 1)))
    (hξ : ξ (Fin.last m) = 0) :
    d ξ =
      ∑ i,
        (WithLp.toLp 2 (fun i => if i = Fin.last m then 0 else d (EuclideanSpace.single i 1)) :
              EuclideanSpace ℝ (Fin (m + 1)))
            i *
          ξ i := by
  rw [clm_apply_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, PiLp.toLp_apply]
  by_cases hi : i = Fin.last m
  · subst hi
    simp [hξ]
  · simp [hi, mul_comm]

theorem normalized_flat_support {m : ℕ} {R C : ℝ} {v : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hv : ContDiffOn ℝ 1 v {x | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)})
    (hconv : ConvexOn ℝ {x | ‖x‖ < R ∧ x (Fin.last m) = 0} v) (hv0 : v 0 = 0)
    (hd0 :
      ∀ ξ : EuclideanSpace ℝ (Fin (m + 1)),
        ξ (Fin.last m) = 0 → fderivWithin ℝ v {x | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} 0 ξ = 0)
    (hbound :
      ∀ z : EuclideanSpace ℝ (Fin (m + 1)),
        ‖z‖ < R →
          z (Fin.last m) = 0 →
            ∀ ξ : EuclideanSpace ℝ (Fin (m + 1)),
              ξ (Fin.last m) = 0 →
                |fderivWithin ℝ v {x | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)} z ξ| ≤ C * ‖ξ‖)
    (zbar : EuclideanSpace ℝ (Fin (m + 1))) (hzbar : ‖zbar‖ < R)
    (hzflat : zbar (Fin.last m) = 0) :
    let K : Set (EuclideanSpace ℝ (Fin (m + 1))) := {x | ‖x‖ ≤ R ∧ 0 ≤ x (Fin.last m)}
    let d := fderivWithin ℝ v K zbar
    let g : EuclideanSpace ℝ (Fin (m + 1)) :=
      WithLp.toLp 2 (fun i => if i = Fin.last m then 0 else d (EuclideanSpace.single i 1))
    let α := ‖g‖
    0 ≤ α ∧
      α ≤ C ∧
        (∀ ξ : EuclideanSpace ℝ (Fin (m + 1)), ξ (Fin.last m) = 0 → d ξ = ∑ i, g i * ξ i) ∧
          (∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ < R → y (Fin.last m) = 0 → 0 ≤ v y) ∧
            (α = 0 ∨
              ∃ (zeta : EuclideanSpace ℝ (Fin (m + 1))) (β : ℝ),
                ‖zeta‖ = 1 ∧
                  zeta (Fin.last m) = 0 ∧
                    g = α • zeta ∧
                      β = (∑ i, zeta i * zbar i) - v zbar / α ∧
                        0 ≤ β ∧
                          β ≤ ‖zbar‖ ∧
                            (∀ ξ : EuclideanSpace ℝ (Fin (m + 1)),
                                ξ (Fin.last m) = 0 → d ξ = α * ∑ i, zeta i * ξ i) ∧
                              (∀ y : EuclideanSpace ℝ (Fin (m + 1)),
                                ‖y‖ < R →
                                  y (Fin.last m) = 0 →
                                    α * max ((∑ i, zeta i * y i) - β) 0 ≤ v y)) := by
  intro K d g
    α
  -- the flat part of the closed half-ball

  have hFlK : {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ x (Fin.last m) = 0} ⊆ K :=
    fun x hx => ⟨hx.1.le, hx.2.ge⟩
  have hdiff : DifferentiableOn ℝ v K :=
    hv.differentiableOn
      one_ne_zero
  -- the within-`K` derivative restricted to the flat set (no `UniqueDiffOn` of the flat set)

  have hderiv :
    ∀ z ∈ {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ x (Fin.last m) = 0},
      HasFDerivWithinAt v (fderivWithin ℝ v K z)
        {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ x (Fin.last m) = 0} z :=
    fun z hz => ((hdiff z (hFlK hz)).hasFDerivWithinAt).mono hFlK
  have hd0' :
    ∀ ξ : EuclideanSpace ℝ (Fin (m + 1)), ξ (Fin.last m) = 0 → fderivWithin ℝ v K 0 ξ = 0 := hd0
  have h0 :
    (0 : EuclideanSpace ℝ (Fin (m + 1))) ∈
      {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ x (Fin.last m) = 0} :=
    ⟨by simpa using hR, by simp⟩
  have hz : zbar ∈ {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < R ∧ x (Fin.last m) = 0} :=
    ⟨hzbar, hzflat⟩
  -- shared coordinate identity

  have hcoord :
    ∀ ξ : EuclideanSpace ℝ (Fin (m + 1)), ξ (Fin.last m) = 0 → d ξ = ∑ i, g i * ξ i :=
    fun ξ hξ =>
    apply_eq_sum_tangential_coordinates d ξ
      hξ
  -- generic support at `0`: the flat trace is nonnegative

  have hnonneg : ∀ y : EuclideanSpace ℝ (Fin (m + 1)), ‖y‖ < R → y (Fin.last m) = 0 → 0 ≤ v y := by
    intro y hyR hyl
    have h := convex_support_of_hasFDerivWithinAt hconv (hderiv 0 h0) h0 ⟨hyR, hyl⟩
    rw [sub_zero, hd0' y hyl, hv0] at h
    linarith
  -- `g` is tangential and `d g = ‖g‖²`

  have hglast : g (Fin.last m) = 0 := by simp [g]
  have hgg : d g = α ^ 2 := by
    rw [hcoord g hglast, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, sq]
  have hα0 : 0 ≤ α := norm_nonneg g
  have hαC : α ≤ C := by
    have hb : |d g| ≤ C * ‖g‖ := hbound zbar hzbar hzflat g hglast
    rw [hgg, abs_of_nonneg (sq_nonneg α)] at hb
    rcases eq_or_lt_of_le hα0 with h | h
    · rw [← h]
      exact hC
    · exact le_of_mul_le_mul_right (by nlinarith) h
  refine ⟨hα0, hαC, hcoord, hnonneg, ?_⟩
  rcases eq_or_lt_of_le hα0 with hα | hαpos
  · exact Or.inl hα.symm
  right
  -- the generated unit tangent

  set zeta : EuclideanSpace ℝ (Fin (m + 1)) := α⁻¹ • g with hzeta
  have hgα : g = α • zeta := by rw [hzeta, smul_inv_smul₀ hαpos.ne']
  have hznorm : ‖zeta‖ = 1 := by
    rw [hzeta, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hαpos]
    exact inv_mul_cancel₀ hαpos.ne'
  have hzlast : zeta (Fin.last m) = 0 := by simp [hzeta, hglast]
  have hdz :
    ∀ ξ : EuclideanSpace ℝ (Fin (m + 1)), ξ (Fin.last m) = 0 → d ξ = α * ∑ i, zeta i * ξ i := by
    intro ξ hξ
    rw [hcoord ξ hξ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgα, PiLp.smul_apply, smul_eq_mul, mul_assoc]
  -- generic support at `z̄`: the support plane with the generated intercept

  have hsupp :
    ∀ y : EuclideanSpace ℝ (Fin (m + 1)),
      ‖y‖ < R →
        y (Fin.last m) = 0 →
          α * ((∑ i, zeta i * y i) - ((∑ i, zeta i * zbar i) - v zbar / α)) ≤ v y := by
    intro y hyR hyl
    have h := convex_support_of_hasFDerivWithinAt hconv (hderiv zbar hz) hz ⟨hyR, hyl⟩
    have hyz : (y - zbar) (Fin.last m) = 0 := by simp [hyl, hzflat]
    have hsum : ∑ i, zeta i * (y - zbar) i = (∑ i, zeta i * y i) - ∑ i, zeta i * zbar i := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [PiLp.sub_apply, mul_sub]
    have hdiv : α * (v zbar / α) = v zbar := mul_div_cancel₀ _ hαpos.ne'
    change v zbar + d (y - zbar) ≤ v y at h
    rw [hdz _ hyz, hsum] at h
    rw [mul_sub, mul_sub, hdiv]
    linarith
  -- `∑ ζᵢ z̄ᵢ ≤ ‖z̄‖`

  have hinner : ∑ i, zeta i * zbar i ≤ ‖zbar‖ := by
    have hi : ∑ i, zeta i * zbar i = inner ℝ zeta zbar := by simp [PiLp.inner_apply, mul_comm]
    rw [hi]
    calc
      inner ℝ zeta zbar ≤ ‖zeta‖ * ‖zbar‖ := real_inner_le_norm zeta zbar
      _ = ‖zbar‖ := by rw [hznorm, one_mul]
  refine ⟨zeta, (∑ i, zeta i * zbar i) - v zbar / α, hznorm, hzlast, hgα, rfl, ?_, ?_, hdz, ?_⟩
  · -- `0 ≤ β` from the support at `y = 0`

    have h := hsupp 0 (by simpa using hR) (by simp)
    simp only [PiLp.zero_apply, mul_zero, Finset.sum_const_zero, zero_sub, hv0] at h
    have hαβ : 0 ≤ α * ((∑ i, zeta i * zbar i) - v zbar / α) := by linarith
    exact (mul_nonneg_iff_of_pos_left hαpos).mp hαβ
  · -- `β ≤ ‖z̄‖` from `v z̄ ≥ 0`

    have hvz := hnonneg zbar hzbar hzflat
    have : 0 ≤ v zbar / α := div_nonneg hvz hα0
    linarith
  · -- the flat max-support

    intro y hyR hyl
    rw [mul_max_of_nonneg _ _ hα0, mul_zero]
    exact max_le (hsupp y hyR hyl) (hnonneg y hyR hyl)

end FunctionalInequalities.Analysis
