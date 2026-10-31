module

public import FunctionalInequalities.Analysis.Convex.Subgradient.HalfBall
public import FunctionalInequalities.Analysis.Elliptic.HalfBall
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Mul

/-! Genuine quartic sources for the normalized flat-support producer. The full closed half-ball
is used for within derivatives. Ambient dimension one has zero tangential space. -/

noncomputable section
open Set
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities.Analysis.FlatConvexSupportClient

private def quartic {m : ℕ} (x : EuclideanSpace ℝ (Fin (m + 1))) : ℝ := (‖x‖ ^ 2) ^ 2

private theorem quartic_derivative {m : ℕ} (z : EuclideanSpace ℝ (Fin (m + 1))) :
    HasFDerivAt (quartic (m := m)) ((4 * ‖z‖ ^ 2) • innerSL ℝ z) z := by
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt).pow 2
  apply h.congr_fderiv
  ext ξ
  simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, _root_.smul_apply, smul_eq_mul]
  ring

private theorem quartic_within {m : ℕ} (z ξ : EuclideanSpace ℝ (Fin (m + 1)))
    (hz : ‖z‖ ≤ 1 ∧ 0 ≤ z (Fin.last m)) :
    fderivWithin ℝ quartic {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last m)} z ξ =
      4 * ‖z‖ ^ 2 * ⟪z, ξ⟫ := by
  have hK := closure_halfBall (m := m) (R := (1 : ℝ)) zero_lt_one
  have hu : UniqueDiffWithinAt ℝ
      {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last m)} z := by
    rw [← hK]
    exact uniqueDiffOn_closure_halfBall zero_lt_one z (by rw [hK]; exact hz)
  rw [(quartic_derivative z).hasFDerivWithinAt.fderivWithin hu]
  rfl

private theorem quartic_bound {m : ℕ} (z ξ : EuclideanSpace ℝ (Fin (m + 1))) (hz : ‖z‖ < 1)
    (hzflat : z (Fin.last m) = 0) :
    |fderivWithin ℝ quartic {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last m)}
          z ξ| ≤
      4 * ‖ξ‖ := by
  rw [quartic_within z ξ ⟨hz.le, hzflat.ge⟩, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 4 * ‖z‖ ^ 2)]
  have hi := abs_real_inner_le_norm z ξ
  have hz0 := norm_nonneg z
  have hξ0 := norm_nonneg ξ
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith
  have hz3 : ‖z‖ ^ 2 * ‖z‖ ≤ 1 := by nlinarith
  calc
    4 * ‖z‖ ^ 2 * |⟪z, ξ⟫| ≤ 4 * ‖z‖ ^ 2 * (‖z‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ 4 * ‖ξ‖ := by nlinarith [mul_le_mul_of_nonneg_right hz3 hξ0]

private theorem quartic_flat_convex {m : ℕ} :
    ConvexOn ℝ {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < 1 ∧ x (Fin.last m) = 0} quartic := by
  have hg : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin (m + 1)))) quartic :=
    (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).pow (fun _ _ => sq_nonneg _) 2
  have hb : Convex ℝ {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ < 1} := by
    simpa only [Metric.ball, dist_zero_right] using
      convex_ball (0 : EuclideanSpace ℝ (Fin (m + 1))) (1 : ℝ)
  apply hg.subset (subset_univ _)
  intro x hx y hy a b ha hb' hab
  refine ⟨hb hx.1 hy.1 ha hb' hab, ?_⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx.2, hy.2, mul_zero, add_zero]

private theorem quartic_normalized {m : ℕ} :
    ContDiffOn ℝ 1 (quartic (m := m)) {x | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last m)} ∧
      quartic (0 : EuclideanSpace ℝ (Fin (m + 1))) = 0 ∧
      (∀ ξ : EuclideanSpace ℝ (Fin (m + 1)), ξ (Fin.last m) = 0 →
        fderivWithin ℝ quartic {x | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last m)} 0 ξ = 0) := by
  refine ⟨((contDiff_norm_sq ℝ).pow 2).contDiffOn, by simp [quartic], ?_⟩
  intro ξ _hξ
  rw [quartic_within 0 ξ ⟨by simp, by simp⟩]
  simp

/-- Nonempty Fin2: the SAME actual quartic at zbar=(1/4,0) generates the nonzero support plane
and beta=3/16, with no supporting-plane/intercept input. -/
theorem quartic_nonzero_flat_support_client :
    ∃ β : ℝ, β = 3 / 16 ∧
      ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ < 1 → y (Fin.last 1) = 0 →
        (1 / 16 : ℝ) * max (y 0 - β) 0 ≤ quartic (m := 1) y := by
  let z : EuclideanSpace ℝ (Fin 2) := (1 / 4 : ℝ) • EuclideanSpace.single 0 1
  have hnz : ‖z‖ = 1 / 4 := by simp [z, norm_smul]
  have hzl : z (Fin.last 1) = 0 := by simp [z]
  obtain ⟨hC1, hq0, hd0⟩ := quartic_normalized (m := 1)
  have hs := normalized_flat_support (m := 1) (R := 1) (C := 4) (v := quartic)
    zero_lt_one (by norm_num) hC1 quartic_flat_convex hq0 hd0
    (fun z hz hzl ξ _hξ => quartic_bound z ξ hz hzl) z (by rw [hnz]; norm_num) hzl
  let g : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i => if i = Fin.last 1 then 0 else
    fderivWithin ℝ quartic {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last 1)} z
      (EuclideanSpace.single i 1))
  have hdval : fderivWithin ℝ quartic
      {x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last 1)} z
        (EuclideanSpace.single 0 1) = 1 / 16 := by
    rw [quartic_within z _ ⟨by rw [hnz]; norm_num, hzl.ge⟩, hnz]
    norm_num [z, inner_smul_left]
  have hg : g = (1 / 16 : ℝ) • EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i
    · simpa [g] using hdval
    · simp [g]
  have hng : ‖g‖ = 1 / 16 := by rw [hg]; simp [norm_smul]
  change 0 ≤ ‖g‖ ∧ _ at hs
  rcases hs with ⟨_h0, _hC, _hc, _hn, hcase⟩
  rcases hcase with hzero | ⟨ζ, β, hζn, hζl, hgz, hβ, _hβ0, _hβz, _hdζ, hsup⟩
  · rw [hng] at hzero
    norm_num at hzero
  · change g = ‖g‖ • ζ at hgz
    change β = (∑ i, ζ i * z i) - quartic z / ‖g‖ at hβ
    have hζ : ζ = EuclideanSpace.single 0 1 := by
      rw [hng] at hgz
      exact (smul_right_injective (M := EuclideanSpace ℝ (Fin 2))
        (by norm_num : (1 / 16 : ℝ) ≠ 0)) (hgz.symm.trans hg)
    have hqz : quartic z = 1 / 256 := by norm_num [quartic, hnz]
    have hβval : β = 3 / 16 := by
      rw [hng, hζ, hqz] at hβ
      norm_num [z] at hβ
      exact hβ
    refine ⟨β, hβval, ?_⟩
    intro y hy hyl
    have h := hsup y hy hyl
    change ‖g‖ * max ((∑ i, ζ i * y i) - β) 0 ≤ quartic y at h
    rw [hng, hζ] at h
    simpa using h

/-- Ambient Fin1 has a genuine one-point flat trace and no nonzero tangent. The new source
eliminates its positive branch and supplies flat nonnegativity. -/
theorem ambient_fin_one_zero_tangent_client :
    let g : EuclideanSpace ℝ (Fin 1) :=
      WithLp.toLp 2
        (fun i =>
          if i = Fin.last 0 then 0
          else
            fderivWithin ℝ (quartic (m := 0)) {x | ‖x‖ ≤ 1 ∧ 0 ≤ x (Fin.last 0)} 0
              (EuclideanSpace.single i 1))
    ‖g‖ = 0 ∧
      ∀ y : EuclideanSpace ℝ (Fin 1), ‖y‖ < 1 → y (Fin.last 0) = 0 → 0 ≤ quartic (m := 0) y := by
  intro g
  obtain ⟨hC1, hq0, hd0⟩ := quartic_normalized (m := 0)
  have hs :=
    normalized_flat_support (m := 0) (R := 1) (C := 4) (v := quartic) zero_lt_one (by norm_num)
      hC1 quartic_flat_convex hq0 hd0 (fun z hz hzl ξ _hξ => quartic_bound z ξ hz hzl) 0
      (by simp) (by simp)
  change 0 ≤ ‖g‖ ∧ _ at hs
  rcases hs with ⟨_h0, _hC, _hc, hn, hcase⟩
  refine ⟨?_, hn⟩
  rcases hcase with hzero | ⟨ζ, _β, hζn, hζl, _hgz, _hβ, _hβ0, _hβz, _hdζ, _hsup⟩
  · exact hzero
  · have hz : ζ = 0 := by ext i; fin_cases i; exact hζl
    simp [hz] at hζn

end FunctionalInequalities.Analysis.FlatConvexSupportClient
