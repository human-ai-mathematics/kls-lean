module

public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Operator
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Uniform gradient estimates from a compact positive Hessian

A reference genuinely C2 on an open neighbourhood of a compact convex set,
with actual positive Hessian there, has uniform
strong-monotonicity and Lipschitz-gradient constants there. Compactness of the
actual derivative produces the bounds; no uniform Hessian estimate is supplied.
This supports the given comparison-reference step toward Letwin
arXiv:2607.24164v1 Lemma2.2 via BB1207.6128v1 Theorem2.24(ii).
No global C2 extension, reference existence or regularity of an unknown Alexandrov solution is
asserted.
-/

@[expose] public section
section
open Set Metric
open scoped RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual local C2 and positive Hessian of the comparison reference produce uniform
strong monotonicity and a Lipschitz gradient on a compact convex set. -/
theorem exists_uniform_gradient_bounds_of_posDef_hessianOn {v : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hv : ContDiffOn ℝ 2 v U) {K : Set E} (hKU : K ⊆ U) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hPD : ∀ x ∈ K, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z) :
    ∃ κ L : ℝ,
      0 < κ ∧
        0 < L ∧
          ∀ x ∈ K,
            ∀ y ∈ K,
              κ * ‖x - y‖ ^ 2 ≤ ⟪gradient v x - gradient v y, x - y⟫ ∧
                ‖gradient v x - gradient v y‖ ≤ L * ‖x - y‖ := by
  have hg : ContDiffOn ℝ 1 (gradient v) U := contDiffOn_gradient hU hv (by norm_num)
  let H : E → E →L[ℝ] E := fderiv ℝ (gradient v)
  have hH : ContinuousOn H U := hg.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ (gradient v) x := by
    intro x hx
    exact (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  let S : Set (E × E) := K ×ˢ sphere 0 1
  let F : E × E → ℝ := fun z => ⟪H z.1 z.2, z.2⟫
  have hS : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hF : ContinuousOn F S :=
    ((hH.comp continuous_fst.continuousOn (fun z hz => hKU hz.1)).clm_apply
          continuous_snd.continuousOn).inner
      continuous_snd.continuousOn
  have hpos : ∀ z ∈ S, 0 < F z := by
    intro z hz
    change 0 < ⟪hessianOperator v z.1 z.2, z.2⟫
    rw [←
      bilinearIteratedFDerivTwo_eq_inner_hessianOperator_at
        (hv.contDiffAt (hU.mem_nhds (hKU hz.1))) z.2 z.2]
    apply hPD z.1 hz.1 z.2
    have hn : ‖z.2‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz.2
    intro he
    simp only [he, norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨κ, hκ, hlo⟩ := hS.exists_forall_le' hF hpos
  obtain ⟨U, hU⟩ := (hK.image_of_continuousOn (hH.mono hKU)).isBounded.exists_norm_le
  let L : ℝ := |U| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hnorm : ∀ x ∈ K, ‖H x‖ ≤ L := by
    intro x hx
    exact (hU (H x) ⟨x, hx, rfl⟩).trans ((le_abs_self U).trans (by dsimp [L]; linarith))
  have hfloor : ∀ x ∈ K, ∀ d : E, κ * ‖d‖ ^ 2 ≤ ⟪H x d, d⟫ := by
    intro x hx d
    by_cases hd : d = 0
    · simp [hd]
    have hn : ‖NormedSpace.normalize d‖ = 1 := NormedSpace.norm_normalize hd
    have hh :=
      hlo (x, NormedSpace.normalize d)
        ⟨hx, by simpa only [mem_sphere_iff_norm, sub_zero] using hn⟩
    calc
      κ * ‖d‖ ^ 2 = ‖d‖ ^ 2 * κ := mul_comm _ _
      _ ≤ ‖d‖ ^ 2 * F (x, NormedSpace.normalize d) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = ⟪H x (‖d‖ • NormedSpace.normalize d), ‖d‖ • NormedSpace.normalize d⟫ := by
        dsimp [F]
        simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
      _ = ⟪H x d, d⟫ := by rw [NormedSpace.norm_smul_normalize]
  refine ⟨κ, L, hκ, hL, ?_⟩
  intro x hx y hy
  constructor
  · let d : E := x - y
    let g : ℝ → ℝ := fun s => ⟪gradient v (AffineMap.lineMap y x s), d⟫
    have hgd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt g (⟪H (AffineMap.lineMap y x s) d, d⟫) s := by
      have hh :=
        (hdiff (AffineMap.lineMap y x s)
              (hKU (hKc.mapsTo_lineMap hy hx hs))).hasFDerivAt.comp_hasDerivAt
          s (AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := s))
      convert! hh.inner ℝ (hasDerivAt_const s d) using 1
      simp [H, d]
    have hgc : ContinuousOn g (Icc (0 : ℝ) 1) := by
      intro s hs
      exact (hgd s hs).continuousAt.continuousWithinAt
    have hm :=
      (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv hgc
        (fun s hs => (hgd s (interior_subset hs)).differentiableAt.differentiableWithinAt) (C :=
        κ * ‖d‖ ^ 2)
        (by
          intro s hs
          rw [(hgd s (interior_subset hs)).deriv]
          exact hfloor _ (hKc.mapsTo_lineMap hy hx (interior_subset hs)) d)
        0 (by simp) 1 (by simp) zero_le_one
    simpa only [g, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, sub_zero, mul_one,
      inner_sub_left, d] using hm
  · exact hKc.norm_image_sub_le_of_norm_fderiv_le (fun z hz => hdiff z (hKU hz)) hnorm hy hx



/-- Actual C2 and positive Hessian of the comparison reference produce uniform
strong monotonicity and a Lipschitz gradient on a compact convex set. -/
theorem exists_uniform_gradient_bounds_of_posDef_hessian {v : E → ℝ} (hv : ContDiff ℝ 2 v)
    {K : Set E}
    (hK : IsCompact K) (hKc : Convex ℝ K)
    (hPD : ∀ x ∈ K, ∀ z : E, z ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ v x z z) :
    ∃ κ L : ℝ, 0 < κ ∧ 0 < L ∧ ∀ x ∈ K, ∀ y ∈ K,
      κ * ‖x-y‖^2 ≤ ⟪gradient v x-gradient v y, x-y⟫ ∧
      ‖gradient v x-gradient v y‖ ≤ L * ‖x-y‖ := by
  exact exists_uniform_gradient_bounds_of_posDef_hessianOn isOpen_univ hv.contDiffOn
    (subset_univ K) hK hKc hPD

end FunctionalInequalities.Analysis.BakryEmery
