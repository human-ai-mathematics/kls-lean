module

public import FunctionalInequalities.Analysis.Convex.Extension

@[expose] public section

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
namespace LetwinC0PatchAudit
open FunctionalInequalities.Analysis

def source (x : ℝ) : ℝ := if x ∈ Ioo (-2 : ℝ) 2 then |x| else 0

theorem actual_piecewise_absolute_patch :
    ∃ (V : ℝ → ℝ) (L : NNReal),
      ConvexOn ℝ univ V ∧
        LipschitzWith L V ∧
          (∀ x ∈ Icc (-1 : ℝ) 1, V x = source x) ∧
            (∀ G ⊆ interior (Icc (-1 : ℝ) 1),
              subgradientImage V G = subgradientImageOn source (Ioo (-2) 2) G) := by
  have heq : EqOn source (fun x : ℝ => |x|) (Ioo (-2) 2) := by
    intro x hx
    simp only [source, ite_eq_left hx]
  have hc : ConvexOn ℝ (Ioo (-2 : ℝ) 2) source := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxy := (convex_Ioo (-2 : ℝ) 2) hx hy ha hb hab
    rw [heq hx, heq hy, heq hxy]
    change |a * x + b * y| ≤ a * |x| + b * |y|
    have h := abs_add_le (a * x) (b * y)
    simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using h
  have hcont : ContinuousOn source (Ioo (-2 : ℝ) 2) := by
    apply continuous_abs.continuousOn.congr
    intro x hx
    exact heq hx
  apply exists_lipschitz_compact_convex_extension isOpen_Ioo hc hcont isCompact_Icc
  · exact ⟨0, by norm_num⟩
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]

theorem actual_zero_dimensional_patch :
    ∃ (V : EuclideanSpace ℝ (Fin 0) → ℝ) (L : NNReal),
      ConvexOn ℝ univ V ∧ LipschitzWith L V ∧
      (∀ x ∈ ({0} : Set (EuclideanSpace ℝ (Fin 0))), V x = 0) ∧
      (∀ G ⊆ interior ({0} : Set (EuclideanSpace ℝ (Fin 0))),
        subgradientImage V G = subgradientImageOn (fun _ => 0) univ G) := by
  exact exists_lipschitz_compact_convex_extension isOpen_univ
    (convexOn_const 0 convex_univ) continuous_const.continuousOn
    isCompact_singleton (singleton_nonempty _) (subset_univ _)
end LetwinC0PatchAudit
set_option pp.fullNames true in
#print axioms LetwinC0PatchAudit.actual_piecewise_absolute_patch
set_option pp.fullNames true in
#print axioms LetwinC0PatchAudit.actual_zero_dimensional_patch

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_lipschitz_compact_convex_extension

namespace LetwinMoreauAudit
open Set Metric Filter
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace Topology
/-- Reuses the actual canonical piecewise-absolute patch source rather than
copying its absolute-value convexity proof. -/
theorem actual_piecewise_absolute_regularization :
    ∃ (V : ℝ → ℝ) (L : NNReal),
      ConvexOn ℝ univ V ∧
        LipschitzWith L V ∧
          (∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), V x = LetwinC0PatchAudit.source x) ∧
            (∀ ε : ℝ,
                0 < ε →
                  ConvexOn ℝ univ (moreauEnvelope V ε) ∧
                    ContDiff ℝ 1 (moreauEnvelope V ε) ∧
                      LipschitzWith (‖(ε⁻¹ : ℝ)‖₊ * 2) (gradient (moreauEnvelope V ε)) ∧
                        (∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2),
                            |moreauEnvelope V ε x - LetwinC0PatchAudit.source x| ≤
                              ε * (L : ℝ) ^ 2 / 2) ∧
                          (∀ x, ‖(proximalPoint (fun z => ε * V z)) x - x‖ ≤ ε * (L : ℝ))) ∧
              TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope V ε) LetwinC0PatchAudit.source
                (𝓝[>] (0 : ℝ)) (Icc (-1 / 2 : ℝ) (1 / 2)) := by
  obtain ⟨W, L, hW, hL, heq, _⟩ := LetwinC0PatchAudit.actual_piecewise_absolute_patch
  have hs : Ioo (-1 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := fun _ hx => ⟨hx.1.le, hx.2.le⟩
  have hc : ConvexOn ℝ (Ioo (-1 : ℝ) 1) LetwinC0PatchAudit.source := by
    refine ⟨convex_Ioo _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxy := (convex_Ioo (-1 : ℝ) 1) hx hy ha hb hab
    rw [← heq x (hs hx), ← heq y (hs hy), ← heq _ (hs hxy)]
    exact hW.2 (mem_univ x) (mem_univ y) ha hb hab
  have hcont : ContinuousOn LetwinC0PatchAudit.source (Ioo (-1 : ℝ) 1) := by
    apply hL.continuous.continuousOn.congr
    intro x hx
    exact (heq x (hs hx)).symm
  apply exists_compact_moreau_regularization isOpen_Ioo hc hcont isCompact_Icc
  · exact ⟨0, by norm_num⟩
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]

/-- Actual nonsmooth absolute-value source produces C1,1 and a real transferred
constant lower contact at its actual proximal point. No source regularity. -/
theorem actual_absolute_value_contact :
    ContDiff ℝ 1 (moreauEnvelope (fun x : ℝ => |x|) 1) ∧
      LipschitzWith 2 (gradient (moreauEnvelope (fun x : ℝ => |x|) 1)) ∧
        (proximalPoint (fun y : ℝ => (1 : ℝ) * |y|) 0) = 0 ∧
          moreauEnvelope (fun x : ℝ => |x|) 1 0 = 0 ∧ (∀ᶠ w : ℝ in 𝓝 0, 0 ≤ |w|) := by
  have hf : ConvexOn ℝ univ (fun x : ℝ => |x|) := by
    convert! (convexOn_norm convex_univ : ConvexOn ℝ univ (fun x : ℝ => ‖x‖)) using 1
  have hp : (proximalPoint (fun y : ℝ => (1 : ℝ) * |y|) 0) = 0 := by
    apply proximalPoint_eq_of_subgradient (by simpa using hf)
    intro y
    simp only [sub_self, inner_zero_left, abs_zero, mul_zero, zero_add, one_mul]
    exact abs_nonneg y
  have he : moreauEnvelope (fun x : ℝ => |x|) 1 0 = 0 := by
    simp only [moreauEnvelope, hp, inv_one, abs_zero, sub_self, norm_zero, zero_pow two_ne_zero,
      mul_zero, add_zero]
  have ht : ∀ᶠ y in 𝓝 (0 : ℝ), 0 ≤ moreauEnvelope (fun x : ℝ => |x|) 1 y := by
    exact Filter.Eventually.of_forall (fun y => by dsimp [moreauEnvelope]; positivity)
  have hh :=
    lower_contact_moreauEnvelope (fun x : ℝ => |x|) hf (by norm_num : (0 : ℝ) < 1) (ψ :=
      fun _ => 0) he ht
  have hlow : ∀ᶠ w : ℝ in 𝓝 0, 0 ≤ |w| := by
    simpa only [hp, sub_self, norm_zero, zero_pow two_ne_zero, mul_zero, sub_zero] using hh.2
  obtain ⟨_, hc, _, hl⟩ :=
    moreauEnvelope_regularization (fun x : ℝ => |x|) hf (by norm_num : (0 : ℝ) < 1)
  exact ⟨hc, by simpa using hl, hp, he, hlow⟩

/-- The actual Euclidean zero-dimensional carrier is nonempty; its constant
moreauEnvelope_regularization stays seven, with actual moreau_derivative zero. No measure claim. -/
theorem actual_fin0_constant (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 1 (moreauEnvelope (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) ε) ∧
      (∀ x, moreauEnvelope (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) ε x = 7) ∧
        (∀ x,
          gradient (moreauEnvelope (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) ε) x = 0) := by
  have hf :=
    convexOn_const (7 : ℝ) (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℝ (Fin 0))))
  obtain ⟨_, hc, hg, _⟩ :=
    moreauEnvelope_regularization (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) hf hε
  refine ⟨hc, ?_, ?_⟩
  · intro x
    have he : (proximalPoint (fun _ : EuclideanSpace ℝ (Fin 0) => ε * (7 : ℝ)) x) = x :=
      Subsingleton.elim _ _
    dsimp [moreauEnvelope]
    rw [he, sub_self, norm_zero, zero_pow two_ne_zero, mul_zero, add_zero]
    field_simp
  · intro x
    rw [hg]
    have he : x = (proximalPoint (fun _ : EuclideanSpace ℝ (Fin 0) => ε * (7 : ℝ)) x) :=
      Subsingleton.elim _ _
    rw [← he, sub_self, smul_zero]
end LetwinMoreauAudit

set_option pp.fullNames true in
#print axioms LetwinMoreauAudit.actual_piecewise_absolute_regularization

set_option pp.fullNames true in
#print axioms LetwinMoreauAudit.actual_absolute_value_contact

set_option pp.fullNames true in
#print axioms LetwinMoreauAudit.actual_fin0_constant
