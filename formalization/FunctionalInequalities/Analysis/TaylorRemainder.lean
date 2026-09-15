import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform remainders at flat points

Compactness makes the remainder estimate uniform in the base point.
The nearby evaluation point need not belong to the compact set.
The order-`n` statement is proved by induction on the derivative, so the quadratic case is a
corollary rather than a separate argument. -/

noncomputable section

open Set Metric

namespace FunctionalInequalities.Analysis

universe u

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
/-- Order zero: uniform continuity on a compact set, with the nearby point outside it. -/
private lemma exists_uniform_zero_remainder {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : V → F} {K : Set V} (hf : Continuous f) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y : V, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε := by
  have hunif := hK.uniformContinuousAt_of_continuousAt f
    (fun _ _ ↦ hf.continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp hunif
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  have hd : dist x y < δ := by rwa [dist_eq_norm, norm_sub_rev]
  have h : dist (f x) (f y) < ε := hclose hd hx
  rw [dist_eq_norm, norm_sub_rev] at h
  exact h.le

/-- One mean-value step: a power bound on the derivative over a ball raises the power. -/
private lemma norm_sub_le_of_norm_fderiv_pow_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : V → F} (hf : Differentiable ℝ f) {x : V} {δ C : ℝ} (hC : 0 ≤ C)
    {m : ℕ} (h : ∀ z ∈ ball x δ, ‖fderiv ℝ f z‖ ≤ C * ‖z - x‖ ^ m)
    {y : V} (hy : ‖y - x‖ < δ) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ ^ (m + 1) := by
  have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z‖ ≤ C * ‖y - x‖ ^ m := by
    intro z hz
    have hn := norm_sub_le_of_mem_segment hz
    have hzb : z ∈ ball x δ := by
      simpa [mem_ball, dist_eq_norm] using hn.trans_lt hy
    exact (h z hzb).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn m) hC)
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hf z) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc ‖f y - f x‖ ≤ C * ‖y - x‖ ^ m * ‖y - x‖ := hmv
    _ = C * ‖y - x‖ ^ (m + 1) := by ring

/-- The inductive step: a uniform order-`m` bound for `fderiv f` gives the order-`m+1` bound
for `f` at points where all derivatives of order `1` to `m+1` vanish. -/
private lemma pow_remainder_step {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} {K : Set V} {m : ℕ} {ε δ : ℝ} (hf : ContDiff ℝ (m + 1 : ℕ) f) (hε : 0 ≤ ε)
    (h : ∀ x ∈ K, (∀ k : ℕ, 1 ≤ k → k ≤ m → iteratedFDeriv ℝ k (fderiv ℝ f) x = 0) →
      ∀ z : V, ‖z - x‖ < δ → ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε * ‖z - x‖ ^ m) :
    ∀ x ∈ K, (∀ k : ℕ, 1 ≤ k → k ≤ m + 1 → iteratedFDeriv ℝ k f x = 0) →
      ∀ y : V, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ (m + 1) := by
  intro x hx hflat y hy
  have hflat' : ∀ k : ℕ, 1 ≤ k → k ≤ m → iteratedFDeriv ℝ k (fderiv ℝ f) x = 0 := by
    intro k hk1 hkm
    refine norm_eq_zero.mp ?_
    rw [norm_iteratedFDeriv_fderiv, hflat (k + 1) (by omega) (by omega)]
    simp
  have hf1 : fderiv ℝ f x = 0 := by
    refine norm_eq_zero.mp ?_
    rw [← norm_iteratedFDeriv_one, hflat 1 le_rfl (by omega)]
    simp
  have hderiv : ∀ z ∈ ball x δ, ‖fderiv ℝ f z‖ ≤ ε * ‖z - x‖ ^ m := by
    intro z hz
    have hz' : ‖z - x‖ < δ := by simpa [mem_ball, dist_eq_norm] using hz
    simpa [hf1] using h x hx hflat' z hz'
  exact norm_sub_le_of_norm_fderiv_pow_le
    (hf.differentiable (by exact_mod_cast Nat.succ_ne_zero m)) hε hderiv hy

/-- The order-`n` uniform remainder for maps into an arbitrary normed space of the same
universe as the domain. The public real-valued statement below removes that restriction. -/
private theorem pow_remainder_aux {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] :
    ∀ (n : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : W → F} {K : Set W},
      IsCompact K → ContDiff ℝ (n : ℕ) f → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ K, (∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k f x = 0) →
          ∀ y : W, ‖y - x‖ < δ → ‖f y - f x‖ ≤ ε * ‖y - x‖ ^ n := by
  intro n
  induction n with
  | zero =>
    intro F _ _ f K hK hf ε hε
    obtain ⟨δ, hδ, h⟩ := exists_uniform_zero_remainder hf.continuous hK hε
    exact ⟨δ, hδ, fun x hx _ y hy => by simpa using h x hx y hy⟩
  | succ m ih =>
    intro F _ _ f K hK hf ε hε
    have hdf : ContDiff ℝ (m : ℕ) (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_refl _)
    obtain ⟨δ, hδ, h⟩ := ih hK hdf ε hε
    exact ⟨δ, hδ, pow_remainder_step hf hε.le h⟩

/-- At points of a compact set where every derivative of order `1` to `n` vanishes, a `C^n`
real-valued function has a uniform remainder of order `n`. No finite-dimensionality,
completeness, inner product or measure structure on the domain is required. -/
theorem exists_uniform_pow_remainder {u : V → ℝ} {K : Set V} {n : ℕ}
    (hu : ContDiff ℝ (n : ℕ) u) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, (∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0) →
        ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ n := by
  intro ε hε
  cases n with
  | zero =>
    obtain ⟨δ, hδ, h⟩ := exists_uniform_zero_remainder hu.continuous hK hε
    exact ⟨δ, hδ, fun x hx _ y hy => by
      simpa [Real.norm_eq_abs] using h x hx y hy⟩
  | succ m =>
    have hdf : ContDiff ℝ (m : ℕ) (fderiv ℝ u) := hu.fderiv_right (by exact_mod_cast le_refl _)
    obtain ⟨δ, hδ, h⟩ := pow_remainder_aux m hK hdf ε hε
    refine ⟨δ, hδ, fun x hx hflat y hy => ?_⟩
    simpa [Real.norm_eq_abs] using pow_remainder_step hu hε.le h x hx hflat y hy

/-- At points of a compact set where the first two derivatives vanish, a `C²` function
has a uniform quadratic remainder bound. No finite-dimensionality, completeness,
inner product or measure structure on the domain is required. -/
theorem exists_uniform_quadratic_remainder {u : V → ℝ} {K : Set V}
    (hu : ContDiff ℝ 2 u) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, fderiv ℝ u x = 0 → iteratedFDeriv ℝ 2 u x = 0 →
        ∀ y : V, ‖y - x‖ < δ → |u y - u x| ≤ ε * ‖y - x‖ ^ 2 := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ :=
    exists_uniform_pow_remainder (n := 2) (by exact_mod_cast hu) hK ε hε
  refine ⟨δ, hδ, fun x hx h1 h2 y hy => h x hx ?_ y hy⟩
  intro k hk1 hk2
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · refine norm_eq_zero.mp ?_
    rw [norm_iteratedFDeriv_one, h1]
    simp
  · exact h2

end FunctionalInequalities.Analysis
