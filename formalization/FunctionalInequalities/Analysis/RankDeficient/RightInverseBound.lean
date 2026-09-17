import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Approximate right inverses of a surjection, pointwise and locally uniformly

Obligation `R3` of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md` and stated in
`research/audits/RankDeficientRouteStatements.lean`.  **Only `R3` is proved here**; together with
the already proved `R1` and `R2` of `Analysis/RankDeficient/Stratification.lean` that is three of the route's
obligations.  `R0`, `R4`–`R10`, `N1` and `N2` remain open, and so does the rank-deficient part of
the codimension-`m` coarea critical set.  Nothing here is a coarea formula, a slicing statement or
a Sard theorem.

**What `R3` is for.**  In the route a fibre of the regular component `v = P ∘ u` is sliced, and the
chord `b - a` of a fibre is *not* a tangent vector: two points of one fibre only give
`‖Dv (b - a)‖ ≤ ε ‖b - a‖`, not `Dv (b - a) = 0`.  Turning that into smallness of `‖Du (b - a)‖`
needs a quantitative statement that a vector almost annihilated by a surjection is close to its
kernel, which is exactly a norm bound on a right inverse.

**Why the uniform version is a hard requirement rather than a convenience.**  The limit `ε → 0` in
the Eilenberg argument uses a *different* approximating partition at every scale, so a constant
depending on the piece is useless; the bound has to hold with one constant on a whole
neighbourhood.  `exists_nhds_uniform_rightInverse_bound` provides that, by perturbing a single
right inverse at the base point: if `A ∘ R₀` stays a unit then `R₀ ∘ (A ∘ R₀)⁻¹` is a right inverse
of `A`, and its norm is controlled because inversion is continuous at a unit.

Neither statement needs an inner product, a measure or completeness of the domain; only the target
is finite-dimensional, and the domain is an arbitrary real normed space.
-/

noncomputable section

open Set Filter Topology
open scoped NNReal

namespace FunctionalInequalities.Analysis

section RightInverse

variable {V W₁ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]

/-- **The core estimate.**  A right inverse `R` of `L` turns every vector into a nearby vector of
the kernel: `z - R (L z)` is killed by `L` and is within `‖R‖ ‖L z‖` of `z`.  No surjectivity,
finite dimension or completeness is used — only the existence of the right inverse. -/
theorem exists_mem_ker_norm_sub_le {L : V →L[ℝ] W₁} {R : W₁ →L[ℝ] V}
    (hR : ∀ y : W₁, L (R y) = y) {C : ℝ} (hC : ‖R‖ ≤ C) (z : V) :
    ∃ w : V, L w = 0 ∧ ‖z - w‖ ≤ C * ‖L z‖ := by
  refine ⟨z - R (L z), ?_, ?_⟩
  · rw [map_sub, hR (L z), sub_self]
  · have hz : z - (z - R (L z)) = R (L z) := by abel
    rw [hz]
    refine (R.le_opNorm _).trans ?_
    gcongr

/-- **`R3`, pointwise.**  A surjection onto a finite-dimensional space admits a single constant `C`
such that every vector is within `C ‖L z‖` of the kernel.

The domain is an arbitrary real normed space: only the target has to be finite-dimensional, which
is what makes the linear right inverse of `L` automatically continuous. -/
theorem exists_rightInverse_bound [FiniteDimensional ℝ W₁] {L : V →L[ℝ] W₁}
    (hL : Function.Surjective L) :
    ∃ C : ℝ≥0, ∀ z : V, ∃ w : V, L w = 0 ∧ ‖z - w‖ ≤ C * ‖L z‖ := by
  have hRI : L.HasRightInverse :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hL
  refine ⟨‖hRI.rightInverse‖₊, fun z => ?_⟩
  exact exists_mem_ker_norm_sub_le hRI.rightInverse_rightInverse
    (le_of_eq (coe_nnnorm hRI.rightInverse).symm) z

end RightInverse

section Uniform

variable {V W₁ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [FiniteDimensional ℝ W₁]

omit [FiniteDimensional ℝ W₁] in
/-- Perturbing a right inverse: if `A ∘ R₀` is a unit of the operator ring, then
`R₀ ∘ (A ∘ R₀)⁻¹` is a right inverse of `A`. -/
theorem rightInverse_comp_inverse {A : V →L[ℝ] W₁} {R₀ : W₁ →L[ℝ] V}
    (h : IsUnit (A.comp R₀)) (y : W₁) :
    A ((R₀.comp (Ring.inverse (A.comp R₀))) y) = y := by
  have hmul : (A.comp R₀) * Ring.inverse (A.comp R₀) = 1 := Ring.mul_inverse_cancel _ h
  have := congrArg (fun T : W₁ →L[ℝ] W₁ => T y) hmul
  simpa using this

/-- **`R3`, locally uniform.**  Around a point where the differential of a `C¹` map is surjective
there is a neighbourhood carrying **one** bound `M` on the differential and **one** constant `C`
for the kernel estimate.

This is the form the route needs: the `ε → 0` limit runs through a different approximating
partition at each scale, so a constant depending on the piece would be useless. -/
theorem exists_nhds_uniform_rightInverse_bound {v : V → W₁} {O : Set V} {x₀ : V}
    (hO : IsOpen O) (hx₀ : x₀ ∈ O) (hv : ContDiffOn ℝ 1 v O)
    (hsurj : Function.Surjective (fderiv ℝ v x₀)) :
    ∃ U ∈ 𝓝 x₀, ∃ C M : ℝ≥0, U ⊆ O ∧ ∀ x ∈ U,
      ‖fderiv ℝ v x‖₊ ≤ M ∧
        ∀ z : V, ∃ w : V, fderiv ℝ v x w = 0 ∧ ‖z - w‖ ≤ C * ‖fderiv ℝ v x z‖ := by
  have : CompleteSpace W₁ := FiniteDimensional.complete ℝ W₁
  have hRI : (fderiv ℝ v x₀).HasRightInverse :=
    ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hsurj
  set R₀ : W₁ →L[ℝ] V := hRI.rightInverse with hR₀def
  have hR₀ : ∀ y : W₁, (fderiv ℝ v x₀) (R₀ y) = y := hRI.rightInverse_rightInverse
  -- the perturbation `A ↦ A ∘ R₀` is a continuous linear map of the operator spaces
  set Φ : (V →L[ℝ] W₁) →L[ℝ] (W₁ →L[ℝ] W₁) :=
    (ContinuousLinearMap.compL ℝ W₁ V W₁).flip R₀ with hΦdef
  have hΦ : ∀ A : V →L[ℝ] W₁, Φ A = A.comp R₀ := fun _ => rfl
  have hΦ₀ : Φ (fderiv ℝ v x₀) = 1 := by
    ext y
    simpa [hΦ] using hR₀ y
  -- the differential is continuous at the base point
  have hfd : ContinuousAt (fun x => fderiv ℝ v x) x₀ :=
    (hv.continuousOn_fderiv_of_isOpen hO le_rfl).continuousAt (hO.mem_nhds hx₀)
  have hΦcont : ContinuousAt (fun x => Φ (fderiv ℝ v x)) x₀ := Φ.continuous.continuousAt.comp hfd
  -- units are open, so the perturbed operator stays invertible nearby
  have hunit : ∀ᶠ x in 𝓝 x₀, IsUnit (Φ (fderiv ℝ v x)) := by
    refine hΦcont (?_ : {B : W₁ →L[ℝ] W₁ | IsUnit B} ∈ 𝓝 (Φ (fderiv ℝ v x₀)))
    rw [hΦ₀]
    exact Units.isOpen.mem_nhds isUnit_one
  -- inversion is continuous at a unit, so the inverse stays bounded nearby
  have hinv1 : ContinuousAt Ring.inverse (Φ (fderiv ℝ v x₀)) := by
    rw [hΦ₀]
    simpa using NormedRing.inverse_continuousAt (1 : (W₁ →L[ℝ] W₁)ˣ)
  have hinv2 : ContinuousAt (fun x => Ring.inverse (Φ (fderiv ℝ v x))) x₀ :=
    Filter.Tendsto.comp hinv1 hΦcont
  have hinvcont : ContinuousAt (fun x => ‖Ring.inverse (Φ (fderiv ℝ v x))‖) x₀ :=
    continuous_norm.continuousAt.comp hinv2
  have hinvval : ‖Ring.inverse (Φ (fderiv ℝ v x₀))‖ < 2 := by
    rw [hΦ₀, Ring.inverse_one]
    exact lt_of_le_of_lt ContinuousLinearMap.norm_id_le one_lt_two
  have hinv : ∀ᶠ x in 𝓝 x₀, ‖Ring.inverse (Φ (fderiv ℝ v x))‖ < 2 :=
    hinvcont.tendsto.eventually_lt_const hinvval
  -- the differential itself stays bounded nearby
  have hnorm : ∀ᶠ x in 𝓝 x₀, ‖fderiv ℝ v x‖ < ‖fderiv ℝ v x₀‖ + 1 :=
    (continuous_norm.continuousAt.comp hfd).tendsto.eventually_lt_const (lt_add_one _)
  -- assemble the neighbourhood
  obtain ⟨U, hUmem, hUsub⟩ :
      ∃ U ∈ 𝓝 x₀, U ⊆ O ∩ {x | IsUnit (Φ (fderiv ℝ v x))}
        ∩ {x | ‖Ring.inverse (Φ (fderiv ℝ v x))‖ < 2}
        ∩ {x | ‖fderiv ℝ v x‖ < ‖fderiv ℝ v x₀‖ + 1} := by
    refine ⟨O ∩ {x | IsUnit (Φ (fderiv ℝ v x))}
        ∩ {x | ‖Ring.inverse (Φ (fderiv ℝ v x))‖ < 2}
        ∩ {x | ‖fderiv ℝ v x‖ < ‖fderiv ℝ v x₀‖ + 1}, ?_, subset_rfl⟩
    exact inter_mem (inter_mem (inter_mem (hO.mem_nhds hx₀) hunit) hinv) hnorm
  refine ⟨U, hUmem, ‖R₀‖₊ * 2, ‖fderiv ℝ v x₀‖₊ + 1,
    fun x hx => ((hUsub hx).1.1.1), fun x hx => ⟨?_, fun z => ?_⟩⟩
  · have h := (hUsub hx).2
    rw [← NNReal.coe_le_coe]
    push_cast
    exact h.le
  · have hu : IsUnit (Φ (fderiv ℝ v x)) := (hUsub hx).1.1.2
    have hb : ‖Ring.inverse (Φ (fderiv ℝ v x))‖ < 2 := (hUsub hx).1.2
    have hcomp : ∀ y : W₁,
        (fderiv ℝ v x) ((R₀.comp (Ring.inverse ((fderiv ℝ v x).comp R₀))) y) = y := by
      intro y
      exact rightInverse_comp_inverse (by rwa [hΦ] at hu) y
    refine exists_mem_ker_norm_sub_le hcomp ?_ z
    rw [hΦ] at hb
    have hcoe : ((‖R₀‖₊ * 2 : ℝ≥0) : ℝ) = ‖R₀‖ * 2 := by push_cast; ring
    rw [hcoe]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left hb.le (norm_nonneg R₀))

end Uniform

end FunctionalInequalities.Analysis
