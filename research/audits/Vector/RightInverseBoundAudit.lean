import FunctionalInequalities.Analysis.Vector.RankDeficient.RightInverseBound
import FunctionalInequalities.Analysis.Vector.Jacobian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the approximate right inverse, pointwise and locally uniform

**What is proved.**  Exactly route obligation `R3` of
`research/audits/Vector/RankDeficientRouteStatements.lean`, whose two propositions are restated
**verbatim** below as `route_R3_pointwise` and `route_R3_uniform` and discharged.  **No coarea
formula, no slicing statement and no Sard theorem is proved here.**

**The library statements are stronger than the route asked for.**  `exists_rightInverse_bound` and
`exists_nhds_uniform_rightInverse_bound` need **no inner product** and **no finite-dimensionality
of the domain**: the domain is an arbitrary real normed space and only the target is
finite-dimensional.  `strengthened_pointwise` and `strengthened_uniform` record that.  The route's
`coareaJacobian (fderiv ℝ v x₀) ≠ 0` is converted to surjectivity by the proved
`coareaJacobian_ne_zero_iff`, so the inner-product hypotheses enter only through that translation.

**What surjectivity is and is not needed for, recorded so the obligation is not overstated.**
It is what makes the right inverse exist: `no_right_inverse` shows the rank-one projection of the
plane admits none.  It is **not** forced by the pointwise conclusion:
`pointwise_conclusion_does_not_imply_surjective` shows the zero map satisfies that conclusion with
`C = 0` while failing to be surjective.  For the **locally uniform** half the hypothesis at the base
point does real work: `uniform_constant_degenerates` shows that along `t • id` the smallest
admissible constant is `|t|⁻¹`, which blows up as the family approaches the non-surjective `0`, so
no neighbourhood of such a point carries a single constant.

**Boundary cases.**  A zero-dimensional target (every map surjective, `C = 0` works and every
vector is already in the kernel), a linear isomorphism (the right inverse is the inverse), and the
zero map into a zero-dimensional target are covered.  The uniform statement is checked on a
constant differential, where the neighbourhood may be taken to be the whole open set.
-/

noncomputable section

open Set Filter Topology Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace RightInverseBoundAudit

/-! ### The route obligations, restated verbatim and discharged -/

/-- **Route obligation `R3`, pointwise**, copied from
`research/audits/Vector/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_R3_pointwise :
    (∀ {V W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
      (L : V →L[ℝ] W₁), Function.Surjective L →
      ∃ C : ℝ≥0, ∀ z : V, ∃ w : V, L w = 0 ∧ ‖z - w‖ ≤ C * ‖L z‖) :=
  fun _ hL => exists_rightInverse_bound hL

/-- **Route obligation `R3` of `RankDeficientRouteStatements.lean`, locally uniform**, copied
verbatim and discharged.  The route states the regularity hypothesis as
`coareaJacobian (fderiv ℝ v x₀) ≠ 0`; the proved `coareaJacobian_ne_zero_iff` turns it into
surjectivity of the differential. -/
theorem route_R3_uniform :
    (∀ {V W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
      {v : V → W₁} {O : Set V} {x₀ : V}, IsOpen O → x₀ ∈ O → ContDiffOn ℝ 1 v O →
      coareaJacobian (fderiv ℝ v x₀) ≠ 0 →
      ∃ U ∈ nhds x₀, ∃ C M : ℝ≥0, U ⊆ O ∧ ∀ x ∈ U,
        ‖fderiv ℝ v x‖₊ ≤ M ∧
          ∀ z : V, ∃ w : V, fderiv ℝ v x w = 0 ∧ ‖z - w‖ ≤ C * ‖fderiv ℝ v x z‖) :=
  fun hO hx₀ hv hreg =>
    exists_nhds_uniform_rightInverse_bound hO hx₀ hv ((coareaJacobian_ne_zero_iff _).1 hreg)

/-! ### The proved statements are stronger than the route asked for -/

section Strengthened

variable {V W₁ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [FiniteDimensional ℝ W₁]

/-- **No inner product and no finite-dimensional domain** are needed for the pointwise bound. -/
theorem strengthened_pointwise {L : V →L[ℝ] W₁} (hL : Function.Surjective L) :
    ∃ C : ℝ≥0, ∀ z : V, ∃ w : V, L w = 0 ∧ ‖z - w‖ ≤ C * ‖L z‖ :=
  exists_rightInverse_bound hL

/-- **No inner product and no finite-dimensional domain** are needed for the uniform bound either;
the regularity hypothesis is plain surjectivity of the differential. -/
theorem strengthened_uniform {v : V → W₁} {O : Set V} {x₀ : V}
    (hO : IsOpen O) (hx₀ : x₀ ∈ O) (hv : ContDiffOn ℝ 1 v O)
    (hsurj : Function.Surjective (fderiv ℝ v x₀)) :
    ∃ U ∈ nhds x₀, ∃ C M : ℝ≥0, U ⊆ O ∧ ∀ x ∈ U,
      ‖fderiv ℝ v x‖₊ ≤ M ∧
        ∀ z : V, ∃ w : V, fderiv ℝ v x w = 0 ∧ ‖z - w‖ ≤ C * ‖fderiv ℝ v x z‖ :=
  exists_nhds_uniform_rightInverse_bound hO hx₀ hv hsurj

omit [FiniteDimensional ℝ W₁] in
/-- **The core estimate needs no surjectivity at all**: any right inverse, however obtained, gives
the bound with its own norm. -/
theorem core_needs_only_a_right_inverse {L : V →L[ℝ] W₁} {R : W₁ →L[ℝ] V}
    (hR : ∀ y : W₁, L (R y) = y) (z : V) :
    ∃ w : V, L w = 0 ∧ ‖z - w‖ ≤ ‖R‖ * ‖L z‖ :=
  exists_mem_ker_norm_sub_le hR le_rfl z

end Strengthened

/-! ### What surjectivity is and is not needed for -/

section Necessity

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- A rank-one endomorphism of the plane: the orthogonal projection onto the first axis. -/
def proj₀ : Plane →L[ℝ] Plane :=
  (innerSL ℝ (EuclideanSpace.single 0 (1 : ℝ))).smulRight (EuclideanSpace.single 0 (1 : ℝ))

@[simp] theorem proj₀_apply (x : Plane) :
    proj₀ x = (⟪EuclideanSpace.single 0 (1 : ℝ), x⟫ : ℝ) • EuclideanSpace.single 0 (1 : ℝ) := rfl

/-- **The hypothesis of the right-inverse bound is not vacuous: without surjectivity there is no
right inverse.**  The rank-one projection of the plane admits none, so the *construction* used to
prove the bound is unavailable for it. -/
theorem no_right_inverse (R : Plane →L[ℝ] Plane) :
    ¬ (∀ y : Plane, proj₀ (R y) = y) := by
  intro h
  have h0 := h (EuclideanSpace.single 1 (1 : ℝ))
  have h1 := congrFun (congrArg (fun v : Plane => (WithLp.ofLp v)) h0) 1
  simp only [proj₀_apply] at h1
  simp at h1

/-- `proj₀` is not surjective, which is why `no_right_inverse` is possible. -/
theorem proj₀_not_surjective : ¬ Function.Surjective proj₀ := by
  intro hsurj
  obtain ⟨y, hy⟩ := hsurj (EuclideanSpace.single 1 (1 : ℝ))
  have h1 := congrFun (congrArg (fun v : Plane => (WithLp.ofLp v)) hy) 1
  simp only [proj₀_apply] at h1
  simp at h1

/-- **But the pointwise conclusion of the bound does not characterize surjectivity**, and this is
recorded so that the obligation is not overstated.  For the zero map into any target the conclusion
holds with `C = 0`, because every vector already lies in the kernel, while the zero map into a
nonzero target is not surjective.  Surjectivity is what makes the *right inverse* exist; it is not
forced by the estimate. -/
theorem pointwise_conclusion_does_not_imply_surjective
    {V W₁ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] (z : V) :
    ∃ w : V, (0 : V →L[ℝ] W₁) w = 0 ∧ ‖z - w‖ ≤ (0 : ℝ≥0) * ‖(0 : V →L[ℝ] W₁) z‖ := by
  refine ⟨z, rfl, ?_⟩
  simp

/-- **The uniform constant of the bound genuinely degenerates where surjectivity fails**, so for
the locally uniform half the hypothesis at the base point is doing real work.

Along the family `t • id` of endomorphisms of `ℝ` the smallest admissible constant is `|t|⁻¹`: for
`t ≠ 0` the kernel is trivial, so the only candidate is `w = 0` and the estimate at `z = 1` reads
`1 ≤ C * t`.  Since `t • id` tends to the non-surjective `0` as `t → 0`, this particular family admits no single kernel-estimate constant on a neighbourhood of `t = 0`.
This does not rule out a uniform estimate for other non-surjective families, such as the
constant zero family. -/
theorem uniform_constant_degenerates (C : ℝ≥0) {t : ℝ} (ht : 0 < t) (htC : t * C < 1) :
    ¬ ∀ z : ℝ, ∃ w : ℝ, (t • (ContinuousLinearMap.id ℝ ℝ)) w = 0 ∧
        ‖z - w‖ ≤ C * ‖(t • (ContinuousLinearMap.id ℝ ℝ)) z‖ := by
  intro h
  obtain ⟨w, hw, hle⟩ := h 1
  have hw0 : w = 0 := by
    have : t * w = 0 := by simpa using hw
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' ht.ne'
    · exact h'
  rw [hw0] at hle
  have h1 : (1 : ℝ) ≤ (C : ℝ) * t := by simpa [abs_of_pos ht] using hle
  nlinarith [h1, htC]

end Necessity

/-! ### Boundary cases -/

section Boundary

variable {V W₁ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [FiniteDimensional ℝ W₁]

section DegenerateRightInverses

omit [FiniteDimensional ℝ W₁]
/-- **A zero-dimensional target**: every map is surjective, every vector is already in the kernel
and the constant `0` works. -/
theorem zero_dimensional_target [Subsingleton W₁] (L : V →L[ℝ] W₁) (z : V) :
    L z = 0 ∧ ‖z - z‖ ≤ (0 : ℝ≥0) * ‖L z‖ := by
  refine ⟨Subsingleton.elim _ _, ?_⟩
  simp

/-- **A linear isomorphism**: the inverse is a right inverse, so the constant is its norm. -/
theorem linear_equiv (e : V ≃L[ℝ] W₁) (z : V) :
    ∃ w : V, (e : V →L[ℝ] W₁) w = 0 ∧
      ‖z - w‖ ≤ ‖(e.symm : W₁ →L[ℝ] V)‖ * ‖(e : V →L[ℝ] W₁) z‖ :=
  exists_mem_ker_norm_sub_le (L := (e : V →L[ℝ] W₁)) (R := (e.symm : W₁ →L[ℝ] V))
    (fun y => by simp) le_rfl z

end DegenerateRightInverses

/-- **A constant map on an open set**: the differential vanishes identically, so the surjectivity-based
theorem applies when the target is zero-dimensional. The kernel-estimate conclusion itself also
holds for constant maps into nonzero targets, with `C = M = 0`; this example uses the theorem. -/
theorem constant_map [Subsingleton W₁] {O : Set V} {x₀ : V} (hO : IsOpen O) (hx₀ : x₀ ∈ O)
    (c : W₁) :
    ∃ U ∈ nhds x₀, ∃ C M : ℝ≥0, U ⊆ O ∧ ∀ x ∈ U,
      ‖fderiv ℝ (fun _ : V => c) x‖₊ ≤ M ∧
        ∀ z : V, ∃ w : V, fderiv ℝ (fun _ : V => c) x w = 0 ∧
          ‖z - w‖ ≤ C * ‖fderiv ℝ (fun _ : V => c) x z‖ := by
  refine exists_nhds_uniform_rightInverse_bound hO hx₀ contDiffOn_const ?_
  exact fun y => ⟨0, Subsingleton.elim _ _⟩

end Boundary

end RightInverseBoundAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.exists_mem_ker_norm_sub_le
#print axioms FunctionalInequalities.Analysis.exists_rightInverse_bound
#print axioms FunctionalInequalities.Analysis.rightInverse_comp_inverse
#print axioms FunctionalInequalities.Analysis.exists_nhds_uniform_rightInverse_bound
#print axioms RightInverseBoundAudit.route_R3_pointwise
#print axioms RightInverseBoundAudit.route_R3_uniform
#print axioms RightInverseBoundAudit.strengthened_pointwise
#print axioms RightInverseBoundAudit.strengthened_uniform
#print axioms RightInverseBoundAudit.core_needs_only_a_right_inverse
#print axioms RightInverseBoundAudit.no_right_inverse
#print axioms RightInverseBoundAudit.proj₀_not_surjective
#print axioms RightInverseBoundAudit.pointwise_conclusion_does_not_imply_surjective
#print axioms RightInverseBoundAudit.uniform_constant_degenerates
#print axioms RightInverseBoundAudit.zero_dimensional_target
#print axioms RightInverseBoundAudit.linear_equiv
#print axioms RightInverseBoundAudit.constant_map
