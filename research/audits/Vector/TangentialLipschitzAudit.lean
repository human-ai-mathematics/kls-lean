import FunctionalInequalities.Analysis.Vector.RankDeficient.TangentialLipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the tangential small-Lipschitz estimate

**What is proved.**  Exactly route obligation `R4` of
`research/audits/Vector/RankDeficientRouteStatements.lean`, whose proposition is restated **verbatim**
below as `route_R4` and discharged.  **No coarea formula, no slicing statement and no Sard theorem
is proved here.**

**What the estimate buys, and what it does not.**  It is the analytic replacement for the step that
fails on a stratum of positive rank: `u` itself is not `ε`-Lipschitz there, but the projected map
`Q ∘ f` is, **along each fibre of `P ∘ f`**, with a constant proportional to `ε`.  The
proportionality constant depends only on `‖A‖`, `‖P‖`, `‖Q‖` and the right-inverse bound, **never
on `ε`, on `f`, on `S` or on the fibre** — that independence is what makes the `ε → 0` limit
possible and is visible in the shape of the statement, `∃ c, ∀ ε, …`.  **It is not the per-stratum
local slicing**: it says nothing about measures, Hausdorff dimension or slices, and it does not
construct the approximating partition that would supply `f` and `S`.

**The kernel hypothesis is necessary, and that is exhibited rather than asserted.**
`ker_hypothesis_necessary` takes the identity of the plane with `P` the first and `Q` the second
coordinate.  The right-inverse hypothesis holds there, since `P ∘ A` is surjective; the kernel
hypothesis fails, since the second basis vector is killed by `P ∘ A` but not by `A`; and the
conclusion of `route_R4` fails outright, because at `ε = 0` it would force the second coordinate to
be constant along the second axis.

**The right-inverse hypothesis is not claimed to be necessary.**  It supplies the *constant*, not a
restriction: in finite dimensions its conclusion is available for every linear map, which this
client does not prove and does not use.  `zero_model_recovers_vanishing_derivative` records the
other end of the range: for the rank-zero stratum `A = 0` both hypotheses hold with `C = 0`, the
constant collapses to `‖Q‖`, and the estimate returns exactly the proved vanishing-derivative
situation in which `f` itself is `ε`-Lipschitz.

**Boundary cases.**  The empty set, `ε = 0` with a genuine linear model, a zero-dimensional
projection target `W₂` (where `Q = 0` and everything is `0`-Lipschitz), and the rank-zero model
`A = 0` are covered.  No inner product, measure, completeness or finite-dimensionality is used by
the estimate itself.
-/

noncomputable section

open Set Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace TangentialLipschitzAudit

/-! ### The route obligation, restated verbatim and discharged -/

/-- **Route obligation `R4`**, copied from
`research/audits/Vector/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_R4 :
    (∀ {V W W₁ W₂ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
      [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
      (A : V →L[ℝ] W) (P : W →L[ℝ] W₁) (Q : W →L[ℝ] W₂) (C : ℝ≥0),
      (∀ z : V, P (A z) = 0 → A z = 0) →
      (∀ z : V, ∃ w : V, P (A w) = 0 ∧ ‖z - w‖ ≤ C * ‖P (A z)‖) →
      ∃ c : ℝ≥0, ∀ (ε : ℝ≥0) (f : V → W) (S : Set V) (s : W₁),
        ApproximatesLinearOn f A S ε →
          LipschitzOnWith (c * ε) (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s})) :=
  fun A P Q C hker hinv => exists_lipschitzOnWith_of_ker_bound A P Q C hker hinv

/-! ### The proved statement is stronger than the route asked for -/

section Strengthened

variable {V W W₁ W₂ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/-- **No inner product and no finite-dimensionality anywhere.** -/
theorem strengthened (A : V →L[ℝ] W) (P : W →L[ℝ] W₁) (Q : W →L[ℝ] W₂) (C : ℝ≥0)
    (hker : ∀ z : V, P (A z) = 0 → A z = 0)
    (hinv : ∀ z : V, ∃ w : V, P (A w) = 0 ∧ ‖z - w‖ ≤ C * ‖P (A z)‖) :
    ∃ c : ℝ≥0, ∀ (ε : ℝ≥0) (f : V → W) (S : Set V) (s : W₁),
      ApproximatesLinearOn f A S ε →
        LipschitzOnWith (c * ε) (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s}) :=
  exists_lipschitzOnWith_of_ker_bound A P Q C hker hinv

/-- **The rank-zero model returns the proved vanishing-derivative situation.**  With `A = 0` both
hypotheses hold with `C = 0`, and the approximation hypothesis then says exactly that `f` is
`ε`-Lipschitz on `S`, so the conclusion is the familiar one with constant `‖Q‖`.  This is the
`r = 0` end of the stratification, already covered by `Analysis/Vector/Slice/Critical.lean`; the
estimate adds nothing there and claims nothing new. -/
theorem zero_model_recovers_vanishing_derivative (P : W →L[ℝ] W₁) (Q : W →L[ℝ] W₂) :
    ∃ c : ℝ≥0, ∀ (ε : ℝ≥0) (f : V → W) (S : Set V) (s : W₁),
      ApproximatesLinearOn f (0 : V →L[ℝ] W) S ε →
        LipschitzOnWith (c * ε) (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s}) := by
  refine exists_lipschitzOnWith_of_ker_bound (0 : V →L[ℝ] W) P Q 0 (fun z _ => rfl) fun z => ?_
  exact ⟨z, by simp, by simp⟩

/-- **A zero-dimensional projection target makes the conclusion trivial**: `Q = 0`, so the
projected map is constant and `0`-Lipschitz. -/
theorem zero_dimensional_projection_target [Subsingleton W₂] (_A : V →L[ℝ] W) (P : W →L[ℝ] W₁)
    (Q : W →L[ℝ] W₂) (f : V → W) (S : Set V) (s : W₁) (K : ℝ≥0) :
    LipschitzOnWith K (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s}) :=
  LipschitzOnWith.of_dist_le_mul fun x _ y _ => by
    rw [Subsingleton.elim (Q (f x)) (Q (f y)), dist_self]
    positivity

/-- **The empty set and `ε = 0` are harmless**, which the statement covers without a side
condition. -/
theorem empty_set (_A : V →L[ℝ] W) (P : W →L[ℝ] W₁) (Q : W →L[ℝ] W₂) (f : V → W) (s : W₁)
    (K : ℝ≥0) :
    LipschitzOnWith K (fun x => Q (f x)) ((∅ : Set V) ∩ {x : V | P (f x) = s}) := by
  simp [LipschitzOnWith]

end Strengthened

/-! ### The kernel hypothesis is necessary -/

section Necessity

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The identity of the plane, the linear model of the counterexample. -/
abbrev idP : Plane →L[ℝ] Plane := ContinuousLinearMap.id ℝ Plane

/-- The first coordinate functional. -/
def coord₀ : Plane →L[ℝ] ℝ := innerSL ℝ (EuclideanSpace.single 0 (1 : ℝ))

/-- The second coordinate functional. -/
def coord₁ : Plane →L[ℝ] ℝ := innerSL ℝ (EuclideanSpace.single 1 (1 : ℝ))

@[simp] theorem coord₀_apply (x : Plane) :
    coord₀ x = (⟪EuclideanSpace.single 0 (1 : ℝ), x⟫ : ℝ) := rfl

@[simp] theorem coord₁_apply (x : Plane) :
    coord₁ x = (⟪EuclideanSpace.single 1 (1 : ℝ), x⟫ : ℝ) := rfl

/-- **Dropping the kernel hypothesis makes `route_R4` false**, and the other hypothesis is not what
is missing.  For `A` the identity of the plane, `P` the first and `Q` the second coordinate:

* the right-inverse hypothesis **holds**, because `P ∘ A` is surjective onto `ℝ`;
* the kernel hypothesis **fails**, because the second basis vector is killed by `P ∘ A` and not by
  `A`;
* the conclusion of `route_R4` **fails**, because at `ε = 0` with `f = A` it would force the second
  coordinate to be constant along the second axis, which it is not.

So the estimate is not a statement about the approximation alone: it is exactly the assertion that
the linear model dies along the fibre directions. -/
theorem ker_hypothesis_necessary :
    (∃ C : ℝ≥0, ∀ z : Plane, ∃ w : Plane,
        coord₀ (idP w) = 0 ∧ ‖z - w‖ ≤ C * ‖coord₀ (idP z)‖) ∧
      (∃ z : Plane, coord₀ (idP z) = 0 ∧ idP z ≠ 0) ∧
      ¬ ∃ c : ℝ≥0, ∀ (ε : ℝ≥0) (f : Plane → Plane) (S : Set Plane) (s : ℝ),
          ApproximatesLinearOn f idP S ε →
            LipschitzOnWith (c * ε) (fun x => coord₁ (f x))
              (S ∩ {x : Plane | coord₀ (f x) = s}) := by
  refine ⟨?_, ?_, ?_⟩
  · have hsurj : Function.Surjective (coord₀.comp idP) := by
      intro c
      refine ⟨EuclideanSpace.single 0 c, ?_⟩
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, coord₀_apply,
        EuclideanSpace.inner_single_left]
      simp
    exact exists_rightInverse_bound hsurj
  · refine ⟨EuclideanSpace.single 1 (1 : ℝ), ?_, ?_⟩
    · rw [ContinuousLinearMap.id_apply, coord₀_apply, EuclideanSpace.inner_single_left]
      simp
    · rw [ContinuousLinearMap.id_apply]
      intro h
      have := congrFun (congrArg (fun v : Plane => (WithLp.ofLp v)) h) 1
      simp at this
  · rintro ⟨c, hc⟩
    have happ : ApproximatesLinearOn (fun x : Plane => x) idP Set.univ 0 := by
      intro x _ y _
      simp
    have hlip := hc 0 (fun x : Plane => x) Set.univ 0 happ
    rw [mul_zero] at hlip
    have hmem0 : (0 : Plane) ∈ Set.univ ∩ {x : Plane | coord₀ x = 0} := by
      refine ⟨Set.mem_univ _, ?_⟩
      simp
    have hmem1 : EuclideanSpace.single 1 (1 : ℝ) ∈ Set.univ ∩ {x : Plane | coord₀ x = 0} := by
      refine ⟨Set.mem_univ _, ?_⟩
      show coord₀ (EuclideanSpace.single 1 (1 : ℝ)) = 0
      rw [coord₀_apply, EuclideanSpace.inner_single_left]
      simp
    have hd := hlip.dist_le_mul _ hmem1 _ hmem0
    rw [NNReal.coe_zero, zero_mul] at hd
    have h1 : coord₁ (EuclideanSpace.single 1 (1 : ℝ)) = 1 := by
      rw [coord₁_apply, EuclideanSpace.inner_single_left]
      simp
    have h0 : coord₁ (0 : Plane) = 0 := by simp
    rw [dist_eq_norm, h1, h0] at hd
    norm_num at hd

end Necessity

/-! ### What the three proved obligations combine to on a rank stratum -/

section Stratum

variable {V W W₁ W₂ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/-- **A corollary of the three proved obligations, not a new one.**  At a point of the rank
stratum, with `P` a projection onto a space of the same dimension as the range of the differential
and `P ∘ A` surjective, the two hypotheses of `route_R4` are automatic and the projected map is
`c ε`-Lipschitz along every fibre.

This is **not the per-stratum local slicing**: no measure, no Hausdorff dimension, no slice and no
approximating partition appears. -/
theorem stratum_combination {A : V →L[ℝ] W} {P : W →L[ℝ] W₁} (Q : W →L[ℝ] W₂)
    (hsurj : Function.Surjective (P.comp A))
    (hrank : finrank ℝ W₁ = finrank ℝ (LinearMap.range (A : V →ₗ[ℝ] W))) :
    ∃ c : ℝ≥0, ∀ (ε : ℝ≥0) (f : V → W) (S : Set V) (s : W₁),
      ApproximatesLinearOn f A S ε →
        LipschitzOnWith (c * ε) (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s}) :=
  exists_lipschitzOnWith_fibre Q hsurj hrank

end Stratum

end TangentialLipschitzAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.norm_comp_apply_sub_le_of_approximatesLinearOn
#print axioms FunctionalInequalities.Analysis.exists_lipschitzOnWith_of_ker_bound
#print axioms FunctionalInequalities.Analysis.exists_lipschitzOnWith_fibre
#print axioms TangentialLipschitzAudit.route_R4
#print axioms TangentialLipschitzAudit.strengthened
#print axioms TangentialLipschitzAudit.zero_model_recovers_vanishing_derivative
#print axioms TangentialLipschitzAudit.zero_dimensional_projection_target
#print axioms TangentialLipschitzAudit.empty_set
#print axioms TangentialLipschitzAudit.ker_hypothesis_necessary
#print axioms TangentialLipschitzAudit.stratum_combination
