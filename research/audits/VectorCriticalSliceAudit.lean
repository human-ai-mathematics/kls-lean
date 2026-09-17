import FunctionalInequalities.Analysis.Vector.CriticalSlice
import FunctionalInequalities.KLS.Geometry.SmoothCoarea
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the codimension-`m` vanishing-derivative slices

**What is proved.**  `ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero`: for a `C¹` map into an
`m`-dimensional target with `m ≥ 1`, almost every level meets `{x | fderiv ℝ u x = 0}` in an
`ℋ^{n-m}`-null set.  The proof is the scalar argument with the codimension-`m` Eilenberg bound:
the derivative vanishes, so the approximating partition makes `u` `ε`-Lipschitz on disjoint pieces,
and the bound's constant `ε ^ m` tends to `0`.  With it,
`coarea_of_contDiff_of_critical_eq_zeroDeriv` extends the regular-case coarea formula to the whole
space **under the hypothesis that the derivative vanishes wherever it fails to be surjective**.

**`m = 1` gives back the proved scalar statements.**  `scalar_L10` reproduces
`KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` and `scalar_L11` reproduces
`KLS.coarea_of_contDiff`, both discharged from the codimension-`m` versions; as in the previous
rounds the recovery carries the extra hypothesis `1 ≤ finrank V`.

**What is not proved, and the gap is exhibited, not asserted.**  For `m ≥ 2` the coarea critical set
is `{x | fderiv ℝ u x` is not surjective`}`, which is **strictly larger** than the
vanishing-derivative set.  `rank_deficient_witness` below exhibits a linear map of the plane of rank
one: its derivative is **nowhere zero** and **nowhere surjective**, so the vanishing-derivative set
is empty while the critical set is everything, and the hypothesis of
`coarea_of_contDiff_of_critical_eq_zeroDeriv` fails at every point.  Nothing here covers the
rank-deficient part, so the **general codimension-`m` coarea formula remains open**.  No Sard
theorem is claimed.  Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy
holes are untouched.
-/

noncomputable section

open Set MeasureTheory Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace VectorCriticalSliceAudit

section Restatements

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **The vanishing-derivative slices are null, restated from scratch.**  `u` is only `C¹`; nothing
is assumed about the set of critical values. -/
theorem zeroDeriv_slices {u : V → W} (hu : ContDiff ℝ 1 u) {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hm : 0 < finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 :=
  ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero hu hk hm

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
/-- **A subsingleton target makes every derivative vanish**, which is why `0 < finrank W` is a
hypothesis: without it the vanishing-derivative set is the whole space and its slices are the whole
slices. -/
theorem zero_dimensional_target_everything_critical [Subsingleton W] (u : V → W) (x : V) :
    fderiv ℝ u x = 0 := by
  ext y
  exact Subsingleton.elim _ _

/-- **A constant map is entirely critical**, and the conclusion is still correct: its only nonempty
slice sits at a single level, which is null in the target. -/
theorem constant_map (c : W) {k : ℕ} (hk : k + finrank ℝ W = finrank ℝ V)
    (hm : 0 < finrank ℝ W) :
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] ({x : V | fderiv ℝ (fun _ : V => c) x = 0} ∩ {x | (fun _ : V => c) x = t})
        = 0 :=
  ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero contDiff_const hk hm

/-- **The coarea formula under the no-intermediate-rank hypothesis, restated from scratch.** -/
theorem coarea_no_intermediate_rank {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ}
    (hk : k + finrank ℝ W = finrank ℝ V) (hm : 0 < finrank ℝ W) (hu : ContDiff ℝ 1 u)
    (hcrit : ∀ x : V, Function.Surjective ((fderiv ℝ u x : V →ₗ[ℝ] W)) ∨ fderiv ℝ u x = 0)
    (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
      (volume : Measure W) ∧
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
          ∂(volume : Measure W)) :=
  coarea_of_contDiff_of_critical_eq_zeroDeriv hk hm hu
    (fun x => (hcrit x).imp (fun h => (coareaJacobian_ne_zero_iff _).2 h) id) hS hg

end Restatements

/-! ### `m = 1` gives back the proved scalar statements -/

section CodimensionOne

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [MeasurableSpace V] [BorelSpace V] in
/-- In codimension one a nonzero differential is surjective, so the dichotomy of
`coarea_of_contDiff_of_critical_eq_zeroDeriv` is automatic. -/
theorem scalar_dichotomy (u : V → ℝ) (x : V) :
    coareaJacobian (fderiv ℝ u x) ≠ 0 ∨ fderiv ℝ u x = 0 := by
  by_cases h : fderiv ℝ u x = 0
  · exact Or.inr h
  refine Or.inl ((coareaJacobian_ne_zero_iff _).2 fun c => ?_)
  obtain ⟨v, hv⟩ : ∃ v : V, fderiv ℝ u x v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (ContinuousLinearMap.ext hcon)
  refine ⟨(c / fderiv ℝ u x v) • v, ?_⟩
  simp only [ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
  field_simp

/-- **`m = 1` is the proved scalar `L10`**, `KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero`,
reproduced verbatim from the codimension-`m` version.  The extra `1 ≤ finrank V` is the same honest
difference as in the previous rounds: the codimension-`m` statements assume the fibre dimension and
the codimension add up to the ambient dimension. -/
theorem scalar_L10 {u : V → ℝ} (hn : 1 ≤ finrank ℝ V) (hu : ContDiff ℝ 1 u) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      KLS.surfaceMeasure V ({x : V | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0 := by
  have hk : (finrank ℝ V - 1) + finrank ℝ ℝ = finrank ℝ V := by rw [finrank_self]; omega
  have hm : 0 < finrank ℝ ℝ := by rw [finrank_self]; omega
  have h := ae_hausdorffNormalized_zeroDeriv_inter_levelSet_eq_zero (V := V) (W := ℝ) hu hk hm
  filter_upwards [h] with t ht
  exact ht

/-- **`m = 1` is the proved scalar `L11`**, `KLS.coarea_of_contDiff`, reproduced verbatim from the
codimension-`m` version. -/
theorem scalar_L11 {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞} (hn : 1 ≤ finrank ℝ V)
    (hu : ContDiff ℝ 1 u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ)) := by
  have hk : (finrank ℝ V - 1) + finrank ℝ ℝ = finrank ℝ V := by rw [finrank_self]; omega
  have hm : 0 < finrank ℝ ℝ := by rw [finrank_self]; omega
  obtain ⟨hmeas, heq⟩ := coarea_of_contDiff_of_critical_eq_zeroDeriv (V := V) (W := ℝ)
    (S := S) (g := g) hk hm hu (scalar_dichotomy u) hS hg
  have hdens : ∀ x : V, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) = ‖gradient u x‖ₑ := by
    intro x
    rw [coareaJacobian_fderiv, ofReal_norm]
  simp_rw [hdens] at heq
  exact ⟨hmeas, heq⟩

end CodimensionOne

/-! ### The rank-deficient gap is real -/

section Gap

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- A rank-one endomorphism of the plane: the orthogonal projection onto the first axis. -/
def proj₀ : Plane →L[ℝ] Plane :=
  (innerSL ℝ (EuclideanSpace.single 0 (1 : ℝ))).smulRight (EuclideanSpace.single 0 (1 : ℝ))

@[simp] theorem proj₀_apply (x : Plane) :
    proj₀ x = (⟪EuclideanSpace.single 0 (1 : ℝ), x⟫ : ℝ) • EuclideanSpace.single 0 (1 : ℝ) := rfl

/-- **The gap between the vanishing-derivative set and the critical set is real.**  For the rank-one
map of the plane the derivative is **nowhere zero** and **nowhere surjective**: the
vanishing-derivative set is empty while the coarea critical set is everything, and the hypothesis of
`coarea_of_contDiff_of_critical_eq_zeroDeriv` fails at every point. -/
theorem rank_deficient_witness (x : Plane) :
    fderiv ℝ (proj₀ : Plane → Plane) x ≠ 0 ∧
      coareaJacobian (fderiv ℝ (proj₀ : Plane → Plane) x) = 0 := by
  have hfd : fderiv ℝ (proj₀ : Plane → Plane) x = proj₀ := proj₀.fderiv
  constructor
  · rw [hfd]
    intro hzero
    have h := congrArg (fun T : Plane →L[ℝ] Plane => T (EuclideanSpace.single 0 (1 : ℝ)))
      hzero
    simp only [proj₀_apply, zero_apply] at h
    rw [EuclideanSpace.inner_single_left] at h
    simp at h
  · rw [hfd, coareaJacobian_eq_zero_iff]
    intro hsurj
    obtain ⟨y, hy⟩ := hsurj (EuclideanSpace.single 1 (1 : ℝ))
    have h := congrFun (congrArg (fun v : Plane => (WithLp.ofLp v)) hy) 1
    simp only [ContinuousLinearMap.coe_coe, proj₀_apply] at h
    simp at h

end Gap

end VectorCriticalSliceAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.isClosed_zeroDeriv
#print axioms FunctionalInequalities.Analysis.exists_lipschitzOnWith_zeroDeriv_cover
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_zeroDeriv_ball_eq_zero
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.Analysis.ae_hausdorffNormalized_zeroDeriv_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.Analysis.isOpen_coareaJacobian_ne_zero
#print axioms FunctionalInequalities.Analysis.coarea_of_contDiff_of_critical_eq_zeroDeriv
#print axioms VectorCriticalSliceAudit.zeroDeriv_slices
#print axioms VectorCriticalSliceAudit.zero_dimensional_target_everything_critical
#print axioms VectorCriticalSliceAudit.constant_map
#print axioms VectorCriticalSliceAudit.coarea_no_intermediate_rank
#print axioms VectorCriticalSliceAudit.scalar_dichotomy
#print axioms VectorCriticalSliceAudit.scalar_L10
#print axioms VectorCriticalSliceAudit.scalar_L11
#print axioms VectorCriticalSliceAudit.rank_deficient_witness

/-! The repository's scalar `L10` and `L11`, for comparison; they are proved independently. -/
#print axioms FunctionalInequalities.KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero
#print axioms FunctionalInequalities.KLS.coarea_of_contDiff
