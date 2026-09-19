import FunctionalInequalities.Analysis.Vector.RankDeficient.RegularFibreFinite
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the finiteness of the regular fibres

**What is proved.**  Exactly route obligation `R5` of
`research/audits/RankDeficientRouteStatements.lean`, whose proposition is restated **verbatim**
below as `route_R5` and discharged.  With `R1`–`R4` and `R6` that is six of the route's thirteen
numbered items.  **`R0`, `R7`–`R10`, `N1` and `N2` are still open**, and so is the rank-deficient
part of the codimension-`m` coarea critical set.  **No coarea formula in a new case, no slicing
statement about the critical set and no Sard theorem is proved here.**

**Relative compactness is necessary, and that is exhibited rather than asserted.**
`relative_compactness_necessary` takes the first coordinate functional of the plane, which is
regular everywhere, on `S = univ`: every fibre is a full line, whose `ℋ^1` measure is infinite, so
the conclusion fails at every level while every other hypothesis holds.  The hypothesis is
therefore not a convenience of the proof.

**Nothing is claimed off the regular set.**  `R5` assumes the differential is surjective on all of
`O`; the critical set of `v` is outside its reach, which is the whole reason the route needs the
rest of the obligations.

**Boundary cases.**  The empty piece, and the transfer between the normalized and the raw Hausdorff
measure in both directions (`hausdorffNormalized_ne_top_iff`), are covered.

Sharp finite-regularity Sard, the two Cheeger comparisons and the five Energy holes are untouched.
-/

noncomputable section

open MeasureTheory Set Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

namespace RegularFibreFiniteAudit

/-! ### The route obligation, restated verbatim and discharged -/

/-- **Route obligation `R5`**, copied from
`research/audits/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_R5 :
    (∀ {V W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
      [MeasurableSpace W₁] [BorelSpace W₁]
      {O S : Set V} {v : V → W₁}, IsOpen O → ContDiffOn ℝ 1 v O →
      (∀ x ∈ O, coareaJacobian (fderiv ℝ v x) ≠ 0) → MeasurableSet S →
      IsCompact (closure S) → closure S ⊆ O →
      ∀ᵐ s ∂(volume : Measure W₁),
        μH[((finrank ℝ V - finrank ℝ W₁ : ℕ) : ℝ)] (S ∩ {x : V | v x = s}) ≠ ⊤) :=
  fun hO hv hreg hS hK hSO => ae_hausdorffMeasure_fibre_ne_top hO hv hreg hS hK hSO

/-! ### The normalized and raw measures agree on finiteness -/

section Transfer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Both directions of the transfer used to state `R5` with the raw measure while the proved coarea
formula uses the normalized one. -/
theorem transfer (k : ℕ) (A : Set V) :
    (KLS.hausdorffNormalized V k A ≠ ⊤ ↔ μH[(k : ℝ)] A ≠ ⊤) :=
  hausdorffNormalized_ne_top_iff k A

/-- **The empty piece** is covered with no side condition. -/
theorem empty_piece {W₁ : Type*} [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁]
    [FiniteDimensional ℝ W₁] [MeasurableSpace W₁] [BorelSpace W₁] {O : Set V} {v : V → W₁}
    (hO : IsOpen O) (hv : ContDiffOn ℝ 1 v O)
    (hreg : ∀ x ∈ O, coareaJacobian (fderiv ℝ v x) ≠ 0) :
    ∀ᵐ s ∂(volume : Measure W₁),
      μH[((finrank ℝ V - finrank ℝ W₁ : ℕ) : ℝ)] ((∅ : Set V) ∩ {x : V | v x = s}) ≠ ⊤ := by
  refine ae_hausdorffMeasure_fibre_ne_top hO hv hreg MeasurableSet.empty ?_ ?_
  · rw [closure_empty]; exact isCompact_empty
  · rw [closure_empty]; exact empty_subset O

end Transfer

/-! ### Relative compactness is necessary -/

section Necessity

/-- The plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate functional on the plane: a submersion onto `ℝ`, regular everywhere. -/
def coord₀ : Plane →L[ℝ] ℝ := innerSL ℝ (EuclideanSpace.single 0 (1 : ℝ))

@[simp] theorem coord₀_apply (x : Plane) :
    coord₀ x = (⟪EuclideanSpace.single 0 (1 : ℝ), x⟫ : ℝ) := rfl

/-- The second coordinate axis, translated to height `s`, parametrized isometrically by `ℝ`. -/
def line (s : ℝ) : ℝ → Plane :=
  fun t => EuclideanSpace.single 1 t + EuclideanSpace.single 0 s

theorem isometry_line (s : ℝ) : Isometry (line s) := by
  refine Isometry.of_dist_eq fun a b => ?_
  have h : line s a - line s b = EuclideanSpace.single 1 (a - b) := by
    simp only [line, add_sub_add_right_eq_sub, ← PiLp.single_sub]
  rw [dist_eq_norm, dist_eq_norm, h, PiLp.norm_single, Real.norm_eq_abs]

theorem coord₀_line (s : ℝ) (t : ℝ) : coord₀ (line s t) = s := by
  simp only [line, coord₀_apply, inner_add_right, EuclideanSpace.inner_single_right]
  simp

/-- **Dropping relative compactness makes `R5` false.**  The first coordinate functional of the
plane is a submersion everywhere, so every hypothesis of `R5` except the compactness of the closure
holds for `S = univ`; but each fibre is a full line and carries infinite `ℋ^1` measure, so the
conclusion fails at **every** level, not merely on a null set of them. -/
theorem relative_compactness_necessary :
    (∀ x ∈ (univ : Set Plane), coareaJacobian (fderiv ℝ coord₀ x) ≠ 0) ∧
      ¬ IsCompact (closure (univ : Set Plane)) ∧
      ∀ s : ℝ, μH[((finrank ℝ Plane - finrank ℝ ℝ : ℕ) : ℝ)]
          ((univ : Set Plane) ∩ {x : Plane | coord₀ x = s}) = ⊤ := by
  refine ⟨fun x _ => ?_, ?_, fun s => ?_⟩
  · rw [coord₀.fderiv, coareaJacobian_ne_zero_iff]
    intro c
    refine ⟨EuclideanSpace.single 0 c, ?_⟩
    rw [ContinuousLinearMap.coe_coe, coord₀_apply, EuclideanSpace.inner_single_left]
    simp
  · rw [closure_univ]
    exact noncompact_univ Plane
  · have hdim : (finrank ℝ Plane - finrank ℝ ℝ : ℕ) = 1 := by
      simp [finrank_euclideanSpace, finrank_self]
    rw [hdim]
    have hsub : line s '' univ ⊆ (univ : Set Plane) ∩ {x : Plane | coord₀ x = s} := by
      rintro _ ⟨t, -, rfl⟩
      exact ⟨mem_univ _, coord₀_line s t⟩
    refine eq_top_mono (measure_mono hsub) ?_
    rw [show (((1 : ℕ) : ℝ)) = (1 : ℝ) by norm_num,
      (isometry_line s).hausdorffMeasure_image (Or.inl zero_le_one), hausdorffMeasure_real]
    simp

end Necessity

end RegularFibreFiniteAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.hausdorffNormalized_ne_top_iff
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_fibre_ne_top
#print axioms RegularFibreFiniteAudit.route_R5
#print axioms RegularFibreFiniteAudit.transfer
#print axioms RegularFibreFiniteAudit.empty_piece
#print axioms RegularFibreFiniteAudit.isometry_line
#print axioms RegularFibreFiniteAudit.coord₀_line
#print axioms RegularFibreFiniteAudit.relative_compactness_necessary
