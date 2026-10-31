module

public import FunctionalInequalities.Analysis.Convex.CompactTilt
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section

noncomputable section
open Set Metric
open scoped RealInnerProductSpace Topology
namespace LetwinCompactTiltAudit
open FunctionalInequalities.Analysis

/-- Real compact quadratic source generates a continuous optimizer with two
computed slope values. Neither the optimizer nor its values are assumptions. -/
theorem actual_real_quadratic_optimizer : ∃ P : ℝ → ℝ, Continuous P ∧ P 0 = 0 ∧ P 4 = 1 := by
  have hs : StrictConvexOn ℝ (univ : Set ℝ) (fun x => x ^ 2) :=
    (by norm_num : Even (2 : ℕ)).strictConvexOn_pow (by norm_num)
  obtain ⟨P, hP, hopt⟩ :=
    exists_continuous_tilt_optimizer (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
      ⟨0, by norm_num⟩ (hs.subset (subset_univ _) (convex_Icc _ _))
      (continuous_pow 2).continuousOn
  have hp0 : ∀ y ∈ Icc (-1 : ℝ) 1, (0 : ℝ) ^ 2 + ⟪(0 : ℝ), y - 0⟫ ≤ y ^ 2 := by
    intro y _hy
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), inner_zero_left, zero_add]
    exact sq_nonneg y
  have hp4 : ∀ y ∈ Icc (-1 : ℝ) 1, (1 : ℝ) ^ 2 + ⟪(4 : ℝ), y - 1⟫ ≤ y ^ 2 := by
    intro y hy
    rw [Real.inner_apply]
    have hy1 : y ≤ 1 := hy.2
    nlinarith [sq_nonneg (y - 1)]
  exact
    ⟨P, hP, ((hopt 0).2.2 0 (by norm_num) hp0).symm, ((hopt 4).2.2 1 (by norm_num) hp4).symm⟩

private lemma fin0_constant_source :
    IsCompact (univ : Set (EuclideanSpace ℝ (Fin 0))) ∧
      StrictConvexOn ℝ univ (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) := by
  have hu : StrictConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin 0))) (fun _ => (7 : ℝ)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy hxy a b _ha _hb _hab
    exact (hxy (Subsingleton.elim x y)).elim
  have hK : IsCompact (univ : Set (EuclideanSpace ℝ (Fin 0))) := by
    have he : (univ : Set (EuclideanSpace ℝ (Fin 0))) = {0} := by
      ext x
      simp only [mem_univ, mem_singleton_iff, true_iff]
      exact Subsingleton.elim x 0
    rw [he]
    exact isCompact_singleton
  exact ⟨hK, hu⟩

/-- True zero-dimensional compact optimization, not an empty carrier or a
mass-zero claim. The source constant is seven and the optimizer is the point. -/
theorem actual_fin0_optimizer :
    ∃ P : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0), Continuous P ∧ ∀ p, P p = 0 := by
  obtain ⟨hK, hu⟩ := fin0_constant_source
  obtain ⟨P, hP, _hopt⟩ :=
    exists_continuous_tilt_optimizer hK ⟨0, mem_univ _⟩ hu continuousOn_const
  exact ⟨P, hP, fun p => Subsingleton.elim (P p) 0⟩

/-- True Fin0 constant source generates its conjugate value minus seven,
actual C1 and zero derivative. No empty carrier or MA mass is claimed. -/
theorem actual_fin0_value :
    ∃ ψ : EuclideanSpace ℝ (Fin 0) → ℝ,
      ContDiff ℝ 1 ψ ∧
        (∀ p, ψ p = -7) ∧ ∀ p, HasFDerivAt ψ (0 : EuclideanSpace ℝ (Fin 0) →L[ℝ] ℝ) p := by
  obtain ⟨hK, hu⟩ := fin0_constant_source
  obtain ⟨P, ψ, L, _hPC, _hopt, _hs, hv, _hc, _hL, hC1, hd⟩ :=
    exists_compact_conjugate hK ⟨0, mem_univ _⟩ hu continuousOn_const
  refine ⟨ψ, hC1, ?_, ?_⟩
  · intro p
    have hp : P p = 0 := Subsingleton.elim _ _
    simpa only [hp, inner_zero_right, zero_sub] using hv p
  · intro p
    have hp : P p = 0 := Subsingleton.elim _ _
    simpa only [hp, map_zero] using hd p

/-- The true Fin0 compact constant source GENERATES optimizer/support data,
then the actual bridge gives image G=G for EVERY set, no mass-zero claim. -/
theorem actual_fin0_preimage (G : Set (EuclideanSpace ℝ (Fin 0))) :
    subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) univ G = G := by
  obtain ⟨hK, hu⟩ := fin0_constant_source
  obtain ⟨P, _hPC, hopt⟩ :=
    exists_continuous_tilt_optimizer hK ⟨0, mem_univ _⟩ hu continuousOn_const
  have hi : G ⊆ interior (univ : Set (EuclideanSpace ℝ (Fin 0))) := by simp
  have he :=
    subgradientImageOn_eq_optimizer_preimage (convexOn_const 7 convex_univ)
      (subset_refl (univ : Set (EuclideanSpace ℝ (Fin 0)))) P hopt hi
  have hPid : P = id := funext fun x => Subsingleton.elim _ _
  simpa only [hPid, preimage_id] using he

/-- True Fin0 constant7/Sup value -7 generates FULL compact sublevels, including
an actually empty level and actually whole point carrier; no mass claim. -/
theorem actual_fin0_tilt_sublevels :
    (∀ R : ℝ, IsCompact {_p : EuclideanSpace ℝ (Fin 0) | (-7 : ℝ) ≤ R}) ∧
      {_p : EuclideanSpace ℝ (Fin 0) | (-7 : ℝ) ≤ -8} = ∅ ∧
        {_p : EuclideanSpace ℝ (Fin 0) | (-7 : ℝ) ≤ -6} = univ := by
  obtain ⟨hK, _hstrict⟩ := fin0_constant_source
  have hs :
    ∀ p : EuclideanSpace ℝ (Fin 0),
      (-7 : ℝ) = sSup ((fun y : EuclideanSpace ℝ (Fin 0) => ⟪p, y⟫ - (7 : ℝ)) '' univ) := by
    intro p
    have hp : p = 0 := Subsingleton.elim _ _
    simp [hp]
  obtain ⟨δ, C, _hδ, _hC, _hl, hcomp⟩ :=
    exists_compact_tilt_sublevels (u := fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ)) (ψ :=
      fun _ => (-7 : ℝ)) hK continuousOn_const continuous_const hs
      (by simp : (0 : EuclideanSpace ℝ (Fin 0)) ∈ interior univ)
  refine ⟨?_, ?_, ?_⟩
  · intro R
    simpa using hcomp R
  · ext p
    norm_num
  · ext p
    norm_num


/-- Genuine Euclidean Fin0 constant-seven data generate an actual contact and
positive section level. The FULL section is the compact point carrier. -/
theorem actual_fin0_contained_section :
    ∃ (ψ : EuclideanSpace ℝ (Fin 0) → ℝ) (R : ℝ),
      (∀ p, ψ p = -7) ∧ (-7 : ℝ) < R ∧ {p | ψ p ≤ R} = univ ∧ IsCompact {p | ψ p ≤ R} := by
  let E := EuclideanSpace ℝ (Fin 0)
  obtain ⟨hK, hstrict⟩ := fin0_constant_source
  obtain ⟨P, ψ, L, hPC, hopt, hs, hv, _hcv, _hLip, hC1, _hd⟩ :=
    exists_compact_conjugate hK ⟨0, mem_univ _⟩ hstrict continuousOn_const
  have hvalue (p : E) : ψ p = -7 := by
    rw [hv p]
    have hp : P p = 0 := Subsingleton.elim _ _
    simp only [hp, inner_zero_right, zero_sub]
  obtain ⟨p₀, R, _hP, _he, hR, hcomp, _hsub⟩ :=
    exists_contained_dual_section isOpen_univ (convexOn_const (7 : ℝ) convex_univ)
      continuousOn_const hK (subset_refl univ) P hPC hopt hC1.continuous hs hv
      (by simp : (0 : E) ∈ interior univ)
  refine ⟨ψ, R, hvalue, hR, ?_, ?_⟩
  · ext p
    simp only [mem_ofPred_eq, mem_univ, iff_true, hvalue p]
    exact hR.le
  · simpa only [inner_zero_right, sub_zero] using hcomp



end LetwinCompactTiltAudit
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_continuous_tilt_optimizer
set_option pp.fullNames true in
#print axioms LetwinCompactTiltAudit.actual_real_quadratic_optimizer
set_option pp.fullNames true in
#print axioms LetwinCompactTiltAudit.actual_fin0_optimizer

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_value_of_optimizer
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_compact_conjugate
set_option pp.fullNames true in
#print axioms LetwinCompactTiltAudit.actual_fin0_value

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.subgradientImageOn_eq_optimizer_preimage
set_option pp.fullNames true in
#print axioms LetwinCompactTiltAudit.actual_fin0_preimage

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_tilt_lower_bound_of_compact_sup
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_compact_tilt_sublevels
set_option pp.fullNames true in
#print axioms LetwinCompactTiltAudit.actual_fin0_tilt_sublevels

set_option pp.fullNames true in
#print axioms LetwinCompactTiltAudit.actual_fin0_contained_section
