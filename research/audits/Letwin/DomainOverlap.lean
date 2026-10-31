module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace
namespace LetwinDomainOverlapAudit
open FunctionalInequalities.Analysis

section RealClient

def Ω₁ : Set ℝ := Set.Ioo (-2 : ℝ) 2

def v₁ (x : ℝ) : ℝ := by
  classical
  exact if x ∈ Ω₁ then |x| else 0

theorem piecewise_abs_overlap_null :
    (volume : Measure ℝ) {p : ℝ | ∃ x ∈ Ω₁, ∃ y ∈ Ω₁,
      x ≠ y ∧
        (∀ z ∈ Ω₁, v₁ x + ⟪p, z - x⟫ ≤ v₁ z) ∧
        (∀ z ∈ Ω₁, v₁ y + ⟪p, z - y⟫ ≤ v₁ z)} = 0 := by
  classical
  have hv₁ : ConvexOn ℝ Ω₁ v₁ := by
    refine ⟨convex_Ioo (-2) 2, ?_⟩
    intro x hx y hy a b ha hb hab
    have hxy : a • x + b • y ∈ Ω₁ :=
      (convex_Ioo (-2 : ℝ) 2) hx hy ha hb hab
    have hxy' : a * x + b * y ∈ Ω₁ := by simpa only [smul_eq_mul] using hxy
    have htri :
        |a * x + b * y| ≤ |a * x| + |b * y| :=
      abs_add_le (a * x) (b * y)
    simpa only [v₁, ite_eq_left hx, ite_eq_left hy, smul_eq_mul, ite_eq_left hxy', abs_mul,
      abs_of_nonneg ha, abs_of_nonneg hb] using htri

  have hvc₁ : ContinuousOn v₁ Ω₁ := by
    apply continuous_abs.continuousOn.congr
    intro x hx
    simp [v₁, hx]

  simpa [Ω₁, v₁] using
    (volume_domain_subgradient_two_points_eq_zero
      (E := ℝ) (v := v₁) (Ω := Ω₁)
      isOpen_Ioo hv₁ hvc₁)

end RealClient

section ZeroDimensionalClient

abbrev E₀ := EuclideanSpace ℝ (Fin 0)

def Ω₀ : Set E₀ := Set.univ

def v₀ : E₀ → ℝ := fun _ => 0

theorem zero_dimensional_overlap_null :
    (volume : Measure E₀) {p : E₀ | ∃ x ∈ Ω₀, ∃ y ∈ Ω₀,
      x ≠ y ∧
        (∀ z ∈ Ω₀, v₀ x + ⟪p, z - x⟫ ≤ v₀ z) ∧
        (∀ z ∈ Ω₀, v₀ y + ⟪p, z - y⟫ ≤ v₀ z)} = 0 := by
  have hv₀ : ConvexOn ℝ Ω₀ v₀ := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b _ha _hb _hab
    simp [v₀]

  have hvc₀ : ContinuousOn v₀ Ω₀ := by
    change ContinuousOn (fun _ : E₀ => (0 : ℝ)) Set.univ
    exact continuousOn_const

  simpa [Ω₀, v₀] using
    (volume_domain_subgradient_two_points_eq_zero
      (E := E₀) (v := v₀) (Ω := Ω₀)
      isOpen_univ hv₀ hvc₀)

end ZeroDimensionalClient

end LetwinDomainOverlapAudit

#print axioms FunctionalInequalities.Analysis.volume_domain_subgradient_two_points_eq_zero
#print axioms FunctionalInequalities.Analysis.volume_inter_subgradientImageOn_eq_zero_of_disjoint
#print axioms LetwinDomainOverlapAudit.piecewise_abs_overlap_null
#print axioms LetwinDomainOverlapAudit.zero_dimensional_overlap_null
