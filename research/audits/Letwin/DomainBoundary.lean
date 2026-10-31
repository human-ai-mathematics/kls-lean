module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison

@[expose] public section

noncomputable section

namespace LetwinDomainBoundaryAudit

open FunctionalInequalities.Analysis
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

private lemma real_unit_dirichlet_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y ^ 2 - 1) / 2) x x := by
  convert ((hasDerivAt_pow 2 x).sub_const 1).div_const 2 using 1
  ring

/-- Actual real unit quadratic Dirichlet client.

Closure convexity, closure continuity, zero frontier values, and unit
DOMAIN-MA are constructed here. The final lower modulus is obtained from the
generic common modulus, not from a separate polynomial boundary estimate. -/
theorem real_unit_quadratic_dirichlet_client :
    ConvexOn ℝ (closure (Ioo (-1 : ℝ) 1)) (fun y : ℝ => (y ^ 2 - 1) / 2) ∧
      ContinuousOn (fun y : ℝ => (y ^ 2 - 1) / 2) (closure (Ioo (-1 : ℝ) 1)) ∧
        (∀ x ∈ frontier (Ioo (-1 : ℝ) 1), (x ^ 2 - 1) / 2 = 0) ∧
          (∀ H : Set ℝ,
              IsOpen H →
                H ⊆ Ioo (-1 : ℝ) 1 →
                  (volume : Measure ℝ)
                      (subgradientImageOn (fun y : ℝ => (y ^ 2 - 1) / 2) (Ioo (-1 : ℝ) 1) H) =
                    ENNReal.ofReal 1 * (volume : Measure ℝ) H) ∧
            (∀ ε : ℝ,
              0 < ε →
                ∃ ρ : ℝ,
                  0 < ρ ∧
                    ∀ x ∈ Ioo (-1 : ℝ) 1,
                      infDist x (frontier (Ioo (-1 : ℝ) 1)) < ρ → -ε ≤ (x ^ 2 - 1) / 2) := by
  let Ω : Set ℝ := Ioo (-1 : ℝ) 1
  let q : ℝ → ℝ := fun y => (y ^ 2 - 1) / 2
  have hΩ : IsOpen Ω := isOpen_Ioo
  have hΩconv : Convex ℝ Ω := convex_Ioo (-1 : ℝ) 1
  have hb : Bornology.IsBounded Ω :=
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).isBounded.subset Ioo_subset_Icc_self
  have hconv : ConvexOn ℝ (closure Ω) q := by
    refine ⟨hΩconv.closure, ?_⟩
    intro x _hx y _hy a b ha hb' hab
    change ((a * x + b * y) ^ 2 - 1) / 2 ≤ a * ((x ^ 2 - 1) / 2) + b * ((y ^ 2 - 1) / 2)
    have hid :
      a * ((x ^ 2 - 1) / 2) + b * ((y ^ 2 - 1) / 2) - ((a * x + b * y) ^ 2 - 1) / 2 =
        a * b * (x - y) ^ 2 / 2 := by
      have hbval : b = 1 - a := by linarith
      rw [hbval]
      ring
    have hnonneg : 0 ≤ a * b * (x - y) ^ 2 / 2 := by positivity
    linarith
  have hcontinuous : Continuous q := by
    dsimp [q]
    fun_prop
  have hcont : ContinuousOn q (closure Ω) := hcontinuous.continuousOn
  have hclosure : closure Ω ⊆ Icc (-1 : ℝ) 1 := by
    exact closure_minimal Ioo_subset_Icc_self isClosed_Icc
  have hfrontier : ∀ x ∈ frontier Ω, q x = 0 := by
    intro x hx
    have hxcl : x ∈ Icc (-1 : ℝ) 1 := hclosure (frontier_subset_closure hx)
    have hxnot : x ∉ Ω := by
      have hx' := hx
      rw [hΩ.frontier_eq] at hx'
      exact hx'.2
    by_cases hleft : x = -1
    · norm_num [q, hleft]
    · have hxl : (-1 : ℝ) < x := lt_of_le_of_ne hxcl.1 (Ne.symm hleft)
      have hright : x = 1 := by
        by_contra hright
        exact hxnot ⟨hxl, lt_of_le_of_ne hxcl.2 hright⟩
      norm_num [q, hright]
  have hderiv (x : ℝ) : HasDerivAt q x x := by
    simpa only [q] using real_unit_dirichlet_hasDerivAt x
  have hgradient (x : ℝ) : gradient q x = x := by
    rw [gradient_eq_deriv']
    exact
      (hderiv x).deriv
        -- This is a direct polynomial proof of the actual global tangent
          -- inequality for this concrete q. It is not an extension assumption
          -- on any unknown generic source.

  have htangent (x y : ℝ) : q x + ⟪x, y - x⟫ ≤ q y := by
    change (x ^ 2 - 1) / 2 + (y - x) * x ≤ (y ^ 2 - 1) / 2
    nlinarith [sq_nonneg (y - x)]
  have himage : ∀ H : Set ℝ, H ⊆ Ω → subgradientImageOn q Ω H = H := by
    intro H hH
    ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      have heq : p = gradient q x :=
        subgradientOn_eq_gradient hΩ (hH hx) (hderiv x).differentiableAt hp
      rw [hgradient x] at heq
      exact heq.symm ▸ hx
    · intro hp
      refine ⟨p, hp, ?_⟩
      intro y _hy
      exact htangent p y
  have hMA :
    ∀ H : Set ℝ,
      IsOpen H →
        H ⊆ Ω →
          (volume : Measure ℝ) (subgradientImageOn q Ω H) =
            ENNReal.ofReal 1 * (volume : Measure ℝ) H := by
    intro H _hH hHΩ
    rw [himage H hHΩ]
    simp
  have hfr : ∀ x ∈ frontier Ω, 0 ≤ q x := by
    intro x hx
    rw [hfrontier x hx]
  have hMAupper :
    ∀ H : Set ℝ,
      IsOpen H →
        H ⊆ Ω →
          (volume : Measure ℝ) (subgradientImageOn q Ω H) ≤
            ENNReal.ofReal 1 * (volume : Measure ℝ) H := by
    intro H hH hHΩ
    exact le_of_eq (hMA H hH hHΩ)
  have hmodulus :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Ω, infDist x (frontier Ω) < ρ → -ε ≤ q x := by
    intro ε hε
    obtain ⟨ρ, hρ, hcommon⟩ :=
      exists_common_lower_boundary_modulus_domain (E := ℝ) (Ω := Ω) hΩ hΩconv hb (Λ := 1)
        (by norm_num) (ε := ε) hε
    refine ⟨ρ, hρ, ?_⟩
    exact hcommon q hconv hcont hfr hMAupper
  change
    ConvexOn ℝ (closure Ω) q ∧
      ContinuousOn q (closure Ω) ∧
        (∀ x ∈ frontier Ω, q x = 0) ∧
          (∀ H : Set ℝ,
              IsOpen H →
                H ⊆ Ω →
                  (volume : Measure ℝ) (subgradientImageOn q Ω H) =
                    ENNReal.ofReal 1 * (volume : Measure ℝ) H) ∧
            (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Ω, infDist x (frontier Ω) < ρ → -ε ≤ q x)
  exact ⟨hconv, hcont, hfrontier, hMA, hmodulus⟩

/-- The same concrete solution has a true common absolute boundary modulus.
Its nonpositivity is produced by actual positive MA comparison, not supplied. -/
theorem real_unit_quadratic_absolute_boundary_client :
    ∀ ε : ℝ,
      0 < ε →
        ∃ ρ : ℝ,
          0 < ρ ∧
            ∀ x ∈ Ioo (-1 : ℝ) 1,
              infDist x (frontier (Ioo (-1 : ℝ) 1)) < ρ → |(x ^ 2 - 1) / 2| ≤ ε := by
  obtain ⟨hconv, hcont, hfr, hMA, _⟩ := real_unit_quadratic_dirichlet_client
  intro ε hε
  obtain ⟨ρ, hρ, hcommon⟩ :=
    exists_common_boundary_modulus_domain (F := ℝ) (Ω := Ioo (-1 : ℝ) 1) isOpen_Ioo
      (convex_Ioo _ _)
      ((isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).isBounded.subset Ioo_subset_Icc_self) (a :=
      1) (Λ := 1) (by norm_num) (by norm_num) hε
  refine ⟨ρ, hρ, ?_⟩
  exact
    hcommon _ hconv hcont hfr (fun H hH hHO => (hMA H hH hHO).ge)
      (fun H hH hHO => (hMA H hH hHO).le)

/-- Pure constant support is valid in dimension zero, independently of the
Nontrivial assumption used for Haar-null constant images. -/
theorem actual_zero_dimensional_constant_support :
    subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (7 : ℝ))
      Set.univ Set.univ ⊆ {0} :=
  subgradientImageOn_const_subset_singleton 7 isOpen_univ (Subset.rfl)

end LetwinDomainBoundaryAudit

set_option pp.fullNames true in
#print axioms
  FunctionalInequalities.Analysis.exists_pos_boundary_power_bound_domain

set_option pp.fullNames true in
#print axioms
  FunctionalInequalities.Analysis.exists_common_lower_boundary_modulus_domain

set_option pp.fullNames true in
#print axioms
  LetwinDomainBoundaryAudit.real_unit_quadratic_dirichlet_client
set_option pp.fullNames true in
#print axioms LetwinDomainBoundaryAudit.real_unit_quadratic_absolute_boundary_client
set_option pp.fullNames true in
#print axioms LetwinDomainBoundaryAudit.actual_zero_dimensional_constant_support
