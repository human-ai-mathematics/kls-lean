module

public import FunctionalInequalities.Analysis.Convex.Dirichlet.Compactness

@[expose] public section

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace Topology
namespace LetwinDomainEquicontinuityAudit
open FunctionalInequalities.Analysis

/-- Concrete one-dimensional client for
`q(x) = (x^2 - 1) / 2` on `(-1,1)`.  Its convexity, continuity, zero
frontier values, and exact unit domain-relative Alexandrov measure identity
are all constructed in this theorem. -/
theorem real_unit_quadratic_dirichlet_equicontinuity_client :
    EquicontinuousOn (fun _ : Unit => fun x : ℝ => (x ^ 2 - 1) / 2)
      (closure (Ioo (-1 : ℝ) 1)) := by
  let Ω : Set ℝ := Ioo (-1 : ℝ) 1
  let q : ℝ → ℝ := fun x => (x ^ 2 - 1) / 2
  have hΩ : IsOpen Ω := by simpa [Ω] using (isOpen_Ioo : IsOpen (Ioo (-1 : ℝ) 1))
  have hΩconv : Convex ℝ Ω := by simpa [Ω] using (convex_Ioo (-1 : ℝ) 1)
  have hb : Bornology.IsBounded Ω :=
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).isBounded.subset Ioo_subset_Icc_self
  have hconv : ConvexOn ℝ (closure Ω) q := by
    refine ⟨hΩconv.closure, ?_⟩
    intro x _hx y _hy c d hc hd hcd
    change ((c * x + d * y) ^ 2 - 1) / 2 ≤ c * ((x ^ 2 - 1) / 2) + d * ((y ^ 2 - 1) / 2)
    have hd' : d = 1 - c := by linarith
    have hid :
      c * ((x ^ 2 - 1) / 2) + d * ((y ^ 2 - 1) / 2) - ((c * x + d * y) ^ 2 - 1) / 2 =
        c * d * (x - y) ^ 2 / 2 := by
      rw [hd']
      ring
    have hnonneg : 0 ≤ c * d * (x - y) ^ 2 / 2 := by positivity
    linarith
  have hcont : ContinuousOn q (closure Ω) := by
    have hqcont : Continuous q := by
      dsimp [q]
      fun_prop
    exact hqcont.continuousOn
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
    convert ((hasDerivAt_pow 2 x).sub_const 1).div_const 2 using 1
    ring
  have hgradient (x : ℝ) : gradient q x = x := by
    rw [gradient_eq_deriv']
    exact (hderiv x).deriv
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
    intro H hH hHΩ
    rw [himage H hHΩ]
    simp
  have hMAl :
    ∀ H : Set ℝ,
      IsOpen H →
        H ⊆ Ω → ENNReal.ofReal 1 * (volume : Measure ℝ) H ≤ volume (subgradientImageOn q Ω H) := by
    intro H hH hHΩ
    exact (hMA H hH hHΩ).ge
  have hMAu :
    ∀ H : Set ℝ,
      IsOpen H →
        H ⊆ Ω → volume (subgradientImageOn q Ω H) ≤ ENNReal.ofReal 1 * (volume : Measure ℝ) H := by
    intro H hH hHΩ
    exact (hMA H hH hHΩ).le
  have hfr : ∀ x ∈ frontier Ω, q x = 0 := hfrontier
  have hresult :=
    equicontinuousOn_of_domain_alexandrov_bounds (E := ℝ) (ι := Unit) (Ω := Ω) hΩ hΩconv hb
      (a := 1) (Λ := 1) (by norm_num) (by norm_num) (fun _ : Unit => q)
      (by
        intro _
        exact hconv)
      (by
        intro _
        exact hcont)
      (by
        intro _ x hx
        exact hfr x hx)
      (by
        intro _ H hH hHΩ
        exact hMAl H hH hHΩ)
      (by
        intro _ H hH hHΩ
        exact hMAu H hH hHΩ)
  simpa [Ω, q] using hresult

/-- The shared geometry needs no inner-product, finite-dimensional, open-domain
or measurable-space structure. -/
theorem normed_geometry_client
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F]
    {Ω : Set F} (hb : Bornology.IsBounded Ω) {x : F} (hx : x ∈ Ω) :
    infDist x (frontier Ω) ≤ diam Ω :=
  infDist_frontier_le_diam_of_mem hb hx

/-- An empty index class does not require a nonempty solution family. -/
theorem empty_index_client :
    EquicontinuousOn (fun i : Empty => Empty.elim i : Empty → ℝ → ℝ)
      (closure (Ioo (-1 : ℝ) 1)) := by
  apply equicontinuousOn_of_domain_alexandrov_bounds
    (hΩ := isOpen_Ioo) (hΩconv := convex_Ioo _ _)
    (hb := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).isBounded.subset Ioo_subset_Icc_self)
    (a := 1) (Λ := 0) (by norm_num) (by norm_num)
  all_goals intro i; exact Empty.elim i

end LetwinDomainEquicontinuityAudit

set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.equicontinuousOn_of_domain_alexandrov_bounds
set_option pp.fullNames true in
#print axioms LetwinDomainEquicontinuityAudit.real_unit_quadratic_dirichlet_equicontinuity_client

set_option pp.fullNames true in
#print axioms LetwinDomainEquicontinuityAudit.normed_geometry_client
set_option pp.fullNames true in
#print axioms LetwinDomainEquicontinuityAudit.empty_index_client
