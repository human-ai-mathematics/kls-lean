import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
import Mathlib.Analysis.Calculus.Deriv.Abs

noncomputable section
namespace LetwinDomainMaximumAudit
open FunctionalInequalities.Analysis
section AlexandrovQuadraticDomainClient

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal

/-- A concrete real quadratic client on the Euclidean unit ball. -/
theorem quadratic_unitBall_domain_client {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧
      ENNReal.ofReal
          (c * (-(quadraticAt
              (1 : Matrix (Fin n) (Fin n) ℝ)
              0 0 (-1 / 2) (0 : EuclideanSpace ℝ (Fin n)))) ^ n) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (subgradientImageOn
              (quadraticAt
                (1 : Matrix (Fin n) (Fin n) ℝ)
                0 0 (-1 / 2))
              (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
              (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
          ENNReal.ofReal
            (diam (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ^ (n - 1) *
              infDist (0 : EuclideanSpace ℝ (Fin n))
                (frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let Ω : Set E := ball (0 : E) 1
  let u : E → ℝ :=
    quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
  have hA : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef :=
    Matrix.PosSemidef.one
  have hconvU : ConvexOn ℝ univ u := by
    dsimp [u]
    exact convexOn_quadraticAt hA 0 0 (-1 / 2)
  have hucont : Continuous u :=
    continuousOn_univ.mp (hconvU.continuousOn isOpen_univ)
  have hconv : ConvexOn ℝ (closure Ω) u :=
    hconvU.subset (subset_univ _) (convex_ball (0 : E) 1).closure
  have huc : ContinuousOn u (closure Ω) :=
    hucont.continuousOn
  have hΩ : IsOpen Ω := by
    dsimp [Ω]
    exact isOpen_ball
  have hΩconv : Convex ℝ Ω := by
    dsimp [Ω]
    exact convex_ball _ _
  have hb : Bornology.IsBounded Ω := by
    dsimp [Ω]
    exact Metric.isBounded_ball
  have hx₀ : (0 : E) ∈ Ω := by
    dsimp [Ω]
    exact mem_ball_self zero_lt_one
  have hformula (x : E) :
      u x = (1 / 2 : ℝ) * (‖x‖ ^ 2 - 1) := by
    dsimp [u, quadraticAt]
    rw [show Matrix.toEuclideanLin
        (1 : Matrix (Fin n) (Fin n) ℝ) = LinearMap.id by
          exact Matrix.toLpLin_one 2]
    simp only [sub_zero, inner_zero_left, LinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    ring
  have hneg : u 0 < 0 := by
    rw [hformula]
    norm_num
  have hfr : ∀ x ∈ frontier Ω, 0 ≤ u x := by
    intro x hx
    have hx' : x ∈ closure Ω ∧ x ∉ Ω := by
      rw [hΩ.frontier_eq] at hx
      exact hx
    have hcl :
        closure Ω ⊆ closedBall (0 : E) 1 := by
      apply closure_minimal
      · exact ball_subset_closedBall
      · exact isClosed_closedBall
    have hle : ‖x‖ ≤ 1 := by
      have hxball := hcl hx'.1
      simpa [Ω, Metric.mem_closedBall, dist_zero_right] using hxball
    have hge : 1 ≤ ‖x‖ := by
      apply le_of_not_gt
      intro hlt
      apply hx'.2
      simpa [Ω, Metric.mem_ball, dist_zero_right] using hlt
    rw [hformula]
    nlinarith [norm_nonneg x]
  obtain ⟨c, hc, hmain⟩ :=
    exists_pos_alexandrov_maximum_principle_domain
      (E := E)
  refine ⟨c, hc, ?_⟩
  simpa [u, Ω, E] using
    hmain u Ω hconv huc hΩ hΩconv hb hfr 0 hx₀ hneg

end AlexandrovQuadraticDomainClient

open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

/-- A genuine nondifferentiable convex source for the retained GLOBAL maximum. -/
theorem abs_shift_not_differentiable :
    ¬ DifferentiableAt ℝ (fun x : ℝ => |x|-1) 0 := by
  intro h
  have hd := h.add_const 1
  have heq : (fun x : ℝ => (|x|-1)+1) = fun x => |x| := by funext x; ring
  rw [heq] at hd
  exact not_differentiableAt_abs_zero hd

theorem actual_nondifferentiable_global_maximum :
    ∃ c : ℝ,0<c ∧ ENNReal.ofReal c ≤
      (volume : Measure ℝ) (subgradientImage (fun x => |x|-1) (Ioo (-1) 1)) *
        ENNReal.ofReal (infDist (0 : ℝ) (frontier (Ioo (-1) 1))) := by
  have hconv : ConvexOn ℝ univ (fun x : ℝ => |x|-1) := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have h := abs_add_le (a*x) (b*y)
    rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb] at h
    change |a*x+b*y|-1≤a*(|x|-1)+b*(|y|-1)
    nlinarith
  have hfr : ∀ x∈frontier (Ioo (-1 : ℝ) 1),0≤|x|-1 := by
    intro x hx
    rw [frontier_Ioo (by norm_num : (-1 : ℝ)<1)] at hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl|rfl <;> norm_num
  obtain ⟨c,hc,hm⟩ := exists_pos_alexandrov_maximum_principle (E := ℝ)
  refine ⟨c,hc,?_⟩
  simpa using hm (fun x => |x|-1) hconv (Ioo (-1) 1) isOpen_Ioo (convex_Ioo (-1) 1)
    (isBounded_Ioo (-1) 1) hfr 0 (by norm_num) (by norm_num)

/-- The old sliding theorem really retains a nonconvex working domain. -/
theorem actual_nonconvex_sliding :
    let Ω : Set ℝ := Ioo (-1) 1 ∪ Ioo 2 3
    ¬ Convex ℝ Ω ∧ (0 : ℝ) ∈ subgradientImage (fun x => x^2-1) Ω := by
  let Ω : Set ℝ := Ioo (-1) 1 ∪ Ioo 2 3
  have hΩ : IsOpen Ω := isOpen_Ioo.union isOpen_Ioo
  have hb : Bornology.IsBounded Ω :=
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 3)).isBounded.subset (by
      intro x hx
      rcases hx with hx|hx
      · exact ⟨hx.1.le,by linarith [hx.2]⟩
      · exact ⟨by linarith [hx.1],hx.2.le⟩)
  have hconv : ConvexOn ℝ univ (fun x : ℝ => x^2-1) := by
    have hq : ConvexOn ℝ univ (fun x : ℝ => x^2) :=
      ((show Even (2 : ℕ) by decide).strictConvexOn_pow (by decide)).convexOn
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    have h := hq.2 hx hy ha hb hab
    simp only [smul_eq_mul] at h ⊢
    nlinarith
  have hfr : ∀ x∈frontier Ω,0≤x^2-1 := by
    intro x hx
    have hh := frontier_union_subset (s := Ioo (-1 : ℝ) 1) (t := Ioo 2 3) hx
    have hh' : x∈frontier (Ioo (-1 : ℝ) 1) ∨ x∈frontier (Ioo (2 : ℝ) 3) := by
      rcases hh with hh|hh
      · exact Or.inl hh.1
      · exact Or.inr hh.2
    rw [frontier_Ioo (by norm_num : (-1 : ℝ)<1),frontier_Ioo (by norm_num : (2 : ℝ)<3)] at hh'
    simp only [mem_insert_iff,mem_singleton_iff] at hh'
    rcases hh' with (rfl|rfl)|(rfl|rfl) <;> norm_num
  constructor
  · intro hc
    have hm := hc (show (0 : ℝ)∈Ω by norm_num [Ω])
      (show (5/2 : ℝ)∈Ω by norm_num [Ω])
      (show (0 : ℝ)≤1/2 by norm_num) (show (0 : ℝ)≤1/2 by norm_num) (by norm_num)
    norm_num [Ω] at hm
  · exact mem_subgradientImage_of_affine_le_of_nonneg_frontier hconv hΩ hb hfr
      (show (0 : ℝ)∈Ω by norm_num [Ω]) (by norm_num) (by intro x hx; simp)

/-- Pure support globalization includes the zero-dimensional carrier. -/
theorem actual_zero_dimensional_support :
    ∀ y : EuclideanSpace ℝ (Fin 0),(0 : ℝ)+⟪(0 : EuclideanSpace ℝ (Fin 0)),y-0⟫≤0 := by
  exact fun y => subgradient_le_on_of_isOpen (convexOn_const (0 : ℝ) convex_univ)
    isOpen_univ (Subset.refl _) (mem_univ (0 : EuclideanSpace ℝ (Fin 0)))
    (by intro z hz; simp) y (mem_univ y)

end LetwinDomainMaximumAudit

set_option pp.fullNames true in
#print axioms LetwinDomainMaximumAudit.quadratic_unitBall_domain_client
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_pos_alexandrov_maximum_principle_domain
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.subgradient_le_on_of_isOpen

set_option pp.fullNames true in
#print axioms LetwinDomainMaximumAudit.abs_shift_not_differentiable
set_option pp.fullNames true in
#print axioms LetwinDomainMaximumAudit.actual_nondifferentiable_global_maximum
set_option pp.fullNames true in
#print axioms LetwinDomainMaximumAudit.actual_nonconvex_sliding
set_option pp.fullNames true in
#print axioms LetwinDomainMaximumAudit.actual_zero_dimensional_support
