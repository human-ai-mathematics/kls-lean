module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section

noncomputable section
open Set Filter Topology Metric Classical
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Analysis
namespace LetwinDomainContactAudit
section QuadraticClient

/-- The reference quadratic used by the concrete Euclidean client. -/
def quadraticClient (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ)
    0 0 (-1 / 2 : ℝ)

/-- The reference agrees with a quadratic only on a neighborhood of the working domain. -/
def referenceClient (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x =>
    if x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 then
      quadraticClient n x
    else 0

theorem quadratic_contact_client (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (w : EuclideanSpace ℝ (Fin n) → ℝ),
        ContinuousOn w
          (closure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) →
        DifferentiableOn ℝ w
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) →
        (∀ y ∈ closure (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1),
          |w y - referenceClient n y| ≤ ε) →
        ∀ z ∈ Metric.closedBall
            (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ),
          ∃ x ∈ Metric.ball
              (0 : EuclideanSpace ℝ (Fin n)) 1,
            gradient w x = gradient (referenceClient n) z ∧
              ∀ y ∈ closure
                  (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1),
                w x +
                    ⟪gradient (referenceClient n) z, y - x⟫ ≤
                  w y := by
  let E := EuclideanSpace ℝ (Fin n)
  let Ω : Set E := Metric.ball 0 1
  let K : Set E := Metric.closedBall 0 (1 / 2 : ℝ)

  have hΩo : IsOpen Ω :=
    isOpen_ball

  have hΩc : Convex ℝ Ω :=
    convex_ball 0 1

  have hΩb : Bornology.IsBounded Ω :=
    Metric.isBounded_ball

  have hK : IsCompact K :=
    isCompact_closedBall _ _

  have hKΩ : K ⊆ Ω := by
    intro x hx
    have hxnorm : ‖x‖ ≤ (1 / 2 : ℝ) := by
      simpa [K, mem_closedBall, dist_zero_right] using hx
    have hxnorm' : ‖x‖ < (1 : ℝ) := by
      linarith
    simpa [Ω, mem_ball, dist_zero_right] using hxnorm'

  have hclsub :
      closure Ω ⊆ Metric.ball (0 : E) 2 := by
    have hclsub1 :
        closure Ω ⊆ Metric.closedBall (0 : E) 1 :=
      closure_minimal ball_subset_closedBall isClosed_closedBall
    intro x hx
    have hx1 := hclsub1 hx
    have hxnorm : ‖x‖ ≤ (1 : ℝ) := by
      simpa [K, mem_closedBall, dist_zero_right] using hx1
    have hxnorm' : ‖x‖ < (2 : ℝ) := by
      linarith
    simpa [Ω, mem_ball, dist_zero_right] using hxnorm'

  have hqC1 :
      ContDiff ℝ 2 (quadraticClient n) := by
    simpa [quadraticClient] using
      (contDiff_quadraticAt
        (A := (1 : Matrix (Fin n) (Fin n) ℝ))
        (x₀ := (0 : E)) (b := (0 : E)) (c := (-1 / 2 : ℝ)))

  have hI :
      (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := by
    simpa using
      (Matrix.PosDef.one :
        (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)

  have hqstrict :
      StrictConvexOn ℝ Set.univ (quadraticClient n) := by
    simpa [quadraticClient] using
      (strictConvexOn_quadraticAt
        (A := (1 : Matrix (Fin n) (Fin n) ℝ))
        hI (x₀ := (0 : E)) (b := (0 : E))
        (c := (-1 / 2 : ℝ)))

  have hqconv :
      ConvexOn ℝ Set.univ (quadraticClient n) :=
    hqstrict.convexOn

  have hΩcl : Convex ℝ (closure Ω) :=
    hΩc.closure

  have hvq :
      Set.EqOn (referenceClient n) (quadraticClient n) (closure Ω) := by
    intro x hx
    simp [referenceClient, hclsub hx]

  have hvcont :
      ContinuousOn (referenceClient n) (closure Ω) := by
    exact
      hqC1.continuous.continuousOn.congr
        (fun x hx => hvq hx)

  have hvC1 :
      ContDiffOn ℝ 1 (referenceClient n) Ω := by
    exact
      (hqC1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffOn.congr
        (fun x hx => hvq (subset_closure hx))

  have hvconv :
      ConvexOn ℝ (closure Ω) (referenceClient n) := by
    refine ⟨hΩcl, ?_⟩
    intro x hx y hy a b ha hb hab
    have hq :=
      hqconv.2 (mem_univ x) (mem_univ y) ha hb hab
    have hxy :
        a • x + b • y ∈ closure Ω :=
      hΩcl hx hy ha hb hab
    rw [hvq hx, hvq hy, hvq hxy]
    exact hq

  have hvstrict :
      StrictConvexOn ℝ Ω (referenceClient n) := by
    refine ⟨hΩc, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hq :=
      hqstrict.2 (mem_univ x) (mem_univ y)
        (fun h => hxy h) ha hb hab
    have hxy' :
        a • x + b • y ∈ Ω :=
      hΩc hx hy ha.le hb.le hab
    rw [
      hvq (subset_closure hx),
      hvq (subset_closure hy),
      hvq (subset_closure hxy')
    ]
    exact hq

  have hmain :=
    exists_contact_of_uniform_close_on_open
      (v := referenceClient n)
      (Ω := Ω) (K := K)
      hΩo hΩb hvconv hvstrict hvcont hvC1 hK hKΩ

  simpa [E, Ω, K] using hmain

end QuadraticClient


/-- The retained global interface really applies on a disconnected, nonconvex
working domain; its tolerance still precedes the unknown perturbation. -/
theorem disconnected_global_contact :
    let Ω : Set ℝ := Ioo (-3) (-1) ∪ Ioo 1 3
    let K : Set ℝ := {-2, 2}
    ¬Convex ℝ Ω ∧
      ∃ ε : ℝ,
        0 < ε ∧
          ∀ w : ℝ → ℝ,
            ContDiff ℝ 1 w →
              (∀ y ∈ closure Ω, |w y - y ^ 2| ≤ ε) →
                ∀ z ∈ K,
                  ∃ x ∈ Ω,
                    gradient w x = gradient (fun t : ℝ => t ^ 2) z ∧
                      ∀ y ∈ closure Ω, w x + ⟪gradient (fun t : ℝ => t ^ 2) z, y - x⟫ ≤ w y := by
  let Ω : Set ℝ := Ioo (-3) (-1) ∪ Ioo 1 3
  let K : Set ℝ := {-2, 2}
  have hΩo : IsOpen Ω := isOpen_Ioo.union isOpen_Ioo
  have hΩb : Bornology.IsBounded Ω :=
    (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3)).isBounded.subset
      (by
        intro x hx
        rcases hx with hx | hx
        · exact ⟨hx.1.le, by linarith [hx.2]⟩
        · exact ⟨by linarith [hx.1], hx.2.le⟩)
  have hK : IsCompact K := ((Set.finite_singleton (2 : ℝ)).insert (-2)).isCompact
  have hKO : K ⊆ Ω := by
    intro x hx
    simp only [K, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> norm_num [Ω]
  constructor
  · intro hc
    have h :=
      hc (show (-2 : ℝ) ∈ Ω by norm_num [Ω]) (show (2 : ℝ) ∈ Ω by norm_num [Ω])
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    norm_num [Ω] at h
  · exact
      exists_contact_of_uniform_close
        ((show Even (2 : ℕ) by decide).strictConvexOn_pow (by decide)) (by fun_prop) hΩo hΩb hK
        hKO

end LetwinDomainContactAudit
set_option pp.fullNames true
#print axioms FunctionalInequalities.Analysis.gradient_tangent_gap_pos_of_strictConvexOn
#print axioms FunctionalInequalities.Analysis.gradient_tangent_gap_pos
#print axioms FunctionalInequalities.Analysis.exists_contact_of_uniform_close_on_open
#print axioms FunctionalInequalities.Analysis.exists_contact_of_uniform_close
set_option pp.fullNames true
#print axioms LetwinDomainContactAudit.quadratic_contact_client

#print axioms LetwinDomainContactAudit.disconnected_global_contact
#check LetwinDomainContactAudit.quadratic_contact_client 0
