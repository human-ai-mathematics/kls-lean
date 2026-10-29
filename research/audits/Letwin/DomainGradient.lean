import FunctionalInequalities.Analysis.Convex.Quadratic
import FunctionalInequalities.Analysis.Convex.Viscosity.Equation

noncomputable section
open Set Metric Filter Topology MeasureTheory Classical
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Analysis

namespace LetwinDomainGradientAudit

open FunctionalInequalities.Analysis

def clientQ (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  quadraticAt
    (1 : Matrix (Fin n) (Fin n) ℝ)
    (0 : EuclideanSpace ℝ (Fin n))
    (0 : EuclideanSpace ℝ (Fin n))
    0

def clientOmega (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.ball 0 2

def clientWorkingOmega (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.ball 0 1

def clientVData (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x =>
    if x ∈ clientOmega n then clientQ n x else 0

private theorem clientVData_eq_q
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ clientWorkingOmega n) :
    clientVData n x = clientQ n x := by
  have hx2 : x ∈ clientOmega n := by
    change dist x 0 < 2
    have hx1 : dist x 0 < 1 := hx
    linarith
  simp [clientVData, hx2]

private theorem clientQ_gradient
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (clientQ n) x = x := by
  simpa [clientQ] using
    gradient_quadraticAt (n := n) Matrix.isHermitian_one 0 0 0 x

private theorem clientQ_convex (n : ℕ) :
    ConvexOn ℝ Set.univ (clientQ n) :=
  convexOn_quadraticAt Matrix.PosDef.one.posSemidef _ _ _

private theorem clientQ_support
    {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)} :
    clientQ n x + ⟪gradient (clientQ n) x, y - x⟫ ≤ clientQ n y := by
  have h :=
    gradient_le_increment
      (clientQ_convex n) x (y - x)
      ((contDiff_quadraticAt
        (1 : Matrix (Fin n) (Fin n) ℝ)
        (0 : EuclideanSpace ℝ (Fin n))
        (0 : EuclideanSpace ℝ (Fin n))
        0).differentiable (by norm_num) x)
  rw [add_sub_cancel] at h
  linarith

private theorem client_subgradientImage_eq
    {n : ℕ} {G : Set (EuclideanSpace ℝ (Fin n))}
    : subgradientImage (clientQ n) G = G := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨x, hx, hpx⟩
    have hpg :
        p = gradient (clientQ n) x :=
      subgradient_eq_gradient
        ((contDiff_quadraticAt
          (1 : Matrix (Fin n) (Fin n) ℝ)
          (0 : EuclideanSpace ℝ (Fin n))
          (0 : EuclideanSpace ℝ (Fin n))
          0).differentiable (by norm_num) x)
        hpx
    rw [clientQ_gradient n x] at hpg
    exact hpg.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y
    simpa [clientQ_gradient n p] using
      (clientQ_support (n := n) (x := p) (y := y))

private theorem client_domain_support_image_eq
    {n : ℕ} {G : Set (EuclideanSpace ℝ (Fin n))}
    (hG : G ⊆ clientWorkingOmega n) :
    subgradientImage (clientQ n) G =
      {p |
        ∃ x ∈ G, ∀ y ∈ clientWorkingOmega n,
          clientVData n x + ⟪p, y - x⟫ ≤ clientVData n y} := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨x, hx, hpx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    rw [clientVData_eq_q (hG hx), clientVData_eq_q hy]
    exact hpx y
  · intro hp
    rcases hp with ⟨x, hx, hpx⟩
    have hpxq :
        ∀ y ∈ clientWorkingOmega n,
          clientQ n x + ⟪p, y - x⟫ ≤ clientQ n y := by
      intro y hy
      rw [← clientVData_eq_q (hG hx), ← clientVData_eq_q hy]
      exact hpx y hy
    have hpg :
        p = gradient (clientQ n) x :=
      subgradientOn_eq_gradient
        isOpen_ball
        (hG hx)
        ((contDiff_quadraticAt
          (1 : Matrix (Fin n) (Fin n) ℝ)
          (0 : EuclideanSpace ℝ (Fin n))
          (0 : EuclideanSpace ℝ (Fin n))
          0).differentiable (by norm_num) x)
        hpxq
    refine ⟨x, hx, ?_⟩
    intro y
    simpa [hpg] using
      (clientQ_support (n := n) (x := x) (y := y))

theorem client_domain_MA
    (n : ℕ) :
    ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      G ⊆ clientWorkingOmega n →
      volume {p | ∃ x ∈ G, ∀ y ∈ clientWorkingOmega n,
        clientVData n x + ⟪p, y - x⟫ ≤ clientVData n y} =
        ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
  intro G _ hG
  rw [← client_domain_support_image_eq hG, client_subgradientImage_eq]
  simp

theorem client_main
    (n : ℕ) :
    ∀ᵐ x ∂(volume.restrict (clientWorkingOmega n)),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
        A.PosDef ∧ A.det = (1 : ℝ) ∧
        HasFDerivAt (gradient (clientVData n))
          (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |clientVData n y -
              quadraticAt A x (gradient (clientVData n) x)
                (clientVData n x) y| ≤
            ε * ‖y - x‖ ^ 2 := by
  let Ω : Set (EuclideanSpace ℝ (Fin n)) :=
    clientWorkingOmega n

  have hstrict :
      StrictConvexOn ℝ Ω (clientVData n) := by
    refine ⟨convex_ball _ _, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hxyΩ :
        a • x + b • y ∈ Ω :=
      (convex_ball (0 : EuclideanSpace ℝ (Fin n)) 1)
        hx hy ha.le hb.le hab
    rw [clientVData_eq_q hx, clientVData_eq_q hy,
      clientVData_eq_q hxyΩ]
    exact
      (strictConvexOn_quadraticAt
        (Matrix.PosDef.one)
        (0 : EuclideanSpace ℝ (Fin n))
        (0 : EuclideanSpace ℝ (Fin n))
        0).2
        (mem_univ _) (mem_univ _) hxy ha hb hab

  have hv :
      ContDiffOn ℝ 1 (clientVData n) Ω := by
    apply
      (contDiff_quadraticAt
        (1 : Matrix (Fin n) (Fin n) ℝ)
        (0 : EuclideanSpace ℝ (Fin n))
        (0 : EuclideanSpace ℝ (Fin n))
        0).of_le (by norm_num) |>.contDiffOn.congr
    intro x hx
    exact clientVData_eq_q hx

  have hf :
      ContinuousOn (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) Ω :=
    continuousOn_const

  have hfpos :
      ∀ x ∈ Ω, 0 < (1 : ℝ) := by
    intro _ _
    norm_num

  simpa [Ω, clientWorkingOmega] using
    ae_exists_gradient_posDef_det_eq_of_strictConvexOn
      (v := clientVData n)
      (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
      (Ω := Ω)
      isOpen_ball
      hstrict
      hv
      hf
      hfpos
      (by
        intro G hGopen hG
        exact client_domain_MA n G hGopen hG)

end LetwinDomainGradientAudit
namespace LetwinDomainGradientAudit

/-- The shared metric cover includes the empty working set in dimension zero. -/
theorem empty_cover :
    ∃ (R : (∅ : Set (EuclideanSpace ℝ (Fin 0))) → ℝ)
      (s : Set (∅ : Set (EuclideanSpace ℝ (Fin 0)))),
      (∀ x, 0 < R x) ∧
      (∀ x : (∅ : Set (EuclideanSpace ℝ (Fin 0))),
        closedBall (x : EuclideanSpace ℝ (Fin 0)) (R x) ⊆ ∅) ∧
      s.Countable ∧ (∅ : Set (EuclideanSpace ℝ (Fin 0))) ⊆
        ⋃ x ∈ s, ball (x : EuclideanSpace ℝ (Fin 0)) (R x / 2) :=
  exists_countable_buffered_ball_cover isOpen_empty

end LetwinDomainGradientAudit

set_option pp.fullNames true
#print axioms FunctionalInequalities.Analysis.ae_exists_gradient_posDef_det_eq_of_strictConvexOn
#print axioms LetwinDomainGradientAudit.client_domain_MA
#print axioms LetwinDomainGradientAudit.client_main
#check LetwinDomainGradientAudit.client_main 0

#print axioms LetwinDomainGradientAudit.empty_cover
#print axioms FunctionalInequalities.Analysis.exists_countable_buffered_ball_cover
