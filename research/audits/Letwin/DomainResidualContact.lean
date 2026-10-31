module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology Metric Classical
open scoped Pointwise RealInnerProductSpace ENNReal
namespace DomainResidualContactAudit
open FunctionalInequalities.Analysis
section QuadraticClient

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def clientQuadratic (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2 : ℝ)

def clientReference (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x =>
    if x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 then
      clientQuadratic n x
    else 0

def clientDomain (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.ball 0 1

def clientCompact (n : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 r

private theorem clientQuadratic_convex :
    ConvexOn ℝ (Set.univ : Set E) (clientQuadratic n) :=
  convexOn_quadraticAt Matrix.PosDef.one.posSemidef _ _ _

private theorem clientQuadratic_strict :
    StrictConvexOn ℝ (Set.univ : Set E) (clientQuadratic n) := by
  simpa [clientQuadratic] using
    (strictConvexOn_quadraticAt
      (A := (1 : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef)
      (x₀ := (0 : E)) (b := (0 : E)) (c := (-1 / 2 : ℝ)))

private theorem clientQuadratic_C1 :
    ContDiff ℝ 1 (clientQuadratic n) :=
  (contDiff_quadraticAt
    (A := (1 : Matrix (Fin n) (Fin n) ℝ))
    (x₀ := (0 : E)) (b := (0 : E)) (c := (-1 / 2 : ℝ))).of_le
      (by norm_num)

private theorem clientQuadratic_gradient (x : E) :
    gradient (clientQuadratic n) x = x := by
  simpa [clientQuadratic] using
    gradient_quadraticAt
      (n := n)
      Matrix.isHermitian_one
      (0 : E) 0 (-1 / 2 : ℝ) x

private theorem clientQuadratic_support (x y : E) :
    clientQuadratic n x +
        ⟪gradient (clientQuadratic n) x, y - x⟫ ≤
      clientQuadratic n y := by
  have h :=
    gradient_le_increment
      (clientQuadratic_convex (n := n))
      x (y - x)
      ((clientQuadratic_C1 (n := n)).differentiable
        (by norm_num) x)
  rw [add_sub_cancel] at h
  linarith

private theorem client_closure_subset_ball_two :
    closure (clientDomain n) ⊆ Metric.ball (0 : E) 2 := by
  have hsub :
      closure (clientDomain n) ⊆ Metric.closedBall (0 : E) 1 :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  intro x hx
  have hx' : dist x 0 ≤ 1 := hsub hx
  change dist x 0 < 2
  linarith

private theorem client_domain_subset_ball_two :
    clientDomain n ⊆ Metric.ball (0 : E) 2 := by
  intro x hx
  have hx' : dist x 0 < 1 := hx
  change dist x 0 < 2
  linarith

private theorem clientReference_eq_quadratic
    {x : E} (hx : x ∈ closure (clientDomain n)) :
    clientReference n x = clientQuadratic n x := by
  simp [clientReference, client_closure_subset_ball_two hx]

private theorem clientReference_continuous :
    ContinuousOn (clientReference n) (closure (clientDomain n)) := by
  apply (clientQuadratic_C1 (n := n)).continuous.continuousOn.congr
  intro x hx
  exact clientReference_eq_quadratic hx

private theorem clientReference_convex :
    ConvexOn ℝ (closure (clientDomain n)) (clientReference n) := by
  refine ⟨(convex_ball (0 : E) 1).closure, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy :
      a • x + b • y ∈ closure (clientDomain n) :=
    (convex_ball (0 : E) 1).closure hx hy ha hb hab
  rw [clientReference_eq_quadratic hx,
    clientReference_eq_quadratic hy,
    clientReference_eq_quadratic hxy]
  exact (clientQuadratic_convex (n := n)).2
    (mem_univ x) (mem_univ y) ha hb hab

private theorem clientReference_strict :
    StrictConvexOn ℝ (clientDomain n) (clientReference n) := by
  refine ⟨convex_ball (0 : E) 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hxy' :
      a • x + b • y ∈ clientDomain n :=
    (convex_ball (0 : E) 1) hx hy ha.le hb.le hab
  have hq :=
    (clientQuadratic_strict (n := n)).2
      (mem_univ x) (mem_univ y) (fun h => hxy h)
      ha hb hab
  rw [clientReference_eq_quadratic (subset_closure hx),
    clientReference_eq_quadratic (subset_closure hy),
    clientReference_eq_quadratic (subset_closure hxy')]
  exact hq

private theorem clientReference_C1 :
    ContDiffOn ℝ 1 (clientReference n) (clientDomain n) := by
  have hq :
      ContDiffOn ℝ 1 (clientQuadratic n) (clientDomain n) :=
    (clientQuadratic_C1 (n := n)).contDiffOn
  exact hq.congr fun x hx =>
    clientReference_eq_quadratic (subset_closure hx)

private theorem clientReference_zero_frontier
    {x : E} (hx : x ∈ frontier (clientDomain n)) :
    clientQuadratic n x = 0 ∧ clientReference n x = 0 := by
  change x ∈ frontier (ball (0 : E) 1) at hx
  rw [isOpen_ball.frontier_eq] at hx
  have hxclosed :
      x ∈ Metric.closedBall (0 : E) 1 := by
    exact closure_minimal ball_subset_closedBall isClosed_closedBall hx.1
  have hnorm : dist x 0 = 1 := by
    apply le_antisymm
    · exact hxclosed
    · by_contra hlt
      apply hx.2
      exact lt_of_not_ge hlt
  have hxnorm : ‖x‖ = 1 := by
    simpa [dist_zero_right] using hnorm
  have hq : clientQuadratic n x = 0 := by
    norm_num [clientQuadratic, quadraticAt,
      Matrix.toEuclideanLin, hxnorm]
  have hv : clientReference n x = 0 := by
    rw [clientReference]
    have hx2 : x ∈ Metric.ball (0 : E) 2 := by
      change dist x 0 < 2
      linarith
    rw [ite_eq_left hx2, hq]
  exact ⟨hq, hv⟩

private theorem client_quadratic_domain_image
    (G : Set E) (hG : G ⊆ clientDomain n) :
    subgradientImageOn (clientQuadratic n) (clientDomain n) G = G := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hpg :
        p = gradient (clientQuadratic n) x :=
      subgradientOn_eq_gradient
        isOpen_ball (hG hx)
        ((clientQuadratic_C1 (n := n)).differentiable
          (by norm_num) x)
        hp
    rw [clientQuadratic_gradient] at hpg
    exact hpg.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y hy
    simpa only [clientQuadratic_gradient] using
      clientQuadratic_support (n := n) p y

private theorem client_reference_domain_image
    (G : Set E) (hG : G ⊆ clientDomain n) :
    subgradientImageOn (clientReference n) (clientDomain n) G = G := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hp' :
        ∀ y ∈ clientDomain n,
          clientQuadratic n x +
              ⟪p, y - x⟫ ≤ clientQuadratic n y := by
      intro y hy
      simpa only [
        clientReference_eq_quadratic (subset_closure (hG hx)),
        clientReference_eq_quadratic (subset_closure hy)] using
        hp y hy
    have hpg :
        p = gradient (clientQuadratic n) x :=
      subgradientOn_eq_gradient
        isOpen_ball (hG hx)
        ((clientQuadratic_C1 (n := n)).differentiable
          (by norm_num) x)
        hp'
    rw [clientQuadratic_gradient] at hpg
    exact hpg.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y hy
    rw [clientReference_eq_quadratic (subset_closure (hG hp)),
      clientReference_eq_quadratic (subset_closure hy)]
    simpa only [clientQuadratic_gradient] using
      clientQuadratic_support (n := n) p y

private theorem client_reference_domain_MA :
    ∀ G : Set E, IsOpen G → G ⊆ clientDomain n →
      (volume : Measure E)
          (subgradientImageOn (clientReference n) (clientDomain n) G) =
        (volume : Measure E) G := by
  intro G _ hG
  rw [client_reference_domain_image G hG]

/-- Concrete unit-density client. The reference is the quadratic on the
two-ball and is zero outside that ball; all Alexandrov data used here are
domain-relative. -/
theorem quadratic_domain_residual_client
    (hn : 0 < n)
    (r : ℝ) (hr1 : r < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (u : E → ℝ),
        ConvexOn ℝ univ u →
        ContDiff ℝ 1 u →
        (∀ x ∈ frontier (clientDomain n), u x = 0) →
        (∀ G : Set E, IsOpen G → G ⊆ clientDomain n →
          ENNReal.ofReal ((1 - ε) ^ n) *
              (volume : Measure E) G ≤
            (volume : Measure E) (subgradientImage u G) ∧
          (volume : Measure E) (subgradientImage u G) ≤
            ENNReal.ofReal ((1 + ε) ^ n) *
              (volume : Measure E) G) →
        ∀ z ∈ clientCompact n r, ∃ x ∈ clientDomain n,
          gradient u x - (1 - δ) •
              gradient (clientReference n) x =
            δ • gradient (clientReference n) z ∧
          ∀ y ∈ closure (clientDomain n),
            u x - (1 - δ) * clientReference n x +
                ⟪δ • gradient (clientReference n) z, y - x⟫ ≤
              u y - (1 - δ) * clientReference n y := by
  let Ω : Set E := clientDomain n
  let K : Set E := clientCompact n r

  have hΩo : IsOpen Ω := isOpen_ball
  have hΩb : Bornology.IsBounded Ω := isBounded_ball

  have hK : IsCompact K := by
    exact isCompact_closedBall _ _

  have hKΩ : K ⊆ Ω := by
    intro x hx
    have hxnorm : ‖x‖ ≤ r := by
      simpa [K, clientCompact, mem_closedBall, dist_zero_right] using hx
    have hxnorm' : ‖x‖ < 1 := lt_of_le_of_lt hxnorm hr1
    simpa [Ω, clientDomain, mem_ball, dist_zero_right] using hxnorm'

  have hv0 :
      ∀ x ∈ frontier Ω, clientReference n x = 0 := by
    intro x hx
    exact (clientReference_zero_frontier hx).2

  have hMAv :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        (volume : Measure E)
            (subgradientImageOn (clientReference n) Ω G) =
          (volume : Measure E) G := by
    intro G hG hGΩ
    exact client_reference_domain_MA G hG hGΩ

  simpa [Ω, K] using
    (FunctionalInequalities.Analysis.exists_residual_contact_of_domain_alexandrov_density_close
      (n := n)
      (v := clientReference n)
      (Ω := Ω) (K := K)
      hn hΩo hΩb
      (clientReference_convex (n := n))
      (clientReference_strict (n := n))
      (clientReference_continuous (n := n))
      (clientReference_C1 (n := n))
      hv0 hMAv hK hKΩ hδ)

end QuadraticClient

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- The same normalized transporting Holder potential produces residual contacts
under displayed local density and boundary conditions and a real given reference. -/
theorem source_residual_contacts (hn : 0 < n)
    {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = volume.withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      (∀ Q : Set E, IsCompact Q → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
        ∀ x ∈ Q, ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
      ∀ Ω : Set E, IsOpen Ω → Bornology.IsBounded Ω →
        ∀ v : E → ℝ, ConvexOn ℝ (closure Ω) v → StrictConvexOn ℝ Ω v →
        ContinuousOn v (closure Ω) → ContDiffOn ℝ 1 v Ω →
        (∀ x ∈ frontier Ω, v x = 0) →
        (∀ H : Set E, IsOpen H → H ⊆ Ω → volume (subgradientImageOn v Ω H) = volume H) →
        ∀ Q : Set E, IsCompact Q → Q ⊆ Ω → ∀ δ : ℝ, 0 < δ →
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
          ((∀ x ∈ frontier Ω, u x = 0) →
          (∀ x ∈ Ω, (1 - ε) ^ n ≤ Real.exp (-u x + W (gradient u x)) ∧
            Real.exp (-u x + W (gradient u x)) ≤ (1 + ε) ^ n) →
          ∀ z ∈ Q, ∃ x ∈ Ω,
            gradient u x - (1 - δ) • gradient v x = δ • gradient v z ∧
            ∀ y ∈ closure Ω, u x - (1 - δ) * v x + ⟪δ • gradient v z, y-x⟫ ≤
              u y - (1 - δ) * v y) := by
    obtain
      ⟨u, L, hs, hl, hn', hm, hC1, he, _hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
      exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne
        hW μ hμ hiso
    refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
    intro Ω hΩo hΩb v hv hvs hvc hvC1 hv0 hMAv Q hQ hQΩ δ hδ
    obtain ⟨ε, hε, hε1, hcontact⟩ :=
      exists_residual_contact_of_domain_alexandrov_density_close hn hΩo hΩb hv hvs hvc
        hvC1 hv0 hMAv hQ hQΩ hδ
    refine ⟨ε, hε, hε1, ?_⟩
    intro hu0 hf
    apply hcontact u hs.convexOn hC1 hu0
    intro H hH hHO
    rw [hMA H hH]
    constructor
    · rw [← setLIntegral_const H]
      apply setLIntegral_mono' hH.measurableSet
      intro y hy
      exact ENNReal.ofReal_le_ofReal (hf y (hHO hy)).1
    · rw [← setLIntegral_const H]
      apply setLIntegral_mono' hH.measurableSet
      intro y hy
      exact ENNReal.ofReal_le_ofReal (hf y (hHO hy)).2

end DomainResidualContactAudit

end

set_option pp.fullNames true in
#print axioms
  FunctionalInequalities.Analysis.exists_residual_contact_of_domain_alexandrov_density_close
set_option pp.fullNames true in
#print axioms DomainResidualContactAudit.quadratic_domain_residual_client

set_option pp.fullNames true in
#print axioms DomainResidualContactAudit.source_residual_contacts
