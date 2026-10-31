module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
public import Mathlib.Analysis.Calculus.Deriv.Abs

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology Metric Classical
open scoped Pointwise RealInnerProductSpace ENNReal
namespace LetwinDomainComparisonAudit
open FunctionalInequalities.Analysis

section QuadraticClient

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

def clientU (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)

def clientV (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x =>
    if x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 2 then
      clientU n x
    else 0

def clientΩ (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.ball 0 1

private theorem clientU_convex :
    ConvexOn ℝ (Set.univ : Set E) (clientU n) :=
  convexOn_quadraticAt Matrix.PosDef.one.posSemidef _ _ _

private theorem clientU_contDiff : ContDiff ℝ 1 (clientU n) :=
  (contDiff_quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : E) 0 (-1 / 2)).of_le (by norm_num)

private theorem clientU_gradient (x : E) : gradient (clientU n) x = x := by
  simpa [clientU] using
    gradient_quadraticAt (n := n) Matrix.isHermitian_one (0 : E) 0 (-1 / 2) x

private theorem clientU_support (x y : E) :
    clientU n x + ⟪gradient (clientU n) x, y - x⟫ ≤
      clientU n y := by
  have h :=
    gradient_le_increment
      (clientU_convex (n := n)) x (y - x)
      ((clientU_contDiff (n := n)).differentiable
        (by norm_num) x)
  rw [add_sub_cancel] at h
  linarith

private theorem client_ball_one_subset_ball_two
    {x : E} (hx : x ∈ clientΩ n) :
    x ∈ Metric.ball 0 2 := by
  change dist x 0 < 2
  have hx' : dist x 0 < 1 := hx
  linarith

private theorem client_closure_one_subset_ball_two :
    closure (clientΩ n) ⊆ Metric.ball 0 2 := by
  have hsub :
      closure (clientΩ n) ⊆
        closedBall (0 : E) 1 :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  intro x hx
  have hx' : dist x 0 ≤ 1 := by
    exact hsub hx
  change dist x 0 < 2
  linarith

private theorem clientV_eq_u
    {x : E} (hx : x ∈ clientΩ n) :
    clientV n x = clientU n x := by
  simp [clientV, client_ball_one_subset_ball_two hx]

private theorem clientV_eq_u_closure
    {x : E} (hx : x ∈ closure (clientΩ n)) :
    clientV n x = clientU n x := by
  simp [clientV, client_closure_one_subset_ball_two hx]

private theorem clientV_continuousOn :
    ContinuousOn (clientV n) (closure (clientΩ n)) := by
  apply (clientU_contDiff (n := n)).continuous.continuousOn.congr
  intro x hx
  exact clientV_eq_u_closure hx

private theorem clientV_convexOn :
    ConvexOn ℝ (closure (clientΩ n)) (clientV n) := by
  refine ⟨(convex_ball (0 : E) 1).closure, ?_⟩
  intro x hx y hy a b ha hb hab
  rw [clientV_eq_u_closure hx, clientV_eq_u_closure hy]
  have hxy :
      a • x + b • y ∈ closure (clientΩ n) :=
    (convex_ball (0 : E) 1).closure hx hy ha hb hab
  rw [clientV_eq_u_closure hxy]
  exact (clientU_convex (n := n)).2
    (mem_univ x) (mem_univ y) ha hb hab

private theorem clientU_convexOn_closure :
    ConvexOn ℝ (closure (clientΩ n)) (clientU n) :=
  (clientU_convex (n := n)).subset (subset_univ _) (convex_ball (0 : E) 1).closure

private theorem client_zero_frontier {x : E} (hx : x ∈ frontier (clientΩ n)) :
    clientU n x = 0 ∧ clientV n x = 0 := by
  change x ∈ frontier (ball (0 : E) 1) at hx
  rw [isOpen_ball.frontier_eq] at hx
  have hxclosed : x ∈ closedBall (0 : E) 1 := by
    exact closure_minimal ball_subset_closedBall isClosed_closedBall hx.1
  have hnorm : dist x 0 = 1 := by
    apply le_antisymm
    · exact hxclosed
    · by_contra hlt
      apply hx.2
      exact lt_of_not_ge hlt
  have hu : clientU n x = 0 := by
    have hxnorm : ‖x‖ = 1 := by simpa [dist_zero_right] using hnorm
    norm_num [clientU, quadraticAt, Matrix.toEuclideanLin, hxnorm]
  have hv : clientV n x = 0 := by
    rw [clientV]
    have hx2 : x ∈ Metric.ball (0 : E) 2 := by
      change dist x 0 < 2
      linarith
    rw [ite_eq_left hx2, hu]
  exact ⟨hu, hv⟩

private theorem client_domainImage_u :
    ∀ G : Set E,
      G ⊆ clientΩ n →
      subgradientImageOn (clientU n) (clientΩ n) G = G := by
  intro G hG
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hpg :
        p = gradient (clientU n) x :=
      subgradientOn_eq_gradient
        isOpen_ball (hG hx)
        ((clientU_contDiff (n := n)).differentiable
          (by norm_num) x)
        hp
    rw [clientU_gradient] at hpg
    exact hpg.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y hy
    simpa only [clientU_gradient] using (clientU_support (n := n) p y)

private theorem client_domainImage_v :
    ∀ G : Set E,
      G ⊆ clientΩ n →
      subgradientImageOn (clientV n) (clientΩ n) G = G := by
  intro G hG
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hp' :
        ∀ y ∈ clientΩ n,
          clientU n x + ⟪p, y - x⟫ ≤ clientU n y := by
      intro y hy
      simpa [clientV_eq_u (hG hx), clientV_eq_u hy] using hp y hy
    have hpg :
        p = gradient (clientU n) x :=
      subgradientOn_eq_gradient
        isOpen_ball (hG hx)
        ((clientU_contDiff (n := n)).differentiable
          (by norm_num) x)
        hp'
    rw [clientU_gradient] at hpg
    exact hpg.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y hy
    rw [clientV_eq_u (hG hp), clientV_eq_u hy]
    simpa only [clientU_gradient] using (clientU_support (n := n) p y)

private theorem client_domain_MA_u :
    ∀ G : Set E, IsOpen G → G ⊆ clientΩ n →
      (volume : Measure E)
          (subgradientImageOn (clientU n) (clientΩ n) G) =
        (volume : Measure E) G := by
  intro G _ hG
  rw [client_domainImage_u G hG]

private theorem client_domain_MA_v :
    ∀ G : Set E, IsOpen G → G ⊆ clientΩ n →
      (volume : Measure E)
          (subgradientImageOn (clientV n) (clientΩ n) G) =
        (volume : Measure E) G := by
  intro G _ hG
  rw [client_domainImage_v G hG]

/-- The shifted quadratic is the global quadratic `‖x‖²/2` minus `1/2`;
the piecewise reference agrees with it on the working ball and is zero
outside the larger ball.  All support images below remain domain-relative. -/
theorem quadratic_domain_client (hn : 0 < n) :
    ∀ x ∈ clientΩ n, |clientU n x - clientV n x| ≤ (0 : ℝ) := by
  intro x hx
  have hbounds :=
    abs_sub_le_of_domain_alexandrov_density_close (n := n) hn (hΩo := isOpen_ball) (hΩc :=
      convex_ball (0 : E) 1) (hΩb := isBounded_ball) (hu := clientU_convexOn_closure (n := n))
      (hv := clientV_convexOn (n := n)) (huc :=
      (clientU_contDiff (n := n)).continuous.continuousOn) (hvc :=
      clientV_continuousOn (n := n)) (hu0 := by
      intro z hz
      exact (client_zero_frontier hz).1) (hv0 := by
      intro z hz
      exact (client_zero_frontier hz).2) (ε := 0) (hε := by norm_num) (hε1 := by norm_num)
      (hMAu := by
      intro G hG hGO
      rw [show ((1 - (0 : ℝ)) ^ n : ℝ) = 1 by norm_num,
        show ((1 + (0 : ℝ)) ^ n : ℝ) = 1 by norm_num, ENNReal.ofReal_one]
      change
        1 * volume G ≤ volume (subgradientImageOn (clientU n) (clientΩ n) G) ∧
          volume (subgradientImageOn (clientU n) (clientΩ n) G) ≤ 1 * volume G
      rw [client_domain_MA_u G hG hGO]
      simp) (hMAv := by
      intro G hG hGO
      exact client_domain_MA_v G hG hGO) x hx
  simpa using hbounds

end QuadraticClient

/-- The generic comparison genuinely accepts the empty zero-dimensional domain. -/
theorem empty_zero_dimensional : ∀ x ∈ (∅ : Set (EuclideanSpace ℝ (Fin 0))), (0 : ℝ) ≤ 0 := by
  apply
    le_of_strict_domain_alexandrov_bounds (u := fun _ => (0 : ℝ)) (v := fun _ => (0 : ℝ))
      isOpen_empty convex_empty isCompact_empty.isBounded
      (by simp only [closure_empty]; exact ⟨convex_empty, by simp⟩)
      (by simp only [closure_empty]; exact ⟨convex_empty, by simp⟩) continuousOn_const
      continuousOn_const (by simp) (a := 1) (b := 0) (by norm_num) (by norm_num)
  · intro G _ hG
    have heq : G = ∅ := subset_empty_iff.mp hG
    simp [heq, subgradientImageOn]
  · intro G _ hG
    have heq : G = ∅ := subset_empty_iff.mp hG
    simp [heq, subgradientImageOn]

/-- A genuinely locally differentiable convex function; abs is not globally differentiable. -/
theorem abs_positive_halfline {G : Set ℝ} (hG : G ⊆ Ioi (0 : ℝ)) :
    subgradientImage (fun x : ℝ => |x|) G =
      {p | ∃ x ∈ G, ∀ y ∈ Ioi (0 : ℝ), |x| + ⟪p, y-x⟫ ≤ |y|} := by
  have hc : ConvexOn ℝ univ (fun x : ℝ => |x|) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    calc
      |a • x + b • y| ≤ |a • x| + |b • y| := abs_add_le _ _
      _ = a • |x| + b • |y| := by
        simp [smul_eq_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hd : DifferentiableOn ℝ (fun x : ℝ => |x|) (Ioi (0 : ℝ)) := by
    intro x hx
    have heq : (fun y : ℝ => |y|) =ᶠ[𝓝 x] (fun y : ℝ => y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact abs_of_pos hy
    exact (differentiableAt_id.congr_of_eventuallyEq heq).differentiableWithinAt
  exact (subgradientImageOn_eq_subgradientImage hc isOpen_Ioi hd hG).symm

theorem abs_not_globally_differentiable : ¬ Differentiable ℝ (fun x : ℝ => |x|) := by
  intro h
  exact not_differentiableAt_abs_zero (h 0)

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- Actual SAME normalized/transporting/Holder source, with DOMAIN MA derived
from global MA and real local differentiability; agreement is not an input. -/
theorem source_domain_MA (hn : 0 < n) {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ :
      (μ : Measure E) =
        volume.withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal),
      StrictConvexOn ℝ univ u ∧
        LipschitzWith L u ∧
          (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
            ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
              ContDiff ℝ 1 u ∧
                (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
                  (∀ Q : Set E,
                      IsCompact Q →
                        ∃ α C : ℝ,
                          0 < α ∧
                            α ≤ 1 ∧
                              0 ≤ C ∧
                                ∀ x ∈ Q,
                                  ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
                    ∀ Ω : Set E,
                      IsOpen Ω →
                        ∀ G : Set E,
                          IsOpen G →
                            G ⊆ Ω →
                              volume (subgradientImageOn u Ω G) =
                                ∫⁻ y in G,
                                  ENNReal.ofReal (Real.exp (-u y + W (gradient u y))) := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, _hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ
      hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  intro Ω hΩ G hG hGO
  rw [subgradientImageOn_eq_subgradientImage hs.convexOn hΩ
      (hC1.differentiable one_ne_zero).differentiableOn hGO]
  exact hMA G hG

end LetwinDomainComparisonAudit
set_option pp.fullNames true in
#print axioms LetwinDomainComparisonAudit.quadratic_domain_client
set_option pp.fullNames true in
#print axioms LetwinDomainComparisonAudit.empty_zero_dimensional
set_option pp.fullNames true in
#print axioms LetwinDomainComparisonAudit.abs_positive_halfline
set_option pp.fullNames true in
#print axioms LetwinDomainComparisonAudit.abs_not_globally_differentiable
set_option pp.fullNames true in
#print axioms LetwinDomainComparisonAudit.source_domain_MA
