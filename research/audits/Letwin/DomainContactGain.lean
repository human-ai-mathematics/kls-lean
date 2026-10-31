module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology Metric Classical
open scoped Pointwise RealInnerProductSpace ENNReal
namespace DomainContactGainAudit
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


private theorem actual_reference_C2 : ContDiffOn ℝ 2 (clientReference n) (clientDomain n) := by
  apply (contDiff_quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2 : ℝ)).contDiffOn.congr
  intro x hx
  exact clientReference_eq_quadratic (subset_closure hx)

private theorem actual_reference_PD {x : E} (hx : x ∈ clientDomain n) {z : E} (hz : z ≠ 0) :
    0 < bilinearIteratedFDerivTwo ℝ (clientReference n) x z z := by
  have heq : clientReference n =ᶠ[𝓝 x] clientQuadratic n := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact clientReference_eq_quadratic (subset_closure hy)
  have hh :
    bilinearIteratedFDerivTwo ℝ (clientReference n) x =
      bilinearIteratedFDerivTwo ℝ (clientQuadratic n) x := by
    unfold bilinearIteratedFDerivTwo
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  have hqC2 : ContDiff ℝ 2 (clientQuadratic n) :=
    (contDiff_quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2 : ℝ)).of_le (by norm_num)
  rw [hh, BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator hqC2]
  change 0 < ⟪(fderiv ℝ (gradient (clientQuadratic n)) x) z, z⟫
  rw [show gradient (clientQuadratic n) = fun y => y by
      funext y;
      exact clientQuadratic_gradient y]
  simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
    sq_pos_of_pos (norm_pos_iff.mpr hz)

/-- True piecewise quadratic reference on ball01, not an assumed Dirichlet reference.
All n>0 and every relatively compact open subball. -/
theorem actual_piecewise_quadratic_gain (hn : 0 < n) {r δ η : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hη : 0 < η) (hη1 : η < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (u f : E → ℝ), ConvexOn ℝ univ u → ContDiff ℝ 1 u →
        ContinuousOn f (clientDomain n) → (∀ x ∈ clientDomain n, 0 < f x) →
        (∀ x ∈ frontier (clientDomain n), u x = 0) →
        (∀ x ∈ clientDomain n, (1-ε) ^ n ≤ f x ∧ f x ≤ (1 + ε) ^ n) →
        (∀ H : Set E, IsOpen H → H ⊆ clientDomain n →
          volume (subgradientImage u H) = ∫⁻ x in H, ENNReal.ofReal (f x)) →
        ENNReal.ofReal (1-η) * volume (ball (0:E) r) ≤
          volume {x | x ∈ clientDomain n ∧ ∀ y ∈ clientDomain n,
            u x-(1-δ) * clientReference n x +
              ⟪gradient u x-(1-δ) • gradient (clientReference n) x, y-x⟫ ≤
                u y-(1-δ) * clientReference n y} := by
    have hGc : IsCompact (closure (ball (0 : E) r)) := isBounded_ball.isCompact_closure
    have hGO : closure (ball (0 : E) r) ⊆ clientDomain n := by
      intro x hx
      have hclosed : x ∈ closedBall (0 : E) r :=
        closure_minimal ball_subset_closedBall isClosed_closedBall hx
      exact lt_of_le_of_lt hclosed hr1
    have _hrnonempty : (ball (0 : E) r).Nonempty := ⟨0, mem_ball_self hr0⟩
    exact
      exists_contact_volume_gain_of_strict_reference_on_domain hn isOpen_ball
        isBounded_ball clientReference_convex clientReference_strict
        clientReference_continuous actual_reference_C2
        (fun x hx => (clientReference_zero_frontier hx).2)
        (fun x hx z hz => actual_reference_PD hx hz) client_reference_domain_MA
        isOpen_ball hGc hGO hδ hδ1 hη hη1
end QuadraticClient
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- The SAME normalized/transporting/Holder literal source, with displayed density
and boundary conditions and real given DOMAIN reference. No source Hessian input. -/
theorem source_domain_contact_volume_gain (hn : 0 < n)
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
        ContinuousOn v (closure Ω) → ContDiffOn ℝ 2 v Ω →
        (∀ x ∈ frontier Ω, v x=0) →
        (∀ x ∈ Ω, ∀ z : E, z≠0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z) →
        (∀ H : Set E, IsOpen H → H⊆Ω → volume (subgradientImageOn v Ω H)=volume H) →
        ∀ G : Set E, IsOpen G → IsCompact (closure G) → closure G⊆Ω →
        ∀ δ η : ℝ, 0<δ → δ<1 → 0<η → η<1 →
        ∃ ε : ℝ, 0<ε ∧ ε<1 ∧
          ((∀ x ∈ frontier Ω, u x=0) →
          (∀ x ∈ Ω, (1-ε) ^ n ≤ Real.exp (-u x + W (gradient u x)) ∧
            Real.exp (-u x + W (gradient u x)) ≤ (1 + ε) ^ n) →
          ENNReal.ofReal (1-η) * volume G ≤
            volume {x | x∈Ω ∧ ∀ y∈Ω,
              u x-(1-δ) * v x+⟪gradient u x-(1-δ) • gradient v x, y-x⟫ ≤ u y-(1-δ) * v y}) := by
    obtain
      ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
      exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne
        hW μ hμ hiso
    refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
    intro Ω hΩo hΩb v hv hvs hvc hvC2 hv0 hPD hMAv G hG hGc hGO δ η hδ hδ1 hη hη1
    obtain ⟨ε, hε, hε1, hgain⟩ :=
      exists_contact_volume_gain_of_strict_reference_on_domain hn hΩo hΩb hv hvs hvc
        hvC2 hv0 hPD hMAv hG hGc hGO hδ hδ1 hη hη1
    refine ⟨ε, hε, hε1, ?_⟩
    intro hu0 hbounds
    exact
      hgain u (fun x => Real.exp (-u x + W (gradient u x))) hs.convexOn hC1
        hf.continuousOn (fun _ _ => Real.exp_pos _) hu0 hbounds (fun H hH _ => hMA H hH)

end DomainContactGainAudit
set_option pp.fullNames true in
#print axioms DomainContactGainAudit.actual_piecewise_quadratic_gain
set_option pp.fullNames true in
#print axioms
  FunctionalInequalities.Analysis.exists_contact_volume_gain_of_strict_reference_on_domain

set_option pp.fullNames true in
#print axioms DomainContactGainAudit.source_domain_contact_volume_gain
