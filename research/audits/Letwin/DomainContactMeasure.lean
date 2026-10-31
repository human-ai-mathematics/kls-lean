module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder

noncomputable section
open MeasureTheory Set Filter Metric Classical
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace LetwinDomainContactMeasureAudit
open FunctionalInequalities.Analysis

private def clientQ (n : ℕ) : (EuclideanSpace ℝ (Fin n)) → ℝ :=
  quadraticAt
    (1 : Matrix (Fin n) (Fin n) ℝ)
    (0 : (EuclideanSpace ℝ (Fin n))) (0 : (EuclideanSpace ℝ (Fin n))) 0

private def clientOmega (n : ℕ) : Set ((EuclideanSpace ℝ (Fin n))) :=
  Metric.ball 0 2

private def clientWorkingOmega (n : ℕ) : Set ((EuclideanSpace ℝ (Fin n))) :=
  Metric.ball 0 1

private def clientV (n : ℕ) : (EuclideanSpace ℝ (Fin n)) → ℝ :=
  fun x =>
    if x ∈ clientOmega n then clientQ n x else 0

private theorem clientQ_eq_norm_sq
    {n : ℕ} (x : (EuclideanSpace ℝ (Fin n))) :
    clientQ n x = (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  simp [clientQ, quadraticAt, Matrix.toEuclideanLin]

private theorem clientQ_gradient
    {n : ℕ} (x : (EuclideanSpace ℝ (Fin n))) :
    gradient (clientQ n) x = x := by
  simpa [clientQ] using
    gradient_quadraticAt
      (n := n) Matrix.isHermitian_one
      (0 : (EuclideanSpace ℝ (Fin n))) 0 0 x

private theorem clientQ_contDiff
    {n : ℕ} :
    ContDiff ℝ 2 (clientQ n) :=
  contDiff_quadraticAt
    (1 : Matrix (Fin n) (Fin n) ℝ)
    (0 : (EuclideanSpace ℝ (Fin n))) 0 0

private theorem clientQ_convex
    {n : ℕ} :
    ConvexOn ℝ univ (clientQ n) :=
  convexOn_quadraticAt Matrix.PosSemidef.one
    (0 : (EuclideanSpace ℝ (Fin n))) 0 0

private theorem clientQ_support
    {n : ℕ} {x y : (EuclideanSpace ℝ (Fin n))} :
    clientQ n x +
        ⟪gradient (clientQ n) x, y - x⟫
      ≤
    clientQ n y := by
  have h :=
    gradient_le_increment
      clientQ_convex x (y - x)
      ((clientQ_contDiff (n := n)).differentiable
        (by norm_num) x)
  rw [add_sub_cancel] at h
  linarith

private theorem clientV_eq_q
    {n : ℕ} {x : (EuclideanSpace ℝ (Fin n))}
    (hx : x ∈ clientWorkingOmega n) :
    clientV n x = clientQ n x := by
  have hx2 : x ∈ clientOmega n := by
    change dist x 0 < 2
    have hx1 : dist x 0 < 1 := hx
    linarith
  simp [clientV, hx2]

private theorem clientV_gradient
    {n : ℕ} {x : (EuclideanSpace ℝ (Fin n))}
    (hx : x ∈ clientWorkingOmega n) :
    gradient (clientV n) x = x := by
  have heq : clientV n =ᶠ[𝓝 x] clientQ n := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact clientV_eq_q hy
  rw [heq.gradient_eq, clientQ_gradient]

private theorem clientV_hessian
    {n : ℕ} {x : (EuclideanSpace ℝ (Fin n))}
    (hx : x ∈ clientWorkingOmega n) :
    bilinearIteratedFDerivTwo ℝ (clientV n) x
        = bilinearIteratedFDerivTwo ℝ (clientQ n) x := by
  have heq : clientV n =ᶠ[𝓝 x] clientQ n := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact clientV_eq_q hy
  unfold bilinearIteratedFDerivTwo
  rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq]

private theorem clientV_posDef
    {n : ℕ} {x : (EuclideanSpace ℝ (Fin n))}
    (hx : x ∈ clientWorkingOmega n)
    {z : (EuclideanSpace ℝ (Fin n))} (hz : z ≠ 0) :
    0 < bilinearIteratedFDerivTwo ℝ (clientV n) x z z := by
  rw [clientV_hessian hx]
  rw [BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator
    clientQ_contDiff]
  change 0 < ⟪(fderiv ℝ (gradient (clientQ n)) x) z, z⟫
  rw [show gradient (clientQ n) = fun y => y by
    funext y
    exact clientQ_gradient y]
  simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq] using
    sq_pos_of_pos (norm_pos_iff.mpr hz)

private theorem clientQ_subgradientImage
    {n : ℕ} {G : Set ((EuclideanSpace ℝ (Fin n)))} :
    subgradientImage (clientQ n) G = G := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨x, hx, hpx⟩
    have hpg :
        p = gradient (clientQ n) x :=
      subgradient_eq_gradient
        ((clientQ_contDiff (n := n)).differentiable
          (by norm_num) x) hpx
    rw [clientQ_gradient] at hpg
    exact hpg.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y
    simpa [clientQ_gradient] using
      (clientQ_support (n := n) (x := p) (y := y))

private theorem clientDomainImage
    {n : ℕ} {G : Set ((EuclideanSpace ℝ (Fin n)))}
    (hG : G ⊆ clientWorkingOmega n) :
    subgradientImage (clientQ n) G =
      {p | ∃ x ∈ G, ∀ y ∈ clientWorkingOmega n,
        clientV n x + ⟪p, y - x⟫ ≤ clientV n y} := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨x, hx, hpx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    rw [clientV_eq_q (hG hx), clientV_eq_q hy]
    exact hpx y
  · intro hp
    rcases hp with ⟨x, hx, hpx⟩
    have hpxq :
        ∀ y ∈ clientWorkingOmega n,
          clientQ n x + ⟪p, y - x⟫ ≤ clientQ n y := by
      intro y hy
      rw [← clientV_eq_q (hG hx), ← clientV_eq_q hy]
      exact hpx y hy
    have hpg :
        p = gradient (clientQ n) x :=
      subgradientOn_eq_gradient
        isOpen_ball (hG hx)
        ((clientQ_contDiff (n := n)).differentiable
          (by norm_num) x) hpxq
    refine ⟨x, hx, ?_⟩
    intro y
    simpa [hpg] using
      (clientQ_support (n := n) (x := x) (y := y))

private theorem client_u_MA
    {n : ℕ} :
    ∀ G : Set ((EuclideanSpace ℝ (Fin n))), IsOpen G →
      G ⊆ clientWorkingOmega n →
      volume (subgradientImage (clientQ n) G) =
        ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
  intro G _ _
  rw [clientQ_subgradientImage]
  simp

private theorem client_domain_MA
    {n : ℕ} :
    ∀ G : Set ((EuclideanSpace ℝ (Fin n))), IsOpen G →
      G ⊆ clientWorkingOmega n →
      volume {p | ∃ x ∈ G, ∀ y ∈ clientWorkingOmega n,
        clientV n x + ⟪p, y - x⟫ ≤ clientV n y} =
        volume G := by
  intro G _ hGO
  rw [← clientDomainImage hGO, clientQ_subgradientImage]

private theorem client_strict
    {n : ℕ} :
    StrictConvexOn ℝ (clientWorkingOmega n) (clientV n) := by
  refine ⟨convex_ball _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hxyΩ :
      a • x + b • y ∈ clientWorkingOmega n :=
    (convex_ball (0 : (EuclideanSpace ℝ (Fin n))) 1) hx hy ha.le hb.le hab
  rw [clientV_eq_q hx, clientV_eq_q hy, clientV_eq_q hxyΩ]
  exact
    (strictConvexOn_quadraticAt Matrix.PosDef.one
      (0 : (EuclideanSpace ℝ (Fin n))) 0 0).2
      (mem_univ _) (mem_univ _) hxy ha hb hab

private theorem client_C1
    {n : ℕ} :
    ContDiffOn ℝ 1 (clientV n) (clientWorkingOmega n) := by
  apply
    (clientQ_contDiff (n := n)).of_le (by norm_num) |>.contDiffOn.congr
  intro x hx
  exact clientV_eq_q hx

private theorem client_support_hessian
    {n : ℕ} :
    ∀ x ∈ clientWorkingOmega n, ∀ z : (EuclideanSpace ℝ (Fin n)), z ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ (clientV n) x z z := by
    intro x hx z hz
    exact clientV_posDef hx hz

/-- A genuine quadratic client for every positive dimension.

The first conjunct is obtained from the arbitrary measurable-contact theorem.
The second conjunct is obtained independently from the derived full-contact
theorem; neither global convexity, global smoothness, nor a global reference
Monge–Ampère identity is used. -/
theorem quadratic_domain_client
    {n : ℕ} (hn : 0 < n) :
    (∀ Γ : Set ((EuclideanSpace ℝ (Fin n))), MeasurableSet Γ →
      Γ ⊆ clientWorkingOmega n →
      (∀ x ∈ Γ, ∀ y ∈ clientWorkingOmega n,
        clientQ n x - (1 - (1 / 2 : ℝ)) * clientV n x +
            ⟪gradient (clientQ n) x -
              (1 - (1 / 2 : ℝ)) • gradient (clientV n) x, y - x⟫
          ≤
        clientQ n y - (1 - (1 / 2 : ℝ)) * clientV n y) →
      volume
          ((fun x => gradient (clientQ n) x -
            (1 - (1 / 2 : ℝ)) • gradient (clientV n) x) '' Γ) ≤
        ENNReal.ofReal ((0 + (1 / 2 : ℝ)) ^ n) * volume Γ) ∧
    (let Γ := {x | x ∈ clientWorkingOmega n ∧
      ∀ y ∈ clientWorkingOmega n,
        clientQ n x - (1 - (1 / 2 : ℝ)) * clientV n x +
            ⟪gradient (clientQ n) x -
              (1 - (1 / 2 : ℝ)) • gradient (clientV n) x, y - x⟫
          ≤
        clientQ n y - (1 - (1 / 2 : ℝ)) * clientV n y}
     volume
          ((fun x => gradient (clientQ n) x -
            (1 - (1 / 2 : ℝ)) • gradient (clientV n) x) '' Γ) ≤
        ENNReal.ofReal ((0 + (1 / 2 : ℝ)) ^ n) * volume Γ) := by
  let Ω : Set ((EuclideanSpace ℝ (Fin n))) := clientWorkingOmega n

  have hconv :
      ConvexOn ℝ univ (clientQ n) :=
    clientQ_convex

  have hu :
      ContDiff ℝ 1 (clientQ n) :=
    (clientQ_contDiff (n := n)).of_le (by norm_num)

  have hv :
      ContDiffOn ℝ 2 (clientV n) Ω := by
    apply
      (clientQ_contDiff (n := n)).contDiffOn.congr
    intro x hx
    exact clientV_eq_q hx

  have hf :
      ContinuousOn (fun _ : (EuclideanSpace ℝ (Fin n)) => (1 : ℝ)) Ω :=
    continuousOn_const

  have hfpos :
      ∀ x ∈ Ω, 0 < (1 : ℝ) := by
    intro _ _
    norm_num

  have hfupper :
      ∀ x ∈ Ω, (1 : ℝ) ≤ (1 + (0 : ℝ)) ^ n := by
    intro _ _
    simp

  have hPD :
      ∀ x ∈ Ω, ∀ z : (EuclideanSpace ℝ (Fin n)), z ≠ 0 →
        0 < bilinearIteratedFDerivTwo ℝ (clientV n) x z z :=
    client_support_hessian

  have hmain :
      ∀ Γ : Set ((EuclideanSpace ℝ (Fin n))), MeasurableSet Γ →
        Γ ⊆ Ω →
        (∀ x ∈ Γ, ∀ y ∈ Ω,
          clientQ n x - (1 - (1 / 2 : ℝ)) * clientV n x +
              ⟪gradient (clientQ n) x -
                (1 - (1 / 2 : ℝ)) • gradient (clientV n) x, y - x⟫
            ≤
          clientQ n y - (1 - (1 / 2 : ℝ)) * clientV n y) →
        volume
            ((fun x => gradient (clientQ n) x -
              (1 - (1 / 2 : ℝ)) • gradient (clientV n) x) '' Γ) ≤
          ENNReal.ofReal ((0 + (1 / 2 : ℝ)) ^ n) * volume Γ := by
    intro Γ hΓ hΓΩ hcontact
    simpa only [Ω, clientWorkingOmega] using
      volume_image_residual_le_of_strict_reference_on_domain
        hn hconv hu isOpen_ball client_strict hv hPD
        hf hfpos client_u_MA client_domain_MA
        (by norm_num) (by norm_num) (by norm_num) hfupper
        hΓ hΓΩ hcontact

  constructor
  · intro Γ hΓ hΓΩ hcontact
    exact hmain Γ hΓ hΓΩ hcontact
  · simpa only [Ω, clientWorkingOmega] using
      full_strict_reference_contact_image_bound
        hn hconv hu isOpen_ball client_strict hv hPD
        hf hfpos client_u_MA client_domain_MA
        (by norm_num) (by norm_num) (by norm_num) hfupper

/-- At the actual quadratic data, all measurable subsets of the working ball
are genuine contacts; no contact inequality is supplied by this client. -/
theorem actual_quadratic_subset {n : ℕ} (hn : 0 < n)
    {Γ : Set (EuclideanSpace ℝ (Fin n))} (hΓ : MeasurableSet Γ)
    (hΓΩ : Γ ⊆ clientWorkingOmega n) :
    volume ((fun x => gradient (clientQ n) x -
      (1 - (1 / 2 : ℝ)) • gradient (clientV n) x) '' Γ) ≤
      ENNReal.ofReal ((0 + (1 / 2 : ℝ)) ^ n) * volume Γ := by
  apply (quadratic_domain_client hn).1 Γ hΓ hΓΩ
  intro x hx y hy
  have hxΩ := hΓΩ hx
  rw [clientV_eq_q hxΩ, clientV_eq_q hy, clientV_gradient hxΩ,
    clientQ_gradient]
  have hq := clientQ_support (n := n) (x := x) (y := y)
  rw [clientQ_gradient] at hq
  simp only [inner_sub_left, real_inner_smul_left]
  nlinarith [hq]

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- Actual source client at the same normalized transporting Holder witness.
The only local extra condition is the displayed density ceiling, not a derivative,
N property, contact measurability or requested image estimate. -/
theorem source_domain_reference_contact_image_bound (hn : 0 < n)
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
      ∀ Ω : Set E, IsOpen Ω → ∀ v : E → ℝ,
        StrictConvexOn ℝ Ω v → ContDiffOn ℝ 2 v Ω →
        (∀ x ∈ Ω, ∀ z : E, z ≠ 0 →
          0 < bilinearIteratedFDerivTwo ℝ v x z z) →
        (∀ G : Set E, IsOpen G → G ⊆ Ω →
          volume {p | ∃ x ∈ G, ∀ y ∈ Ω, v x + ⟪p, y-x⟫ ≤ v y} = volume G) →
        ∀ ε δ : ℝ, 0 ≤ ε → 0 < δ → δ < 1 →
        (∀ x ∈ Ω, Real.exp (-u x + W (gradient u x)) ≤ (1 + ε) ^ n) →
        let Γ := {x | x ∈ Ω ∧ ∀ y ∈ Ω,
          u x - (1 - δ) * v x +
            ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
              u y - (1 - δ) * v y}
        volume ((fun x => gradient u x - (1 - δ) • gradient v x) '' Γ) ≤
          ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  intro Ω hΩ v hvconv hv hPD hMAv ε δ hε hδ hδ1 hfupper
  exact full_strict_reference_contact_image_bound hn hs.convexOn hC1 hΩ hvconv hv hPD
    hf.continuousOn (fun x _ => Real.exp_pos _)
    (fun G hG _ => hMA G hG) hMAv hε hδ hδ1 hfupper


end LetwinDomainContactMeasureAudit
set_option pp.fullNames true in
#print axioms LetwinDomainContactMeasureAudit.quadratic_domain_client
set_option pp.fullNames true in
#print axioms LetwinDomainContactMeasureAudit.actual_quadratic_subset
set_option pp.fullNames true in
#print axioms LetwinDomainContactMeasureAudit.source_domain_reference_contact_image_bound
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.volume_image_residual_le_of_strict_reference_on_domain
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.full_strict_reference_contact_image_bound
