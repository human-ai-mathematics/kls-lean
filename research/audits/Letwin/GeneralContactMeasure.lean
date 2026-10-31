module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
public import FunctionalInequalities.Probability.Stein.HessianKernel
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
@[expose] public section

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
namespace GeneralContactMeasureAudit
open FunctionalInequalities.Analysis

set_option maxHeartbeats 1200000 in
/-- Actual quadratic solution/reference, unit MA and residual contacts are
constructed. No image bound, derivative or null-image property is an input. -/
theorem quadratic_image_bound {n : ℕ} (hn : 0 < n) :
    let q := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : EuclideanSpace ℝ (Fin n)) 0 0
    volume
          ((fun x => gradient q x - (1 - (1 / 2 : ℝ)) • gradient q x) ''
            ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
      (let Γ :=
        {x |
          x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
            ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
              q x - (1 - (1 / 2 : ℝ)) * q x +
                  ⟪gradient q x - (1 - (1 / 2 : ℝ)) • gradient q x, y - x⟫ ≤
                q y - (1 - (1 / 2 : ℝ)) * q y}
      volume ((fun x => gradient q x - (1 - (1 / 2 : ℝ)) • gradient q x) '' Γ) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * volume Γ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let q : E → ℝ := quadraticAt 1 0 0 0
  have hq : ContDiff ℝ 2 q := contDiff_quadraticAt _ _ _ _
  have hc : ConvexOn ℝ univ q := convexOn_quadraticAt Matrix.PosSemidef.one _ _ _
  have hMAv :
    ∀ G : Set E, IsOpen G → G ⊆ ball (0 : E) 1 → volume (subgradientImage q G) = volume G := by
    intro G hG _
    dsimp [q]
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 0 hG.measurableSet,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
  have hMAu :
    ∀ G : Set E,
      IsOpen G →
        G ⊆ ball (0 : E) 1 →
          volume (subgradientImage q G) = ∫⁻ _x in G, ENNReal.ofReal (1 : ℝ) := by
    intro G hG hGO
    rw [hMAv G hG hGO]
    simp
  have hpos : ∀ x ∈ ball (0 : E) 1, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ q x z z := by
    intro x _ z hz
    rw [← FunctionalInequalities.Probability.Stein.inner_action_hessian]
    have hPD : (FunctionalInequalities.Probability.Stein.hessianMatrix q x).PosDef := by
      dsimp [q]
      rw [hessianMatrix_quadraticAt Matrix.isHermitian_one]
      exact Matrix.PosDef.one
    have hne : z.ofLp ≠ 0 := by
      intro he
      apply hz
      apply PiLp.ext
      intro i
      exact congrFun he i
    simpa only [FunctionalInequalities.Probability.Stein.action, PiLp.inner_apply,
      Real.inner_apply, Matrix.mulVec, dotProduct, star_trivial, mul_comm] using
      hPD.dotProduct_mulVec_pos hne
  have hs :
    ∀ x ∈ ball (0 : E) 1,
      ∀ y ∈ ball (0 : E) 1,
        q x - (1 - (1 / 2 : ℝ)) * q x +
            ⟪gradient q x - (1 - (1 / 2 : ℝ)) • gradient q x, y - x⟫ ≤
          q y - (1 - (1 / 2 : ℝ)) * q y := by
    intro x _ y _
    have hh := gradient_le_increment hc x (y - x) (hq.differentiable (by norm_num) x)
    rw [add_sub_cancel] at hh
    simp only [inner_sub_left, real_inner_smul_left]
    nlinarith
  have hb :=
    volume_image_residual_le_of_posDef_reference hn hc (hq.of_le (by norm_num)) hc hq
      isOpen_ball hpos continuousOn_const (fun _ _ => zero_lt_one) hMAu hMAv (ε := 0) (δ :=
      1 / 2) le_rfl (by norm_num) (by norm_num) (by intro x _; simp) (isOpen_ball.measurableSet)
      Subset.rfl hs
  refine ⟨by simpa only [zero_add] using hb, ?_⟩
  simpa only [zero_add] using
    full_reference_contact_image_bound hn hc (hq.of_le (by norm_num)) hc hq isOpen_ball hpos
      continuousOn_const (fun _ _ => zero_lt_one) hMAu hMAv (ε := 0) (δ := 1 / 2) le_rfl
      (by norm_num) (by norm_num) (by intro x _; simp)
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- Actual source client at the same normalized transporting Holder witness.
The only local extra condition is the displayed density ceiling, not a derivative,
N property, contact measurability or requested image estimate. -/
theorem source_reference_contact_image_bound (hn : 0 < n)
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
        ConvexOn ℝ univ v → ContDiff ℝ 2 v →
        (∀ x ∈ Ω, ∀ z : E, z ≠ 0 →
          0 < bilinearIteratedFDerivTwo ℝ v x z z) →
        (∀ G : Set E, IsOpen G → G ⊆ Ω →
          volume (subgradientImage v G) = volume G) →
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
  exact full_reference_contact_image_bound hn hs.convexOn hC1 hvconv hv hΩ hPD
    hf.continuousOn (fun x _ => Real.exp_pos _)
    (fun G hG _ => hMA G hG) hMAv hε hδ hδ1 hfupper

end GeneralContactMeasureAudit
#print axioms GeneralContactMeasureAudit.quadratic_image_bound

#print axioms GeneralContactMeasureAudit.source_reference_contact_image_bound
