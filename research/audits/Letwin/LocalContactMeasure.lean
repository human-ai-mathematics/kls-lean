module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal RealInnerProductSpace Topology
open FunctionalInequalities.Analysis
namespace LetwinLocalContactMeasureAudit

/-- A true globally convex reference with a radial kink outside the working
ball. Only local C2/PD/unit MA are constructed and used. -/
theorem radial_hinge_reference {n : ℕ} (hn : 0 < n) :
    let E := EuclideanSpace ℝ (Fin n)
    let q : E → ℝ := quadraticAt 1 0 0 0
    let v : E → ℝ := fun x => q x + max 0 (‖x‖ - 2)
    let Ω : Set E := ball 0 1
    (∀ Γ : Set E,
        MeasurableSet Γ →
          Γ ⊆ Ω →
            volume ((fun x => gradient q x - (1 / 2 : ℝ) • gradient v x) '' Γ) ≤
              ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * volume Γ) ∧
      (let Γ :=
        {x |
          x ∈ Ω ∧
            ∀ y ∈ Ω,
              q x - (1 / 2 : ℝ) * v x + ⟪gradient q x - (1 / 2 : ℝ) • gradient v x, y - x⟫ ≤
                q y - (1 / 2 : ℝ) * v y}
      volume ((fun x => gradient q x - (1 / 2 : ℝ) • gradient v x) '' Γ) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * volume Γ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let q : E → ℝ := quadraticAt 1 0 0 0
  let v : E → ℝ := fun x => q x + max 0 (‖x‖ - 2)
  let Ω : Set E := ball 0 1
  have hq : ContDiff ℝ 2 q := contDiff_quadraticAt _ _ _ _
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  have hc : ConvexOn ℝ univ q := convexOn_quadraticAt Matrix.PosSemidef.one _ _ _
  have hcv : ConvexOn ℝ univ v := by
    have hh :=
      (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set E))).sup
        ((convexOn_univ_norm : ConvexOn ℝ univ (fun x : E => ‖x‖)).add_const (-2))
    convert hc.add hh using 1
  have heq (x : E) (hx : x ∈ Ω) : v x = q x := by
    have hh : ‖x‖ < 1 := by simpa only [Ω, mem_ball, dist_zero_right] using hx
    dsimp [v]
    rw [max_eq_left (by linarith : ‖x‖ - 2 ≤ 0), add_zero]
  have hvgerm (x : E) (hx : x ∈ Ω) : v =ᶠ[𝓝 x] q := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact heq y hy
  have hv : ContDiffOn ℝ 2 v Ω := hq.contDiffOn.congr heq
  have hvg (x : E) (hx : x ∈ Ω) : gradient v x = gradient q x := (hvgerm x hx).gradient_eq
  have hvd (x : E) (hx : x ∈ Ω) : DifferentiableAt ℝ v x :=
    ((hv.differentiableOn (by norm_num)) x hx).differentiableAt (isOpen_ball.mem_nhds hx)
  have hqgrad : gradient q = (fun x : E => x) := by
    funext x
    dsimp [q]
    rw [gradient_quadraticAt Matrix.isHermitian_one]
    simp [Matrix.toEuclideanLin]
  have hPD : ∀ x ∈ Ω, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z := by
    intro x hx z hz
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
      ((hvgerm x hx).iteratedFDeriv ℝ 2).eq_of_nhds, ←
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
      BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator hq]
    change 0 < ⟪(fderiv ℝ (gradient q) x) z, z⟫
    rw [hqgrad]
    simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
      sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hqs (x y : E) : q x + ⟪gradient q x, y - x⟫ ≤ q y := by
    have ht := gradient_le_increment hc x (y - x) (hq1.differentiable one_ne_zero x)
    rw [add_sub_cancel] at ht
    linarith
  have hvs (x : E) (hx : x ∈ Ω) (y : E) : v x + ⟪gradient v x, y - x⟫ ≤ v y := by
    have ht := gradient_le_increment hcv x (y - x) (hvd x hx)
    rw [add_sub_cancel] at ht
    linarith
  have hMAq (G : Set E) (hG : IsOpen G) : volume (subgradientImage q G) = volume G := by
    dsimp [q]
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 0 hG.measurableSet,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
  have hMAv : ∀ G : Set E, IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = volume G := by
    intro G hG hGO
    have himage : subgradientImage v G = subgradientImage q G := by
      ext p
      constructor
      · rintro ⟨x, hx, hp⟩
        have hpg := subgradient_eq_gradient (hvd x (hGO hx)) hp
        refine ⟨x, hx, ?_⟩
        rw [hpg, hvg x (hGO hx)]
        exact hqs x
      · rintro ⟨x, hx, hp⟩
        have hpg := subgradient_eq_gradient (hq1.differentiable one_ne_zero x) hp
        refine ⟨x, hx, ?_⟩
        rw [hpg, ← hvg x (hGO hx)]
        exact hvs x (hGO hx)
    rw [himage]
    exact hMAq G hG
  have hMA :
    ∀ G : Set E,
      IsOpen G → G ⊆ Ω → volume (subgradientImage q G) = ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
    intro G hG _
    rw [hMAq G hG]
    simp
  have hs (x : E) (hx : x ∈ Ω) (y : E) (hy : y ∈ Ω) :
    q x - (1 / 2 : ℝ) * v x + ⟪gradient q x - (1 / 2 : ℝ) • gradient v x, y - x⟫ ≤
      q y - (1 / 2 : ℝ) * v y := by
    rw [heq x hx, heq y hy, hvg x hx]
    simp only [inner_sub_left, real_inner_smul_left]
    nlinarith only [hqs x y]
  constructor
  · intro Γ hΓ hGO
    have hh :=
      volume_image_residual_le_of_posDef_reference_on_open hn hc hq1 hcv isOpen_ball hv hPD
        continuousOn_const (fun _ _ => zero_lt_one) hMA hMAv (by norm_num : (0 : ℝ) ≤ 0)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        (by intro x hx; simp : ∀ x ∈ Ω, (1 : ℝ) ≤ (1 + 0) ^ n) hΓ hGO
        (fun x hx y hy => by
          simpa only [show (1 : ℝ) - (1 / 2 : ℝ) = 1 / 2 by norm_num] using hs x (hGO hx) y hy)
    simpa only [zero_add, show (1 : ℝ) - (1 / 2 : ℝ) = 1 / 2 by norm_num] using hh
  · have hh :=
      full_reference_contact_image_bound_on_open hn hc hq1 hcv isOpen_ball hv hPD
        continuousOn_const (fun _ _ => zero_lt_one) hMA hMAv (by norm_num : (0 : ℝ) ≤ 0)
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        (by intro x hx; simp : ∀ x ∈ Ω, (1 : ℝ) ≤ (1 + 0) ^ n)
    simpa only [zero_add, show (1 : ℝ) - (1 / 2 : ℝ) = 1 / 2 by norm_num] using hh

/-- The local continuous-support Borel primitive also has a real zero-dimensional client. -/
theorem zero_dimensional_contacts :
    MeasurableSet
      {x : EuclideanSpace ℝ (Fin 0) |
        x ∈ ball 0 1 ∧ ∀ y ∈ ball 0 1, (0 : ℝ) + ⟪(0 : EuclideanSpace ℝ (Fin 0)), y - x⟫ ≤ 0} := by
  exact measurableSet_support_contactsOn isOpen_ball continuousOn_const continuousOn_const

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- Actual source client at the same normalized transporting Holder witness.
The only local extra condition is the displayed density ceiling, not a derivative,
N property, contact measurability or requested image estimate. -/
theorem source_local_reference_contact_image_bound (hn : 0 < n)
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
        ConvexOn ℝ univ v → ContDiffOn ℝ 2 v Ω →
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
  exact full_reference_contact_image_bound_on_open hn hs.convexOn hC1 hvconv hΩ hv hPD
    hf.continuousOn (fun x _ => Real.exp_pos _)
    (fun G hG _ => hMA G hG) hMAv hε hδ hδ1 hfupper

end LetwinLocalContactMeasureAudit
#print axioms LetwinLocalContactMeasureAudit.radial_hinge_reference

#print axioms LetwinLocalContactMeasureAudit.zero_dimensional_contacts

#print axioms LetwinLocalContactMeasureAudit.source_local_reference_contact_image_bound
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiffOn_gradient
#print axioms FunctionalInequalities.Analysis.measurableSet_support_contactsOn
#print axioms FunctionalInequalities.Analysis.volume_image_residual_le_of_posDef_reference_on_open
#print axioms FunctionalInequalities.Analysis.full_reference_contact_image_bound_on_open
