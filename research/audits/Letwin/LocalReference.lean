module

public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Compact
public import FunctionalInequalities.Analysis.Convex.ContactMeasure
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
@[expose] public section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal RealInnerProductSpace Topology Classical
namespace LocalReferenceBoundsAudit
open FunctionalInequalities.Analysis.BakryEmery

/-- An actual reference defined by a quadratic inside an open interval and
zero outside. Only its local C2 property is proved or used. -/
theorem interval_reference_bounds :
    let v : ℝ → ℝ := fun x => if x ∈ Ioo (-2 : ℝ) 2 then x ^ 2 / 2 else 0
    ∃ κ L : ℝ,
      0 < κ ∧
        0 < L ∧
          ∀ x ∈ Icc (-1 : ℝ) 1,
            ∀ y ∈ Icc (-1 : ℝ) 1,
              κ * ‖x - y‖ ^ 2 ≤ ⟪gradient v x - gradient v y, x - y⟫ ∧
                ‖gradient v x - gradient v y‖ ≤ L * ‖x - y‖ := by
  let U : Set ℝ := Ioo (-2) 2
  let K : Set ℝ := Icc (-1) 1
  let q : ℝ → ℝ := fun x => x ^ 2 / 2
  let v : ℝ → ℝ := fun x => if x ∈ U then q x else 0
  have hq : ContDiff ℝ 2 q := by fun_prop
  have hv : ContDiffOn ℝ 2 v U := by
    apply hq.contDiffOn.congr
    intro x hx
    simp [v, hx]
  have hKU : K ⊆ U := by
    intro x hx
    exact
      ⟨lt_of_lt_of_le (by norm_num : (-2 : ℝ) < -1) hx.1,
        lt_of_le_of_lt hx.2 (by norm_num : (1 : ℝ) < 2)⟩
  have hqpos (x z : ℝ) (hz : z ≠ 0) : 0 < bilinearIteratedFDerivTwo ℝ q x z z := by
    have hqeq : q = fun y : ℝ => (0 : ℝ) + (1 : ℝ) / 2 * ‖y‖ ^ 2 := by
      funext y
      simp [q, Real.norm_eq_abs, sq_abs, div_eq_mul_inv, mul_comm]
    have he :=
      bilinearIteratedFDerivTwo_add_quadratic
        (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ))) 1 x z
    have hc : bilinearIteratedFDerivTwo ℝ (fun _ : ℝ => (0 : ℝ)) x z z = 0 := by
      rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
      simp
    rw [← hqeq, hc, zero_add, one_mul] at he
    rw [he]
    exact pow_pos (norm_pos_iff.mpr hz) 2
  have hPD : ∀ x ∈ K, ∀ z : ℝ, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z := by
    intro x hx z hz
    have heq : v =ᶠ[𝓝 x] q := by
      filter_upwards [isOpen_Ioo.mem_nhds (hKU hx)] with y hy
      simp only [v, ite_eq_left (show y ∈ U from hy)]
    rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, (heq.iteratedFDeriv ℝ 2).eq_of_nhds, ←
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    exact hqpos x z hz
  exact
    FunctionalInequalities.Analysis.BakryEmery.exists_uniform_gradient_bounds_of_posDef_hessianOn
      isOpen_Ioo hv hKU (isCompact_Icc) (convex_Icc (-1 : ℝ) 1) hPD
end LocalReferenceBoundsAudit
#print axioms LocalReferenceBoundsAudit.interval_reference_bounds

namespace LocalReferenceContactsAudit
open FunctionalInequalities.Analysis
/-- Actual globally convex unit-MA solution q, with a reference equal to q inside
ball0 2 and zero outside. Only reference C2 on ball0 1 is supplied or used. Actual
MA upper and residual supports are constructed; includes dimension zero. -/
theorem actual_quadratic_local_null {n : ℕ} :
    let E := EuclideanSpace ℝ (Fin n)
    let q : E → ℝ := quadraticAt 1 0 0 0
    let v : E → ℝ := fun x => if x ∈ ball (0 : E) 2 then q x else 0
    ∀ N : Set E,
      N ⊆ ball 0 1 →
        volume N = 0 → volume ((fun x => gradient q x - (1 / 2 : ℝ) • gradient v x) '' N) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let q : E → ℝ := quadraticAt 1 0 0 0
  let v : E → ℝ := fun x => if x ∈ ball (0 : E) 2 then q x else 0
  let Ω : Set E := ball 0 1
  have hq : ContDiff ℝ 2 q := contDiff_quadraticAt _ _ _ _
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  have hc : ConvexOn ℝ univ q := convexOn_quadraticAt Matrix.PosSemidef.one _ _ _
  have hveq : ∀ x ∈ Ω, v x = q x := by
    intro x hx
    exact ite_eq_left (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hx)
  have hvgerm (x : E) (hx : x ∈ Ω) : v =ᶠ[𝓝 x] q := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hx)] with
      y hy
    exact ite_eq_left hy
  have hv : ContDiffOn ℝ 2 v Ω := hq.contDiffOn.congr hveq
  have hqg : gradient q = (fun x : E => x) := by
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
    rw [hqg]
    simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
      sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hMA :
    ∀ G : Set E,
      IsOpen G → G ⊆ Ω → volume (subgradientImage q G) ≤ ENNReal.ofReal (1 : ℝ) * volume G := by
    intro G hG _
    dsimp [q]
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 0 hG.measurableSet,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
  have hs :
    ∀ x ∈ Ω,
      ∀ y ∈ Ω,
        q x - (1 / 2 : ℝ) * v x + ⟪gradient q x - (1 / 2 : ℝ) • gradient v x, y - x⟫ ≤
          q y - (1 / 2 : ℝ) * v y := by
    intro x hx y hy
    rw [hveq x hx, hveq y hy, (hvgerm x hx).gradient_eq]
    have ht := gradient_le_increment hc x (y - x) (hq1.differentiable one_ne_zero x)
    rw [add_sub_cancel] at ht
    simp only [inner_sub_left, real_inner_smul_left]
    nlinarith only [ht]
  exact
    FunctionalInequalities.Analysis.volume_image_residual_eq_zero_of_posDef_referenceOn hc hq1
      isOpen_ball hv hPD (by norm_num : (0 : ℝ) ≤ 1) hMA (by norm_num : (0 : ℝ) < 1 / 2)
      Subset.rfl hs
end LocalReferenceContactsAudit
#print axioms LocalReferenceContactsAudit.actual_quadratic_local_null
#check LocalReferenceContactsAudit.actual_quadratic_local_null (n := 0)

namespace LetwinLocalReferenceSourceAudit
open FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
/-- The same actual normalized transporting Holder literal-source u derives its
finite local MA bound. The given positive-Hessian reference is only C2 on the
working ball; no global reference extension or unknown-u Hessian input. -/
theorem source_local_reference_null_image (hn : 0 < n)
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
      ∀ (R : ℝ), 0 < R → ∀ v : E → ℝ, ContDiffOn ℝ 2 v (ball (0 : E) R) →
        (∀ x ∈ ball (0:E) R, ∀ z : E, z ≠ 0 →
          0 < bilinearIteratedFDerivTwo ℝ v x z z) →
        ∀ t : ℝ, 0 < t → ∀ (Γ : Set E), Γ ⊆ ball (0 : E) R →
        (∀ x ∈ Γ, ∀ y ∈ ball (0 : E) R,
          u x-t * v x+⟪gradient u x-t • gradient v x, y-x⟫ ≤
          u y-t * v y) →
        ∀ N : Set E, N ⊆ Γ → volume N = 0 →
          volume ((fun x => gradient u x-t • gradient v x) '' N) = 0 := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  intro R _hR v hv hPD t ht Γ hΓ hc
  let f : E → ℝ := fun x => Real.exp (-u x + W (gradient u x))
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    hf.continuousOn
  let C : ℝ := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  apply volume_image_residual_eq_zero_of_posDef_referenceOn hs.convexOn hC1 isOpen_ball hv hPD
    hC ?_ ht hΓ hc
  intro G hG hGb
  rw [hMA G hG]
  calc
    ∫⁻ y in G, ENNReal.ofReal (f y) ≤ ∫⁻ _y in G, ENNReal.ofReal C := by
      apply setLIntegral_mono' hG.measurableSet
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self (f y)).trans
        ((hM y (ball_subset_closedBall (hGb hy))).trans (le_max_left _ _))
    _ = ENNReal.ofReal C * volume G := setLIntegral_const G _


end LetwinLocalReferenceSourceAudit
#print axioms LetwinLocalReferenceSourceAudit.source_local_reference_null_image
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator_at
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.exists_uniform_gradient_bounds_of_posDef_hessianOn
#print axioms FunctionalInequalities.Analysis.exists_residual_gradient_bound_of_posDef_referenceOn
#print axioms FunctionalInequalities.Analysis.volume_image_residual_eq_zero_of_posDef_referenceOn
#check
  FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator_at
    (E := EuclideanSpace ℝ (Fin 0))
