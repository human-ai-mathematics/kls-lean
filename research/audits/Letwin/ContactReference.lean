module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.ContactImage
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.Probability.Stein.HessianKernel
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace NNReal
namespace LetwinContactReferenceAudit
open FunctionalInequalities.Analysis

def unitReference {n : ℕ} : EuclideanSpace ℝ (Fin n) → ℝ := quadraticAt 1 0 0 0

private theorem unit_hessian_pos {n : ℕ} (x z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    0 < bilinearIteratedFDerivTwo ℝ unitReference x z z := by
  rw [← FunctionalInequalities.Probability.Stein.inner_action_hessian]
  have hne : z.ofLp ≠ 0 := by
    intro he
    apply hz
    apply PiLp.ext
    intro i
    exact congrFun he i
  have hPD : (FunctionalInequalities.Probability.Stein.hessianMatrix unitReference x).PosDef := by
    dsimp [unitReference]
    rw [hessianMatrix_quadraticAt Matrix.isHermitian_one]
    exact Matrix.PosDef.one
  simpa only [FunctionalInequalities.Probability.Stein.action, PiLp.inner_apply,
    Real.inner_apply, Matrix.mulVec, dotProduct, star_trivial, mul_comm] using
    hPD.dotProduct_mulVec_pos hne

private theorem unit_residual_support {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    unitReference x - (1 / 2 : ℝ) * unitReference x +
        ⟪gradient unitReference x - (1 / 2 : ℝ) • gradient unitReference x, y - x⟫ ≤
      unitReference y - (1 / 2 : ℝ) * unitReference y := by
  have hv : ContDiff ℝ 2 (unitReference (n := n)) := contDiff_quadraticAt _ _ _ _
  have hh :=
    gradient_le_increment (convexOn_quadraticAt Matrix.PosSemidef.one 0 0 0) x (y - x)
      (hv.differentiable (by norm_num) x)
  rw [add_sub_cancel] at hh
  change ⟪gradient unitReference x, y - x⟫ ≤ unitReference y - unitReference x at hh
  simp only [inner_sub_left, real_inner_smul_left]
  linarith

private theorem unit_MA_upper {n : ℕ} (G : Set (EuclideanSpace ℝ (Fin n))) (hG : IsOpen G) :
    volume (subgradientImage unitReference G) ≤ ENNReal.ofReal (1 : ℝ) * volume G := by
  dsimp only [unitReference]
  rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : EuclideanSpace ℝ (Fin n)) 0 0
      hG.measurableSet,
    Matrix.det_one, ENNReal.ofReal_one, one_mul]

/-- Actual quadratic reference and actual residual supports, without an
assumed reference bound or residual relative inequality. -/
theorem quadratic_residual_gradient_bound {n : ℕ} :
    ∃ C : ℝ≥0,
      0 < C ∧
        ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
          ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
            ‖(gradient unitReference x - (1 / 2 : ℝ) • gradient unitReference x) -
                  (gradient unitReference y - (1 / 2 : ℝ) • gradient unitReference y)‖ ≤
              (C : ℝ) * ‖gradient unitReference x - gradient unitReference y‖ := by
  have hv : ContDiff ℝ 2 (unitReference (n := n)) := contDiff_quadraticAt _ _ _ _
  obtain ⟨C, hC, hbound⟩ :=
    exists_residual_gradient_bound_of_posDef_reference hv (isCompact_closedBall 0 1)
      (convex_closedBall 0 1) (fun x _ => unit_hessian_pos x)
  refine ⟨C, hC, ?_⟩
  exact
    hbound unitReference (1 / 2) (by norm_num) (closedBall 0 1) Subset.rfl
      (fun x _ y _ => unit_residual_support x y)

/-- Actual unit-quadratic MA input produces gradient null images. -/
theorem quadratic_gradient_null_image {n : ℕ} {N : Set (EuclideanSpace ℝ (Fin n))}
    (hN : N ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1) (hz : volume N = 0) :
    volume (gradient (unitReference (n := n)) '' N) = 0 := by
  exact
    volume_gradient_image_eq_zero_of_alexandrov_upper
      (convexOn_quadraticAt Matrix.PosSemidef.one 0 0 0)
      ((contDiff_quadraticAt _ _ _ _).of_le (by norm_num)) isOpen_ball (C := 1) zero_le_one
      (fun G hG _ => unit_MA_upper G hG) N hN hz

/-- C2/PD reference, MA upper and all actual residual contacts are built.
Only the arbitrary null subset is supplied. Includes dimension zero. -/
theorem quadratic_reference_null_image {n : ℕ} {N : Set (EuclideanSpace ℝ (Fin n))}
    (hN : N ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1) (hz : volume N = 0) :
    volume ((fun x => gradient unitReference x - (1 / 2 : ℝ) • gradient unitReference x) '' N) =
      0 := by
  exact
    volume_image_residual_eq_zero_of_posDef_reference
      (convexOn_quadraticAt Matrix.PosSemidef.one 0 0 0)
      ((contDiff_quadraticAt _ _ _ _).of_le (by norm_num)) (contDiff_quadraticAt _ _ _ _)
      isOpen_ball (fun x _ => unit_hessian_pos x) (C := 1) zero_le_one
      (fun G hG _ => unit_MA_upper G hG) (by norm_num : (0 : ℝ) < 1 / 2)
      (Subset.rfl : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ _)
      (fun x _ y _ => unit_residual_support x y) N hN hz

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The same actual normalized transporting Holder source witness supplies its
MA upper bound. The comparison reference is given, with explicit global C2/PD. -/
theorem source_reference_null_image (hn : 0 < n)
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
      ∀ (R : ℝ), 0 < R → ∀ v : E → ℝ, ContDiff ℝ 2 v →
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
  apply volume_image_residual_eq_zero_of_posDef_reference hs.convexOn hC1 hv isOpen_ball hPD
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


end LetwinContactReferenceAudit
#print axioms LetwinContactReferenceAudit.quadratic_residual_gradient_bound
#check LetwinContactReferenceAudit.quadratic_residual_gradient_bound (n:=0)

#print axioms LetwinContactReferenceAudit.quadratic_gradient_null_image
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.exists_uniform_gradient_bounds_of_posDef_hessian
#print axioms FunctionalInequalities.Analysis.exists_residual_gradient_bound_of_posDef_reference
#print axioms FunctionalInequalities.Analysis.volume_gradient_image_eq_zero_of_alexandrov_upper

#print axioms LetwinContactReferenceAudit.quadratic_reference_null_image
#print axioms LetwinContactReferenceAudit.source_reference_null_image
#print axioms FunctionalInequalities.Analysis.volume_image_residual_eq_zero_of_posDef_reference
#check LetwinContactReferenceAudit.quadratic_reference_null_image (n:=0)
