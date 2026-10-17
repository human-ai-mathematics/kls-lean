import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
import FunctionalInequalities.Analysis.Convex.Alexandrov
import FunctionalInequalities.Analysis.Convex.Caffarelli
import FunctionalInequalities.Analysis.Convex.GradientLipschitz
import FunctionalInequalities.Analysis.Convex.Subgradient
import FunctionalInequalities.Analysis.Convex.Viscosity
import FunctionalInequalities.KLS.CEK.MomentMap
import FunctionalInequalities.KLS.Isotropic

/-!
# Actual regular-class C1 moment potentials

Existing statements, names and proof payloads are preserved.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/-- A regular-class isotropic law has a convex Lipschitz C1 moment potential with
16/kappa-Lipschitz gradient and the a.e. Hessian/log-det package. -/
theorem exists_regular_moment_potential {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
    {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal), ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial E := inferInstance
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  let L : NNReal := ⟨R, hR.le⟩
  have hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ) := by
    rw [hμ]
    refine (ae_withDensity_iff ?_).2 ?_
    · exact Measurable.indicator
        (Measurable.ennreal_ofReal
          (Real.continuous_exp.measurable.comp
            (Measurable.neg hW.continuous.measurable)))
        hK.measurableSet
    · filter_upwards [] with y hy
      by_cases hyK : y ∈ K
      · exact hRK y hyK
      · rw [Set.indicator_of_notMem hyK] at hy
        exact (hy rfl).elim
  obtain ⟨u, huconv, huLip, hunorm, humap⟩ :=
    KLS.CEK.exists_momentMap_of_isotropic_of_ae_norm_le μ hiso L hL
  have hmap :
      ((volume : Measure E).tilted (-u)).map (gradient u) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))) :=
    humap.trans hμ
  have huC1 : ContDiff ℝ 1 u :=
    contDiff_one_of_map_gradient huLip huconv hunorm hK hKc hKint
      hW.continuous hmap
  have hgradLip : LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) :=
    lipschitzWith_gradient_of_map_gradient huLip huconv hunorm hK hKc
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hκ hstrong hmap huC1
  let f : E → ℝ := fun x => Real.exp (-u x + W (gradient u x))
  have hgradc : Continuous (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (huC1.continuous_fderiv (by norm_num))
  have hf : Continuous f :=
    Real.continuous_exp.comp
      (huC1.continuous.neg.add (hW.continuous.comp hgradc))
  have hfpos : ∀ x, 0 < f x := fun x => Real.exp_pos _
  have hMA : ∀ G : Set E, IsOpen G →
      volume (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) := by
    intro G hG
    exact volume_subgradientImage_eq_lintegral_of_isOpen huLip huconv hunorm
      hK.isClosed hKc hW.continuous.measurable hmap hG
  have hdiff :
      ∀ᵐ x ∂(volume : Measure E), DifferentiableAt ℝ (gradient u) x :=
    hgradLip.ae_differentiableAt
  have hmain :
      ∀ᵐ x ∂(volume : Measure E),
        (hessianMatrix u x).PosDef ∧
          Real.log (hessianMatrix u x).det = -u x + W (gradient u x) := by
    filter_upwards [hdiff] with x hx
    let T : E →L[ℝ] E := fderiv ℝ (gradient u) x
    have hT : HasFDerivAt (gradient u) T x := hx.hasFDerivAt
    have hfd : ∀ y, HasFDerivAt u (fderiv ℝ u y) y :=
      fun y => (huC1.differentiable (by norm_num) y).hasFDerivAt
    have hsub (y q : E)
        (hq : ∀ w, u y + ⟪q, w - y⟫ ≤ u w) :
        q = gradient u y := by
      have hm : IsLocalMin (fun z => u z -
          (InnerProductSpace.toDual ℝ E q) z) y := by
        filter_upwards [] with z
        change u y - (InnerProductSpace.toDual ℝ E q) y ≤
          u z - (InnerProductSpace.toDual ℝ E q) z
        simp only [InnerProductSpace.toDual_apply_apply]
        have hz := hq z
        rw [inner_sub_right] at hz
        linarith
      have hz := hm.hasFDerivAt_eq_zero
        ((hfd y).sub (InnerProductSpace.toDual ℝ E q).hasFDerivAt)
      have hdu :
          fderiv ℝ u y =
            (InnerProductSpace.toDual ℝ E) (gradient u y) :=
        (toDual_gradient (f := u) (x := y)).symm
      rw [hdu] at hz
      exact ((InnerProductSpace.toDual ℝ E).injective
        (sub_eq_zero.mp hz)).symm
    have hexp :
        ∀ ε > 0, ∀ᶠ y in 𝓝 x, ∀ q : E,
          (∀ w, u y + ⟪q, w - y⟫ ≤ u w) →
            ‖q - gradient u x - T (y - x)‖ ≤ ε * ‖y - x‖ := by
      intro ε hε
      have hlittle := hT.isLittleO
      filter_upwards [hlittle.bound hε] with y hy q hq
      have hqeq := hsub y q hq
      simpa only [hqeq] using hy
    have hquad :
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - u x - ⟪gradient u x, y - x⟫ -
              1 / 2 * ⟪T (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 :=
      fun ε hε =>
        eventually_abs_sub_quadratic_le_of_subgradient_expansion
          huconv hexp ε hε
    have hmat := hessianMatrix_toEuclideanLin_of_differentiableAt_gradient huC1 hx
    have hquad' :
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt (hessianMatrix u x) x
              (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
      intro ε hε
      filter_upwards [hquad ε hε] with y hy
      rw [quadraticAt, hmat]
      change
        |u y - (u x + ⟪gradient u x, y - x⟫ +
          1 / 2 * ⟪y - x, T (y - x)⟫)| ≤ ε * ‖y - x‖ ^ 2
      rw [real_inner_comm (T (y - x)) (y - x)]
      simpa only [sub_add_eq_sub_sub] using hy
    have hres := posDef_and_det_eq_of_quadratic_expansion huconv
      isOpen_univ (fun G hG _ => hMA G hG) (mem_univ x)
      hf.continuousAt (hfpos x)
      (hessianMatrix_isHermitian_of_differentiableAt_gradient huC1 hx) hquad'
    refine ⟨hres.1, ?_⟩
    calc
      Real.log (hessianMatrix u x).det = Real.log (f x) := by
        rw [hres.2]
      _ = -u x + W (gradient u x) := by
        simp [f]
  refine ⟨u, L, huconv, huLip, hunorm, humap, huC1, hgradLip, ?_⟩
  filter_upwards [hmain, hdiff] with x hx hxd
  refine ⟨hx.1, hx.2, ?_⟩
  let T : E →L[ℝ] E := fderiv ℝ (gradient u) x
  have hTnorm : ‖T‖ ≤ 16 / κ := by
    have h := norm_fderiv_le_of_lipschitz ℝ hgradLip (x₀ := x)
    have hc : (0 : ℝ) ≤ 16 / κ := by positivity
    rw [Real.coe_toNNReal (16 / κ) hc] at h
    exact h
  have hmat := hessianMatrix_toEuclideanLin_of_differentiableAt_gradient huC1 hxd
  have hH : (hessianMatrix u x).IsHermitian :=
    hessianMatrix_isHermitian_of_differentiableAt_gradient huC1 hxd
  have hsym : T.toLinearMap.IsSymmetric := by
    have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
    rw [hmat] at hs
    exact hs
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hone :
      Matrix.toLin b.toBasis b.toBasis
          (1 : Matrix (Fin n) (Fin n) ℝ) =
        LinearMap.id :=
    Matrix.toLin_one _
  have hop :
      Matrix.toEuclideanLin
          ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
            hessianMatrix u x) =
        (16 / κ) • LinearMap.id - T.toLinearMap := by
    have hmat' := hmat
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at hmat'
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, map_sub, map_smul, hone, hmat']
  rw [← Matrix.isPositive_toEuclideanLin_iff, hop]
  constructor
  · intro v w
    change
      ⟪(16 / κ) • v - T v, w⟫ =
        ⟪v, (16 / κ) • w - T w⟫
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    have hsw : ⟪T v, w⟫ = ⟪v, T w⟫ := hsym v w
    rw [hsw]
  · intro v
    change 0 ≤ ⟪(16 / κ) • v - T v, v⟫
    rw [inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have hv := T.le_opNorm v
    have hv' : ‖T v‖ ≤ (16 / κ) * ‖v‖ :=
      hv.trans (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg v))
    have hi := real_inner_le_norm (T v) v
    have hq := mul_le_mul_of_nonneg_right hv' (norm_nonneg v)
    nlinarith



end FunctionalInequalities.Analysis
