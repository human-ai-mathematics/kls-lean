import FunctionalInequalities.Analysis.Convex.Coercivity
import FunctionalInequalities.Analysis.Lipschitz.Exponential
import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative
import FunctionalInequalities.Analysis.Matrix.WeakDerivative
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakInverseHessian
import FunctionalInequalities.Analysis.Convex.HessianRegularity
import FunctionalInequalities.Analysis.Lipschitz.Gradient
import FunctionalInequalities.Analysis.Convex.Caffarelli
import FunctionalInequalities.Analysis.Convex.GradientLipschitz
import FunctionalInequalities.KLS.CEK.MomentMap
import FunctionalInequalities.Probability.Stein.HessianKernel

/-!
# Weak regularity of regular-class moment potentials

Letwin arXiv:2607.24164v1 Lemma 2.2, weak regular-class support for Theorems 2.5 and 1.2.
The bounded CEK moment-map producer, Caffarelli C1 regularity and the gradient Lipschitz
estimate give a C1 potential with an a.e. positive definite Hessian, the Monge–Ampere
log-det identity and the exact 16/kappa upper bound. The Hessian is identified with the
gradient derivative at Rademacher points through the independently accepted N11e bridge.
The actual-source tensor producer additionally derives the global centered-difference bound and
Lipschitz exponent, then constructs the locally L2 weak third tensor from the original data.
It does not establish global C2/smooth regularity, a gradient diffeomorphism, the
integrated trace bound or the constant-8 theorem.

Proof provenance: existing strong-API R0 round18 assembly, corrected and independently
checked by Codex after acceptance of the weak Hessian identification bridge. Historical
failed candidates remain unchanged.
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


/-- Actual source-law tensor: both original hw and hF inputs are produced;
all original R0 data and the weak/local-L2 tensor are retained. -/
theorem exists_regular_moment_weak_tensor {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      ∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, L, hconv, hLip, hnorm, hmap, hC1, hG, hdata⟩ :=
    exists_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hV : ContDiff ℝ 1 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hw := secondDifference_le_of_map_gradient hLip hconv hnorm hK hKc hV hκ hstrong
    (hmap.trans hμ) hC1
  obtain ⟨LF, hF⟩ := exists_lipschitzWith_neg_add_comp_gradient hLip hG hV
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he :
        (fun y => W y - κ / 2 * ‖y‖ ^ 2) +
          (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  obtain ⟨T, hT⟩ := exists_weak_third_derivative hC1 hconv hG hV hVc hF
    (show 0 < 16 / κ by positivity) hdata hw
  exact ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG, hF, hw, hdata, hT⟩


open Matrix Metric
open scoped Matrix.Norms.Elementwise

/-- The actual normalized convex potential supplies an exponent upper bound.
No bound on F or minimum of u is assumed. -/
private theorem exponent_upper_of_normalized_convex {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hconv : ConvexOn ℝ univ u) (hLip : LipschitzWith L u)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (hV : Continuous V) :
    ∃ C : ℝ, ∀ x, -u x + V (gradient u x) ≤ C := by
  have hint : Integrable (fun x => Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  obtain ⟨x₀, hx₀⟩ :=
    (exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      volume hconv hint).1
  obtain ⟨D, hD⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ)).exists_bound_of_continuousOn
      hV.continuousOn
  have hgrad (x : EuclideanSpace ℝ (Fin n)) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hLip)
  refine ⟨D - u x₀, ?_⟩
  intro x
  have hg : gradient u x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (L : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hgrad x
  have hv : V (gradient u x) ≤ D :=
    (le_abs_self (V (gradient u x))).trans (hD _ hg)
  linarith [hx₀ x]


/-- The same actual-source moment potential and weak tensor retain all original
regularity data and satisfy the first weak Monge–Ampère identity (Letwin v1 (2.4)).
The determinant derivative is locally L2; the logarithmic weak derivative is
identified with the explicit source-law right-hand side. No C2 Hessian regularity
or prescribed derivative tensor is assumed. This does not prove the second
evolution identity, the integrated trace bound, or the constant-8 theorem. -/
theorem exists_regular_moment_weak_first_derivative {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
  classical
  obtain ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG,
      hF, hw, hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨C, hC⟩ := exponent_upper_of_normalized_convex hconv hLip hnorm hW.continuous
  have hmaps : MapsTo (fun x => -u x + W (gradient u x)) univ (Iic C) := by
    intro x _
    exact hC x
  have he : LipschitzWith (Real.toNNReal (Real.exp C) * LF)
      (fun x => Real.exp (-u x + W (gradient u x))) :=
    lipschitzOnWith_univ.mp ((lipschitzOnWith_exp_Iic C).comp hF.lipschitzOnWith hmaps)
  refine ⟨u, L, LF, T, hconv, hLip, hnorm, hmap, hC1, hG, hF, hw, hdata, hT, ⟨_, he⟩, ?_⟩
  intro k
  have hbound (r s : Fin n) : MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u r s).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x r s)
  have hp := hasWeakDerivAlong_det_of_locally_memLp_two
    (A := fun x => hessianMatrix u x)
    (DA := fun x => Matrix.of fun i j => T x k i j)
    (fun i j => (hT k i j).1) hbound (fun i j => (hT k i j).2)
  have hchain :
      (fun x => fderiv ℝ (fun y => Real.exp (-u y + W (gradient u y))) x
        (EuclideanSpace.basisFun (Fin n) ℝ k)) =ᵐ[
          (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.exp (-u x + W (gradient u x)) *
        fderiv ℝ (fun y => -u y + W (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    filter_upwards [hF.ae_differentiableAt (μ := volume)] with x hx
    have h := congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ k))
      hx.hasFDerivAt.exp.fderiv
    simpa only [_root_.smul_apply, smul_eq_mul] using h
  have hExpWeak := (hasWeakDerivAlong_of_lipschitz he
      (EuclideanSpace.basisFun (Fin n) ℝ k)).congr_ae
        Filter.EventuallyEq.rfl hchain
  have hExpDet : (fun x => Real.exp (-u x + W (gradient u x))) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => (hessianMatrix u x).det) := by
    filter_upwards [hdata] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  have hDetExpWeak := hExpWeak.congr_ae hExpDet Filter.EventuallyEq.rfl
  have hDensity := hp.1.ae_eq hDetExpWeak
  have hW1 : ContDiff ℝ 1 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hAll :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : Fin n, T x k (σ i) i *
          ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
        (hessianMatrix u x).det *
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace ∧
      ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
        fderiv ℝ (fun y => -u y + W (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
          ∑ a : Fin n, hessianMatrix u x k a *
            fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) := by
    filter_upwards [hdata, hDensity, ae_fderiv_mongeAmpere_exponent hC1 hG hW1]
      with x hx hd hRight
    have hunit : IsUnit (hessianMatrix u x).det :=
      isUnit_iff_ne_zero.mpr (ne_of_gt hx.1.det_pos)
    have hJ :
        (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ i : Fin n, T x k (σ i) i *
            ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
        (hessianMatrix u x).det *
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace := by
      calc
        (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∑ i : Fin n, T x k (σ i) i *
              ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) =
            fderiv ℝ Matrix.det (hessianMatrix u x) (Matrix.of fun i j => T x k i j) :=
          (fderiv_det_eq_sum_permutation (hessianMatrix u x) (Matrix.of fun i j => T x k i j)).symm
        _ = (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace :=
          fderiv_det_eq_det_mul_trace _ _ hunit
    have hExpEq : (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
      rw [← hx.2.1, Real.exp_log hx.1.det_pos]
    have hTrace :
        ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
          fderiv ℝ (fun y => -u y + W (gradient u y)) x
            (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      apply mul_left_cancel₀ (ne_of_gt hx.1.det_pos)
      calc
        (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ∑ i : Fin n, T x k (σ i) i *
                ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, hessianMatrix u x (σ j) j) := hJ.symm
        _ = Real.exp (-u x + W (gradient u x)) *
              fderiv ℝ (fun y => -u y + W (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ k) := hd
        _ = (hessianMatrix u x).det *
              fderiv ℝ (fun y => -u y + W (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ k) := by rw [hExpEq]
    exact ⟨hJ, hTrace, hTrace.trans (hRight k)⟩
  have hJac := hAll.mono fun _ hx => hx.1
  have hTrace :
      (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace) =ᵐ[
        (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => fderiv ℝ (fun y => -u y + W (gradient u y)) x
        (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    hAll.mono fun _ hx => hx.2.1
  have hRight := hAll.mono fun _ hx => hx.2.2
  have hLog : (fun x => -u x + W (gradient u x)) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ (Fin n)))]
      (fun x => Real.log (hessianMatrix u x).det) :=
    hdata.mono fun _ hx => hx.2.1.symm
  have hLogWeak := (hasWeakDerivAlong_of_lipschitz hF
      (EuclideanSpace.basisFun (Fin n) ℝ k)).congr_ae hLog hTrace.symm
  exact ⟨hp.1.congr_ae Filter.EventuallyEq.rfl hJac,
    fun S hS => MemLp.ae_eq (ae_restrict_of_ae hJac) (hp.2 S hS), hLogWeak, hTrace, hRight⟩

end FunctionalInequalities.Analysis
