module

public import FunctionalInequalities.KLS.Letwin.Approximation
public import FunctionalInequalities.KLS.Letwin.HessianTrace
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GivenGradient
public import FunctionalInequalities.KLS.Klartag.HessianBound
public import FunctionalInequalities.KLS.Klartag.MomentLimit
public import FunctionalInequalities.Analysis.LocalExtension
public import FunctionalInequalities.Probability.MomentMeasure.Uniqueness.BoundedSupport

/-!
# Smooth moment potentials for bounded open convex supports

Letwin, arXiv:2607.24164v1, Lemma 2.2, Theorem 2.5 and the moment-map calculus of Lemmas 2.3,
2.4 and A.4–A.6, for the paper's own source class: `K ⊆ ℝⁿ`
bounded, open, convex and nonempty, `V` smooth on an open `U ⊇ closure K` and convex on `K`, and an
isotropic probability measure `μ = 1_K e^{-V} dx`, in every dimension `n > 0`.

* `exists_smooth_moment_potential_of_bounded_open_convex` (Lemma 2.2): a convex `C∞` potential
  `φ` with `∫ e^{-φ} = 1` and `(∇φ)_* e^{-φ} dx = μ`, positive definite Hessian,
  `log det ∇²φ = -φ + V(∇φ)` everywhere, `∇φ : ℝⁿ ≃ₜ K` with a smooth inverse on `K`, and a uniform
  bound `∇²φ ≤ C Id`.
* `exists_smooth_moment_potential_trace_le_of_bounded_open_convex` (Theorem 2.5): the same
  potential satisfies `E_ν tr(B ∇²φ B ∇²φ) ≤ 2 tr(B²)` for every real symmetric `B`, with
  `ν = e^{-φ} dx`, by `integral_trace_hessian_quadratic_le`; the paper imports the moment-map
  properties from Klartag [41], here they are proved.
* `exists_smooth_moment_calculus_of_bounded_open_convex` (Lemmas 2.3, 2.4, A.4, A.5, A.6): one
  produced potential, with Lipschitz `φ` and `∇φ`, satisfies `E_ν ∇²φ = Id`, the pointwise
  twice-differentiated Monge–Ampère identity with its two positive semidefinite terms, the cutoff
  and conservativity statements for `L = tr((∇²φ)⁻¹ ∇²·) − ⟪∇V(∇φ), ∇·⟫`, and the scalar
  Brascamp–Lieb inequality for `ν`, through the given-potential results
  `KLS.integral_hessian_eq_inner_of_isotropic_map`, `stdHessianMatrixGenerator_eq_on_range`,
  `exists_cutoffs_hessianInverseOperator`,
  `integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs` and
  `KLS.LogConcave.scalar_brascamp_lieb_extended_energy`.

Every moment potential of `μ` has these properties, not only the produced one:
`smooth_of_moment_potential_of_bounded_open_convex` (Lemma 2.2),
`integral_trace_le_of_moment_potential_of_bounded_open_convex` (Theorem 2.5) and
`smooth_moment_calculus_of_moment_potential_of_bounded_open_convex` (Lemmas 2.3, 2.4, A.4–A.6)
take any convex `φ : ℝⁿ → ℝ` with `∫ e^{-φ} = 1` and `(∇φ)_* e^{-φ} dx = μ`; the
`_of_ofPotential_` versions take the moment map of Lemma 2.1 itself, any convex essentially
continuous `ψ : ℝⁿ → ℝ ∪ {+∞}` with `ofPotential volume ψ = μ`, and show it is finite. Such a
potential is a translate of the produced one (`exists_eq_translate_of_map_gradient_eq`,
`exists_eq_coe_of_ofPotential_eq`: CEK Theorem 2 uniqueness for bounded-support laws), and every
stated property is translation invariant.

Proof. `μ` is log-concave with compact support, hence the weak limit of isotropic strong
regular-class laws `1_{K_j} e^{-W_j} dx` with `K_j` in one ball `B(0, R)`
(`KLS.LogConcave.exists_regularClass_seq_tendsto_of_compact`). Each approximant has a smooth CEK
moment potential `u`. It is `R`-Lipschitz because `∇u` takes values in `K_j ⊆ B(0, R)`, and the
κ-free maximum-principle Hessian bound `Δu + |∇u|² ≤ 3R²` (`trace_hessian_add_sq_le`) gives second
differences `≤ 3R² ‖h‖²`; after centering (`exists_centered_regular_potential`) Klartag's
nondegeneracy (13) with `ε = 1/R` and Klartag Lemma 2.3 (`exists_two_sided_linear_bounds`) give
uniform two-sided linear bounds. The compactness step of Klartag Proposition 2.1
(`exists_limit_potential`) produces a centered limit potential with moment measure `μ` and
`12R²`-Lipschitz gradient. Finally `V` is replaced by a globally smooth `W` that agrees with it on
`closure K` (`Analysis.exists_contDiff_eqOn_closure`), and the given-gradient smoothness chain
(`Analysis.smooth_moment_potential_of_lipschitzWith_gradient`) makes the limit potential smooth with
all the stated properties.

Not claimed: Klartag's Theorem 1.1 constant `2R²` (the statement gives some uniform `C` with
`∇²φ ≤ C Id`; the proof's witness is `C = 12R²`, the Lipschitz constant of `∇φ`, and any uniform
bound suffices for Theorem 2.5); Klartag Lemma 2.3 is used only for `C¹` potentials; uniqueness
for laws with unbounded support.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Probability.MomentMeasure

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A Hessian form bounded by `c ‖v‖²` gives the coordinate matrix bound `∇²u(x) ≤ c Id`. -/
private theorem smul_one_sub_hessianMatrix_posSemidef
    {u : E → ℝ} {x : E}
    (hH : (hessianMatrix u x).IsHermitian) {c : ℝ}
    (hb : ∀ v, bilinearIteratedFDerivTwo ℝ u x v v ≤ c * ‖v‖ ^ 2) :
    (c • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
  have h1 : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (h1.sub hH) fun w => ?_
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let v : E := ∑ i, w i • b i
  have hq : dotProduct (star w) ((hessianMatrix u x).mulVec w) =
      bilinearIteratedFDerivTwo ℝ u x v v := by
    rw [bilinear_sum_smul_sum_smul]
    simp only [b, hessianMatrix, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum,
      mul_assoc, mul_comm]
  have hv : ‖v‖ ^ 2 = ∑ i, w i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [v, b, Pi.single_apply]
  have hc : dotProduct (star w) ((c • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec w) = c * ‖v‖ ^ 2 := by
    rw [hv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    simp [dotProduct, pow_two]
  rw [Matrix.sub_mulVec, dotProduct_sub, hq, hc]
  linarith [hb v]

/-- Conversely, `∇²u(x) ≤ c Id` as matrices bounds the Hessian form by `c ‖v‖²`. -/
private theorem bilinearIteratedFDerivTwo_le_of_smul_one_sub_posSemidef
    {u : E → ℝ} {x : E} {c : ℝ}
    (h : (c • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) (v : E) :
    bilinearIteratedFDerivTwo ℝ u x v v ≤ c * ‖v‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let w : Fin n → ℝ := fun i => v i
  have hvw : (∑ i, w i • b i) = v := b.sum_repr v
  have hq : dotProduct (star w) ((hessianMatrix u x).mulVec w) =
      bilinearIteratedFDerivTwo ℝ u x v v := by
    rw [← hvw, bilinear_sum_smul_sum_smul]
    simp only [b, hessianMatrix, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum,
      mul_assoc, mul_comm]
  have hv : ‖v‖ ^ 2 = ∑ i, w i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [w]
  have hc : dotProduct (star w) ((c • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec w) = c * ‖v‖ ^ 2 := by
    rw [hv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    simp [dotProduct, pow_two]
  have h0 := h.dotProduct_mulVec_nonneg w
  rw [Matrix.sub_mulVec, dotProduct_sub, hq, hc] at h0
  linarith

/-- A `G`-Lipschitz gradient bounds the Hessian form of a `C²` function by `G ‖v‖²`. -/
private theorem bilinearIteratedFDerivTwo_le_of_lipschitzWith_gradient
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (y v : E) :
    bilinearIteratedFDerivTwo ℝ u y v v ≤ G * ‖v‖ ^ 2 := by
  rw [hessian_eq_inner_fderiv_gradient hu]
  calc ⟪fderiv ℝ (gradient u) y v, v⟫
      ≤ ‖fderiv ℝ (gradient u) y v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ ‖fderiv ℝ (gradient u) y‖ * ‖v‖ * ‖v‖ :=
        mul_le_mul_of_nonneg_right ((fderiv ℝ (gradient u) y).le_opNorm v) (norm_nonneg _)
    _ ≤ G * ‖v‖ * ‖v‖ := by gcongr; exact norm_fderiv_le_of_lipschitz ℝ hG
    _ = G * ‖v‖ ^ 2 := by ring

/-- **Centered regular-class potentials with κ-free bounds**: let `n > 0`, `K` compact convex with
nonempty interior and `K ⊆ B(0, R)` (`R > 0`), `W` smooth with `W − (κ/2)‖·‖²` convex on `ℝⁿ`
(`κ > 0`), and `μ = 1_K e^{-W} dx` an isotropic probability measure. There is a convex `C¹`,
`R`-Lipschitz moment potential `u` of `μ` (`∫ e^{-u} = 1`, `(∇u)_* e^{-u} dx = μ`) that is centered
(`∫ x e^{-u} = 0`), has `‖∇u‖ ≤ R`, and satisfies `u(x + h) + u(x − h) − 2 u(x) ≤ 3R² ‖h‖²`; none
of these bounds depends on `κ`. -/
theorem exists_centered_regular_potential (hn : 0 < n)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) {W : E → ℝ} (hW : ContDiff ℝ ∞ W)
    {κ : ℝ} (hκ : 0 < κ) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) =
      (volume : Measure E).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) {R : ℝ} (hR : 0 < R) (hKR : ∀ y ∈ K, ‖y‖ ≤ R) :
    ∃ u : E → ℝ, ConvexOn ℝ univ u ∧ ContDiff ℝ 1 u ∧
      LipschitzWith (Real.toNNReal R) u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ∫ x, Real.exp (-u x) • x ∂(volume : Measure E) = 0 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) =
        (μ : Measure E) ∧
      (∀ x, ‖gradient u x‖ ≤ R) ∧
      ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ 3 * R ^ 2 * ‖h‖ ^ 2 := by
  have hstrongK : ConvexOn ℝ (interior K) (fun y => W y - (κ / 2) * ‖y‖ ^ 2) :=
    hstrong.subset (subset_univ _) hKc.interior
  obtain ⟨u, L, hc, -, hnorm, hmap, hG, hsm, -, hPD, hMA, ⟨e, he⟩, -⟩ :=
    exists_regular_moment_potential_smooth_on_range hn hK hKc hKint hW hκ hstrongK μ hμ hiso
  have hC2 : ContDiff ℝ 2 u := hsm.of_le (by decide)
  have hC1 : ContDiff ℝ 1 u := hsm.of_le (by decide)
  have hrange : range (gradient u) ⊆ interior K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  have hgrad (x : E) : ‖gradient u x‖ ≤ R := hKR _ (interior_subset (hrange ⟨x, rfl⟩))
  have hLipR : LipschitzWith (Real.toNNReal R) u := by
    refine lipschitzWith_of_nnnorm_fderiv_le (hC1.differentiable one_ne_zero) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hR.le]
    simpa only [gradient, LinearIsometryEquiv.norm_map] using hgrad x
  -- Convexity of `W` on `interior K`, from strong convexity.
  have hWc : ConvexOn ℝ (interior K) W :=
    UniformConvexOn.convexOn (strongConvexOn_iff_convex.mpr hstrongK) fun r => by positivity
  -- Coercivity from integrability of `e^{-u}`.
  have hint : Integrable (fun x => Real.exp (-u x)) (volume : Measure E) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; exact one_ne_zero)
  obtain ⟨-, hsub⟩ :=
    exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg
      (volume : Measure E) hc hint
  have hcoer : Tendsto u (cocompact E) atTop := by
    exact tendsto_atTop.2 fun c =>
      mem_cocompact.2 ⟨_, hsub c, fun x (hx : ¬u x ≤ c) => (not_le.1 hx).le⟩
  -- The a-priori Hessian bound `16/κ` from the Lipschitz gradient.
  have hdiag (y v : E) : bilinearIteratedFDerivTwo ℝ u y v v ≤ 16 / κ * ‖v‖ ^ 2 := by
    simpa only [Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ 16 / κ)] using
      bilinearIteratedFDerivTwo_le_of_lipschitzWith_gradient hC2 hG y v
  have hbound : ∃ C : ℝ, ∀ x, ∑ i, bilinearIteratedFDerivTwo ℝ u x
      (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) ≤ C := by
    refine ⟨∑ _i : Fin (Module.finrank ℝ E), 16 / κ, fun x => Finset.sum_le_sum fun i _ => ?_⟩
    have h1 : ‖stdOrthonormalBasis ℝ E i‖ = 1 := (stdOrthonormalBasis ℝ E).orthonormal.1 i
    simpa only [h1, one_pow, mul_one] using hdiag x (stdOrthonormalBasis ℝ E i)
  have hPD' (x v : E) (hv : v ≠ 0) : 0 < bilinearIteratedFDerivTwo ℝ u x v v :=
    bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef (hPD x) v hv
  -- The κ-free maximum-principle bound `Δu + |∇u|² ≤ 3R²`.
  have htrace (x : E) :
      (∑ i, bilinearIteratedFDerivTwo ℝ u x (stdOrthonormalBasis ℝ E i)
        (stdOrthonormalBasis ℝ E i)) + ‖gradient u x‖ ^ 2 ≤ 3 * R ^ 2 :=
    trace_hessian_add_sq_le hsm isOpen_interior isOpen_univ (subset_univ _) hW.contDiffOn hWc
      hrange (fun y hy => hKR y (interior_subset hy))
      (fun y => (logDetHessian_std_eq_log_det_hessianMatrix hC2 y).trans (hMA y))
      hPD' hbound hcoer x
  have hbil (x v : E) : bilinearIteratedFDerivTwo ℝ u x v v ≤ 3 * R ^ 2 * ‖v‖ ^ 2 := by
    have hpsd (w : E) : 0 ≤ bilinearIteratedFDerivTwo ℝ u x w w := by
      by_cases hw : w = 0
      · rw [hw, hessian_eq_inner_fderiv_gradient hC2]
        simp
      · exact (hPD' x w hw).le
    have ht := bilinearIteratedFDerivTwo_le_trace_mul_norm_sq hC2 x hpsd v
    have htr : (∑ i, bilinearIteratedFDerivTwo ℝ u x (stdOrthonormalBasis ℝ E i)
        (stdOrthonormalBasis ℝ E i)) ≤ 3 * R ^ 2 := by
      nlinarith [htrace x, sq_nonneg ‖gradient u x‖]
    exact ht.trans (mul_le_mul_of_nonneg_right htr (by positivity))
  have hsecond (x h : E) : u (x + h) + u (x - h) - 2 * u x ≤ 3 * R ^ 2 * ‖h‖ ^ 2 :=
    secondDifference_le_of_bilinearIteratedFDerivTwo_le hC2 hbil x h
  -- Centering by translation.
  obtain ⟨a, ha⟩ := exists_translate_centered hnorm
  obtain ⟨hnorm', hmap', hgrad'⟩ :=
    translate_moment_potential_of_normalized hnorm (μ : Measure E) hmap a
  refine ⟨fun x => u (x + a), ?_, hC1.comp (contDiff_id.add contDiff_const), ?_, hnorm', ha,
    hmap', fun x => by rw [hgrad']; exact hgrad _, fun x h => ?_⟩
  · have h := hc.translate_left a
    rw [preimage_univ] at h
    exact h
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa only [dist_add_right] using hLipR.dist_le_mul (x + a) (y + a)
  · have e1 : x + h + a = x + a + h := add_right_comm _ _ _
    have e2 : x - h + a = x + a - h := sub_add_eq_add_sub _ _ _
    simp only [e1, e2]
    exact hsecond (x + a) h

/-- Given-potential form of Letwin arXiv:2607.24164v1, Lemmas 2.3, 2.4, A.4, A.5 and A.6: a
smooth convex normalized moment potential `φ` of `μ` with positive definite Hessian,
`log det ∇²φ = -φ + V(∇φ)`, `range ∇φ ⊆ K` and `∇²φ ≤ C Id` is Lipschitz with Lipschitz gradient
and satisfies the conclusions of `exists_smooth_moment_calculus_of_bounded_open_convex`. -/
private theorem smooth_moment_calculus_of_potential
    {K U : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hU : IsOpen U)
    (hKU : closure K ⊆ U) {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
    (μ : ProbabilityMeasure E) (hiso : KLS.Isotropic μ)
    {φ : E → ℝ} {C : ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : ConvexOn ℝ univ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E))
    (hPD : ∀ x, (hessianMatrix φ x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x))
    (hrange : range (gradient φ) ⊆ K)
    (hC : ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) :
    ∃ L G : NNReal, LipschitzWith L φ ∧ LipschitzWith G (gradient φ) ∧
      (∀ u v : E,
        Integrable (fun x => bilinearIteratedFDerivTwo ℝ φ x u v)
            ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, bilinearIteratedFDerivTwo ℝ φ x u v ∂((volume : Measure E).tilted (-φ))) =
            ⟪u, v⟫) ∧
      (∀ x, stdHessianMatrixGenerator φ V x = -stdHessianMatrix φ x +
          stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
            stdHessianMatrix φ x + stdThirdGram φ x ∧
        (stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
          stdHessianMatrix φ x).PosSemidef ∧
        (stdThirdGram φ x).PosSemidef) ∧
      (∃ (χ : ℕ → E → ℝ) (D : ℝ), 0 ≤ D ∧
        (∀ N, ContDiff ℝ ∞ (χ N)) ∧ (∀ N, HasCompactSupport (χ N)) ∧
        (∀ N x, 0 ≤ χ N x ∧ χ N x ≤ 1) ∧
        (∀ x, Monotone (fun N => χ N x)) ∧
        (∀ x, Tendsto (fun N => χ N x) atTop (𝓝 1)) ∧
        (∀ N, Integrable (hessianInverseOperator φ V (χ N)) ((volume : Measure E).tilted (-φ))) ∧
        (∀ N, (∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) ≤ D / ((N : ℝ) + 1)) ∧
        Tendsto (fun N => ∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) atTop (𝓝 0)) ∧
      (∀ f : E → ℝ, ContDiff ℝ ∞ f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
        ∀ c : ℝ, 0 < c → (∀ x, 0 ≤ hessianInverseOperator φ V f x + c * f x) →
          Integrable (hessianInverseOperator φ V f) ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, hessianInverseOperator φ V f x ∂((volume : Measure E).tilted (-φ))) = 0) ∧
      ∀ f : E → ℝ, ContDiff ℝ 1 f → MemLp f 2 ((volume : Measure E).tilted (-φ)) →
        ENNReal.ofReal (ProbabilityTheory.variance f ((volume : Measure E).tilted (-φ))) ≤
          ∫⁻ x, ENNReal.ofReal ⟪gradient f x, Ring.inverse (hessianOperator φ x) (gradient f x)⟫
            ∂((volume : Measure E).tilted (-φ)) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hPD' (x v : E) (hv : v ≠ 0) : 0 < bilinearIteratedFDerivTwo ℝ φ x v v :=
    bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef (hPD x) v hv
  have hMA' (y : E) :
      logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y) := by
    rw [logDetHessian_std_eq_log_det_hessianMatrix h2]
    exact hMA y
  -- `φ` is Lipschitz since `∇φ` takes values in the bounded set `K`.
  obtain ⟨R, hR⟩ := hKb.exists_norm_le
  have hL : LipschitzWith (max R 0).toNNReal φ := by
    refine lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable (by simp)) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (hR _ (hrange ⟨x, rfl⟩)).trans (le_max_left R 0)
  -- `∇φ` is Lipschitz from `∇²φ ≤ C Id` and convexity.
  have hbil (x v : E) : bilinearIteratedFDerivTwo ℝ φ x v v ≤ max C 0 * ‖v‖ ^ 2 :=
    (bilinearIteratedFDerivTwo_le_of_smul_one_sub_posSemidef (hC x) v).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hG := lipschitzWith_gradient_of_second_difference_le hc (hφ.differentiable (by simp))
    (le_max_right C 0) (secondDifference_le_of_bilinearIteratedFDerivTwo_le h2 hbil)
  -- The law `ν = e^{-φ} dx`.
  have hprob : IsProbabilityMeasure ((volume : Measure E).tilted (-φ)) :=
    isProbabilityMeasure_tilted_neg_of_integral_eq_one _ φ hnorm
  let ν : ProbabilityMeasure E := ⟨(volume : Measure E).tilted (-φ), hprob⟩
  have hνμ : ν.map (gradient φ) = μ := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    exact hmap
  have hU' : range (gradient φ) ⊆ U := hrange.trans (subset_closure.trans hKU)
  obtain ⟨χ, D, hD, hχ, hχS, hχB, hχM, hχL, hχI, hχD, hχDL⟩ :=
    exists_cutoffs_hessianInverseOperator (volume : Measure E) hφ hc hKb hrange hU hKU hV hMA' hPD'
      hnorm
  refine ⟨_, _, hL, hG, fun u v => ⟨?_, ?_⟩,
    fun x => ⟨?_, ?_, ?_⟩, ⟨χ, D, hD, hχ, hχS, hχB, hχM, hχL, hχI, hχD, hχDL⟩, ?_, ?_⟩
  · -- Lemma 2.3: the Hessian form is bounded by the Lipschitz constant of `∇φ`.
    refine Integrable.of_bound
      (contDiff_bilinearIteratedFDerivTwo_apply hφ u v).continuous.aestronglyMeasurable
      ((Real.toNNReal (4 * max C 0) : ℝ) * ‖u‖ * ‖v‖) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, hessian_eq_inner_fderiv_gradient h2]
    calc |⟪fderiv ℝ (gradient φ) x u, v⟫|
        ≤ ‖fderiv ℝ (gradient φ) x u‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖fderiv ℝ (gradient φ) x‖ * ‖u‖ * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((fderiv ℝ (gradient φ) x).le_opNorm u) (norm_nonneg _)
      _ ≤ _ := by gcongr; exact norm_fderiv_le_of_lipschitz ℝ hG
  · exact KLS.integral_hessian_eq_inner_of_isotropic_map φ hφ hc hnorm ν rfl (hνμ ▸ hiso) u v
  · exact stdHessianMatrixGenerator_eq_on_range hφ hU hKU hV hrange hMA' hPD' x
  · rw [← stdHessianConjugate_eq]
    exact stdHessianConjugate_posSemidef hφ hKo hKU hV hVc hrange x
  · exact stdThirdGram_posSemidef hφ x (hPD' x)
  · intro f hf D' hfD c hc' hLower
    exact integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs (volume : Measure E)
      hφ hf hU hV hU' hMA' hPD' hnorm D' hfD c hc' hLower χ hχ hχS hχB hχL hχI hχDL
  · intro f hf hf2
    exact KLS.LogConcave.scalar_brascamp_lieb_extended_energy (ν := ν) (volume : Measure E)
      (KLS.LogConcave.logConcave_of_eq_tilted (ν := ν) rfl hφ.continuous hc) rfl hφ hPD' hf hf2

section Translation

/-- The gradient of a translate is the translated gradient. -/
private theorem gradient_comp_add_right (F : E → ℝ) (a x : E) :
    gradient (fun y => F (y + a)) x = gradient F (x + a) := by
  simp only [gradient, fderiv_comp_add_right]

/-- The Hessian matrix of a translate is the translated Hessian matrix. -/
private theorem hessianMatrix_comp_add_right (F : E → ℝ) (a x : E) :
    hessianMatrix (fun y => F (y + a)) x = hessianMatrix F (x + a) := by
  have h : fderiv ℝ (fun y => F (y + a)) = fun y => fderiv ℝ F (y + a) :=
    funext fun y => fderiv_comp_add_right a
  ext i j
  simp only [hessianMatrix, bilinearIteratedFDerivTwo, h, fderiv_comp_add_right]

/-- Translation transfer of the Lemma 2.2 regularity bundle: if `F` is smooth with positive definite
Hessian, `log det ∇²F = -F + V(∇F)`, `∇F : ℝⁿ ≃ₜ K` with a smooth inverse on `K` and
`∇²F ≤ C Id`, then so is `φ = F(· + a)`. -/
private theorem smooth_moment_potential_translate {K : Set E} {V F φ : E → ℝ} {C : ℝ} (a : E)
    (hφF : ∀ x, φ x = F (x + a)) (hF : ContDiff ℝ ∞ F) (hPD : ∀ x, (hessianMatrix F x).PosDef)
    (hMA : ∀ x, Real.log (hessianMatrix F x).det = -F x + V (gradient F x))
    (he : ∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient F x)
    (hΨ : ∃ Ψ : E → E,
      Function.LeftInverse Ψ (gradient F) ∧ (∀ y ∈ K, gradient F (Ψ y) = y) ∧
        ContDiffOn ℝ ∞ Ψ K)
    (hC : ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix F x).PosSemidef) :
    ContDiff ℝ ∞ φ ∧ (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      ∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef := by
  obtain rfl : φ = fun x => F (x + a) := funext hφF
  obtain ⟨e, he⟩ := he
  obtain ⟨Ψ, hl, hr, hs⟩ := hΨ
  refine ⟨hF.comp (contDiff_id.add contDiff_const), fun x => ?_, fun x => ?_,
    ⟨(Homeomorph.addRight a).trans e, fun x => ?_⟩,
    ⟨fun y => Ψ y - a, fun x => ?_, fun y hy => ?_, hs.sub contDiffOn_const⟩, C, fun x => ?_⟩
  · rw [hessianMatrix_comp_add_right]
    exact hPD _
  · rw [hessianMatrix_comp_add_right, gradient_comp_add_right]
    exact hMA _
  · rw [gradient_comp_add_right]
    exact he _
  · simp only [gradient_comp_add_right, hl (x + a), add_sub_cancel_right]
  · rw [gradient_comp_add_right, sub_add_cancel]
    exact hr y hy
  · rw [hessianMatrix_comp_add_right]
    exact hC _

end Translation

/-- For `μ = 1_K e^{-V} dx` with `K` bounded and open, `μ`-a.e. `‖y‖ ≤ R` for some `R`. -/
private theorem exists_ae_norm_le_of_bounded {K : Set E} (hKb : Bornology.IsBounded K)
    (hKo : IsOpen K) {V : E → ℝ} (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) =
      (volume : Measure E).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    ∃ R : ℝ, ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ R := by
  obtain ⟨R, hR⟩ := hKb.exists_norm_le
  have hzero : (μ : Measure E) Kᶜ = 0 := by
    rw [hμ, withDensity_apply _ hKo.measurableSet.compl]
    calc
      _ = ∫⁻ x in Kᶜ, (0 : ENNReal) ∂(volume : Measure E) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hKo.measurableSet.compl] with x hx
        exact indicator_of_notMem hx _
      _ = 0 := by simp
  have hK : ∀ᵐ y ∂(μ : Measure E), y ∈ K := mem_ae_iff.mpr hzero
  exact ⟨R, hK.mono fun y hy => hR y hy⟩

/-- The essentially continuous moment potentials of `μ = 1_K e^{-V} dx` (`K` bounded open) are
finite, convex and normalized, with real moment measure `μ`. -/
private theorem exists_eq_coe_of_ofPotential_eq_of_bounded {K : Set E}
    (hKb : Bornology.IsBounded K) (hKo : IsOpen K) {V : E → ℝ} (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) =
      (volume : Measure E).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) (hψμ : ofPotential volume ψ = (μ : Measure E)) :
    ∃ φ : E → ℝ, (∀ x, ψ x = φ x) ∧ ConvexOn ℝ univ φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) := by
  obtain ⟨R, hR⟩ := exists_ae_norm_le_of_bounded hKb hKo μ hμ
  obtain ⟨φ, hcoe, hc, -, hnorm, hmap⟩ := exists_eq_coe_of_ofPotential_eq hψ hess hψμ hR
  exact ⟨φ, hcoe, hc, hnorm, hmap⟩

section BoundedOpenConvexSource

/-! The literal source class of Letwin Lemma 2.2: `K` bounded open convex nonempty, `V` smooth on
an open `U ⊇ closure K` and convex on `K`, and an isotropic `μ = 1_K e^{-V} dx`, `n > 0`. -/

-- `E` is a local notation over the section variable `n`; section variables spell the space out.
variable (hn : 0 < n) {K U : Set (EuclideanSpace ℝ (Fin n))}
  (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
  (hU : IsOpen U) (hKU : closure K ⊆ U) {V : EuclideanSpace ℝ (Fin n) → ℝ}
  (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
  (hiso : KLS.Isotropic μ)

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemma 2.2.** For `K` bounded open convex and nonempty, `V`
smooth on an open neighbourhood of `closure K` and convex on `K`, and an isotropic
`μ = e^{-V} 1_K dx`, there is a smooth convex moment potential with positive definite Hessian,
`log det ∇²φ = -φ + V(∇φ)`, `∇φ : ℝⁿ ≃ K` with a smooth inverse on `K`, and a uniform Hessian
bound. -/
theorem exists_smooth_moment_potential_of_bounded_open_convex :
    ∃ (φ : E → ℝ) (C : ℝ), ConvexOn ℝ univ φ ∧ ContDiff ℝ ∞ φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) =
        (μ : Measure E) ∧
      (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef := by
  have hLC : KLS.LogConcave μ :=
    KLS.LogConcave.logConcave_of_eq_restricted_exp_on_closure μ hKc
      (hV.continuousOn.mono hKU) hVc hμ
  have hzero :
      (μ : Measure E) (closure K)ᶜ = 0 := by
    rw [hμ, withDensity_apply _ isClosed_closure.measurableSet.compl]
    calc
      _ = ∫⁻ x in (closure K)ᶜ, (0 : ENNReal)
          ∂(volume : Measure E) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem isClosed_closure.measurableSet.compl] with x hx
        exact indicator_of_notMem (fun hxK => hx (subset_closure hxK)) _
      _ = 0 := by simp
  have hcompact :
      IsCompact (μ : Measure E).support :=
    hKb.isCompact_closure.of_isClosed_subset Measure.isClosed_support
      (Measure.support_subset_of_isClosed isClosed_closure (mem_ae_iff.2 hzero))
  obtain ⟨ζ, Kj, Wj, κ, hj, -, hζ, R₀, hR₀⟩ :=
    KLS.LogConcave.exists_regularClass_seq_tendsto_of_compact
      μ hLC hiso hcompact
  let R : ℝ := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKR : ∀ j, ∀ y ∈ Kj j, ‖y‖ ≤ R := by
    intro j y hy
    exact (hR₀ j y hy).trans (le_max_left _ _)
  have hu :
      ∀ j, ∃ u : E → ℝ,
        ConvexOn ℝ univ u ∧ ContDiff ℝ 1 u ∧
        LipschitzWith (Real.toNNReal R) u ∧
        (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
        (∫ x, Real.exp (-u x) • x ∂(volume : Measure E)) = 0 ∧
        ((volume : Measure E).tilted (-u)).map (gradient u) =
          (ζ j : Measure E) ∧
        (∀ x, ‖gradient u x‖ ≤ R) ∧
        ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ 3 * R ^ 2 * ‖h‖ ^ 2 := by
    intro j
    obtain ⟨hi, hk, hc, hconv, hint, hw, hs, hm⟩ := hj j
    exact exists_centered_regular_potential hn hc hconv hint hw hk hs
      (ζ j) hm hi hR (hKR j)
  choose u huc huC1 huLip hunorm hubar humap hugrad husd using hu
  obtain ⟨α, β, γ, hα, -, -, hlinear⟩ :=
    exists_two_sided_linear_bounds
      (volume : Measure E) hR (one_div_pos.mpr hR)
  have hb : ∀ j x, α * ‖x‖ - β ≤ u j x ∧
      u j x ≤ ((Real.toNNReal R : NNReal) : ℝ) * ‖x‖ + γ := by
    intro j x
    have heps :
        ∀ θ : E, ‖θ‖ = 1 →
          1 / R ≤ ∫ x, |⟪gradient (u j) x, θ⟫| * Real.exp (-u j x)
            ∂(volume : Measure E) := by
      intro θ hθ
      exact inv_le_integral_abs_inner_gradient_of_isotropic
        (huC1 j) (hunorm j) (ζ j) (hj j).1 (humap j) hR (hugrad j) hθ
    simpa only [Real.coe_toNNReal _ hR.le] using
      hlinear (u j) (huc j) (huC1 j) (huLip j) (hunorm j) (hubar j) heps x
  obtain ⟨F, hFc, hFLip, -, hFnorm, -, hFmap, hFG, -⟩ :=
    exists_limit_potential
      (volume : Measure E) hζ
      hα (show 0 ≤ 3 * R ^ 2 by positivity)
      huc huC1 huLip hunorm hubar humap hb husd
  obtain ⟨W, hW, hWV⟩ := Analysis.exists_contDiff_eqOn_closure hKb hU hKU hV
  have hintK : (interior K).Nonempty := by
    simpa only [hKo.interior_eq] using hKne
  have hi : interior (closure K) = K := by
    simpa only [hKo.interior_eq] using
      hKc.interior_closure_eq_interior_of_nonempty_interior hintK
  have hae :
      ∀ᵐ x ∂(volume : Measure E), x ∉ frontier K :=
    measure_eq_zero_iff_ae_notMem.mp (hKc.addHaar_frontier volume)
  have hμW :
      (μ : Measure E) =
        (volume : Measure E).withDensity
          ((closure K).indicator fun p => ENNReal.ofReal (Real.exp (-W p))) := by
    rw [hμ]
    apply withDensity_congr_ae
    filter_upwards [hae] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, indicator_of_mem (subset_closure hxK),
        hWV (subset_closure hxK)]
    · have hxcl : x ∉ closure K := by
        intro hxcl
        apply hx
        exact ⟨hxcl, by simpa only [hKo.interior_eq] using hxK⟩
      rw [indicator_of_notMem hxK, indicator_of_notMem hxcl]
  have hWc : ConvexOn ℝ (interior (closure K)) W := by
    rw [hi]
    exact hVc.congr (fun x hx => (hWV (subset_closure hx)).symm)
  have hintcl : (interior (closure K)).Nonempty := by
    rw [hi]
    exact hKne
  obtain ⟨hFsmooth, -, hFPD, hFMA, ⟨e, he⟩, Ψ, hΨl, hΨr, hΨs⟩ :=
    Analysis.smooth_moment_potential_of_lipschitzWith_gradient hn
      hKb.isCompact_closure hKc.closure hintcl hW hWc μ hμW
      hFc hFLip hFnorm hFmap hFG
  have hgradK (x : E) : gradient F x ∈ K := by
    have hm : (e x : E) ∈ K := by
      simpa only [hi] using (e x).property
    simpa only [he x] using hm
  let G : NNReal := Real.toNNReal (4 * (3 * R ^ 2))
  refine ⟨F, (G : ℝ), hFc, hFsmooth, hFnorm, hFmap, hFPD, ?_, ?_, ?_, fun x =>
    smul_one_sub_hessianMatrix_posSemidef (hFPD x).isHermitian
      (bilinearIteratedFDerivTwo_le_of_lipschitzWith_gradient (hFsmooth.of_le (by decide)) hFG x)⟩
  · intro x
    rw [hFMA x, hWV (subset_closure (hgradK x))]
  · exact ⟨e.trans (Homeomorph.setCongr hi), he⟩
  · exact ⟨Ψ, hΨl, fun y hy => hΨr y (hi.symm ▸ hy), hi ▸ hΨs⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Theorem 2.5.** Under the hypotheses of Lemma 2.2
(`exists_smooth_moment_potential_of_bounded_open_convex`), the moment potential produced there
also satisfies `E_ν tr(B ∇²φ B ∇²φ) ≤ 2 tr(B²)` for every real symmetric `B`, with
`ν = e^{-φ} dx`, and the integrand is `ν`-integrable. -/
theorem exists_smooth_moment_potential_trace_le_of_bounded_open_convex :
    ∃ (φ : E → ℝ) (C : ℝ),
      ConvexOn ℝ univ φ ∧
        ContDiff ℝ ∞ φ ∧
          (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
            ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
              (∀ x, (hessianMatrix φ x).PosDef) ∧
                (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
                  (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
                    (∃ Ψ : E → E,
                        Function.LeftInverse Ψ (gradient φ) ∧
                          (∀ y ∈ K, gradient φ (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ K) ∧
                      (∀ x,
                          (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) ∧
                        ∀ B : Matrix (Fin n) (Fin n) ℝ,
                          B.IsSymm →
                            Integrable
                                (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
                                ((volume : Measure E).tilted (-φ)) ∧
                              (∫ x,
                                  (B * hessianMatrix φ x * B *
                                      hessianMatrix φ
                                        x).trace ∂((volume : Measure E).tilted (-φ))) ≤
                                2 * (B * B).trace := by
  obtain ⟨φ, C, hc, hφ, hnorm, hmap, hPD, hMA, ⟨e, he⟩, hΨ, hC⟩ :=
    exists_smooth_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc μ hμ
      hiso
  have hrange : range (gradient φ) ⊆ K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  exact
    ⟨φ, C, hc, hφ, hnorm, hmap, hPD, hMA, ⟨e, he⟩, hΨ, hC, fun B hB =>
      integral_trace_hessian_quadratic_le hKb hKo hU hKU hV hVc μ hiso hφ hnorm hmap hrange hPD
        hMA ⟨C, hC⟩ B hB⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemmas 2.3, 2.4, A.4, A.5 and A.6 at the produced potential.**
Under the hypotheses of Lemma 2.2 (`exists_smooth_moment_potential_of_bounded_open_convex`: `K`
bounded open convex nonempty, `V` smooth on an open `U ⊇ closure K` and convex on `K`, isotropic
`μ = 1_K e^{-V} dx`, `n > 0`), one smooth convex moment potential `φ` has all the Lemma 2.2
conclusions, is Lipschitz with Lipschitz gradient, and, with `ν = e^{-φ} dx` and the generator
`L f = tr((∇²φ)⁻¹ ∇²f) − ⟪∇V(∇φ), ∇f⟫` (`hessianInverseOperator φ V`), satisfies:
* Lemma 2.3: `∫ ∇²φ(x)[u, v] dν = ⟪u, v⟫` for all `u, v`, with integrable integrand;
* Lemma 2.4: pointwise `L(∇²φ) + ∇²φ = ∇²φ ∇²V(∇φ) ∇²φ + Γ₃` in the standard orthonormal basis,
  `Γ₃` the inverse-Hessian-weighted third-derivative Gram matrix, and both matrices on the right
  are positive semidefinite;
* Lemma A.4: smooth compactly supported cutoffs `0 ≤ χ_N ≤ 1`, increasing to `1`, with
  `L χ_N ∈ L¹(ν)` and `‖L χ_N‖_{L¹(ν)} ≤ D / (N + 1)`;
* Lemma A.5: `L f ∈ L¹(ν)` and `E_ν L f = 0` for every smooth bounded `f` with `L f + c f ≥ 0`,
  `c > 0`;
* Lemma A.6: `Var_ν f ≤ E_ν ⟪∇f, (∇²φ)⁻¹ ∇f⟫`, the right side possibly infinite, for every `C¹`
  `f ∈ L²(ν)`; this contains the paper's bounded smooth tests.

The same conclusions hold for every moment potential of `μ`:
`smooth_moment_calculus_of_moment_potential_of_bounded_open_convex` (finite convex normalized) and
`smooth_moment_calculus_of_ofPotential_of_bounded_open_convex` (essentially continuous). -/
theorem exists_smooth_moment_calculus_of_bounded_open_convex :
    ∃ (φ : E → ℝ) (L G : NNReal) (C : ℝ), ContDiff ℝ ∞ φ ∧ ConvexOn ℝ univ φ ∧
      LipschitzWith L φ ∧ LipschitzWith G (gradient φ) ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
      (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      (∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) ∧
      (∀ u v : E,
        Integrable (fun x => bilinearIteratedFDerivTwo ℝ φ x u v)
            ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, bilinearIteratedFDerivTwo ℝ φ x u v ∂((volume : Measure E).tilted (-φ))) =
            ⟪u, v⟫) ∧
      (∀ x, stdHessianMatrixGenerator φ V x = -stdHessianMatrix φ x +
          stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
            stdHessianMatrix φ x + stdThirdGram φ x ∧
        (stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
          stdHessianMatrix φ x).PosSemidef ∧
        (stdThirdGram φ x).PosSemidef) ∧
      (∃ (χ : ℕ → E → ℝ) (D : ℝ), 0 ≤ D ∧
        (∀ N, ContDiff ℝ ∞ (χ N)) ∧ (∀ N, HasCompactSupport (χ N)) ∧
        (∀ N x, 0 ≤ χ N x ∧ χ N x ≤ 1) ∧
        (∀ x, Monotone (fun N => χ N x)) ∧
        (∀ x, Tendsto (fun N => χ N x) atTop (𝓝 1)) ∧
        (∀ N, Integrable (hessianInverseOperator φ V (χ N)) ((volume : Measure E).tilted (-φ))) ∧
        (∀ N, (∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) ≤ D / ((N : ℝ) + 1)) ∧
        Tendsto (fun N => ∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) atTop (𝓝 0)) ∧
      (∀ f : E → ℝ, ContDiff ℝ ∞ f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
        ∀ c : ℝ, 0 < c → (∀ x, 0 ≤ hessianInverseOperator φ V f x + c * f x) →
          Integrable (hessianInverseOperator φ V f) ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, hessianInverseOperator φ V f x ∂((volume : Measure E).tilted (-φ))) = 0) ∧
      ∀ f : E → ℝ, ContDiff ℝ 1 f → MemLp f 2 ((volume : Measure E).tilted (-φ)) →
        ENNReal.ofReal (ProbabilityTheory.variance f ((volume : Measure E).tilted (-φ))) ≤
          ∫⁻ x, ENNReal.ofReal ⟪gradient f x, Ring.inverse (hessianOperator φ x) (gradient f x)⟫
            ∂((volume : Measure E).tilted (-φ)) := by
  obtain ⟨φ, C, hc, hφ, hnorm, hmap, hPD, hMA, ⟨e, he⟩, hΨ, hC⟩ :=
    exists_smooth_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc
      μ hμ hiso
  have hrange : range (gradient φ) ⊆ K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  obtain ⟨L, G, hL, hG, h23, h24, hA4, hA5, hA6⟩ :=
    smooth_moment_calculus_of_potential hKb hKo hU hKU hV hVc μ hiso hφ hc hnorm hmap hPD hMA
      hrange hC
  exact ⟨φ, L, G, C, hφ, hc, hL, hG, hnorm, hmap, hPD, hMA, ⟨e, he⟩, hΨ, hC, h23, h24, hA4, hA5,
    hA6⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemma 2.2, for every finite moment potential.** Under the
hypotheses of Lemma 2.2 (`K` bounded open convex nonempty, `V` smooth on an open `U ⊇ closure K`
and convex on `K`, isotropic `μ = 1_K e^{-V} dx`, `n > 0`), every convex `φ : ℝⁿ → ℝ` with
`∫ e^{-φ} = 1` and `(∇φ)_* e^{-φ} dx = μ` is smooth with positive definite Hessian,
`log det ∇²φ = -φ + V(∇φ)`, `∇φ : ℝⁿ ≃ₜ K` with a smooth inverse on `K`, and `∇²φ ≤ C Id` for
some `C`. Proof: `φ` is a translate of the potential of
`exists_smooth_moment_potential_of_bounded_open_convex` (`exists_eq_translate_of_map_gradient_eq`,
CEK Theorem 2 uniqueness), and every property is translation invariant. -/
theorem smooth_of_moment_potential_of_bounded_open_convex
    {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E)) :
    ContDiff ℝ ∞ φ ∧ (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      ∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef := by
  obtain ⟨F, C, hFc, hF, hFnorm, hFmap, hPD, hMA, he, hΨ, hC⟩ :=
    exists_smooth_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc
      μ hμ hiso
  obtain ⟨R, hR⟩ := exists_ae_norm_le_of_bounded hKb hKo μ hμ
  obtain ⟨y₀, hy₀⟩ := exists_eq_translate_of_map_gradient_eq hFc hc hFnorm hnorm hFmap hmap hR
  exact smooth_moment_potential_translate (-y₀) (fun x => by rw [hy₀, sub_eq_add_neg]) hF hPD
    hMA he hΨ hC

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Theorem 2.5, for every finite moment potential.** Under the
hypotheses of Lemma 2.2, every convex `φ` with `∫ e^{-φ} = 1` and `(∇φ)_* e^{-φ} dx = μ` has the
conclusions of `smooth_of_moment_potential_of_bounded_open_convex` and satisfies
`E_ν tr(B ∇²φ B ∇²φ) ≤ 2 tr(B²)` for every real symmetric `B`, with `ν = e^{-φ} dx` and a
`ν`-integrable integrand. -/
theorem integral_trace_le_of_moment_potential_of_bounded_open_convex
    {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E)) :
    ContDiff ℝ ∞ φ ∧ (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      (∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
            ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, (B * hessianMatrix φ x * B * hessianMatrix φ x).trace
            ∂((volume : Measure E).tilted (-φ))) ≤ 2 * (B * B).trace := by
  obtain ⟨hφ, hPD, hMA, ⟨e, he⟩, hΨ, C, hC⟩ :=
    smooth_of_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso hc
      hnorm hmap
  have hrange : range (gradient φ) ⊆ K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  exact ⟨hφ, hPD, hMA, ⟨e, he⟩, hΨ, ⟨C, hC⟩, fun B hB =>
    integral_trace_hessian_quadratic_le hKb hKo hU hKU hV hVc μ hiso hφ hnorm hmap hrange hPD hMA
      ⟨C, hC⟩ B hB⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemmas 2.3, 2.4, A.4, A.5 and A.6, for every finite moment
potential.** Under the hypotheses of Lemma 2.2, every convex `φ` with `∫ e^{-φ} = 1` and
`(∇φ)_* e^{-φ} dx = μ` has the conclusions of `smooth_of_moment_potential_of_bounded_open_convex`,
is Lipschitz with Lipschitz gradient, and satisfies the Lemma 2.3, 2.4, A.4, A.5 and A.6
conclusions of `exists_smooth_moment_calculus_of_bounded_open_convex`. -/
theorem smooth_moment_calculus_of_moment_potential_of_bounded_open_convex
    {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (hnorm : (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E)) :
    ContDiff ℝ ∞ φ ∧ (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      (∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) ∧
      ∃ L G : NNReal, LipschitzWith L φ ∧ LipschitzWith G (gradient φ) ∧
      (∀ u v : E,
        Integrable (fun x => bilinearIteratedFDerivTwo ℝ φ x u v)
            ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, bilinearIteratedFDerivTwo ℝ φ x u v ∂((volume : Measure E).tilted (-φ))) =
            ⟪u, v⟫) ∧
      (∀ x, stdHessianMatrixGenerator φ V x = -stdHessianMatrix φ x +
          stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
            stdHessianMatrix φ x + stdThirdGram φ x ∧
        (stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
          stdHessianMatrix φ x).PosSemidef ∧
        (stdThirdGram φ x).PosSemidef) ∧
      (∃ (χ : ℕ → E → ℝ) (D : ℝ), 0 ≤ D ∧
        (∀ N, ContDiff ℝ ∞ (χ N)) ∧ (∀ N, HasCompactSupport (χ N)) ∧
        (∀ N x, 0 ≤ χ N x ∧ χ N x ≤ 1) ∧
        (∀ x, Monotone (fun N => χ N x)) ∧
        (∀ x, Tendsto (fun N => χ N x) atTop (𝓝 1)) ∧
        (∀ N, Integrable (hessianInverseOperator φ V (χ N)) ((volume : Measure E).tilted (-φ))) ∧
        (∀ N, (∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) ≤ D / ((N : ℝ) + 1)) ∧
        Tendsto (fun N => ∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) atTop (𝓝 0)) ∧
      (∀ f : E → ℝ, ContDiff ℝ ∞ f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
        ∀ c : ℝ, 0 < c → (∀ x, 0 ≤ hessianInverseOperator φ V f x + c * f x) →
          Integrable (hessianInverseOperator φ V f) ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, hessianInverseOperator φ V f x ∂((volume : Measure E).tilted (-φ))) = 0) ∧
      ∀ f : E → ℝ, ContDiff ℝ 1 f → MemLp f 2 ((volume : Measure E).tilted (-φ)) →
        ENNReal.ofReal (ProbabilityTheory.variance f ((volume : Measure E).tilted (-φ))) ≤
          ∫⁻ x, ENNReal.ofReal ⟪gradient f x, Ring.inverse (hessianOperator φ x) (gradient f x)⟫
            ∂((volume : Measure E).tilted (-φ)) := by
  obtain ⟨hφ, hPD, hMA, ⟨e, he⟩, hΨ, C, hC⟩ :=
    smooth_of_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso hc
      hnorm hmap
  have hrange : range (gradient φ) ⊆ K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  exact ⟨hφ, hPD, hMA, ⟨e, he⟩, hΨ, ⟨C, hC⟩,
    smooth_moment_calculus_of_potential hKb hKo hU hKU hV hVc μ hiso hφ hc hnorm hmap hPD hMA
      hrange hC⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemma 2.2, for the moment map of Lemma 2.1.** Under the
hypotheses of Lemma 2.2, every convex, essentially continuous `ψ : ℝⁿ → ℝ ∪ {+∞}` (CEK
arXiv:1304.0630v1, Definition 2) with moment measure `ofPotential volume ψ = μ` is finite,
`ψ = φ` with `φ` convex, `∫ e^{-φ} = 1`, `(∇φ)_* e^{-φ} dx = μ`, and `φ` has the conclusions of
`smooth_of_moment_potential_of_bounded_open_convex`. -/
theorem smooth_of_ofPotential_of_bounded_open_convex
    {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) (hψμ : ofPotential volume ψ = (μ : Measure E)) :
    ∃ φ : E → ℝ, (∀ x, ψ x = φ x) ∧ ConvexOn ℝ univ φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
      ContDiff ℝ ∞ φ ∧ (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      ∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef := by
  obtain ⟨φ, hcoe, hc, hnorm, hmap⟩ :=
    exists_eq_coe_of_ofPotential_eq_of_bounded hKb hKo μ hμ hψ hess hψμ
  exact ⟨φ, hcoe, hc, hnorm, hmap,
    smooth_of_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso hc
      hnorm hmap⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Theorem 2.5, for the moment map of Lemma 2.1.** Under the
hypotheses of Lemma 2.2, every convex, essentially continuous `ψ : ℝⁿ → ℝ ∪ {+∞}` with moment
measure `μ` is a finite normalized convex potential `φ` with the conclusions of
`integral_trace_le_of_moment_potential_of_bounded_open_convex`. -/
theorem integral_trace_le_of_ofPotential_of_bounded_open_convex
    {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) (hψμ : ofPotential volume ψ = (μ : Measure E)) :
    ∃ φ : E → ℝ, (∀ x, ψ x = φ x) ∧ ConvexOn ℝ univ φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
      ContDiff ℝ ∞ φ ∧ (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      (∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix φ x * B * hessianMatrix φ x).trace)
            ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, (B * hessianMatrix φ x * B * hessianMatrix φ x).trace
            ∂((volume : Measure E).tilted (-φ))) ≤ 2 * (B * B).trace := by
  obtain ⟨φ, hcoe, hc, hnorm, hmap⟩ :=
    exists_eq_coe_of_ofPotential_eq_of_bounded hKb hKo μ hμ hψ hess hψμ
  exact ⟨φ, hcoe, hc, hnorm, hmap,
    integral_trace_le_of_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc μ
      hμ hiso hc hnorm hmap⟩

include hn hKb hKo hKc hKne hU hKU hV hVc hμ hiso in
/-- **Letwin arXiv:2607.24164v1, Lemmas 2.3, 2.4, A.4, A.5 and A.6, for the moment map of
Lemma 2.1.** Under the hypotheses of Lemma 2.2, every convex, essentially continuous
`ψ : ℝⁿ → ℝ ∪ {+∞}` with moment measure `μ` is a finite normalized convex potential `φ` with the
conclusions of `smooth_moment_calculus_of_moment_potential_of_bounded_open_convex`. -/
theorem smooth_moment_calculus_of_ofPotential_of_bounded_open_convex
    {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) (hψμ : ofPotential volume ψ = (μ : Measure E)) :
    ∃ φ : E → ℝ, (∀ x, ψ x = φ x) ∧ ConvexOn ℝ univ φ ∧
      (∫ x, Real.exp (-φ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
      ContDiff ℝ ∞ φ ∧ (∀ x, (hessianMatrix φ x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix φ x).det = -φ x + V (gradient φ x)) ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient φ x) ∧
      (∃ Ψ : E → E,
        Function.LeftInverse Ψ (gradient φ) ∧ (∀ y ∈ K, gradient φ (Ψ y) = y) ∧
          ContDiffOn ℝ ∞ Ψ K) ∧
      (∃ C : ℝ, ∀ x, (C • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix φ x).PosSemidef) ∧
      ∃ L G : NNReal, LipschitzWith L φ ∧ LipschitzWith G (gradient φ) ∧
      (∀ u v : E,
        Integrable (fun x => bilinearIteratedFDerivTwo ℝ φ x u v)
            ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, bilinearIteratedFDerivTwo ℝ φ x u v ∂((volume : Measure E).tilted (-φ))) =
            ⟪u, v⟫) ∧
      (∀ x, stdHessianMatrixGenerator φ V x = -stdHessianMatrix φ x +
          stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
            stdHessianMatrix φ x + stdThirdGram φ x ∧
        (stdHessianMatrix φ x * hessianMatrixIn V (stdOrthonormalBasis ℝ E) (gradient φ x) *
          stdHessianMatrix φ x).PosSemidef ∧
        (stdThirdGram φ x).PosSemidef) ∧
      (∃ (χ : ℕ → E → ℝ) (D : ℝ), 0 ≤ D ∧
        (∀ N, ContDiff ℝ ∞ (χ N)) ∧ (∀ N, HasCompactSupport (χ N)) ∧
        (∀ N x, 0 ≤ χ N x ∧ χ N x ≤ 1) ∧
        (∀ x, Monotone (fun N => χ N x)) ∧
        (∀ x, Tendsto (fun N => χ N x) atTop (𝓝 1)) ∧
        (∀ N, Integrable (hessianInverseOperator φ V (χ N)) ((volume : Measure E).tilted (-φ))) ∧
        (∀ N, (∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) ≤ D / ((N : ℝ) + 1)) ∧
        Tendsto (fun N => ∫ x, |hessianInverseOperator φ V (χ N) x|
          ∂((volume : Measure E).tilted (-φ))) atTop (𝓝 0)) ∧
      (∀ f : E → ℝ, ContDiff ℝ ∞ f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
        ∀ c : ℝ, 0 < c → (∀ x, 0 ≤ hessianInverseOperator φ V f x + c * f x) →
          Integrable (hessianInverseOperator φ V f) ((volume : Measure E).tilted (-φ)) ∧
          (∫ x, hessianInverseOperator φ V f x ∂((volume : Measure E).tilted (-φ))) = 0) ∧
      ∀ f : E → ℝ, ContDiff ℝ 1 f → MemLp f 2 ((volume : Measure E).tilted (-φ)) →
        ENNReal.ofReal (ProbabilityTheory.variance f ((volume : Measure E).tilted (-φ))) ≤
          ∫⁻ x, ENNReal.ofReal ⟪gradient f x, Ring.inverse (hessianOperator φ x) (gradient f x)⟫
            ∂((volume : Measure E).tilted (-φ)) := by
  obtain ⟨φ, hcoe, hc, hnorm, hmap⟩ :=
    exists_eq_coe_of_ofPotential_eq_of_bounded hKb hKo μ hμ hψ hess hψμ
  exact ⟨φ, hcoe, hc, hnorm, hmap,
    smooth_moment_calculus_of_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV
      hVc μ hμ hiso hc hnorm hmap⟩

end BoundedOpenConvexSource

end FunctionalInequalities.Probability.MomentMeasure
