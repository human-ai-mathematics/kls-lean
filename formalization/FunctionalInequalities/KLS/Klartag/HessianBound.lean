import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere

/-!
# A maximum-principle bound for the Hessian of a moment potential

Supporting result toward Klartag, *Logarithmically-concave moment measures I*,
arXiv:1309.2767v1, Theorem 1.1 (the Laplacian bound `Δψ ≤ 2R(K)²` for the moment potential of a
log-concave measure on a convex body `K`, `R(K) = sup_K |x|`). Let `φ` be a smooth function with
positive definite Hessian solving the Monge–Ampère equation `log det ∇²φ = -φ + V(∇φ)` (in the
standard orthonormal basis, as in Letwin arXiv:2607.24164v1),
with `∇φ(E) ⊆ K ⊆ B(0, R)`, `K` open, `V` smooth on an open `U ⊇ closure K` and convex on `K`,
the Laplacian `Δφ` bounded above and `φ → ∞` at infinity. Then
`Δφ + |∇φ|² ≤ 3R²` everywhere (`MomentMeasure.trace_hessian_add_sq_le`); with
`bilinearIteratedFDerivTwo_le_trace_mul_norm_sq` this bounds the Hessian form by `3R² ‖v‖²`.

Proof: for the operator `L = hessianInverseOperator φ V` of Letwin (2.3), the first partial
derivatives of `φ` are eigenfunctions with eigenvalue `-1` (Letwin (2.4),
`MomentMeasure.hessianInverseOperator_fderiv_apply`), and the second-derivative identity (2.6) with
convexity of `V` gives `L(Δφ + |∇φ|²) ≥ Δφ - 2|∇φ|²`
(`MomentMeasure.trace_sub_two_mul_sq_le_hessianInverseOperator`). At a maximum of
`Δφ + |∇φ|² - δφ` (which exists by coercivity) `L ≤ 0`, and `Lφ` is bounded
(`BakryEmery.bounded_hessianInverseOperator_self`); letting `δ ↓ 0` gives the bound.

Scope: this is an elliptic maximum-principle proof, not Klartag's diffusion argument, and its
constant is `Δφ ≤ 3R²` rather than Klartag's `2R²`. It is not Theorem 1.1 itself: the smoothness,
positive definiteness, the equation, the upper bound on `Δφ` and the coercivity of `φ` are
hypotheses, and no moment measure or transport map is constructed here.
-/

noncomputable section
open scoped ContDiff RealInnerProductSpace Topology
open Filter
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section MaximumPrinciple

/-! The potential and Monge–Ampère data shared by the three results, in their original order. -/

variable {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
  {K U : Set E} (hK : IsOpen K) (hU : IsOpen U) (hKU : closure K ⊆ U)
  (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
  (hrange : Set.range (gradient φ) ⊆ K)

include hφ hU hV in
/-- First partial derivatives are eigenfunctions with eigenvalue `-1`: `L ∂_iφ = -∂_iφ`
(Letwin arXiv:2607.24164v1, (2.4)). -/
theorem hessianInverseOperator_fderiv_apply
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    {x : E} (hx : gradient φ x ∈ U)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (i : Fin (Module.finrank ℝ E)) :
    hessianInverseOperator φ V (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E i)) x =
      -fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) := by
  set e := stdOrthonormalBasis ℝ E
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by decide)
  have hi : ContDiff ℝ 2 (fun y => fderiv ℝ φ y (e i)) :=
    contDiff_fderiv_apply hφ (by decide) (e i)
  have hD (u : E) :
      fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x u = bilinearIteratedFDerivTwo ℝ φ x u (e i) :=
    (bilinearIteratedFDerivTwo_eq_fderiv_apply hφ2 x u (e i)).symm
  have hH (u v : E) :
      bilinearIteratedFDerivTwo ℝ (fun y => fderiv ℝ φ y (e i)) x u v =
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y u v) x (e i) := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hi]
    have heq : (fun y => fderiv ℝ (fun z => fderiv ℝ φ z (e i)) y v) =
        fun y => bilinearIteratedFDerivTwo ℝ φ y (e i) v := by
      funext y
      rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hφ2]
      exact bilinearIteratedFDerivTwo_symm hφ2 y v (e i)
    rw [heq]
    exact fderiv_bilinearIteratedFDerivTwo_comm hφ x (e i) v u
  simp only [hessianInverseOperator, nondivergenceOperator]
  simp_rw [hH, hD]
  rw [mongeAmpere_first_derivative e hφ hU hV hMA hx hPD i]
  ring

include hφ hK hU hKU hV hVc hrange in
/-- **The subsolution inequality** `L(Δφ + |∇φ|²) ≥ Δφ - 2|∇φ|²`, from Letwin (2.4), (2.6) and the
convexity of `V` on the open `K ⊇ range ∇φ` (sums over the standard orthonormal basis). -/
theorem trace_sub_two_mul_sq_le_hessianInverseOperator
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (x : E) :
    (∑ i, bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)) -
        2 * ∑ i, (fderiv ℝ φ x (stdOrthonormalBasis ℝ E i)) ^ 2 ≤
      hessianInverseOperator φ V (fun y => ∑ i,
        (bilinearIteratedFDerivTwo ℝ φ y (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) +
          (fderiv ℝ φ y (stdOrthonormalBasis ℝ E i)) ^ 2)) x := by
  let e := stdOrthonormalBasis ℝ E
  let B : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ :=
    fun i j y => bilinearIteratedFDerivTwo ℝ φ y (e i) (e j)
  let H : Fin (Module.finrank ℝ E) → E → ℝ := fun i y => B i i y
  let d : Fin (Module.finrank ℝ E) → E → ℝ := fun i y => fderiv ℝ φ y (e i)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by decide)
  have hxU : gradient φ x ∈ U := hKU (subset_closure (hrange ⟨x, rfl⟩))
  have hH2 (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ 2 (H i) :=
    (contDiff_bilinearIteratedFDerivTwo_apply hφ (e i) (e i)).of_le (by decide)
  have hd2 (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ 2 (d i) :=
    contDiff_fderiv_apply hφ (by decide) (e i)
  have hq2 (i : Fin (Module.finrank ℝ E)) : ContDiff ℝ 2 (fun y => d i y ^ 2) := (hd2 i).pow 2
  -- `L (∂_iφ)² = -2 (∂_iφ)² + 2 φ_ii`
  have hq (i : Fin (Module.finrank ℝ E)) :
      hessianInverseOperator φ V (fun y => d i y ^ 2) x = -2 * d i x ^ 2 + 2 * H i x := by
    have hcross :
        (∑ a, ∑ c, inverseHessianEntry φ e x a c *
          fderiv ℝ (d i) x (e a) * fderiv ℝ (d i) x (e c)) = H i x := by
      have hderiv (a : Fin (Module.finrank ℝ E)) : fderiv ℝ (d i) x (e a) = B a i x :=
        (bilinearIteratedFDerivTwo_eq_fderiv_apply hφ2 x (e a) (e i)).symm
      simp_rw [hderiv]
      exact sum_inverseHessianEntry_mul_hessian_hessian hφ2 x (hPD x) i
    have hm := hessianInverseOperator_mul hφ2 V (hd2 i) (hd2 i) x
    simp only [← pow_two] at hm
    rw [hessianInverseOperator_fderiv_apply hφ hU hV hMA hxU (hPD x) i, hcross] at hm
    rw [hm]
    ring
  -- `L φ_ii ≥ -φ_ii` by (2.6), convexity of `V` and the Gram term
  have hLH (i : Fin (Module.finrank ℝ E)) : -H i x ≤ hessianInverseOperator φ V (H i) x := by
    have hs := mongeAmpere_second_derivative_on_range hφ hU hKU hV hrange hMA hPD x i i
    have hcdiag :=
      (posSemidef_hessian_conj_hessian_on_range e hφ2 hK hKU (hV.of_le (by decide)) hVc
        hrange x).diag_nonneg (i := i)
    have hgdiag := (posSemidef_inverseHessian_third_gram e hφ x (hPD x)).diag_nonneg (i := i)
    simp only [Matrix.of_apply] at hcdiag hgdiag
    change hessianInverseOperator φ V (H i) x + H i x = _ at hs
    linarith
  have hterm (i : Fin (Module.finrank ℝ E)) :
      H i x - 2 * d i x ^ 2 ≤ hessianInverseOperator φ V (fun y => H i y + d i y ^ 2) x := by
    have hadd := hessianInverseOperator_sub_const_mul φ V (hH2 i) (hq2 i) (-1) x
    simp only [neg_one_mul, sub_neg_eq_add] at hadd
    rw [hadd, hq i]
    linarith [hLH i]
  have hsplit := hessianInverseOperator_sum Finset.univ φ V
    (f := fun i y => H i y + d i y ^ 2) (fun i _ => (hH2 i).add (hq2 i)) x
  change (∑ i, H i x) - 2 * ∑ i, d i x ^ 2 ≤
    hessianInverseOperator φ V (fun y => ∑ i, (H i y + d i y ^ 2)) x
  rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => hterm i

include hφ hK hU hKU hV hVc hrange in
/-- **A-priori Hessian bound by the maximum principle** (supporting Klartag arXiv:1309.2767v1,
Theorem 1.1, with constant `3R²` in place of `2R²`). For a smooth solution of
`log det ∇²φ = -φ + V(∇φ)` with positive definite Hessian, `∇φ(E) ⊆ K ⊆ B(0, R)`, `V` smooth near
`closure K` and convex on the open `K`, a Laplacian bounded above and `φ → ∞` at infinity, one has
`Δφ + |∇φ|² ≤ 3R²` everywhere. -/
theorem trace_hessian_add_sq_le {R : ℝ} (hR : ∀ y ∈ K, ‖y‖ ≤ R)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hbound : ∃ C : ℝ, ∀ x, ∑ i, bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E i) ≤ C)
    (hcoer : Tendsto φ (cocompact E) atTop) (x : E) :
    (∑ i, bilinearIteratedFDerivTwo ℝ φ x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)) +
      ‖gradient φ x‖ ^ 2 ≤ 3 * R ^ 2 := by
  let e := stdOrthonormalBasis ℝ E
  let T : E → ℝ := fun y => ∑ i, bilinearIteratedFDerivTwo ℝ φ y (e i) (e i)
  let N : E → ℝ := fun y => ∑ i, (fderiv ℝ φ y (e i)) ^ 2
  let G : E → ℝ := fun y =>
    ∑ i, (bilinearIteratedFDerivTwo ℝ φ y (e i) (e i) + (fderiv ℝ φ y (e i)) ^ 2)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by decide)
  have hG_eq (y : E) : G y = T y + N y := Finset.sum_add_distrib
  have hN_eq (y : E) : N y = ‖gradient φ y‖ ^ 2 := (norm_gradient_sq_eq_sum φ y).symm
  have hN_le (y : E) : N y ≤ R ^ 2 := by
    rw [hN_eq y]
    exact pow_le_pow_left₀ (norm_nonneg _) (hR _ (hrange ⟨y, rfl⟩)) 2
  have hG2 : ContDiff ℝ 2 G := ContDiff.sum fun i _ =>
    ((contDiff_bilinearIteratedFDerivTwo_apply hφ (e i) (e i)).of_le (by decide)).add
      ((contDiff_fderiv_apply hφ (by decide) (e i)).pow 2)
  obtain ⟨C, hC⟩ := hbound
  have hG_bound (y : E) : G y ≤ C + R ^ 2 := by
    rw [hG_eq y]
    exact add_le_add (hC y) (hN_le y)
  obtain ⟨D, -, hD⟩ :=
    bounded_hessianInverseOperator_self hφ2 hPD (isBounded_iff_forall_norm_le.mpr ⟨R, hR⟩)
      hrange hU hKU (hV.of_le (by decide))
  obtain ⟨m, hm⟩ := hφ.continuous.exists_forall_le hcoer
  -- the penalized maximum of `G - δφ`
  have hdelta (δ : ℝ) (hδ : 0 < δ) : G x ≤ 3 * R ^ 2 + δ * (D + φ x - φ m) := by
    let F : E → ℝ := fun y => G y - δ * φ y
    have hF2 : ContDiff ℝ 2 F := hG2.sub (contDiff_const.mul hφ2)
    have hFcoer : Tendsto F (cocompact E) atBot := by
      refine tendsto_atBot.mpr fun b => ?_
      filter_upwards [tendsto_atTop.mp hcoer ((C + R ^ 2 - b) / δ)] with y hy
      have hprod : C + R ^ 2 - b ≤ φ y * δ := (div_le_iff₀ hδ).mp hy
      change G y - δ * φ y ≤ b
      nlinarith [hG_bound y]
    obtain ⟨y, hy⟩ := hF2.continuous.exists_forall_ge hFcoer
    have hLF : hessianInverseOperator φ V F y ≤ 0 :=
      hessianInverseOperator_nonpos_of_isLocalMax hφ2 V hF2 (Eventually.of_forall hy) (hPD y)
    have hlin := hessianInverseOperator_sub_const_mul φ V hG2 hφ2 δ y
    have hmul : δ * hessianInverseOperator φ V φ y ≤ δ * D :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hD y)) hδ.le
    have htrace :=
      trace_sub_two_mul_sq_le_hessianInverseOperator hφ hK hU hKU hV hVc hrange hMA hPD y
    change T y - 2 * N y ≤ hessianInverseOperator φ V G y at htrace
    change hessianInverseOperator φ V F y = _ at hlin
    have hGy : G y ≤ 3 * R ^ 2 + δ * D := by
      rw [hG_eq y]
      linarith [hN_le y]
    have hpen : G x - δ * φ x ≤ G y - δ * φ y := hy x
    have hmin : δ * φ m ≤ δ * φ y := mul_le_mul_of_nonneg_left (hm y) hδ.le
    nlinarith
  have hmain : G x ≤ 3 * R ^ 2 := by
    by_contra hn
    have hgap : 0 < G x - 3 * R ^ 2 := by linarith [lt_of_not_ge hn]
    have hA : 0 ≤ D + φ x - φ m := by
      have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD x)
      linarith [hm x]
    have hden : 0 < 2 * (D + φ x - φ m + 1) := by positivity
    have hh := hdelta _ (div_pos hgap hden)
    have hδeq : (G x - 3 * R ^ 2) / (2 * (D + φ x - φ m + 1)) * (2 * (D + φ x - φ m + 1)) =
        G x - 3 * R ^ 2 := div_mul_cancel₀ _ hden.ne'
    nlinarith
  rw [hG_eq x, hN_eq x] at hmain
  exact hmain

end MaximumPrinciple

end FunctionalInequalities.Probability.MomentMeasure
