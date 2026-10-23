import FunctionalInequalities.KLS.CEK.MomentRegularity.BootstrapThree

/-!
# Audit: the one-step Schauder bootstrap and the `C³` regular moment potential

Real clients of `contDiffOn_three_of_quotient_equations` (one-step gain, Gilbarg–Trudinger,
Classics 2001, Lemma 17.16 method with Theorem 6.2) and of
`exists_regular_moment_potential_contDiff_three` (Letwin, arXiv:2607.24164v1, Lemma 2.2 support,
strong class).

* Namespace `LetwinBootstrapThreeAudit`, planar quadratic `u(x) = ‖x‖²` (`n = 2`): its Hessian is the constant
  `2 ⟪·,·⟫`, so the Hölder cap of the Hessian is `Hu = 0`; for every unit `e` and `0 < q ≤ 1` the
  finite difference is `v(x) = 2 ⟪x, e⟫ + q` with `D²v = 0`, and it satisfies the equation
  `Σ δⁱʲ D_{ij} v + Σ 0 · D_i v + v = v` with `λ = Λ = 1`, `K = Kb = 0`, `|v| ≤ 3`, `|g| ≤ 3` and
  `[g]_{1/2} ≤ 4` on `closedBall 0 1` (`c = 0`, `R = 1/2`). Every hypothesis of
  `UniformQuotientEquations` is proved (`normSq_uniformQuotientEquations`), and the theorem gives
  `ContDiffOn ℝ 3 u (ball 0 (1/2))` with bounded `1/2`-Hölder third derivative
  (`normSq_bootstrap_client`).
* `regular_moment_potential_contDiff_three_client`: from the original Letwin inputs only (`n ≥ 2`,
  smooth `κ`-uniformly convex `W`, compact convex `K` with nonempty interior, normalized isotropic
  law `1_K e^{−W}`), one potential `u` with the gradient transport, `ContDiff ℝ 3 u`, a bounded
  Hölder third derivative on every ball `ball 0 s`, and a `C²` left inverse of `∇u` on
  `interior K`.

`#print axioms` for the clients and for the library producers they invoke.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ContDiff ENNReal RealInnerProductSpace

namespace LetwinBootstrapThreeAudit

open FunctionalInequalities FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein

-- The standard operator-norm instances at the concrete second- and third-derivative types (same
-- device as the library modules).
local instance {n : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance {n : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance {n : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance {n : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The Euclidean plane. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The quadratic `u(x) = ‖x‖²`. -/
def normSq (x : E) : ℝ := ‖x‖ ^ 2

theorem normSq_contDiff : ContDiff ℝ 2 normSq := contDiff_norm_sq ℝ

theorem fderiv_normSq (x : E) : fderiv ℝ normSq x = 2 • innerSL ℝ x :=
  fderiv_norm_sq_apply x

theorem fderiv_fderiv_normSq (x : E) :
    fderiv ℝ (fderiv ℝ normSq) x = 2 • (innerSL ℝ (E := E)) := by
  have hfun : fderiv ℝ normSq = fun y => 2 • innerSL ℝ y := funext fderiv_normSq
  rw [hfun]
  exact ((innerSL ℝ (E := E)).hasFDerivAt.const_smul (2 : ℕ)).fderiv

/-- The Hessian of `‖x‖²` is constant: Hölder cap `Hu = 0`. -/
theorem normSq_hessian_holder (x y : E) :
    ‖fderiv ℝ (fderiv ℝ normSq) x - fderiv ℝ (fderiv ℝ normSq) y‖ ≤
      0 * ‖x - y‖ ^ ((1 / 2 : ℝ≥0) : ℝ) := by
  rw [fderiv_fderiv_normSq, fderiv_fderiv_normSq, sub_self, zero_mul]
  exact le_of_eq (ContinuousLinearMap.opNorm_zero)

/-- The finite difference of `‖x‖²` in a unit direction: `v(x) = 2 ⟪x, e⟫ + q`. -/
theorem differenceQuotient_normSq {e : E} (he : ‖e‖ = 1) {q : ℝ} (hq : 0 < q) (x : E) :
    differenceQuotient normSq (q • e) q x = 2 * ⟪x, e⟫ + q := by
  unfold differenceQuotient normSq
  rw [norm_add_sq_real, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hq,
    real_inner_smul_right]
  field_simp
  ring

/-- The Hessian of the finite difference vanishes. -/
theorem fderiv_fderiv_differenceQuotient_normSq (e : E) (q : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (differenceQuotient normSq (q • e) q)) x = 0 := by
  rw [fderiv_fderiv_differenceQuotient normSq_contDiff, fderiv_fderiv_normSq, fderiv_fderiv_normSq,
    sub_self, smul_zero]

/-- `t ≤ 2 √t` for `0 ≤ t ≤ 4`. -/
theorem le_two_mul_sqrt {t : ℝ} (h0 : 0 ≤ t) (h4 : t ≤ 4) : t ≤ 2 * Real.sqrt t := by
  have hs : Real.sqrt t ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  calc t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt h0).symm
    _ ≤ 2 * Real.sqrt t := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg t)

/-- The uniform quotient equations of `‖x‖²` on `closedBall 0 1` with the identity coefficients,
no first-order term, forcing `g = v`, `λ = Λ = 1`, `K = Kb = 0`, `V = M = 3`, `H = 4`,
`α = 1/2`, `q₀ = 1`. -/
theorem normSq_uniformQuotientEquations :
    UniformQuotientEquations (1 / 2 : ℝ≥0) 1 1 0 0 (0 : E) (1 / 2) normSq 1 3 3
      (Real.toNNReal 4) := by
  intro e he q hq hq1
  refine ⟨fun i j _ => if i = j then 1 else 0, fun _ _ => 0,
    differenceQuotient normSq (q • e) q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _ i j
    simp only [eq_comm]
  · intro x _ ξ
    have hsum : (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * ξ i * ξ j) = ‖ξ‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Finset.sum_ite_eq, sq]
    rw [hsum, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  · intro i j x _ y _
    simp
  · intro i x _
    simp
  · intro i x _ y _
    simp
  · intro x _
    simp [fderiv_fderiv_differenceQuotient_normSq]
  · intro x hx
    rw [differenceQuotient_normSq he hq x]
    have hx' : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
    have hi : |⟪x, e⟫| ≤ 1 := by
      calc |⟪x, e⟫| ≤ ‖x‖ * ‖e‖ := abs_real_inner_le_norm x e
        _ ≤ 1 := by rw [he, mul_one]; exact hx'
    calc |2 * ⟪x, e⟫ + q| ≤ |2 * ⟪x, e⟫| + |q| := abs_add_le _ _
      _ ≤ 2 * 1 + 1 := by
          rw [abs_mul, abs_of_pos hq]
          gcongr
          norm_num
      _ = 3 := by norm_num
  · intro x hx
    rw [differenceQuotient_normSq he hq x]
    have hx' : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
    have hi : |⟪x, e⟫| ≤ 1 := by
      calc |⟪x, e⟫| ≤ ‖x‖ * ‖e‖ := abs_real_inner_le_norm x e
        _ ≤ 1 := by rw [he, mul_one]; exact hx'
    calc |2 * ⟪x, e⟫ + q| ≤ |2 * ⟪x, e⟫| + |q| := abs_add_le _ _
      _ ≤ 2 * 1 + 1 := by
          rw [abs_mul, abs_of_pos hq]
          gcongr
          norm_num
      _ = 3 := by norm_num
  · refine holderOnWith_of_dist_le (by norm_num) fun x hx y hy => ?_
    rw [differenceQuotient_normSq he hq x, differenceQuotient_normSq he hq y, Real.dist_eq,
      dist_eq_norm]
    have hx' : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
    have hy' : ‖y‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hy
    have hxy : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
    have hinner : |⟪x - y, e⟫| ≤ ‖x - y‖ := by
      calc |⟪x - y, e⟫| ≤ ‖x - y‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ = ‖x - y‖ := by rw [he, mul_one]
    have hsqrt : ‖x - y‖ ≤ 2 * Real.sqrt ‖x - y‖ :=
      le_two_mul_sqrt (norm_nonneg _) (by linarith)
    have hcoe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [hcoe, ← Real.sqrt_eq_rpow]
    calc |2 * ⟪x, e⟫ + q - (2 * ⟪y, e⟫ + q)| = 2 * |⟪x - y, e⟫| := by
          rw [inner_sub_left, ← abs_of_pos (two_pos : (0 : ℝ) < 2), ← abs_mul]
          congr 1
          rw [abs_of_pos (two_pos : (0 : ℝ) < 2)]
          ring
      _ ≤ 2 * ‖x - y‖ := by gcongr
      _ ≤ 2 * (2 * Real.sqrt ‖x - y‖) := by gcongr
      _ = 4 * Real.sqrt ‖x - y‖ := by ring

/-- The one-step bootstrap on the quadratic: `C³` on `ball 0 (1/2)` with bounded `1/2`-Hölder
third derivative. Every hypothesis is proved, not assumed. -/
theorem normSq_bootstrap_client :
    ∃ C : ℝ, 0 < C ∧ ContDiffOn ℝ 3 normSq (ball (0 : E) (1 / 2)) ∧
      (∀ x ∈ ball (0 : E) (1 / 2), ‖fderiv ℝ (fderiv ℝ (fderiv ℝ normSq)) x‖ ≤ C) ∧
      ∀ x ∈ ball (0 : E) (1 / 2), ∀ y ∈ ball (0 : E) (1 / 2),
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ normSq)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ normSq)) y‖ ≤
          C * ‖x - y‖ ^ ((1 / 2 : ℝ≥0) : ℝ) := by
  obtain ⟨C₀, hC₀, h⟩ := contDiffOn_three_of_quotient_equations (n := 2) le_rfl
    (α := 1 / 2) (by norm_num) (by norm_num) (lam := 1) (Lam := 1) one_pos le_rfl
    (K := 0) le_rfl (Kb := 0) le_rfl
  have hres := h 0 (1 / 2) (by norm_num) (by norm_num) normSq normSq_contDiff 1 0 one_pos le_rfl
    (fun x _ y _ => normSq_hessian_holder x y) 3 3 (Real.toNNReal 4)
    normSq_uniformQuotientEquations
  refine ⟨C₀ * (3 * (1 / 2 : ℝ) ^ (-(2 : ℝ) - ((1 / 2 : ℝ≥0) : ℝ)) +
    3 * (1 / 2 : ℝ) ^ (-((1 / 2 : ℝ≥0) : ℝ)) + (Real.toNNReal 4 : ℝ)), by positivity,
    hres.1, hres.2.1, hres.2.2⟩

section Letwin
variable {n : ℕ} (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
  {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- From the original Letwin inputs (`n ≥ 2`): one potential `u` with the gradient transport,
`C³` regularity, a bounded Hölder third derivative on every ball, positive definite Hessian
everywhere and a `C²` left inverse of `∇u` on `interior K`, all for the same `u`. -/
theorem regular_moment_potential_contDiff_three_client :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 3 u ∧ (∀ x, (hessianMatrix u x).PosDef) ∧
      (∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C) ∧
        ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
          ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
            ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
              C * ‖x - y‖ ^ (η : ℝ)) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ 2 Ψ (interior K) := by
  obtain ⟨u, _L, _LF, _T, _hconv, _hl, _hnorm, hmap, _hC1, _hG, _hF, _hd, _hT, _hC2, _hHc,
      hEvery, _hHol, _he, _hΨ, h3, hholder, hΨ2⟩ :=
    exists_regular_moment_potential_contDiff_three hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, hmap, h3, fun x => (hEvery x).1, hholder, hΨ2⟩

end Letwin

end LetwinBootstrapThreeAudit

#print axioms LetwinBootstrapThreeAudit.normSq_contDiff
#print axioms LetwinBootstrapThreeAudit.fderiv_fderiv_normSq
#print axioms LetwinBootstrapThreeAudit.normSq_hessian_holder
#print axioms LetwinBootstrapThreeAudit.differenceQuotient_normSq
#print axioms LetwinBootstrapThreeAudit.fderiv_fderiv_differenceQuotient_normSq
#print axioms LetwinBootstrapThreeAudit.le_two_mul_sqrt
#print axioms LetwinBootstrapThreeAudit.normSq_uniformQuotientEquations
#print axioms LetwinBootstrapThreeAudit.normSq_bootstrap_client
#print axioms LetwinBootstrapThreeAudit.regular_moment_potential_contDiff_three_client
#print axioms FunctionalInequalities.Analysis.directional_derivative_contDiffOn_two_of_quotient_equations
#print axioms FunctionalInequalities.Analysis.contDiffOn_three_of_quotient_equations
#print axioms FunctionalInequalities.Analysis.contDiffOn_three_balls_of_regular_fields
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential_contDiff_three
