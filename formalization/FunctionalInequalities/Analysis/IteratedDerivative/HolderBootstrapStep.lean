import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import FunctionalInequalities.Analysis.IteratedDerivative.VariableCoefficientSchauder
import FunctionalInequalities.Analysis.IteratedDerivative.QuotientLimit
import FunctionalInequalities.Analysis.BakryEmery.DifferenceQuotient

/-!
# One Schauder bootstrap step: `C^{2,α}` difference-quotient equations give `C^{3,α}`

Supporting Letwin, arXiv:2607.24164v1, Lemma 2.2 (strong regular class), through the method of
difference quotients of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, with the interior a priori
estimate of Theorem 6.2, pp. 90–92.

For a `C²` function `u : ℝⁿ → ℝ` (`n ≥ 2`) whose Hessian is `α`-Hölder on `closedBall c (2R + q₀)`
(`0 < R ≤ 1`, `0 < α < 1`), and whose scalar-step difference quotients
`v = differenceQuotient u (q • e) q` in every unit direction `e` with `0 < |q| ≤ q₀` satisfy on
`closedBall c (2R)` a uniformly elliptic equation `Σ aⁱʲ D_{ij} v + Σ bⁱ D_i v + v = g` with
symmetric `(λ, Λ)`-elliptic `α`-Hölder coefficients, bounded Hölder `bⁱ`, and `|v| ≤ V`,
`|g| ≤ M`, `[g]_α ≤ H`, all caps chosen before `e` and `q`:

* `fderiv_fderiv_differenceQuotient`, `differenceQuotient_hessian_bound`,
  `differenceQuotient_hessian_holder`: the Hessian of the finite difference is the finite
  difference of the Hessians, hence bounded and Hölder (with step-dependent constants) wherever
  the Hessian of `u` is Hölder;
* `norm_fderiv_differenceQuotient_sub_le`, `tendstoUniformlyOn_fderiv_differenceQuotient`: the
  gradients of the quotients converge uniformly on `ball c R` to the gradient of the directional
  derivative `D_e u` (mean value theorem with the Hölder Hessian);
* `directional_derivative_contDiffOn_two_of_quotient_equations`: for every unit `e`, the
  directional derivative `x ↦ D u (x) e` is `C²` on `ball c R` with Hessian bounded and
  `α`-Hölder by `C (V R^{-2-α} + M R^{-α} + H)`, where `C = C(n, α, λ, Λ, K, Kb)` is the constant
  of `variable_coefficient_interior_hessian_holder` (Theorem 6.2) and precedes `c`, `R`, `u`
  and all data;
* `contDiffOn_three_of_quotient_equations`: hence `u` is `C³` on `ball c R`, with third
  derivative bounded and `α`-Hölder there by the same constant.

The equations are hypotheses here (they are derived for the regular moment potential in
`KLS/CEK/MomentRegularity/BootstrapThree`); no higher-order bootstrap, no `C^∞` conclusion, and no boundary
regularity is claimed.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

open Set Metric Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped NNReal ContDiff BigOperators

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)


/-- The Hessian of a scalar-step finite difference of a `C²` function is the finite difference
of the Hessians (operator form of `hessianMatrix_differenceQuotient`). -/
theorem fderiv_fderiv_differenceQuotient {u : E → ℝ} (hu : ContDiff ℝ 2 u) (d : E) (q : ℝ)
    (x : E) :
    fderiv ℝ (fderiv ℝ (differenceQuotient u d q)) x =
      q⁻¹ • (fderiv ℝ (fderiv ℝ u) (x + d) - fderiv ℝ (fderiv ℝ u) x) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ u) := hD.differentiable (by norm_num)
  have hds : HasFDerivAt (fun y => fderiv ℝ u (y + d))
      (fderiv ℝ (fderiv ℝ u) (x + d)) x :=
    (hasFDerivAt_comp_add_right d).mpr (hd (x + d)).hasFDerivAt
  have hdiff := (hds.sub (hd x).hasFDerivAt).const_smul q⁻¹
  rw [fderiv_differenceQuotient hu d q]
  exact hdiff.fderiv

/-- A priori Hessian cap of the finite difference from a Hölder Hessian of `u`:
`‖D²v x‖ ≤ Hu ‖d‖^α / |q|`. -/
theorem differenceQuotient_hessian_bound {u : E → ℝ} (hu : ContDiff ℝ 2 u) {s : Set E}
    {Hu α : ℝ}
    (hHu : ∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu * ‖x - y‖ ^ α)
    {d : E} {q : ℝ} {x : E} (hx : x ∈ s) (hxd : x + d ∈ s) :
    ‖fderiv ℝ (fderiv ℝ (differenceQuotient u d q)) x‖ ≤ |q|⁻¹ * (Hu * ‖d‖ ^ α) := by
  rw [fderiv_fderiv_differenceQuotient hu d q x]
  have h1 := hHu (x + d) hxd x hx
  rw [add_sub_cancel_left] at h1
  calc ‖q⁻¹ • (fderiv ℝ (fderiv ℝ u) (x + d) - fderiv ℝ (fderiv ℝ u) x)‖
      ≤ ‖q⁻¹‖ * ‖fderiv ℝ (fderiv ℝ u) (x + d) - fderiv ℝ (fderiv ℝ u) x‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ |q|⁻¹ * (Hu * ‖d‖ ^ α) := by
        rw [norm_inv, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (abs_nonneg q))

/-- A priori Hölder cap of the Hessian of the finite difference: `[D²v]_α ≤ 2 Hu / |q|`. -/
theorem differenceQuotient_hessian_holder {u : E → ℝ} (hu : ContDiff ℝ 2 u) {s : Set E}
    {Hu α : ℝ}
    (hHu : ∀ x ∈ s, ∀ y ∈ s,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu * ‖x - y‖ ^ α)
    {d : E} {q : ℝ} {x y : E} (hx : x ∈ s) (hxd : x + d ∈ s) (hy : y ∈ s) (hyd : y + d ∈ s) :
    ‖fderiv ℝ (fderiv ℝ (differenceQuotient u d q)) x -
        fderiv ℝ (fderiv ℝ (differenceQuotient u d q)) y‖ ≤
      (2 * |q|⁻¹ * Hu) * ‖x - y‖ ^ α := by
  rw [fderiv_fderiv_differenceQuotient hu d q x, fderiv_fderiv_differenceQuotient hu d q y]
  have h1 := hHu (x + d) hxd (y + d) hyd
  have h2 := hHu x hx y hy
  rw [add_sub_add_right_eq_sub] at h1
  set A := fderiv ℝ (fderiv ℝ u) (x + d) - fderiv ℝ (fderiv ℝ u) (y + d) with hA
  set B := fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y with hB
  set P := fderiv ℝ (fderiv ℝ u) (x + d) - fderiv ℝ (fderiv ℝ u) x with hP
  set Q := fderiv ℝ (fderiv ℝ u) (y + d) - fderiv ℝ (fderiv ℝ u) y with hQ
  have ePQ : P - Q = A - B := by
    rw [hP, hQ, hA, hB]
    abel
  have e : q⁻¹ • P - q⁻¹ • Q = q⁻¹ • (A - B) := by
    rw [← ePQ, smul_sub q⁻¹ P Q]
  rw [e]
  have hn : ‖A - B‖ ≤ Hu * ‖x - y‖ ^ α + Hu * ‖x - y‖ ^ α :=
    (norm_sub_le A B).trans (add_le_add h1 h2)
  have hq : 0 ≤ |q|⁻¹ := inv_nonneg.mpr (abs_nonneg q)
  calc ‖q⁻¹ • (A - B)‖ ≤ ‖q⁻¹‖ * ‖A - B‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ |q|⁻¹ * (Hu * ‖x - y‖ ^ α + Hu * ‖x - y‖ ^ α) := by
        rw [norm_inv, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hn hq
    _ = (2 * |q|⁻¹ * Hu) * ‖x - y‖ ^ α := by ring

/-- The gradient of the directional derivative `x ↦ D u (x) e` of a `C²` function is the
Hessian applied to `e` (symmetry of the second derivative). -/
theorem fderiv_directional_eq {u : E → ℝ} (hu : ContDiff ℝ 2 u) (e x : E) :
    fderiv ℝ (fun y => fderiv ℝ u y e) x = fderiv ℝ (fderiv ℝ u) x e := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x := hD.differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const e)]
  ext h
  have hsym := (hu.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_const_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  exact hsym h e

/-- Mean value bound for the gradient of the finite difference: if the Hessian of `u` is
`α`-Hölder with constant `Hu` on `closedBall c (2R + q₀)`, then for `x ∈ ball c R` and
`0 < q ≤ q₀`, `‖D v (x) - D (D_e u) (x)‖ ≤ Hu q^α` for `v = differenceQuotient u (q • e) q`
and unit `e`. -/
theorem norm_fderiv_differenceQuotient_sub_le {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {c : E} {R q₀ Hu α : ℝ} (hR : 0 < R) (hq₀ : 0 < q₀) (hHu0 : 0 ≤ Hu) (hα : 0 ≤ α)
    (hHu : ∀ x ∈ closedBall c (2 * R + q₀), ∀ y ∈ closedBall c (2 * R + q₀),
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu * ‖x - y‖ ^ α)
    {e : E} (he : ‖e‖ = 1) {q : ℝ} (hq : 0 < q) (hqq : q ≤ q₀) {x : E} (hx : x ∈ ball c R) :
    ‖fderiv ℝ (differenceQuotient u (q • e) q) x - fderiv ℝ (fun y => fderiv ℝ u y e) x‖ ≤
      Hu * q ^ α := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hd : Differentiable ℝ (fderiv ℝ u) := hD.differentiable (by norm_num)
  have hxc : ‖x - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hx
  -- the ball `ball x (R + q₀)` lies in the Hölder region
  have hsub : ball x (R + q₀) ⊆ closedBall c (2 * R + q₀) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    calc ‖z - c‖ = ‖(z - x) + (x - c)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖x - c‖ := norm_add_le _ _
      _ ≤ 2 * R + q₀ := by linarith
  have hy : x + q • e ∈ ball x (R + q₀) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos hq]
    linarith
  have hx' : x ∈ closedBall c (2 * R + q₀) := hsub (mem_ball_self (by linarith))
  have key := norm_sub_sub_le_of_holder_fderiv (f := fderiv ℝ u) (f' := fderiv ℝ (fderiv ℝ u))
    (x := x) (r := R + q₀) hHu0 hα (fun z _ => (hd z).hasFDerivAt)
    (fun z hz => hHu z (hsub hz) x hx') hy
  rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos hq] at key
  rw [fderiv_differenceQuotient hu, fderiv_directional_eq hu]
  have e1 : q⁻¹ • (fderiv ℝ u (x + q • e) - fderiv ℝ u x) - fderiv ℝ (fderiv ℝ u) x e =
      q⁻¹ • (fderiv ℝ u (x + q • e) - fderiv ℝ u x - fderiv ℝ (fderiv ℝ u) x (q • e)) := by
    rw [map_smul, smul_sub (q⁻¹) (fderiv ℝ u (x + q • e) - fderiv ℝ u x)
      (q • fderiv ℝ (fderiv ℝ u) x e), smul_smul, inv_mul_cancel₀ hq.ne', one_smul]
  rw [e1]
  calc ‖q⁻¹ • (fderiv ℝ u (x + q • e) - fderiv ℝ u x - fderiv ℝ (fderiv ℝ u) x (q • e))‖
      ≤ ‖q⁻¹‖ * ‖fderiv ℝ u (x + q • e) - fderiv ℝ u x - fderiv ℝ (fderiv ℝ u) x (q • e)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ q⁻¹ * (Hu * q ^ α * q) := by
        rw [norm_inv, Real.norm_eq_abs, abs_of_pos hq]
        exact mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hq.le)
    _ = Hu * q ^ α := by field_simp

/-- Uniform convergence on `ball c R` of the gradients of the finite differences along
`q_m = q₀ / (m + 1)` to the gradient of the directional derivative. -/
theorem tendstoUniformlyOn_fderiv_differenceQuotient {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {c : E} {R q₀ Hu α : ℝ} (hR : 0 < R) (hq₀ : 0 < q₀) (hHu0 : 0 ≤ Hu) (hα : 0 < α)
    (hHu : ∀ x ∈ closedBall c (2 * R + q₀), ∀ y ∈ closedBall c (2 * R + q₀),
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu * ‖x - y‖ ^ α)
    {e : E} (he : ‖e‖ = 1) :
    TendstoUniformlyOn
      (fun m : ℕ => fderiv ℝ (differenceQuotient u ((q₀ / ((m : ℝ) + 1)) • e) (q₀ / ((m : ℝ) + 1))))
      (fderiv ℝ (fun y => fderiv ℝ u y e)) atTop (ball c R) := by
  have hq : ∀ m : ℕ, 0 < q₀ / ((m : ℝ) + 1) := fun m => by positivity
  have hqq : ∀ m : ℕ, q₀ / ((m : ℝ) + 1) ≤ q₀ := fun m => by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hq₀, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hlim : Tendsto (fun m : ℕ => Hu * (q₀ / ((m : ℝ) + 1)) ^ α) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => q₀ / ((m : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul q₀
      rw [mul_zero] at this
      refine this.congr fun m => ?_
      ring
    have h2 := h1.rpow_const (Or.inr hα.le)
    rw [Real.zero_rpow hα.ne'] at h2
    simpa using h2.const_mul Hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with m hm x hx
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  exact (norm_fderiv_differenceQuotient_sub_le hu hR hq₀ hHu0 hα.le hHu he (hq m) (hqq m)
    hx).trans_lt hm

/-- **Uniform difference-quotient equations.** For every unit direction `e` and every step
`0 < q ≤ q₀`, the finite difference `v = differenceQuotient u (q • e) q` satisfies on
`closedBall c (2R)` an equation `Σ aⁱʲ D_{ij} v + Σ bⁱ D_i v + v = g` with symmetric
`(λ, Λ)`-elliptic `α`-Hölder (constant `K`) coefficients `a`, first-order coefficients bounded and
`α`-Hölder by `Kb`, `|v| ≤ V`, `|g| ≤ M` and `[g]_α ≤ H`; the coefficients and the forcing may
depend on `e` and `q`, the caps do not. This is the hypothesis shape of the one-step Schauder gain;
no claim is made here. -/
def UniformQuotientEquations (α : ℝ≥0) (lam Lam K Kb : ℝ) (c : E) (R : ℝ) (u : E → ℝ)
    (q₀ V M : ℝ) (H : ℝ≥0) : Prop :=
  ∀ e : E, ‖e‖ = 1 → ∀ q : ℝ, 0 < q → q ≤ q₀ →
    ∃ (a : Fin n → Fin n → E → ℝ) (b : Fin n → E → ℝ) (g : E → ℝ),
      (∀ x ∈ closedBall c (2 * R), ∀ i j, a i j x = a j i x) ∧
      (∀ x ∈ closedBall c (2 * R), ∀ ξ : E,
        lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j ∧
          ∑ i, ∑ j, a i j x * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2) ∧
      (∀ i j, ∀ x ∈ closedBall c (2 * R), ∀ y ∈ closedBall c (2 * R),
        |a i j x - a i j y| ≤ K * ‖x - y‖ ^ (α:ℝ)) ∧
      (∀ i, ∀ x ∈ closedBall c (2 * R), |b i x| ≤ Kb) ∧
      (∀ i, ∀ x ∈ closedBall c (2 * R), ∀ y ∈ closedBall c (2 * R),
        |b i x - b i y| ≤ Kb * ‖x - y‖ ^ (α:ℝ)) ∧
      (∀ x ∈ closedBall c (2 * R), (∑ i, ∑ j, a i j x *
          fderiv ℝ (fderiv ℝ (differenceQuotient u (q • e) q)) x
            (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
          (∑ i, b i x * fderiv ℝ (differenceQuotient u (q • e) q) x
            (EuclideanSpace.basisFun (Fin n) ℝ i)) +
          differenceQuotient u (q • e) q x = g x) ∧
      (∀ x ∈ closedBall c (2 * R), |differenceQuotient u (q • e) q x| ≤ V) ∧
      (∀ x ∈ closedBall c (2 * R), |g x| ≤ M) ∧
      HolderOnWith H α g (closedBall c (2 * R))

/-- **One-step Schauder gain for directional derivatives** (Gilbarg–Trudinger, Classics 2001,
Lemma 17.16 method with Theorem 6.2). Let `n ≥ 2`, `0 < α < 1`, `0 < λ ≤ Λ`, `0 ≤ K`, `0 ≤ Kb`.
There is `C = C(n, α, λ, Λ, K, Kb) > 0` such that for every centre `c`, radius `0 < R ≤ 1`,
`C²` function `u` whose Hessian is `α`-Hölder with constant `Hu` on `closedBall c (2R + q₀)`,
and caps `V, M, H` with `UniformQuotientEquations`, every directional derivative `x ↦ D u (x) e`
(`‖e‖ = 1`) is `C²` on `ball c R`, with Hessian bounded and `α`-Hölder there by
`C (V R^{-2-α} + M R^{-α} + H)`. The constant does not depend on `Hu` or `q₀`. -/
theorem directional_derivative_contDiffOn_two_of_quotient_equations (hn : 2 ≤ n) {α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) {lam Lam K Kb : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hK : 0 ≤ K) (hKb : 0 ≤ Kb) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E) (R : ℝ), 0 < R → R ≤ 1 →
      ∀ (u : E → ℝ), ContDiff ℝ 2 u →
      ∀ (q₀ Hu : ℝ), 0 < q₀ → 0 ≤ Hu →
      (∀ x ∈ closedBall c (2 * R + q₀), ∀ y ∈ closedBall c (2 * R + q₀),
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu * ‖x - y‖ ^ (α:ℝ)) →
      ∀ (V M : ℝ) (H : ℝ≥0), UniformQuotientEquations α lam Lam K Kb c R u q₀ V M H →
      ∀ e : E, ‖e‖ = 1 →
        ContDiffOn ℝ 2 (fun x => fderiv ℝ u x e) (ball c R) ∧
        (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x‖ ≤
          C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H)) ∧
        ∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x -
              fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) y‖ ≤
            C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
  have hαr : (0:ℝ) < α := hα0
  obtain ⟨C, hC, hS⟩ := variable_coefficient_interior_hessian_holder hn hα0 hα1 hlam hLam hK hKb
  refine ⟨C, hC, ?_⟩
  intro c R hR hR1 u hu q₀ Hu hq₀ hHu0 hHu V M H hdata e he
  set Kc : ℝ := C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) with hKc
  -- the steps `q_m = q₀ / (m + 1)`
  have hq : ∀ m : ℕ, 0 < q₀ / ((m : ℝ) + 1) := fun m => by positivity
  have hqq : ∀ m : ℕ, q₀ / ((m : ℝ) + 1) ≤ q₀ := fun m => by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hq₀, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  -- nonnegativity of the caps
  have hcmem : c ∈ closedBall c (2 * R) := mem_closedBall_self (by positivity)
  obtain ⟨_, _, _, _, _, _, _, _, _, hV0, hM0, _⟩ := hdata e he (q₀ / ((0:ℕ) + 1)) (hq 0) (hqq 0)
  have hV : 0 ≤ V := (abs_nonneg _).trans (hV0 c hcmem)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hM0 c hcmem)
  -- both Schauder bounds are dominated by `Kc` because `R ≤ 1`
  have hR2 : R ^ (-(2:ℝ)) ≤ R ^ (-(2:ℝ) - α) :=
    Real.rpow_le_rpow_of_exponent_ge hR hR1 (by linarith)
  have hR0 : (1:ℝ) ≤ R ^ (-(α:ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hR hR1 (by linarith)
  have hle1 : C * (V * R ^ (-(2:ℝ)) + M + H) ≤ Kc := by
    rw [hKc]
    have : M ≤ M * R ^ (-(α:ℝ)) := le_mul_of_one_le_right hM hR0
    have : V * R ^ (-(2:ℝ)) ≤ V * R ^ (-(2:ℝ) - α) := mul_le_mul_of_nonneg_left hR2 hV
    nlinarith
  -- uniform `C^{2,α}` bounds of the quotients on `ball c R`
  have hbounds : ∀ m : ℕ,
      (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ
        (differenceQuotient u ((q₀ / ((m : ℝ) + 1)) • e) (q₀ / ((m : ℝ) + 1)))) x‖ ≤ Kc) ∧
      ∀ x ∈ ball c R, ∀ y ∈ ball c R,
        ‖fderiv ℝ (fderiv ℝ
            (differenceQuotient u ((q₀ / ((m : ℝ) + 1)) • e) (q₀ / ((m : ℝ) + 1)))) x -
          fderiv ℝ (fderiv ℝ
            (differenceQuotient u ((q₀ / ((m : ℝ) + 1)) • e) (q₀ / ((m : ℝ) + 1)))) y‖ ≤
          Kc * ‖x - y‖ ^ (α:ℝ) := by
    intro m
    set q : ℝ := q₀ / ((m : ℝ) + 1) with hq_def
    obtain ⟨a, b, g, hsymm, hell, hahol, hbcap, hbhol, heq, hVv, hMg, hHg⟩ :=
      hdata e he q (hq m) (hqq m)
    have hsub : closedBall c (2 * R) ⊆ closedBall c (2 * R + q₀) :=
      closedBall_subset_closedBall (by linarith)
    have hshift : ∀ x ∈ closedBall c (2 * R), x + q • e ∈ closedBall c (2 * R + q₀) := by
      intro x hx
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      calc ‖x + q • e - c‖ = ‖(x - c) + q • e‖ := by congr 1; abel
        _ ≤ ‖x - c‖ + ‖q • e‖ := norm_add_le _ _
        _ ≤ 2 * R + q₀ := by
            rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (hq m)]
            linarith [hqq m]
    have hN : ∀ x ∈ closedBall c (2 * R),
        ‖fderiv ℝ (fderiv ℝ (differenceQuotient u (q • e) q)) x‖ ≤
          |q|⁻¹ * (Hu * ‖q • e‖ ^ (α:ℝ)) :=
      fun x hx => differenceQuotient_hessian_bound hu hHu (hsub hx) (hshift x hx)
    have hN2 : ∀ x ∈ closedBall c (2 * R), ∀ y ∈ closedBall c (2 * R),
        ‖fderiv ℝ (fderiv ℝ (differenceQuotient u (q • e) q)) x -
          fderiv ℝ (fderiv ℝ (differenceQuotient u (q • e) q)) y‖ ≤
          (2 * |q|⁻¹ * Hu) * ‖x - y‖ ^ (α:ℝ) :=
      fun x hx y hy =>
        differenceQuotient_hessian_holder hu hHu (hsub hx) (hshift x hx) (hsub hy) (hshift y hy)
    have hres := hS c R hR hR1 a b hsymm hell hahol hbcap hbhol
      (differenceQuotient u (q • e) q) g V _ _ M H (contDiff_differenceQuotient hu _ _)
      hN hN2 heq hVv hMg hHg
    refine ⟨fun x hx => (hres.1 x hx).trans hle1, fun x hx y hy => ?_⟩
    exact (hres.2 x hx y hy).trans (mul_le_mul_of_nonneg_right le_rfl (by positivity))
  -- the limit
  have hg : ContDiffOn ℝ 1 (fun x => fderiv ℝ u x e) (ball c R) :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).contDiffOn
  have hD := (tendstoUniformlyOn_fderiv_differenceQuotient hu hR hq₀ hHu0 hαr hHu
    he).tendstoLocallyUniformlyOn
  exact contDiffOn_two_of_hessian_limit isOpen_ball (fun x => fderiv ℝ u x e)
    (fun m => differenceQuotient u ((q₀ / ((m : ℝ) + 1)) • e) (q₀ / ((m : ℝ) + 1))) Kc hαr
    (fun m => (contDiff_differenceQuotient hu _ _).contDiffOn) hg hD
    (fun m => (hbounds m).1) (fun m => (hbounds m).2)

/-- A continuous linear functional on `ℝⁿ` is the sum of its values on the standard basis
times the coordinate projections. -/
theorem clm_eq_sum_basisFun_smul_proj (L : E →L[ℝ] ℝ) :
    L = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) • EuclideanSpace.proj (𝕜 := ℝ) i := by
  ext h
  have hh : h = ∑ i, h i • EuclideanSpace.basisFun (Fin n) ℝ i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
    rfl
  conv_lhs => rw [hh]
  rw [map_sum]
  simp only [map_smul, sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.coe_proj]
  ring

/-- If every coordinate directional derivative `x ↦ D u (x) eᵢ` of a differentiable `u` is
`C^k` on an open set, so is the gradient `D u`, and hence `u` is `C^{k+1}` there. -/
theorem contDiffOn_succ_of_coordinate_directional {k : ℕ} {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hd : DifferentiableOn ℝ u U)
    (h : ∀ i : Fin n, ContDiffOn ℝ k (fun x => fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i)) U) :
    ContDiffOn ℝ (k + 1) u U := by
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hd, by simp, ?_⟩
  have e : fderiv ℝ u = fun x => ∑ i, fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) •
      EuclideanSpace.proj (𝕜 := ℝ) i := funext fun x => clm_eq_sum_basisFun_smul_proj _
  rw [e]
  exact ContDiffOn.sum fun i _ => (h i).smul contDiffOn_const

/-- The Hessian of the directional derivative `x ↦ D u (x) e` is the third derivative of `u`
with `e` in the middle slot, at points where the Hessian of `u` is differentiable. -/
theorem fderiv_fderiv_directional_apply {u : E → ℝ} (hu : ContDiff ℝ 2 u) {x : E}
    (hx : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x) (e h₁ h₂ : E) :
    fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x h₁ h₂ =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x h₁ e h₂ := by
  have hfun : fderiv ℝ (fun y => fderiv ℝ u y e) = fun y => fderiv ℝ (fderiv ℝ u) y e :=
    funext (fderiv_directional_eq hu e)
  rw [hfun, fderiv_clm_apply hx (differentiableAt_const e)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_const_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]

/-- A trilinear form whose middle-slot unit-direction sections are bounded by `K` has operator
norm at most `K`. -/
theorem opNorm_le_of_middle_sections (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ e : E, ‖e‖ = 1 → ∀ h₁ h₃ : E, |T h₁ e h₃| ≤ K * ‖h₁‖ * ‖h₃‖) : ‖T‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun h₁ => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h₂ => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h₃ => ?_
  rw [Real.norm_eq_abs]
  by_cases h2 : h₂ = 0
  · simp [h2]
  have hn : 0 < ‖h₂‖ := norm_pos_iff.mpr h2
  set e : E := ‖h₂‖⁻¹ • h₂ with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h2e : h₂ = ‖h₂‖ • e := by
    rw [he_def, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have key := h e he h₁ h₃
  have hT : T h₁ h₂ h₃ = ‖h₂‖ * T h₁ e h₃ := by
    conv_lhs => rw [h2e]
    rw [map_smul, smul_apply, smul_eq_mul]
  rw [hT, abs_mul, abs_norm]
  calc ‖h₂‖ * |T h₁ e h₃| ≤ ‖h₂‖ * (K * ‖h₁‖ * ‖h₃‖) := by gcongr
    _ = K * ‖h₁‖ * ‖h₂‖ * ‖h₃‖ := by ring

/-- **One-step Schauder gain: `C³` with Hölder third derivative** (Gilbarg–Trudinger, Classics
2001, Lemma 17.16 method with Theorem 6.2). Under the hypotheses of
`directional_derivative_contDiffOn_two_of_quotient_equations`, `u` is `C³` on `ball c R` and its
third derivative is bounded and `α`-Hölder there by `C (V R^{-2-α} + M R^{-α} + H)`, with
`C = C(n, α, λ, Λ, K, Kb)` chosen before `c`, `R`, `u`, `q₀`, `Hu`, `V`, `M`, `H`. -/
theorem contDiffOn_three_of_quotient_equations (hn : 2 ≤ n) {α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) {lam Lam K Kb : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hK : 0 ≤ K) (hKb : 0 ≤ Kb) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : E) (R : ℝ), 0 < R → R ≤ 1 →
      ∀ (u : E → ℝ), ContDiff ℝ 2 u →
      ∀ (q₀ Hu : ℝ), 0 < q₀ → 0 ≤ Hu →
      (∀ x ∈ closedBall c (2 * R + q₀), ∀ y ∈ closedBall c (2 * R + q₀),
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ Hu * ‖x - y‖ ^ (α:ℝ)) →
      ∀ (V M : ℝ) (H : ℝ≥0), UniformQuotientEquations α lam Lam K Kb c R u q₀ V M H →
        ContDiffOn ℝ 3 u (ball c R) ∧
        (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤
          C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H)) ∧
        ∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
            C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
  obtain ⟨C, hC, hdir⟩ := directional_derivative_contDiffOn_two_of_quotient_equations hn hα0 hα1
    hlam hLam hK hKb
  refine ⟨C, hC, ?_⟩
  intro c R hR hR1 u hu q₀ Hu hq₀ hHu0 hHu V M H hdata
  have hd := hdir c R hR hR1 u hu q₀ Hu hq₀ hHu0 hHu V M H hdata
  set Kc : ℝ := C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) with hKc
  -- `C³` from the coordinate directional derivatives
  have h3 : ContDiffOn ℝ 3 u (ball c R) := by
    have := contDiffOn_succ_of_coordinate_directional (k := 2) isOpen_ball
      (hu.differentiable (by norm_num)).differentiableOn
      (fun i => (hd _ (by simp)).1)
    exact_mod_cast this
  have hdiff : ∀ x ∈ ball c R, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ u)) x := by
    intro x hx
    have h1 : ContDiffAt ℝ 3 u x := h3.contDiffAt (isOpen_ball.mem_nhds hx)
    have h2 : ContDiffAt ℝ 2 (fderiv ℝ u) x := h1.fderiv_right (by norm_num)
    have h4 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) x := h2.fderiv_right (by norm_num)
    exact h4.differentiableAt (by simp)
  have hKc0 : 0 ≤ Kc := by
    have hcmem : c ∈ ball c R := mem_ball_self hR
    have he : ‖EuclideanSpace.basisFun (Fin n) ℝ ⟨0, by omega⟩‖ = 1 := by simp
    exact (ContinuousLinearMap.opNorm_nonneg _).trans ((hd _ he).2.1 c hcmem)
  refine ⟨h3, fun x hx => ?_, fun x hx y hy => ?_⟩
  · refine opNorm_le_of_middle_sections _ hKc0 fun e he h₁ h₃ => ?_
    rw [← fderiv_fderiv_directional_apply hu (hdiff x hx) e h₁ h₃]
    calc |fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x h₁ h₃|
        ≤ ‖fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x‖ * ‖h₁‖ * ‖h₃‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm₂ _ h₁ h₃
      _ ≤ Kc * ‖h₁‖ * ‖h₃‖ := by gcongr; exact (hd e he).2.1 x hx
  · refine opNorm_le_of_middle_sections _ (by positivity) fun e he h₁ h₃ => ?_
    rw [sub_apply, sub_apply, sub_apply,
      ← fderiv_fderiv_directional_apply hu (hdiff x hx) e h₁ h₃,
      ← fderiv_fderiv_directional_apply hu (hdiff y hy) e h₁ h₃]
    calc |fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x h₁ h₃ -
          fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) y h₁ h₃|
        = |(fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x -
            fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) y) h₁ h₃| := by
          rw [sub_apply, sub_apply]
      _ ≤ ‖fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) x -
            fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y e)) y‖ * ‖h₁‖ * ‖h₃‖ := by
          rw [← Real.norm_eq_abs]
          exact ContinuousLinearMap.le_opNorm₂ _ h₁ h₃
      _ ≤ Kc * ‖x - y‖ ^ (α:ℝ) * ‖h₁‖ * ‖h₃‖ := by gcongr; exact (hd e he).2.2 x hx y hy

end FunctionalInequalities.Analysis
