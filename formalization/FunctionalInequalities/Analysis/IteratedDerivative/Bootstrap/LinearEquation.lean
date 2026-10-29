import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
import FunctionalInequalities.Analysis.IteratedDerivative.Bootstrap.Step
import FunctionalInequalities.Analysis.IteratedDerivative.LocalHolder

/-!
# Linearized-equation bootstrap: `C^{2,α}` solutions with `C^{1,α}` data are `C^{3,α}`

Supporting Letwin, arXiv:2607.24164v1, Lemma 2.2 (strong regular class), through the iterated
method of difference quotients of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16, pp. 463–464, with the interior a
priori estimate of Theorem 6.2, pp. 90–92.

Let `w : ℝⁿ → ℝ` (`n ≥ 2`) be `C²` and solve on `closedBall c S` the linear equation
`Σ aⁱʲ D_{ij} w + Σ bⁱ D_i w + w = g` with symmetric `(λ, Λ)`-elliptic coefficients `a`, where
`a`, `b`, `g` are `C¹` with `α`-Hölder first derivatives and `w` has an `α`-Hölder Hessian on
`closedBall c S`. For a unit direction `f` and a step `0 < q ≤ S/2`, the finite difference
`v_q = differenceQuotient w (q • f) q` solves on `closedBall c (2R)` (`R = min (S/4) 1`) the shifted
equation
`Σ aⁱʲ(· + q f) D_{ij} v_q + Σ bⁱ(· + q f) D_i v_q + v_q = g_q`,
`g_q = Δ_q g − Σ (Δ_q aⁱʲ) D_{ij} w − Σ (Δ_q bⁱ) D_i w`, `Δ_q h = (h (· + q f) − h)/q`
(`shifted_quotient_equation`). The shifted coefficients keep the ellipticity and Hölder caps, and
`g_q` is bounded and `α`-Hölder uniformly in `q` by the mean value theorem along the step
(`abs_differenceQuotient_le_of_fderiv_bound`, `abs_differenceQuotient_sub_le_of_fderiv_holder`).
Hence `UniformQuotientEquations` holds and `contDiffOn_three_of_quotient_equations` gives:

* `contDiffOn_three_ball_of_linear_equation`: `w` is `C³` on `ball c R` with third derivative
  bounded and `α`-Hölder there by a constant `Kc` chosen before the centre `c` and the functions,
  depending only on `n, α, λ, Λ, S` and the caps of the data;
* `directional_linear_equation`: once `w` is `C³`, every directional derivative `D_f w` solves
  `Σ aⁱʲ D_{ij}(D_f w) + Σ bⁱ D_i (D_f w) + D_f w = D_f g − Σ (D_f aⁱʲ) D_{ij} w − Σ (D_f bⁱ) D_i w`.

No `C^k` for `k ≥ 4`, no `C^∞` and no boundary regularity is claimed here; the induction is in
`IteratedDerivative/Bootstrap/Induction`.
-/

noncomputable section

namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

open Set Metric Filter Topology
open FunctionalInequalities.Analysis.BakryEmery
open scoped NNReal ContDiff BigOperators

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)


section Tools

/-- Two points of `closedBall c S` are at distance at most `2S`. -/
theorem norm_sub_le_two_mul_of_mem_closedBall {c x y : E} {S : ℝ} (hx : x ∈ closedBall c S)
    (hy : y ∈ closedBall c S) : ‖x - y‖ ≤ 2 * S := by
  rw [mem_closedBall, dist_eq_norm] at hx hy
  calc ‖x - y‖ = ‖(x - c) - (y - c)‖ := by congr 1; abel
    _ ≤ ‖x - c‖ + ‖y - c‖ := norm_sub_le _ _
    _ ≤ 2 * S := by linarith

/-- Mean value bound on a closed ball: a `C¹` function with `‖D h‖ ≤ N` there is `N`-Lipschitz
there. -/
theorem norm_sub_le_of_fderiv_bound_closedBall {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {h : E → G} (hh : Differentiable ℝ h) {c : E} {S N : ℝ}
    (hN : ∀ z ∈ closedBall c S, ‖fderiv ℝ h z‖ ≤ N) {x y : E} (hx : x ∈ closedBall c S)
    (hy : y ∈ closedBall c S) : ‖h x - h y‖ ≤ N * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hh z) hN (convex_closedBall c S) hy hx

/-- Entry bound of a bilinear form by its operator norm (unit basis vectors). -/
theorem abs_apply_basisFun_le_opNorm (B : E →L[ℝ] E →L[ℝ] ℝ) (i j : Fin n) :
    |B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ ‖B‖ := by
  have h := ContinuousLinearMap.le_opNorm₂ B (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa using h

/-- Coordinate bound of a linear functional by its operator norm. -/
theorem abs_apply_basisFun_le_opNorm' (L : E →L[ℝ] ℝ) (i : Fin n) :
    |L (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ ‖L‖ := by
  have h := ContinuousLinearMap.le_opNorm L (EuclideanSpace.basisFun (Fin n) ℝ i)
  simpa using h

end Tools

section DifferenceQuotients

/-- Mean value bound for the scalar-step finite difference of a differentiable function along a
unit direction: `|Δ_q h x| ≤ N` when `‖D h‖ ≤ N` on a closed ball containing `x` and `x + q f`. -/
theorem abs_differenceQuotient_le_of_fderiv_bound {h : E → ℝ} (hh : Differentiable ℝ h) {c : E}
    {S N : ℝ} (hN : ∀ z ∈ closedBall c S, ‖fderiv ℝ h z‖ ≤ N) {f : E} (hf : ‖f‖ = 1) {q : ℝ}
    (hq : 0 < q) {x : E} (hx : x ∈ closedBall c S) (hxq : x + q • f ∈ closedBall c S) :
    |differenceQuotient h (q • f) q x| ≤ N := by
  unfold differenceQuotient
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
  have key := norm_sub_le_of_fderiv_bound_closedBall hh hN hxq hx
  rw [add_sub_cancel_left, norm_smul, hf, mul_one] at key
  simp only [Real.norm_eq_abs, abs_of_pos hq] at key
  exact key

/-- Hölder bound, uniform in the step, for the scalar-step finite differences of a `C¹` function
with `α`-Hölder derivative: `|Δ_q h x − Δ_q h y| ≤ K ‖x − y‖^α` for `x, y ∈ closedBall c S'`,
`0 < q ≤ q₀`, `S' + q₀ ≤ S` (mean value theorem along the step applied to
`z ↦ h (z + (x − y)) − h z`). -/
theorem abs_differenceQuotient_sub_le_of_fderiv_holder {h : E → ℝ} (hh : Differentiable ℝ h)
    {c : E} {S S' q₀ K α : ℝ} (hS' : S' + q₀ ≤ S)
    (hhol : ∀ z ∈ closedBall c S, ∀ z' ∈ closedBall c S,
      ‖fderiv ℝ h z - fderiv ℝ h z'‖ ≤ K * ‖z - z'‖ ^ α)
    {f : E} (hf : ‖f‖ = 1) {q : ℝ} (hq : 0 < q) (hqq : q ≤ q₀) {x y : E}
    (hx : x ∈ closedBall c S') (hy : y ∈ closedBall c S') :
    |differenceQuotient h (q • f) q x - differenceQuotient h (q • f) q y| ≤ K * ‖x - y‖ ^ α := by
  rw [mem_closedBall, dist_eq_norm] at hx hy
  set F : E → ℝ := fun z => h (z + (x - y)) - h z with hF
  have hFd : Differentiable ℝ F := fun z =>
    ((differentiableAt_comp_add_right (x - y)).mpr (hh _)).sub (hh z)
  have hFderiv : ∀ z, fderiv ℝ F z = fderiv ℝ h (z + (x - y)) - fderiv ℝ h z := by
    intro z
    rw [hF]
    rw [fderiv_fun_sub ((differentiableAt_comp_add_right (x - y)).mpr (hh _)) (hh z),
      fderiv_comp_add_right]
  -- the segment ball lies in the Hölder region, and so does its translate
  have hmem : ∀ z ∈ closedBall y q, z ∈ closedBall c S := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    calc ‖z - c‖ = ‖(z - y) + (y - c)‖ := by congr 1; abel
      _ ≤ ‖z - y‖ + ‖y - c‖ := norm_add_le _ _
      _ ≤ S := by linarith
  have hmem' : ∀ z ∈ closedBall y q, z + (x - y) ∈ closedBall c S := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    calc ‖z + (x - y) - c‖ = ‖(z - y) + (x - c)‖ := by congr 1; abel
      _ ≤ ‖z - y‖ + ‖x - c‖ := norm_add_le _ _
      _ ≤ S := by linarith
  have hbound : ∀ z ∈ closedBall y q, ‖fderiv ℝ F z‖ ≤ K * ‖x - y‖ ^ α := by
    intro z hz
    rw [hFderiv]
    have := hhol _ (hmem' z hz) z (hmem z hz)
    rwa [add_sub_cancel_left] at this
  have hyq : y + q • f ∈ closedBall y q := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hf, mul_one,
      Real.norm_eq_abs, abs_of_pos hq]
  have hmv := norm_sub_le_of_fderiv_bound_closedBall hFd hbound hyq
    (mem_closedBall_self hq.le)
  rw [add_sub_cancel_left, norm_smul, hf, mul_one] at hmv
  simp only [Real.norm_eq_abs, abs_of_pos hq] at hmv
  have e1 : F (y + q • f) - F y = q * (differenceQuotient h (q • f) q x -
      differenceQuotient h (q • f) q y) := by
    rw [hF]
    simp only [differenceQuotient]
    have e2 : y + q • f + (x - y) = x + q • f := by abel
    have e3 : y + (x - y) = x := by abel
    rw [e2, e3]
    field_simp
    ring
  rw [e1, abs_mul, abs_of_pos hq] at hmv
  have hq' : 0 < q := hq
  nlinarith [hmv, abs_nonneg (differenceQuotient h (q • f) q x -
    differenceQuotient h (q • f) q y)]

/-- The pure algebra of the shifted finite-difference equation: subtracting the equation at `x`
from the equation at `x + q f` and dividing by `q`. -/
theorem quotient_equation_algebra {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ)
    (A A' W W' : ι → κ → ℝ) (B B' V V' : ι → ℝ) (w w' g g' : ℝ)
    (h1 : (∑ i, ∑ j, A' i j * W' i j) + (∑ i, B' i * V' i) + w' = g')
    (h2 : (∑ i, ∑ j, A i j * W i j) + (∑ i, B i * V i) + w = g) :
    (∑ i, ∑ j, A' i j * ((W' i j - W i j) / q)) + (∑ i, B' i * ((V' i - V i) / q)) +
        (w' - w) / q =
      (g' - g) / q - (∑ i, ∑ j, ((A' i j - A i j) / q) * W i j) -
        (∑ i, ((B' i - B i) / q) * V i) := by
  have s1 : ∀ i, ∑ j, A' i j * ((W' i j - W i j) / q) =
      (∑ j, A' i j * W' i j) / q - (∑ j, A' i j * W i j) / q := by
    intro i
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have s2 : ∀ i, ∑ j, ((A' i j - A i j) / q) * W i j =
      (∑ j, A' i j * W i j) / q - (∑ j, A i j * W i j) / q := by
    intro i
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have s3 : ∑ i, B' i * ((V' i - V i) / q) = (∑ i, B' i * V' i) / q - (∑ i, B' i * V i) / q := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have s4 : ∑ i, ((B' i - B i) / q) * V i = (∑ i, B' i * V i) / q - (∑ i, B i * V i) / q := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [s1, s2]
  rw [s3, s4, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.sum_div]
  rw [← h1, ← h2]
  ring

/-- The shifted forcing `g_q = Δ_q g − Σ (Δ_q aⁱʲ) D_{ij} w − Σ (Δ_q bⁱ) D_i w` of the finite
difference `v_q = differenceQuotient w (q • f) q`. -/
def shiftedForcing (w g : E → ℝ) (a : Fin n → Fin n → E → ℝ) (b : Fin n → E → ℝ) (f : E)
    (q : ℝ) (x : E) : ℝ :=
  differenceQuotient g (q • f) q x -
    (∑ i, ∑ j, differenceQuotient (a i j) (q • f) q x *
      fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) -
    (∑ i, differenceQuotient (b i) (q • f) q x * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i))

/-- **The shifted finite-difference equation.** If `Σ aⁱʲ D_{ij} w + Σ bⁱ D_i w + w = g` holds at
`x` and at `x + q f`, then `v_q = differenceQuotient w (q • f) q` satisfies at `x`
`Σ aⁱʲ(x + q f) D_{ij} v_q + Σ bⁱ(x + q f) D_i v_q + v_q = shiftedForcing w g a b f q x`. -/
theorem shifted_quotient_equation {w g : E → ℝ} {a : Fin n → Fin n → E → ℝ} {b : Fin n → E → ℝ}
    (hw : ContDiff ℝ 2 w) (f : E) (q : ℝ) (x : E)
    (h1 : (∑ i, ∑ j, a i j (x + q • f) * fderiv ℝ (fderiv ℝ w) (x + q • f)
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
        (∑ i, b i (x + q • f) * fderiv ℝ w (x + q • f) (EuclideanSpace.basisFun (Fin n) ℝ i)) +
        w (x + q • f) = g (x + q • f))
    (h2 : (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ w) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
        (∑ i, b i x * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) + w x = g x) :
    (∑ i, ∑ j, a i j (x + q • f) *
        fderiv ℝ (fderiv ℝ (differenceQuotient w (q • f) q)) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
      (∑ i, b i (x + q • f) * fderiv ℝ (differenceQuotient w (q • f) q) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)) +
      differenceQuotient w (q • f) q x = shiftedForcing w g a b f q x := by
  rw [fderiv_fderiv_differenceQuotient hw, fderiv_differenceQuotient hw]
  simp only [smul_apply, sub_apply, smul_eq_mul, shiftedForcing, differenceQuotient]
  have e : ∀ t : ℝ, q⁻¹ * t = t / q := fun t => by rw [div_eq_mul_inv, mul_comm]
  simp only [e]
  exact quotient_equation_algebra q (fun i j => a i j x) (fun i j => a i j (x + q • f))
    (fun i j => fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))
    (fun i j => fderiv ℝ (fderiv ℝ w) (x + q • f) (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j))
    (fun i => b i x) (fun i => b i (x + q • f))
    (fun i => fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i))
    (fun i => fderiv ℝ w (x + q • f) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (w x) (w (x + q • f)) (g x) (g (x + q • f)) h1 h2

end DifferenceQuotients

section BallStep

set_option maxHeartbeats 1600000 in
/-- **One Schauder step for a linear equation with `C^{1,α}` data on a ball** (Gilbarg–Trudinger,
Classics 2001, Lemma 17.16 method with Theorem 6.2). Let `n ≥ 2`, `0 < α < 1`, `0 < λ ≤ Λ`,
`S > 0` and caps `Ka, Kb, Kg, Nw ≥ 0`. There are `R > 0` and `Kc ≥ 0`, chosen before the centre
and the functions, such that for every centre `c`, every `C²` function `w`, `C¹` coefficients
`a`, `b` and `C¹` forcing `g` with, on `closedBall c S`: `a` symmetric and `(λ, Λ)`-elliptic,
`‖D aⁱʲ‖ ≤ Ka` and `[D aⁱʲ]_α ≤ Ka`, `|bⁱ| ≤ Kb`, `‖D bⁱ‖ ≤ Kb`, `[D bⁱ]_α ≤ Kb`, `‖D g‖ ≤ Kg`,
`[D g]_α ≤ Kg`, `‖D w‖ ≤ Nw`, `‖D² w‖ ≤ Nw`, `[D² w]_α ≤ Nw`, and the equation
`Σ aⁱʲ D_{ij} w + Σ bⁱ D_i w + w = g`: `w` is `C³` on `ball c R` with third derivative bounded by
`Kc` and `α`-Hölder with constant `Kc` there. -/
theorem contDiffOn_three_ball_of_linear_equation (hn : 2 ≤ n) {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α < 1) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) {S : ℝ} (hS : 0 < S)
    {Ka Kb Kg Nw : ℝ} (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKg : 0 ≤ Kg) (hNw : 0 ≤ Nw) :
    ∃ R Kc : ℝ, 0 < R ∧ 0 ≤ Kc ∧
    ∀ (c : E) (w g : E → ℝ) (a : Fin n → Fin n → E → ℝ) (b : Fin n → E → ℝ),
      ContDiff ℝ 2 w → (∀ i j, ContDiff ℝ 1 (a i j)) → (∀ i, ContDiff ℝ 1 (b i)) →
      ContDiff ℝ 1 g →
      (∀ x ∈ closedBall c S, ∀ i j, a i j x = a j i x) →
      (∀ x ∈ closedBall c S, ∀ ξ : E,
        lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j ∧
          ∑ i, ∑ j, a i j x * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, ∀ x ∈ closedBall c S, ‖fderiv ℝ (a i j) x‖ ≤ Ka) →
      (∀ i j, ∀ x ∈ closedBall c S, ∀ y ∈ closedBall c S,
        ‖fderiv ℝ (a i j) x - fderiv ℝ (a i j) y‖ ≤ Ka * ‖x - y‖ ^ (α:ℝ)) →
      (∀ i, ∀ x ∈ closedBall c S, |b i x| ≤ Kb) →
      (∀ i, ∀ x ∈ closedBall c S, ‖fderiv ℝ (b i) x‖ ≤ Kb) →
      (∀ i, ∀ x ∈ closedBall c S, ∀ y ∈ closedBall c S,
        ‖fderiv ℝ (b i) x - fderiv ℝ (b i) y‖ ≤ Kb * ‖x - y‖ ^ (α:ℝ)) →
      (∀ x ∈ closedBall c S, ‖fderiv ℝ g x‖ ≤ Kg) →
      (∀ x ∈ closedBall c S, ∀ y ∈ closedBall c S,
        ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ Kg * ‖x - y‖ ^ (α:ℝ)) →
      (∀ x ∈ closedBall c S, ‖fderiv ℝ w x‖ ≤ Nw) →
      (∀ x ∈ closedBall c S, ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ Nw) →
      (∀ x ∈ closedBall c S, ∀ y ∈ closedBall c S,
        ‖fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) y‖ ≤ Nw * ‖x - y‖ ^ (α:ℝ)) →
      (∀ x ∈ closedBall c S, (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ w) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
          (∑ i, b i x * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) + w x = g x) →
      ContDiffOn ℝ 3 w (ball c R) ∧
        (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x‖ ≤ Kc) ∧
        ∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ w)) y‖ ≤
            Kc * ‖x - y‖ ^ (α:ℝ) := by
  have hαr : (0:ℝ) < α := hα0
  have hα1r : (α:ℝ) ≤ 1 := by exact_mod_cast hα1.le
  -- the radii and the caps
  set R : ℝ := min (S / 4) 1 with hR_def
  have hR : 0 < R := lt_min (by positivity) one_pos
  have hR1 : R ≤ 1 := min_le_right _ _
  have hRS : R ≤ S / 4 := min_le_left _ _
  set q₀ : ℝ := S / 2 with hq₀_def
  have hq₀ : 0 < q₀ := by positivity
  set D : ℝ := (2 * S) ^ (1 - (α:ℝ)) with hD_def
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  set K : ℝ := Ka * D with hK_def
  set Kb' : ℝ := Kb * (1 + D) with hKb'_def
  set V : ℝ := Nw with hV_def
  set M : ℝ := Kg + (n:ℝ) ^ 2 * (Ka * Nw) + (n:ℝ) * (Kb * Nw) with hM_def
  set H0 : ℝ := Kg + (n:ℝ) ^ 2 * (Ka * Nw + Ka * Nw) + (n:ℝ) * (Kb * Nw + Kb * (Nw * D))
    with hH0_def
  have hH0 : 0 ≤ H0 := by positivity
  set H : ℝ≥0 := Real.toNNReal H0 with hH_def
  obtain ⟨C, hC, hstep⟩ := contDiffOn_three_of_quotient_equations hn hα0 hα1 hlam hLam
    (K := K) (Kb := Kb') (by positivity) (by positivity)
  refine ⟨R, C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H), hR, by positivity, ?_⟩
  intro c w g a b hw ha hb hg hsymm hell haN hahol hbN hbdN hbhol hgN hghol hwN hw2N hw2hol heq
  -- memberships
  have hsub2 : closedBall c (2 * R) ⊆ closedBall c S :=
    closedBall_subset_closedBall (by linarith)
  have hsub3 : closedBall c (2 * R + q₀) ⊆ closedBall c S :=
    closedBall_subset_closedBall (by linarith)
  have hshift : ∀ (f : E), ‖f‖ = 1 → ∀ (q : ℝ), 0 < q → q ≤ q₀ →
      ∀ x ∈ closedBall c (2 * R), x + q • f ∈ closedBall c (2 * R + q₀) := by
    intro f hf q hq hqq x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    calc ‖x + q • f - c‖ = ‖(x - c) + q • f‖ := by congr 1; abel
      _ ≤ ‖x - c‖ + ‖q • f‖ := norm_add_le _ _
      _ ≤ 2 * R + q₀ := by
          rw [norm_smul, hf, mul_one, Real.norm_eq_abs, abs_of_pos hq]
          linarith
  -- Lipschitz-to-Hölder on the data ball
  have hlipHol : ∀ (h : E → ℝ) (N : ℝ), 0 ≤ N → Differentiable ℝ h →
      (∀ z ∈ closedBall c S, ‖fderiv ℝ h z‖ ≤ N) →
      ∀ x ∈ closedBall c S, ∀ y ∈ closedBall c S, |h x - h y| ≤ N * D * ‖x - y‖ ^ (α:ℝ) := by
    intro h N hN hh hhN x hx y hy
    have h1 := norm_sub_le_of_fderiv_bound_closedBall hh hhN hx hy
    rw [Real.norm_eq_abs] at h1
    have h2 := le_rpow_one_sub_mul_rpow (norm_nonneg (x - y))
      (norm_sub_le_two_mul_of_mem_closedBall hx hy) hα1r
    calc |h x - h y| ≤ N * ‖x - y‖ := h1
      _ ≤ N * (D * ‖x - y‖ ^ (α:ℝ)) := mul_le_mul_of_nonneg_left h2 hN
      _ = N * D * ‖x - y‖ ^ (α:ℝ) := by ring
  -- entry bounds of the Hessian and the gradient of `w`
  have hWN : ∀ x ∈ closedBall c S, ∀ i j, |fderiv ℝ (fderiv ℝ w) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ Nw :=
    fun x hx i j => (abs_apply_basisFun_le_opNorm _ i j).trans (hw2N x hx)
  have hWhol : ∀ x ∈ closedBall c S, ∀ y ∈ closedBall c S, ∀ i j,
      |fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j) -
        fderiv ℝ (fderiv ℝ w) y (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ Nw * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy i j
    have := abs_apply_basisFun_le_opNorm (fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) y) i j
    rw [sub_apply, sub_apply] at this
    exact this.trans (hw2hol x hx y hy)
  have hVN : ∀ x ∈ closedBall c S, ∀ i,
      |fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ Nw :=
    fun x hx i => (abs_apply_basisFun_le_opNorm' _ i).trans (hwN x hx)
  have hVhol : ∀ x ∈ closedBall c S, ∀ y ∈ closedBall c S, ∀ i,
      |fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) -
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ Nw * D * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy i
    have h1 := abs_apply_basisFun_le_opNorm' (fderiv ℝ w x - fderiv ℝ w y) i
    rw [sub_apply] at h1
    have hwd : Differentiable ℝ (fderiv ℝ w) :=
      (hw.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have h2 := norm_sub_le_of_fderiv_bound_closedBall hwd hw2N hx hy
    have h3 := le_rpow_one_sub_mul_rpow (norm_nonneg (x - y))
      (norm_sub_le_two_mul_of_mem_closedBall hx hy) hα1r
    calc |fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)|
        ≤ ‖fderiv ℝ w x - fderiv ℝ w y‖ := h1
      _ ≤ Nw * ‖x - y‖ := h2
      _ ≤ Nw * (D * ‖x - y‖ ^ (α:ℝ)) := mul_le_mul_of_nonneg_left h3 hNw
      _ = Nw * D * ‖x - y‖ ^ (α:ℝ) := by ring
  -- the uniform quotient equations
  have hUQE : UniformQuotientEquations α lam Lam K Kb' c R w q₀ V M H := by
    intro f hf q hq hqq
    have hmem : ∀ x ∈ closedBall c (2 * R), x + q • f ∈ closedBall c S :=
      fun x hx => hsub3 (hshift f hf q hq hqq x hx)
    have hmemS : ∀ x ∈ closedBall c (2 * R), x ∈ closedBall c S := fun x hx => hsub2 hx
    have hshiftsub : ∀ x ∈ closedBall c (2 * R), ∀ y ∈ closedBall c (2 * R),
        (x + q • f) - (y + q • f) = x - y := fun x _ y _ => by abel
    -- the step range for the Hölder bounds of the quotients: `2R + q₀ ≤ S`
    have hS' : 2 * R + q₀ ≤ S := by linarith
    refine ⟨fun i j x => a i j (x + q • f), fun i x => b i (x + q • f),
      shiftedForcing w g a b f q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx i j
      exact hsymm _ (hmem x hx) i j
    · intro x hx ξ
      exact hell _ (hmem x hx) ξ
    · intro i j x hx y hy
      have := hlipHol (a i j) Ka hKa ((ha i j).differentiable one_ne_zero) (haN i j) _ (hmem x hx) _
        (hmem y hy)
      rwa [hshiftsub x hx y hy] at this
    · intro i x hx
      exact (hbN i _ (hmem x hx)).trans (by rw [hKb'_def]; nlinarith)
    · intro i x hx y hy
      have := hlipHol (b i) Kb hKb ((hb i).differentiable one_ne_zero) (hbdN i) _ (hmem x hx) _
        (hmem y hy)
      rw [hshiftsub x hx y hy] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      rw [hKb'_def]; nlinarith
    · intro x hx
      exact shifted_quotient_equation hw f q x (heq _ (hmem x hx)) (heq _ (hmemS x hx))
    · intro x hx
      exact abs_differenceQuotient_le_of_fderiv_bound (hw.differentiable (by norm_num)) hwN hf hq
        (hmemS x hx) (hmem x hx)
    · intro x hx
      unfold shiftedForcing
      have hg1 := abs_differenceQuotient_le_of_fderiv_bound (hg.differentiable one_ne_zero) hgN hf hq
        (hmemS x hx) (hmem x hx)
      have ha1 : ∀ i j, |differenceQuotient (a i j) (q • f) q x *
          fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ Ka * Nw := by
        intro i j
        rw [abs_mul]
        exact mul_le_mul (abs_differenceQuotient_le_of_fderiv_bound
          ((ha i j).differentiable one_ne_zero) (haN i j) hf hq (hmemS x hx) (hmem x hx))
          (hWN x (hmemS x hx) i j) (abs_nonneg _) hKa
      have hb1 : ∀ i, |differenceQuotient (b i) (q • f) q x *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ Kb * Nw := by
        intro i
        rw [abs_mul]
        exact mul_le_mul (abs_differenceQuotient_le_of_fderiv_bound
          ((hb i).differentiable one_ne_zero) (hbdN i) hf hq (hmemS x hx) (hmem x hx))
          (hVN x (hmemS x hx) i) (abs_nonneg _) hKb
      have hsa : |∑ i, ∑ j, differenceQuotient (a i j) (q • f) q x *
          fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤ (n:ℝ) ^ 2 * (Ka * Nw) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => ha1 i j)).trans ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply le_of_eq; ring
      have hsb : |∑ i, differenceQuotient (b i) (q • f) q x *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ (n:ℝ) * (Kb * Nw) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => hb1 i).trans ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact le_rfl
      rw [hM_def]
      calc |differenceQuotient g (q • f) q x -
            (∑ i, ∑ j, differenceQuotient (a i j) (q • f) q x *
              fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
                (EuclideanSpace.basisFun (Fin n) ℝ j)) -
            (∑ i, differenceQuotient (b i) (q • f) q x *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i))|
          ≤ |differenceQuotient g (q • f) q x| +
            |∑ i, ∑ j, differenceQuotient (a i j) (q • f) q x *
              fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
                (EuclideanSpace.basisFun (Fin n) ℝ j)| +
            |∑ i, differenceQuotient (b i) (q • f) q x *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)| := by
            refine (abs_sub _ _).trans ?_
            linarith [abs_sub (differenceQuotient g (q • f) q x)
              (∑ i, ∑ j, differenceQuotient (a i j) (q • f) q x *
                fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
                  (EuclideanSpace.basisFun (Fin n) ℝ j))]
        _ ≤ Kg + (n:ℝ) ^ 2 * (Ka * Nw) + (n:ℝ) * (Kb * Nw) := by linarith
    · -- Hölder bound of the shifted forcing
      refine holderOnWith_of_dist_le hH0 fun x hx y hy => ?_
      rw [Real.dist_eq, dist_eq_norm]
      unfold shiftedForcing
      have hpow : 0 ≤ ‖x - y‖ ^ (α:ℝ) := by positivity
      have hg1 := abs_differenceQuotient_sub_le_of_fderiv_holder (hg.differentiable one_ne_zero)
        hS' hghol hf hq hqq hx hy
      have ha1 : ∀ i j, |differenceQuotient (a i j) (q • f) q x *
          fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j) -
          differenceQuotient (a i j) (q • f) q y *
          fderiv ℝ (fderiv ℝ w) y (EuclideanSpace.basisFun (Fin n) ℝ i)
            (EuclideanSpace.basisFun (Fin n) ℝ j)| ≤
          (Ka * Nw + Ka * Nw) * ‖x - y‖ ^ (α:ℝ) := by
        intro i j
        set P := differenceQuotient (a i j) (q • f) q x
        set P' := differenceQuotient (a i j) (q • f) q y
        set Q := fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)
        set Q' := fderiv ℝ (fderiv ℝ w) y (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)
        have hP := abs_differenceQuotient_sub_le_of_fderiv_holder
          ((ha i j).differentiable one_ne_zero) hS' (hahol i j) hf hq hqq hx hy
        have hP' := abs_differenceQuotient_le_of_fderiv_bound ((ha i j).differentiable one_ne_zero)
          (haN i j) hf hq (hmemS y hy) (hmem y hy)
        have hQ := hWN x (hmemS x hx) i j
        have hQQ := hWhol x (hmemS x hx) y (hmemS y hy) i j
        have e : P * Q - P' * Q' = (P - P') * Q + P' * (Q - Q') := by ring
        rw [e]
        calc |(P - P') * Q + P' * (Q - Q')| ≤ |(P - P') * Q| + |P' * (Q - Q')| := abs_add_le _ _
          _ = |P - P'| * |Q| + |P'| * |Q - Q'| := by rw [abs_mul, abs_mul]
          _ ≤ (Ka * ‖x - y‖ ^ (α:ℝ)) * Nw + Ka * (Nw * ‖x - y‖ ^ (α:ℝ)) := by
              gcongr
          _ = (Ka * Nw + Ka * Nw) * ‖x - y‖ ^ (α:ℝ) := by ring
      have hb1 : ∀ i, |differenceQuotient (b i) (q • f) q x *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          differenceQuotient (b i) (q • f) q y *
          fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
          (Kb * Nw + Kb * (Nw * D)) * ‖x - y‖ ^ (α:ℝ) := by
        intro i
        set P := differenceQuotient (b i) (q • f) q x
        set P' := differenceQuotient (b i) (q • f) q y
        set Q := fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)
        set Q' := fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)
        have hP := abs_differenceQuotient_sub_le_of_fderiv_holder
          ((hb i).differentiable one_ne_zero) hS' (hbhol i) hf hq hqq hx hy
        have hP' := abs_differenceQuotient_le_of_fderiv_bound ((hb i).differentiable one_ne_zero)
          (hbdN i) hf hq (hmemS y hy) (hmem y hy)
        have hQ := hVN x (hmemS x hx) i
        have hQQ := hVhol x (hmemS x hx) y (hmemS y hy) i
        have e : P * Q - P' * Q' = (P - P') * Q + P' * (Q - Q') := by ring
        rw [e]
        calc |(P - P') * Q + P' * (Q - Q')| ≤ |(P - P') * Q| + |P' * (Q - Q')| := abs_add_le _ _
          _ = |P - P'| * |Q| + |P'| * |Q - Q'| := by rw [abs_mul, abs_mul]
          _ ≤ (Kb * ‖x - y‖ ^ (α:ℝ)) * Nw + Kb * (Nw * D * ‖x - y‖ ^ (α:ℝ)) := by
              gcongr
          _ = (Kb * Nw + Kb * (Nw * D)) * ‖x - y‖ ^ (α:ℝ) := by ring
      have hsa : |(∑ i, ∑ j, differenceQuotient (a i j) (q • f) q x *
            fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
              (EuclideanSpace.basisFun (Fin n) ℝ j)) -
          (∑ i, ∑ j, differenceQuotient (a i j) (q • f) q y *
            fderiv ℝ (fderiv ℝ w) y (EuclideanSpace.basisFun (Fin n) ℝ i)
              (EuclideanSpace.basisFun (Fin n) ℝ j))| ≤
          (n:ℝ) ^ 2 * (Ka * Nw + Ka * Nw) * ‖x - y‖ ^ (α:ℝ) := by
        rw [← Finset.sum_sub_distrib]
        simp_rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => ha1 i j)).trans ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply le_of_eq; ring
      have hsb : |(∑ i, differenceQuotient (b i) (q • f) q x *
            fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) -
          (∑ i, differenceQuotient (b i) (q • f) q y *
            fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i))| ≤
          (n:ℝ) * (Kb * Nw + Kb * (Nw * D)) * ‖x - y‖ ^ (α:ℝ) := by
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => hb1 i).trans ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        apply le_of_eq; ring
      set Gx := differenceQuotient g (q • f) q x
      set Gy := differenceQuotient g (q • f) q y
      set Ax := ∑ i, ∑ j, differenceQuotient (a i j) (q • f) q x *
        fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)
      set Ay := ∑ i, ∑ j, differenceQuotient (a i j) (q • f) q y *
        fderiv ℝ (fderiv ℝ w) y (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)
      set Bx := ∑ i, differenceQuotient (b i) (q • f) q x *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)
      set By := ∑ i, differenceQuotient (b i) (q • f) q y *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)
      have e : Gx - Ax - Bx - (Gy - Ay - By) = (Gx - Gy) - (Ax - Ay) - (Bx - By) := by ring
      rw [e, hH0_def]
      calc |(Gx - Gy) - (Ax - Ay) - (Bx - By)| ≤ |Gx - Gy| + |Ax - Ay| + |Bx - By| := by
            have h1 := abs_sub ((Gx - Gy) - (Ax - Ay)) (Bx - By)
            have h2 := abs_sub (Gx - Gy) (Ax - Ay)
            linarith
        _ ≤ Kg * ‖x - y‖ ^ (α:ℝ) + (n:ℝ) ^ 2 * (Ka * Nw + Ka * Nw) * ‖x - y‖ ^ (α:ℝ) +
            (n:ℝ) * (Kb * Nw + Kb * (Nw * D)) * ‖x - y‖ ^ (α:ℝ) := by linarith
        _ = (Kg + (n:ℝ) ^ 2 * (Ka * Nw + Ka * Nw) + (n:ℝ) * (Kb * Nw + Kb * (Nw * D))) *
            ‖x - y‖ ^ (α:ℝ) := by ring
  -- the one-step gain
  exact hstep c R hR hR1 w hw q₀ Nw hq₀ hNw
    (fun x hx y hy => hw2hol x (hsub3 hx) y (hsub3 hy)) V M H hUQE

end BallStep

section DirectionalEquation

/-- Derivative of a Hessian entry: `D (y ↦ D²w(y)(e₁, e₂)) x f = D³w(x)(f, e₁, e₂)` at points
where the Hessian is differentiable. -/
theorem fderiv_hessian_entry_apply {w : E → ℝ} {x : E}
    (hx : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ w)) x) (e₁ e₂ f : E) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ w) y e₁ e₂) x f =
      fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x f e₁ e₂ := by
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ w) y e₁) x :=
    hx.clm_apply (differentiableAt_const e₁)
  rw [fderiv_clm_apply h1 (differentiableAt_const e₂)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_const_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  rw [fderiv_clm_apply hx (differentiableAt_const e₁)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, fderiv_const_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]

/-- Derivative of a gradient entry: `D (y ↦ D w (y) e) x f = D²w(x)(e, f)` for a `C²` function. -/
theorem fderiv_gradient_entry_apply {w : E → ℝ} (hw : ContDiff ℝ 2 w) (e f x : E) :
    fderiv ℝ (fun y => fderiv ℝ w y e) x f = fderiv ℝ (fderiv ℝ w) x e f := by
  rw [fderiv_directional_eq hw]

/-- **The differentiated linear equation.** If `w` is `C³`, `a`, `b` are differentiable and
`Σ aⁱʲ D_{ij} w + Σ bⁱ D_i w + w = g` holds everywhere, then for every direction `f` the
directional derivative `D_f w` solves
`Σ aⁱʲ D_{ij}(D_f w) + Σ bⁱ D_i (D_f w) + D_f w = D_f g − Σ (D_f aⁱʲ) D_{ij} w − Σ (D_f bⁱ) D_i w`. -/
theorem directional_linear_equation {w g : E → ℝ} {a : Fin n → Fin n → E → ℝ}
    {b : Fin n → E → ℝ} (hw : ContDiff ℝ 3 w) (ha : ∀ i j, Differentiable ℝ (a i j))
    (hb : ∀ i, Differentiable ℝ (b i))
    (heq : ∀ x, (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
        (∑ i, b i x * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) + w x = g x)
    (f x : E) :
    (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ w y f)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
      (∑ i, b i x * fderiv ℝ (fun y => fderiv ℝ w y f) x (EuclideanSpace.basisFun (Fin n) ℝ i)) +
      fderiv ℝ w x f =
      fderiv ℝ g x f -
        (∑ i, ∑ j, fderiv ℝ (a i j) x f * fderiv ℝ (fderiv ℝ w) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) -
        (∑ i, fderiv ℝ (b i) x f * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  have hw2 : ContDiff ℝ 2 w := hw.of_le (by norm_num)
  have hD1 : ContDiff ℝ 2 (fderiv ℝ w) := hw.fderiv_right (by norm_num)
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ w)) := hD1.fderiv_right (by norm_num)
  have hD2d : Differentiable ℝ (fderiv ℝ (fderiv ℝ w)) := hD2.differentiable one_ne_zero
  have hD1d : Differentiable ℝ (fderiv ℝ w) := hD1.differentiable (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  -- the function identity
  have hΦ : (fun y => (∑ i, ∑ j, a i j y * fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
      (∑ i, b i y * fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) + w y) = g :=
    funext heq
  -- differentiability of the pieces
  have hWd : ∀ i j, DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x :=
    fun i j => ((hD2d x).clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
  have hVd : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ w y
      (EuclideanSpace.basisFun (Fin n) ℝ i)) x :=
    fun i => (hD1d x).clm_apply (differentiableAt_const _)
  have hAd : ∀ i j, DifferentiableAt ℝ (fun y => a i j y * fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x :=
    fun i j => (ha i j x).mul (hWd i j)
  have hBd : ∀ i, DifferentiableAt ℝ (fun y => b i y * fderiv ℝ w y
      (EuclideanSpace.basisFun (Fin n) ℝ i)) x :=
    fun i => (hb i x).mul (hVd i)
  have hSAd : ∀ i, DifferentiableAt ℝ (fun y => ∑ j, a i j y * fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x :=
    fun i => DifferentiableAt.fun_sum fun j _ => hAd i j
  have hSA : DifferentiableAt ℝ (fun y => ∑ i, ∑ j, a i j y * fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x :=
    DifferentiableAt.fun_sum fun i _ => hSAd i
  have hSB : DifferentiableAt ℝ (fun y => ∑ i, b i y * fderiv ℝ w y
      (EuclideanSpace.basisFun (Fin n) ℝ i)) x :=
    DifferentiableAt.fun_sum fun i _ => hBd i
  -- differentiate the identity at `x` in direction `f`
  have hder := congrArg (fun φ => fderiv ℝ φ x f) hΦ
  have hSAB : DifferentiableAt ℝ (fun y => (∑ i, ∑ j, a i j y * fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
      (∑ i, b i y * fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i))) x := hSA.add hSB
  rw [fderiv_fun_add hSAB (hwd x), fderiv_fun_add hSA hSB, fderiv_fun_sum fun i _ => hSAd i,
    fderiv_fun_sum fun i _ => hBd i] at hder
  simp only [add_apply, sum_apply] at hder
  have hsym3 : IsSymmSndFDerivAt ℝ (fderiv ℝ w) x := hD1.contDiffAt.isSymmSndFDerivAt (by simp)
  have hsym2 : IsSymmSndFDerivAt ℝ w x := hw2.contDiffAt.isSymmSndFDerivAt (by simp)
  have hder2 : ∀ i, fderiv ℝ (fun y => ∑ j, a i j y * fderiv ℝ (fderiv ℝ w) y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x f =
      ∑ j, (a i j x * fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x f (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) +
        fderiv ℝ (a i j) x f * fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    intro i
    rw [fderiv_fun_sum fun j _ => hAd i j, sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fderiv_fun_mul (ha i j x) (hWd i j), add_apply, smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul, fderiv_hessian_entry_apply (hD2d x)]
    ring
  have hder3 : ∀ i, fderiv ℝ (fun y => b i y * fderiv ℝ w y
      (EuclideanSpace.basisFun (Fin n) ℝ i)) x f =
      b i x * fderiv ℝ (fderiv ℝ w) x f (EuclideanSpace.basisFun (Fin n) ℝ i) +
        fderiv ℝ (b i) x f * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    intro i
    rw [fderiv_fun_mul (hb i x) (hVd i), add_apply, smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul, fderiv_gradient_entry_apply hw2, hsym2 (EuclideanSpace.basisFun (Fin n) ℝ i) f]
    ring
  simp only [hder2, hder3, Finset.sum_add_distrib] at hder
  -- rewrite the left-hand side through the symmetry of the derivatives
  have hL1 : ∀ i j, fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ w y f)) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
      fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x f (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    intro i j
    rw [fderiv_fderiv_directional_apply hw2 (hD2d x)]
    exact congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin n) ℝ j)) (hsym3 _ f)
  have hL2 : ∀ i, fderiv ℝ (fun y => fderiv ℝ w y f) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      fderiv ℝ (fderiv ℝ w) x f (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    intro i
    rw [fderiv_gradient_entry_apply hw2]
  simp only [hL1, hL2]
  linear_combination hder

end DirectionalEquation

end FunctionalInequalities.Analysis
