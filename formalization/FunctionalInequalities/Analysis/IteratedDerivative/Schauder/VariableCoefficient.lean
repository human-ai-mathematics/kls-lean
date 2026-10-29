import FunctionalInequalities.Analysis.IteratedDerivative.Schauder.ConstantCoefficient
import FunctionalInequalities.Analysis.IteratedDerivative.Schauder.CoefficientCoordinates
import FunctionalInequalities.Analysis.Iteration.Absorption
import FunctionalInequalities.Analysis.Newtonian.Schauder.KernelBounds

/-!
# Interior a priori Schauder estimate for variable Hölder coefficients (GT Theorem 6.2)

Theorem 6.2 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Classics 2001 (ISBN 3-540-41160-7), pp. 90–92, in its a priori ball form with the Hessian taken as
the nested Fréchet derivative `fderiv ℝ (fderiv ℝ ·)`. For `n ≥ 2`, `0 < α < 1`, ellipticity
constants `0 < λ ≤ Λ` and Hölder bounds `K`, `Kb` of the coefficients,
`variable_coefficient_interior_hessian_holder` gives one constant `C(n, α, λ, Λ, K, Kb) > 0`,
chosen before the centre `c`, the radius `R ≤ 1`, the coefficients and the data, such that every
`C²` solution `v` of `Σ_{ij} aⁱʲ D_{ij} v + Σ_i bⁱ D_i v + v = g` on `closedBall c (2R)` with
symmetric, `(λ, Λ)`-elliptic, `(K, α)`-Hölder principal coefficients, `|bⁱ| ≤ Kb`,
`[bⁱ]_α ≤ Kb`, `|v| ≤ V`, `|g| ≤ M`, `[g]_α ≤ H`, and a finite Hessian bound and Hessian Hölder
bound on `closedBall c (2R)`, satisfies on `ball c R`
`‖D²v‖ ≤ C (V R⁻² + M + H)` and `‖D²v(x) - D²v(y)‖ ≤ C (V R^(-2-α) + M R^(-α) + H) ‖x - y‖^α`.
The finite a priori bounds `N`, `N2` of the Hessian enter only as hypotheses, never the constant.

The proof follows GT pp. 90–92 in the ball/absorption form. For `0 < r ≤ 2R` let `T(r)` be the
`α`-Hölder seminorm of `D²v` on `closedBall c r` (`hessianHolderSeminorm`). For `x₀ ∈ closedBall c r`
and a small radius `ρ` the coefficients are frozen at `x₀` (`freezing_step`): `v` solves the
constant-coefficient equation `Σ_{ij} aⁱʲ(x₀) D_{ij} v = F` on `ball x₀ (2ρ)` with
`F = g - v - Σ_i bⁱ D_i v + (Σ_{ij} (aⁱʲ(x₀) - aⁱʲ) D_{ij} v)`; the sup and Hölder bounds of `F`
come from the data, the gradient bounds `gradient_bound_of_hessian` and
`gradient_lipschitz_of_hessian`, and the freezing error bounds `euclidean_freezing_bounds`, and GT
Lemma 6.1 (`constant_coefficient_interior_hessian_holder`) bounds the Hölder quotient of `D²v` at
pairs closer than `ρ`. Farther pairs are bounded by twice the sup of `‖D²v‖`, and every sup of
`‖D²v‖` is interpolated between `V` and `T(r')` (`exists_hessian_interpolation_constant`), so
that `T(r) ≤ ½ T(r') + Γ_V V ρ^(-2-α) + C₀ M ρ^(-α) + C₀ H` (`seminorm_recursion`) once `ρ` is
below a threshold `ρ₀(n, α, λ, Λ, K, Kb)`. With `ρ = min(ρ₀, (r' - r)/8)`, the radius absorption
lemma `exists_absorption_constant` applied to `r ↦ r^(2+α) T(r)` on `(0, 2R]` bounds
`T(3R/2)`, and one more interpolation gives the sup bound on `ball c R`.

Scope: the coefficient hypotheses are pointwise on the closed ball `closedBall c (2R)`; the
equation is pointwise there; the estimate is on the open ball `ball c R` with the operator norm of
the nested Hessian; `0 < α < 1`, `0 < R ≤ 1` (`R ≤ 1` is used to absorb powers of `R` and of
`ρ₀` into the constant). The lower-order term `v` has coefficient one and the first-order
coefficients are bounded and Hölder with the same constant `Kb`. The global weighted interior
norms of GT (6.14)–(6.16), the case `α = 1`, boundary estimates and the existence theory are not
claimed. The constant is coarse and only its dependence on `(n, α, λ, Λ, K, Kb)` is recorded.
-/

noncomputable section

open Set Metric
open scoped Topology ContDiff NNReal

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `0 < α ≤ 1` and `0 ≤ t ≤ 4`, `t ≤ 4 t^α`: distances below `4` are dominated by their
`α`-th power. -/
private theorem le_four_mul_rpow {t α : ℝ} (ht0 : 0 ≤ t) (ht4 : t ≤ 4) (hα0 : 0 < α)
    (hα1 : α ≤ 1) : t ≤ 4 * t ^ α := by
  have hp : 0 ≤ t ^ α := Real.rpow_nonneg ht0 _
  by_cases h1 : t ≤ 1
  · have := Real.self_le_rpow_of_le_one ht0 h1 hα1
    linarith
  · have h1' : 1 ≤ t := (not_le.mp h1).le
    have := Real.one_le_rpow h1' hα0.le
    linarith

/-- The gradient of a `C²` function is Lipschitz on a convex set with the sup of the Hessian as
constant. -/
private theorem gradient_lipschitz_of_hessian {v : E → ℝ} (hv : ContDiff ℝ 2 v) {s : Set E}
    (hs : Convex ℝ s) {S : ℝ} (hS : ∀ z ∈ s, ‖fderiv ℝ (fderiv ℝ v) z‖ ≤ S)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖fderiv ℝ v y - fderiv ℝ v x‖ ≤ S * ‖y - x‖ := by
  have hd : ∀ z ∈ s, DifferentiableAt ℝ (fderiv ℝ v) z := fun z _ =>
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z
  exact hs.norm_image_sub_le_of_norm_fderiv_le hd hS hx hy

/-- Gradient bound by the values and the Hessian: if `|v| ≤ V` and `‖D²v‖ ≤ S` on
`closedBall x h`, then `‖Dv(x)‖ ≤ 2V/h + S h`. -/
private theorem gradient_bound_of_hessian {v : E → ℝ} (hv : ContDiff ℝ 2 v) {x : E} {h V S : ℝ}
    (hh : 0 < h) (hS0 : 0 ≤ S)
    (hV : ∀ z ∈ closedBall x h, |v z| ≤ V)
    (hS : ∀ z ∈ closedBall x h, ‖fderiv ℝ (fderiv ℝ v) z‖ ≤ S) :
    ‖fderiv ℝ v x‖ ≤ 2 * V / h + S * h := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV x (mem_closedBall_self hh.le))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro e he
  -- the auxiliary function `φ(z) = v z - Dv(x)(z - x)` has derivative `Dv z - Dv x`
  set φ : E → ℝ := fun z => v z - fderiv ℝ v x (z - x) with hφ
  have hdv : ∀ z, HasFDerivAt v (fderiv ℝ v z) z := fun z =>
    ((hv.differentiable (by norm_num)) z).hasFDerivAt
  have hφ' : ∀ z ∈ closedBall x h,
      HasFDerivWithinAt φ (fderiv ℝ v z - fderiv ℝ v x) (closedBall x h) z := by
    intro z _
    have h1 : HasFDerivAt (fun z : E => fderiv ℝ v x (z - x)) (fderiv ℝ v x) z := by
      have := (fderiv ℝ v x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)
      rwa [ContinuousLinearMap.comp_id] at this
    exact ((hdv z).sub h1).hasFDerivWithinAt
  have hbound : ∀ z ∈ closedBall x h, ‖fderiv ℝ v z - fderiv ℝ v x‖ ≤ S * h := by
    intro z hz
    have hzx : ‖z - x‖ ≤ h := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact (gradient_lipschitz_of_hessian hv (convex_closedBall x h) hS
      (mem_closedBall_self hh.le) hz).trans (mul_le_mul_of_nonneg_left hzx hS0)
  have hy : x + h • e ∈ closedBall x h := by
    simp [mem_closedBall, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hh, he]
  have hmv := (convex_closedBall x h).norm_image_sub_le_of_norm_hasFDerivWithin_le hφ' hbound
    (mem_closedBall_self hh.le) hy
  have hφx : φ x = v x := by simp [hφ]
  have hφy : φ (x + h • e) = v (x + h • e) - h * fderiv ℝ v x e := by
    simp [hφ, map_smul, smul_eq_mul]
  have hne : ‖x + h • e - x‖ = h := by
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hh, he]
  rw [hφy, hφx, hne, Real.norm_eq_abs] at hmv
  have hvx := hV x (mem_closedBall_self hh.le)
  have hvy := hV _ hy
  have hkey : h * |fderiv ℝ v x e| ≤ 2 * V + S * h * h := by
    have : |h * fderiv ℝ v x e| ≤ |v (x + h • e)| + |v x| + S * h * h := by
      calc |h * fderiv ℝ v x e|
          = |v (x + h • e) - v x - (v (x + h • e) - h * fderiv ℝ v x e - v x)| := by
            congr 1; ring
        _ ≤ |v (x + h • e) - v x| + |v (x + h • e) - h * fderiv ℝ v x e - v x| := abs_sub _ _
        _ ≤ (|v (x + h • e)| + |v x|) + S * h * h := add_le_add (abs_sub _ _) hmv
    rw [abs_mul, abs_of_pos hh] at this
    linarith
  rw [Real.norm_eq_abs]
  rw [show 2 * V / h + S * h = (2 * V + S * h * h) / h by field_simp]
  rw [le_div_iff₀ hh]
  linarith

/-- Sum bound: `|Σ_i g i| ≤ card ι · T` when every `|g i| ≤ T`. -/
private theorem abs_sum_le_card_mul {ι : Type*} [Fintype ι] (g : ι → ℝ) (T : ℝ)
    (hg : ∀ i, |g i| ≤ T) : |∑ i, g i| ≤ Fintype.card ι * T := by
  calc
    _ ≤ ∑ i, |g i| := by simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ g
    _ ≤ ∑ _i : ι, T := Finset.sum_le_sum fun i _ => hg i
    _ = _ := by simp

/-- The `α`-Hölder seminorm of the Hessian of `v` on `closedBall c r`: the supremum of the Hölder
quotients over pairs of distinct points of the ball (`0` if there are none). -/
private def hessianHolderSeminorm (v : E → ℝ) (α : ℝ) (c : E) (r : ℝ) : ℝ :=
  sSup ((fun p : E × E => ‖fderiv ℝ (fderiv ℝ v) p.1 - fderiv ℝ (fderiv ℝ v) p.2‖ /
      ‖p.1 - p.2‖ ^ α) '' {p | p.1 ∈ closedBall c r ∧ p.2 ∈ closedBall c r ∧ p.1 ≠ p.2})

private theorem hessianHolderSeminorm_nonneg (v : E → ℝ) (α : ℝ) (c : E) (r : ℝ) :
    0 ≤ hessianHolderSeminorm v α c r := by
  apply Real.sSup_nonneg
  rintro _ ⟨p, _, rfl⟩
  exact div_nonneg (ContinuousLinearMap.opNorm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- Every Hölder cap of the Hessian on the ball dominates the seminorm. -/
private theorem hessianHolderSeminorm_le {v : E → ℝ} {α : ℝ} {c : E} {r H' : ℝ} (hH' : 0 ≤ H')
    (h : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ H' * ‖x - y‖ ^ α) :
    hessianHolderSeminorm v α c r ≤ H' := by
  apply Real.sSup_le _ hH'
  rintro _ ⟨p, ⟨hp1, hp2, hne⟩, rfl⟩
  have hpos : 0 < ‖p.1 - p.2‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _
  rw [div_le_iff₀ hpos]
  exact h _ hp1 _ hp2

/-- If the Hessian has some finite Hölder cap on the ball, the seminorm is itself a cap. -/
private theorem le_hessianHolderSeminorm {v : E → ℝ} {α : ℝ} (hα : 0 < α) {c : E} {r N2 : ℝ}
    (hbdd : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ N2 * ‖x - y‖ ^ α)
    {x y : E} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤
      hessianHolderSeminorm v α c r * ‖x - y‖ ^ α := by
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self, sub_self, ContinuousLinearMap.opNorm_zero, norm_zero, Real.zero_rpow hα.ne',
      mul_zero]
  · have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    have hmem : ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ / ‖x - y‖ ^ α ∈
        (fun p : E × E => ‖fderiv ℝ (fderiv ℝ v) p.1 - fderiv ℝ (fderiv ℝ v) p.2‖ /
          ‖p.1 - p.2‖ ^ α) '' {p | p.1 ∈ closedBall c r ∧ p.2 ∈ closedBall c r ∧ p.1 ≠ p.2} :=
      ⟨(x, y), ⟨hx, hy, hxy⟩, rfl⟩
    have hbdd' : BddAbove ((fun p : E × E =>
        ‖fderiv ℝ (fderiv ℝ v) p.1 - fderiv ℝ (fderiv ℝ v) p.2‖ / ‖p.1 - p.2‖ ^ α) ''
          {p | p.1 ∈ closedBall c r ∧ p.2 ∈ closedBall c r ∧ p.1 ≠ p.2}) := by
      refine ⟨N2, ?_⟩
      rintro _ ⟨p, ⟨hp1, hp2, hne⟩, rfl⟩
      have hpos' : 0 < ‖p.1 - p.2‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _
      rw [div_le_iff₀ hpos']
      exact hbdd _ hp1 _ hp2
    have := le_csSup hbdd' hmem
    rwa [div_le_iff₀ hpos] at this

/-- The conclusion of `constant_coefficient_interior_hessian_holder` for a fixed constant `C₀`
(GT Lemma 6.1 in interior ball form). -/
private def ConstantCoefficientBound (n : ℕ) (α : ℝ≥0) (lam Lam C₀ : ℝ) : Prop :=
  ∀ (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
    (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j ∧
      ∑ i, ∑ j, A i j * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2) →
    ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
    ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ) (U M : ℝ) (H : ℝ≥0),
    ContDiffOn ℝ 2 u (ball c (2 * R)) →
    (∀ x ∈ ball c (2 * R), ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) = f x) →
    (∀ x ∈ ball c (2 * R), |u x| ≤ U) → (∀ y ∈ ball c (2 * R), |f y| ≤ M) →
    HolderOnWith H α f (ball c (2 * R)) →
    (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C₀ * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H)) ∧
    ∀ x ∈ ball c R, ∀ y ∈ ball c R,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        C₀ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ)

/-- **Freezing step on one small ball** (GT (6.17)–(6.19), p. 91). With the coefficients frozen
at `x₀`, `v` solves `Σ_{ij} aⁱʲ(x₀) D_{ij} v = F` on `ball x₀ (2ρ)` with
`F = g - v - Σ_i bⁱ D_i v + (Σ_{ij} (aⁱʲ(x₀) - aⁱʲ) D_{ij} v)`. Given a sup bound `S` of the Hessian
on `closedBall x₀ (4ρ)` and a Hölder cap `T'` on `closedBall x₀ (2ρ)`, the gradient is bounded by
`G = V/ρ + 2ρS`, `|F| ≤ MF` and `[F]_α ≤ HF` on `ball x₀ (2ρ)`, and GT Lemma 6.1 bounds the Hölder
quotient of `D²v` between `x₀` and the points of `ball x₀ ρ`. -/
private theorem freezing_step {n : ℕ} {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {lam Lam K Kb C₀ : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb)
    (hP : ConstantCoefficientBound n α lam Lam C₀)
    {c : EuclideanSpace ℝ (Fin n)} {Rd : ℝ}
    {a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hsymm : ∀ x ∈ closedBall c Rd, ∀ i j, a i j x = a j i x)
    (hell : ∀ x ∈ closedBall c Rd, ∀ ξ : EuclideanSpace ℝ (Fin n),
      lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j ∧
        ∑ i, ∑ j, a i j x * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2)
    (haH : ∀ i j, ∀ x ∈ closedBall c Rd, ∀ y ∈ closedBall c Rd,
      |a i j x - a i j y| ≤ K * ‖x - y‖ ^ (α:ℝ))
    (hb : ∀ i, ∀ x ∈ closedBall c Rd, |b i x| ≤ Kb)
    (hbH : ∀ i, ∀ x ∈ closedBall c Rd, ∀ y ∈ closedBall c Rd,
      |b i x - b i y| ≤ Kb * ‖x - y‖ ^ (α:ℝ))
    {v g : EuclideanSpace ℝ (Fin n) → ℝ} {V M : ℝ} {H : ℝ≥0} (hv : ContDiff ℝ 2 v)
    (heq : ∀ x ∈ closedBall c Rd, (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
        (∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) + v x = g x)
    (hV : ∀ x ∈ closedBall c Rd, |v x| ≤ V) (hM : ∀ x ∈ closedBall c Rd, |g x| ≤ M)
    (hH : HolderOnWith H α g (closedBall c Rd))
    {x₀ : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsub : closedBall x₀ (4 * ρ) ⊆ closedBall c Rd)
    {S T' : ℝ} (hS0 : 0 ≤ S) (hT0 : 0 ≤ T')
    (hS : ∀ z ∈ closedBall x₀ (4 * ρ), ‖fderiv ℝ (fderiv ℝ v) z‖ ≤ S)
    (hT : ∀ x ∈ closedBall x₀ (2 * ρ), ∀ y ∈ closedBall x₀ (2 * ρ),
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ T' * ‖x - y‖ ^ (α:ℝ))
    {G MF HF : ℝ} (hG : G = 2 * V / (2 * ρ) + S * (2 * ρ))
    (hMF : MF = M + V + n * (Kb * G) + (n:ℝ) ^ 2 * K * (2 * ρ) ^ (α:ℝ) * S)
    (hHF : HF = H + 4 * G + n * (Kb * G + Kb * (4 * S)) +
      (n:ℝ) ^ 2 * K * (S + (2 * ρ) ^ (α:ℝ) * T')) :
    ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (fderiv ℝ v) x₀ - fderiv ℝ (fderiv ℝ v) y‖ ≤
      C₀ * (V * ρ ^ (-(2:ℝ) - α) + MF * ρ ^ (-(α:ℝ)) + HF) * ‖x₀ - y‖ ^ (α:ℝ) := by
  intro y hy
  have hαr : (0:ℝ) < α := hα0
  have hα1r : (α:ℝ) ≤ 1 := by exact_mod_cast hα1.le
  -- geometry of the nested balls
  have h2sub : closedBall x₀ (2 * ρ) ⊆ closedBall x₀ (4 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hball : ball x₀ (2 * ρ) ⊆ closedBall x₀ (2 * ρ) := ball_subset_closedBall
  have hx₀ : x₀ ∈ closedBall c Rd := hsub (mem_closedBall_self (by linarith))
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV x₀ hx₀)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ hx₀)
  have hbasis : ∀ i, ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ = 1 :=
    (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one
  -- gradient bounds on the doubled ball
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have hgrad : ∀ x ∈ closedBall x₀ (2 * ρ), ‖fderiv ℝ v x‖ ≤ G := by
    intro x hx
    rw [hG]
    have hxs : closedBall x (2 * ρ) ⊆ closedBall x₀ (4 * ρ) :=
      closedBall_subset_closedBall' (by rw [mem_closedBall] at hx; linarith)
    exact gradient_bound_of_hessian hv (by positivity) hS0
      (fun z hz => hV z (hsub (hxs hz))) (fun z hz => hS z (hxs hz))
  have hgradL : ∀ x ∈ closedBall x₀ (2 * ρ), ∀ y ∈ closedBall x₀ (2 * ρ),
      ‖fderiv ℝ v x - fderiv ℝ v y‖ ≤ S * ‖x - y‖ := fun x hx y hy =>
    gradient_lipschitz_of_hessian hv (convex_closedBall _ _) (fun z hz => hS z (h2sub hz)) hy hx
  have hdist4 : ∀ x ∈ closedBall x₀ (2 * ρ), ∀ y ∈ closedBall x₀ (2 * ρ),
      ‖x - y‖ ≤ 4 * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy
    apply le_four_mul_rpow (norm_nonneg _) _ hαr hα1r
    have := dist_triangle_right x y x₀
    rw [mem_closedBall] at hx hy
    rw [← dist_eq_norm]
    linarith
  -- freezing error bounds
  obtain ⟨herr, herrH⟩ := euclidean_freezing_bounds (a := a) (u := v) (c := x₀) (r := 2 * ρ)
    (α := (α:ℝ)) (K := K) (N := S) (H := T') (by positivity) hαr.le hK
    (fun i j x hx y hy => haH i j x (hsub (h2sub hx)) y (hsub (h2sub hy)))
    (fun x hx => hS x (h2sub hx)) hT
  -- the frozen matrix
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => a i j x₀ with hA
  have hAsymm : A.IsSymm := Matrix.IsSymm.ext fun i j => by
    simp only [hA, Matrix.of_apply]
    exact hsymm x₀ hx₀ j i
  have hAell : ∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j ∧
      ∑ i, ∑ j, A i j * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2 := fun ξ => by
    simpa only [hA, Matrix.of_apply] using hell x₀ hx₀ ξ
  -- the frozen right-hand side
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ v) x
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) with hF
  have hFeq : ∀ x ∈ closedBall x₀ (2 * ρ), F x = g x - v x -
      (∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) +
      euclideanError a v x₀ x := by
    intro x hx
    have h := heq x (hsub (h2sub hx))
    rw [euclideanError_eq_sum]
    simp only [hF, hA, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib]
    linarith
  -- sup bound of `F`
  have hbsum : ∀ x ∈ closedBall x₀ (2 * ρ),
      |∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ n * (Kb * G) := by
    intro x hx
    have := abs_sum_le_card_mul (fun i => b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (Kb * G) (fun i => by
        rw [abs_mul]
        apply mul_le_mul (hb i x (hsub (h2sub hx))) _ (abs_nonneg _) hKb
        calc |fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)|
            = ‖fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ v x‖ * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ := (fderiv ℝ v x).le_opNorm _
          _ ≤ G := by rw [hbasis, mul_one]; exact hgrad x hx)
    rwa [Fintype.card_fin] at this
  have hFbound : ∀ x ∈ ball x₀ (2 * ρ), |F x| ≤ MF := by
    intro x hx
    have hx' := hball hx
    rw [hFeq x hx', hMF]
    calc |g x - v x - (∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) +
          euclideanError a v x₀ x|
        ≤ |g x - v x - (∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))| +
          |euclideanError a v x₀ x| := abs_add_le _ _
      _ ≤ (|g x - v x| + |∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)|) +
          |euclideanError a v x₀ x| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ ((|g x| + |v x|) + |∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)|) +
          |euclideanError a v x₀ x| := add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
      _ ≤ ((M + V) + n * (Kb * G)) + (n:ℝ) ^ 2 * K * (2 * ρ) ^ (α:ℝ) * S :=
          add_le_add (add_le_add (add_le_add (hM x (hsub (h2sub hx'))) (hV x (hsub (h2sub hx'))))
            (hbsum x hx')) (herr x hx')
  -- Hölder bound of `F`
  have hFholder : ∀ x ∈ ball x₀ (2 * ρ), ∀ y ∈ ball x₀ (2 * ρ),
      |F x - F y| ≤ HF * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy
    have hx' := hball hx
    have hy' := hball hy
    have hxd := hsub (h2sub hx')
    have hyd := hsub (h2sub hy')
    rw [hFeq x hx', hFeq y hy', hHF]
    have hg : |g x - g y| ≤ H * ‖x - y‖ ^ (α:ℝ) := by
      have := hH.dist_le hxd hyd
      rwa [Real.dist_eq, dist_eq_norm] at this
    have hvv : |v x - v y| ≤ 4 * G * ‖x - y‖ ^ (α:ℝ) := by
      have h1 : ‖v x - v y‖ ≤ G * ‖x - y‖ :=
        (convex_closedBall x₀ (2 * ρ)).norm_image_sub_le_of_norm_fderiv_le
          (fun z _ => (hv.differentiable (by norm_num)) z) hgrad hy' hx'
      rw [Real.norm_eq_abs] at h1
      calc |v x - v y| ≤ G * ‖x - y‖ := h1
        _ ≤ G * (4 * ‖x - y‖ ^ (α:ℝ)) := mul_le_mul_of_nonneg_left (hdist4 x hx' y hy') hG0
        _ = 4 * G * ‖x - y‖ ^ (α:ℝ) := by ring
    have hbb : |(∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) -
        ∑ i, b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
        n * (Kb * G + Kb * (4 * S)) * ‖x - y‖ ^ (α:ℝ) := by
      rw [← Finset.sum_sub_distrib]
      have := abs_sum_le_card_mul
        (fun i => b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i))
        ((Kb * G + Kb * (4 * S)) * ‖x - y‖ ^ (α:ℝ)) (fun i => by
          have he : b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i) -
              b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i) =
              (b i x - b i y) * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i) +
              b i y * ((fderiv ℝ v x - fderiv ℝ v y) (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
            simp only [sub_apply]
            ring
          rw [he]
          calc _ ≤ |(b i x - b i y) * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)| +
                |b i y * ((fderiv ℝ v x - fderiv ℝ v y) (EuclideanSpace.basisFun (Fin n) ℝ i))| :=
                abs_add_le _ _
            _ ≤ (Kb * ‖x - y‖ ^ (α:ℝ)) * G + Kb * (S * (4 * ‖x - y‖ ^ (α:ℝ))) := by
                rw [abs_mul, abs_mul]
                apply add_le_add
                · apply mul_le_mul (hbH i x hxd y hyd) _ (abs_nonneg _) (by positivity)
                  calc |fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)|
                      = ‖fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ :=
                        (Real.norm_eq_abs _).symm
                    _ ≤ ‖fderiv ℝ v x‖ * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
                        (fderiv ℝ v x).le_opNorm _
                    _ ≤ G := by rw [hbasis, mul_one]; exact hgrad x hx'
                · apply mul_le_mul (hb i y hyd) _ (abs_nonneg _) hKb
                  calc |(fderiv ℝ v x - fderiv ℝ v y) (EuclideanSpace.basisFun (Fin n) ℝ i)|
                      = ‖(fderiv ℝ v x - fderiv ℝ v y) (EuclideanSpace.basisFun (Fin n) ℝ i)‖ :=
                        (Real.norm_eq_abs _).symm
                    _ ≤ ‖fderiv ℝ v x - fderiv ℝ v y‖ * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
                        (fderiv ℝ v x - fderiv ℝ v y).le_opNorm _
                    _ ≤ S * ‖x - y‖ := by rw [hbasis, mul_one]; exact hgradL x hx' y hy'
                    _ ≤ S * (4 * ‖x - y‖ ^ (α:ℝ)) :=
                        mul_le_mul_of_nonneg_left (hdist4 x hx' y hy') hS0
            _ = _ := by ring)
      rw [Fintype.card_fin, ← mul_assoc] at this
      exact this
    have herr' := herrH x hx' y hy'
    calc |(g x - v x - (∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) +
          euclideanError a v x₀ x) -
          (g y - v y - (∑ i, b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i)) +
          euclideanError a v x₀ y)|
        = |((g x - g y) - (v x - v y) -
            ((∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) -
              ∑ i, b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i))) +
            (euclideanError a v x₀ x - euclideanError a v x₀ y)| := by congr 1; ring
      _ ≤ |(g x - g y) - (v x - v y) -
            ((∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) -
              ∑ i, b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i))| +
            |euclideanError a v x₀ x - euclideanError a v x₀ y| := abs_add_le _ _
      _ ≤ (|(g x - g y) - (v x - v y)| +
            |(∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) -
              ∑ i, b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i)|) +
            |euclideanError a v x₀ x - euclideanError a v x₀ y| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ ((|g x - g y| + |v x - v y|) +
            |(∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) -
              ∑ i, b i y * fderiv ℝ v y (EuclideanSpace.basisFun (Fin n) ℝ i)|) +
            |euclideanError a v x₀ x - euclideanError a v x₀ y| :=
          add_le_add (add_le_add (abs_sub _ _) le_rfl) le_rfl
      _ ≤ ((H * ‖x - y‖ ^ (α:ℝ) + 4 * G * ‖x - y‖ ^ (α:ℝ)) +
            n * (Kb * G + Kb * (4 * S)) * ‖x - y‖ ^ (α:ℝ)) +
            (n:ℝ) ^ 2 * K * (S + (2 * ρ) ^ (α:ℝ) * T') * ‖x - y‖ ^ (α:ℝ) :=
          add_le_add (add_le_add (add_le_add hg hvv) hbb) herr'
      _ = _ := by ring
  have hHF0 : 0 ≤ HF := by rw [hHF]; positivity
  have hFH : HolderOnWith (Real.toNNReal HF) α F (ball x₀ (2 * ρ)) := by
    apply holderOnWith_of_dist_le hHF0
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    exact hFholder x hx y hy
  -- GT Lemma 6.1 on `ball x₀ (2ρ)`
  have hcont : ContDiffOn ℝ 2 v (ball x₀ (2 * ρ)) := hv.contDiffOn
  have hmain := (hP A hAsymm hAell x₀ ρ hρ v F V MF (Real.toNNReal HF) hcont (fun x _ => rfl)
    (fun x hx => hV x (hsub (h2sub (hball hx)))) hFbound hFH).2 x₀ (mem_ball_self hρ) y hy
  rwa [Real.coe_toNNReal _ hHF0] at hmain

/-- Algebra of the recursion step. With `p = ρ⁻¹` and `qi = (ρ^α)⁻¹`, the near-point cap
`C₀ (V ρ^(-2-α) + MF ρ^(-α) + HF)` of the freezing step plus the far-point cap `2 S ρ^(-α)` is at
most `½ T' + Γ_V V ρ^(-2-α) + C₀ M ρ^(-α) + C₀ H`, where the sup bound `S` of the Hessian comes from
interpolation with `ε = 1/8` and `ρ` is below the freezing threshold. -/
private theorem recursion_algebra {n K Kb C₀ Cε V M H T' ρ q p qi w S G MF HF : ℝ}
    (hn : 0 ≤ n) (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hC₀ : 0 < C₀) (hCε : 0 < Cε)
    (hV : 0 ≤ V) (hT : 0 ≤ T')
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) (hρq : ρ ≤ q)
    (hp : ρ * p = 1) (hqi : q * qi = 1) (hw : w ≤ 2 * q)
    (hsmall : C₀ * (1 + n * Kb + 3 * n ^ 2 * K) * q ≤ 1 / 4)
    (hS : S = Cε * V * p ^ 2 + 1 / 8 * q * T')
    (hG : G = 2 * V / (2 * ρ) + S * (2 * ρ))
    (hMF : MF = M + V + n * (Kb * G) + n ^ 2 * K * w * S)
    (hHF : HF = H + 4 * G + n * (Kb * G + Kb * (4 * S)) + n ^ 2 * K * (S + w * T')) :
    C₀ * (V * (p ^ 2 * qi) + MF * qi + HF) + 2 * S * qi ≤
      1 / 2 * T' + (C₀ * (6 + 2 * n * Kb + 3 * n ^ 2 * K) * (1 + 4 * Cε) + 2 * Cε) *
        (V * (p ^ 2 * qi)) + C₀ * M * qi + C₀ * H := by
  have hp1 : 1 ≤ p := le_of_mul_le_mul_left (by rw [hp, mul_one]; exact hρ1 : ρ * 1 ≤ ρ * p) hρ
  have hqi1 : 1 ≤ qi := le_of_mul_le_mul_left (by rw [hqi, mul_one]; exact hq1 : q * 1 ≤ q * qi) hq
  have hp0 : 0 ≤ p := by linarith
  have hqi0 : 0 ≤ qi := by linarith
  -- the atoms `Y = V p²`, `q T'`, `q² T'`
  set Y := V * p ^ 2 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hp2 : 1 ≤ p ^ 2 := one_le_pow₀ hp1
  have hpp : p ≤ p ^ 2 := by rw [pow_two]; exact le_mul_of_one_le_left hp0 hp1
  have hVY : V ≤ Y := le_mul_of_one_le_right hV hp2
  have hVpY : V * p ≤ Y := mul_le_mul_of_nonneg_left hpp hV
  have hqY : q * Y ≤ Y := mul_le_of_le_one_left hY0 hq1
  have hρp2 : ρ * p ^ 2 = p := by rw [pow_two, ← mul_assoc, hp, one_mul]
  have hdiv : 2 * V / (2 * ρ) = V * p := by
    rw [div_eq_iff (by positivity)]
    linear_combination (-2 * V) * hp
  have hρS : ρ * S = Cε * (V * p) + 1 / 8 * (ρ * q) * T' := by
    rw [hS]; linear_combination (Cε * V) * hρp2
  have hGe : G = V * p + 2 * (ρ * S) := by rw [hG, hdiv]; ring
  have hρqT : ρ * q * T' ≤ q ^ 2 * T' := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρq hq.le) hT
  have hq2T : q ^ 2 * T' ≤ q * T' := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hq.le hq1) hT
  have hG' : G ≤ (1 + 2 * Cε) * Y + 1 / 4 * (q ^ 2 * T') := by
    rw [hGe, hρS]
    have h1 := mul_le_mul_of_nonneg_left hVpY (by positivity : (0:ℝ) ≤ 1 + 2 * Cε)
    linarith
  have hG0 : 0 ≤ G := by
    rw [hGe, hρS]; positivity
  have hS' : S = Cε * Y + 1 / 8 * (q * T') := by rw [hS, hY]; ring
  have hS0 : 0 ≤ S := by rw [hS']; positivity
  have hwS : w * S ≤ 2 * Cε * Y + 1 / 4 * (q ^ 2 * T') := by
    have h1 := mul_le_mul_of_nonneg_left hqY (by positivity : (0:ℝ) ≤ 2 * Cε)
    calc w * S ≤ 2 * q * S := mul_le_mul_of_nonneg_right hw hS0
      _ = 2 * Cε * (q * Y) + 1 / 4 * (q ^ 2 * T') := by rw [hS']; ring
      _ ≤ _ := by linarith
  have hqG : q * G ≤ (1 + 2 * Cε) * Y + 1 / 4 * (q ^ 2 * T') :=
    (mul_le_of_le_one_left hG0 hq1).trans hG'
  have hqS : q * S ≤ Cε * Y + 1 / 8 * (q ^ 2 * T') := by
    have h1 := mul_le_mul_of_nonneg_left hqY hCε.le
    rw [hS']
    linarith
  have hqwT : q * (w * T') ≤ 2 * (q ^ 2 * T') := by
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hT) hq.le
    linarith
  -- bounds for `MF` and `q HF`
  have hnKb : 0 ≤ n * Kb := by positivity
  have hn2K : 0 ≤ n ^ 2 * K := by positivity
  have hMF' : MF ≤ M + (1 + n * Kb * (1 + 2 * Cε) + 2 * n ^ 2 * K * Cε) * Y +
      (n * Kb / 4 + n ^ 2 * K / 4) * (q ^ 2 * T') := by
    rw [hMF]
    have h1 := mul_le_mul_of_nonneg_left hG' hnKb
    have h2 := mul_le_mul_of_nonneg_left hwS hn2K
    linarith
  have hqHF : q * HF ≤ q * H + (4 * (1 + 2 * Cε) + n * Kb * (1 + 2 * Cε) + 4 * n * Kb * Cε +
      n ^ 2 * K * Cε) * Y + (1 + n * Kb / 4 + n * Kb / 2 + n ^ 2 * K / 8 + 2 * n ^ 2 * K) *
      (q ^ 2 * T') := by
    rw [hHF]
    have h1 := mul_le_mul_of_nonneg_left hqG hnKb
    have h2 := mul_le_mul_of_nonneg_left hqS hnKb
    have h3 := mul_le_mul_of_nonneg_left hqS hn2K
    have h4 := mul_le_mul_of_nonneg_left hqwT hn2K
    linarith
  -- the absorbed term
  have hT'small : C₀ * (1 + n * Kb + 3 * n ^ 2 * K) * (q ^ 2 * T') ≤ 1 / 4 * (q * T') := by
    have := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hq.le hT)
    linarith
  -- multiply the claim by `q > 0`
  apply le_of_mul_le_mul_left _ hq
  have hqY' : q * (V * (p ^ 2 * qi)) = Y := by
    rw [hY]; linear_combination (V * p ^ 2) * hqi
  have hZ0 : 0 ≤ q ^ 2 * T' := by positivity
  have hcoefY : (C₀ * (6 + 8 * Cε + 2 * n * Kb + 8 * n * Kb * Cε + 3 * n ^ 2 * K * Cε) + 2 * Cε) * Y ≤
      (C₀ * (6 + 2 * n * Kb + 3 * n ^ 2 * K) * (1 + 4 * Cε) + 2 * Cε) * Y := by
    apply mul_le_mul_of_nonneg_right _ hY0
    linarith [mul_nonneg hC₀.le hCε.le, mul_nonneg hC₀.le hn2K,
      mul_nonneg (mul_nonneg hC₀.le hn2K) hCε.le]
  have hcoefZ : C₀ * (1 + n * Kb / 4 + n * Kb / 2 + n ^ 2 * K / 8 + 2 * n ^ 2 * K +
      (n * Kb / 4 + n ^ 2 * K / 4)) * (q ^ 2 * T') ≤
      C₀ * (1 + n * Kb + 3 * n ^ 2 * K) * (q ^ 2 * T') := by
    apply mul_le_mul_of_nonneg_right _ hZ0
    linarith [mul_nonneg hC₀.le hn2K]
  have hMF'' := mul_le_mul_of_nonneg_left hMF' hC₀.le
  have hqHF' := mul_le_mul_of_nonneg_left hqHF hC₀.le
  have hlhs : q * (C₀ * (V * (p ^ 2 * qi) + MF * qi + HF) + 2 * S * qi) =
      C₀ * (Y + MF + q * HF) + 2 * S := by
    linear_combination (C₀ * (V * p ^ 2) + C₀ * MF + 2 * S) * hqi
  have hrhs : q * (1 / 2 * T' + (C₀ * (6 + 2 * n * Kb + 3 * n ^ 2 * K) * (1 + 4 * Cε) + 2 * Cε) *
      (V * (p ^ 2 * qi)) + C₀ * M * qi + C₀ * H) = 1 / 2 * (q * T') +
      (C₀ * (6 + 2 * n * Kb + 3 * n ^ 2 * K) * (1 + 4 * Cε) + 2 * Cε) * Y + C₀ * M + C₀ * (q * H) := by
    rw [← hqY']
    linear_combination (C₀ * M) * hqi
  rw [hlhs, hrhs, hS']
  linarith

/-- **Recursion for the Hessian Hölder seminorm** (GT pp. 91–92, the step before the absorption).
For `0 < r < r' ≤ Rd` and a radius `ρ ≤ ρ₀` with `8ρ ≤ r' - r`, the seminorm on `closedBall c r`
is at most half the seminorm on `closedBall c r'` plus `Γ_V V ρ^(-2-α) + C₀ M ρ^(-α) + C₀ H`.
The sup of the Hessian on `closedBall c (r + 4ρ)` is interpolated between `V` and the seminorm on
`closedBall c r'` (`hI`, with `ε = 1/8`), pairs closer than `ρ` use `freezing_step`, farther pairs
use the sup bound, and `recursion_algebra` collects the terms. -/
private theorem seminorm_recursion {n : ℕ} {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1)
    {lam Lam K Kb C₀ Cε : ℝ} (hK : 0 ≤ K) (hKb : 0 ≤ Kb) (hC₀ : 0 < C₀) (hCε : 0 < Cε)
    (hP : ConstantCoefficientBound n α lam Lam C₀)
    (hI : ∀ (r : ℝ), 0 < r → ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (f'' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      (∀ z, HasFDerivAt f (f' z) z) → (∀ z, HasFDerivAt f' (f'' z) z) →
      ∀ (x : EuclideanSpace ℝ (Fin n)) (M H : ℝ), 0 ≤ H →
      (∀ z ∈ closedBall x r, |f z| ≤ M) →
      (∀ z ∈ closedBall x r, ‖f'' z - f'' x‖ ≤ H * ‖z - x‖ ^ (α:ℝ)) →
      r ^ 2 * ‖f'' x‖ ≤ Cε * M + 1 / 8 * H * r ^ (2 + (α:ℝ)))
    {ρ₀ : ℝ} (hρ₀1 : ρ₀ ≤ 1)
    (hsmall : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      C₀ * (1 + n * Kb + 3 * (n:ℝ) ^ 2 * K) * ρ ^ (α:ℝ) ≤ 1 / 4)
    {c : EuclideanSpace ℝ (Fin n)} {Rd : ℝ}
    {a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hsymm : ∀ x ∈ closedBall c Rd, ∀ i j, a i j x = a j i x)
    (hell : ∀ x ∈ closedBall c Rd, ∀ ξ : EuclideanSpace ℝ (Fin n),
      lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j ∧
        ∑ i, ∑ j, a i j x * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2)
    (haH : ∀ i j, ∀ x ∈ closedBall c Rd, ∀ y ∈ closedBall c Rd,
      |a i j x - a i j y| ≤ K * ‖x - y‖ ^ (α:ℝ))
    (hb : ∀ i, ∀ x ∈ closedBall c Rd, |b i x| ≤ Kb)
    (hbH : ∀ i, ∀ x ∈ closedBall c Rd, ∀ y ∈ closedBall c Rd,
      |b i x - b i y| ≤ Kb * ‖x - y‖ ^ (α:ℝ))
    {v g : EuclideanSpace ℝ (Fin n) → ℝ} {V M : ℝ} {H : ℝ≥0} (hv : ContDiff ℝ 2 v)
    (heq : ∀ x ∈ closedBall c Rd, (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
        (∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) + v x = g x)
    (hV : ∀ x ∈ closedBall c Rd, |v x| ≤ V) (hM : ∀ x ∈ closedBall c Rd, |g x| ≤ M)
    (hH : HolderOnWith H α g (closedBall c Rd))
    {N2 : ℝ} (hN2 : ∀ x ∈ closedBall c Rd, ∀ y ∈ closedBall c Rd,
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ N2 * ‖x - y‖ ^ (α:ℝ))
    {r r' : ℝ} (hr : 0 < r) (hr'R : r' ≤ Rd)
    {ρ : ℝ} (hρ : 0 < ρ) (hρρ₀ : ρ ≤ ρ₀) (h8 : 8 * ρ ≤ r' - r) :
    hessianHolderSeminorm v α c r ≤ 1 / 2 * hessianHolderSeminorm v α c r' +
      (C₀ * (6 + 2 * n * Kb + 3 * (n:ℝ) ^ 2 * K) * (1 + 4 * Cε) + 2 * Cε) * V *
        ρ ^ (-(2:ℝ) - α) + C₀ * M * ρ ^ (-(α:ℝ)) + C₀ * H := by
  have hαr : (0:ℝ) < α := hα0
  have hα1r : (α:ℝ) ≤ 1 := by exact_mod_cast hα1.le
  have hρ1 : ρ ≤ 1 := hρρ₀.trans hρ₀1
  have hsubr' : closedBall c r' ⊆ closedBall c Rd := closedBall_subset_closedBall hr'R
  have hc : c ∈ closedBall c Rd := mem_closedBall_self (by linarith)
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV c hc)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c hc)
  set T' := hessianHolderSeminorm v α c r' with hT'def
  have hT0 : 0 ≤ T' := hessianHolderSeminorm_nonneg v α c r'
  have hT : ∀ x ∈ closedBall c r', ∀ y ∈ closedBall c r',
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ T' * ‖x - y‖ ^ (α:ℝ) :=
    fun x hx y hy => le_hessianHolderSeminorm hαr
      (fun x hx y hy => hN2 x (hsubr' hx) y (hsubr' hy)) hx hy
  -- derivative witnesses
  have hdv : ∀ z, HasFDerivAt v (fderiv ℝ v z) z := fun z =>
    ((hv.differentiable (by norm_num)) z).hasFDerivAt
  have hddv : ∀ z, HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) z) z := fun z =>
    (((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z).hasFDerivAt
  -- powers of `ρ`
  set q := ρ ^ (α:ℝ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hρ _
  have hq1 : q ≤ 1 := Real.rpow_le_one hρ.le hρ1 hαr.le
  have hρq : ρ ≤ q := Real.self_le_rpow_of_le_one hρ.le hρ1 hα1r
  have hρ2α : ρ ^ (2 + (α:ℝ)) = ρ ^ 2 * q := by rw [Real.rpow_add hρ, Real.rpow_two]
  have hw : (2 * ρ) ^ (α:ℝ) ≤ 2 * q := by
    rw [Real.mul_rpow (by norm_num) hρ.le]
    apply mul_le_mul_of_nonneg_right _ hq0.le
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hα1r
    rwa [Real.rpow_one] at this
  -- sup bound of the Hessian on `closedBall c (r + 4ρ)` by interpolation
  set S := Cε * V * ρ⁻¹ ^ 2 + 1 / 8 * q * T' with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hSbound : ∀ z ∈ closedBall c (r + 4 * ρ), ‖fderiv ℝ (fderiv ℝ v) z‖ ≤ S := by
    intro z hz
    have hzsub : closedBall z ρ ⊆ closedBall c r' :=
      closedBall_subset_closedBall' (by rw [mem_closedBall] at hz; linarith)
    have h := hI ρ hρ v (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v)) hdv hddv z V T' hT0
      (fun w hw => hV w (hsubr' (hzsub hw)))
      (fun w hw => hT w (hzsub hw) z (hzsub (mem_closedBall_self hρ.le)))
    rw [hρ2α] at h
    have hρ2 : 0 < ρ ^ 2 := by positivity
    have hS2 : ρ ^ 2 * S = Cε * V + 1 / 8 * T' * (ρ ^ 2 * q) := by
      rw [hSdef]; field_simp
    rw [← mul_le_mul_iff_right₀ hρ2, hS2]
    linarith
  -- the quantities of the freezing step
  set G := 2 * V / (2 * ρ) + S * (2 * ρ) with hGdef
  set MF := M + V + n * (Kb * G) + (n:ℝ) ^ 2 * K * (2 * ρ) ^ (α:ℝ) * S with hMFdef
  set HF := H + 4 * G + n * (Kb * G + Kb * (4 * S)) +
    (n:ℝ) ^ 2 * K * (S + (2 * ρ) ^ (α:ℝ) * T') with hHFdef
  -- near pairs: the freezing step
  have hnear : ∀ x ∈ closedBall c r, ∀ y ∈ ball x ρ,
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤
        C₀ * (V * ρ ^ (-(2:ℝ) - α) + MF * ρ ^ (-(α:ℝ)) + HF) * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy
    rw [mem_closedBall] at hx
    have hsub4 : closedBall x (4 * ρ) ⊆ closedBall c Rd :=
      (closedBall_subset_closedBall' (by linarith : 4 * ρ + dist x c ≤ r')).trans hsubr'
    have hsub4' : closedBall x (4 * ρ) ⊆ closedBall c (r + 4 * ρ) :=
      closedBall_subset_closedBall' (by linarith)
    have hsub2 : closedBall x (2 * ρ) ⊆ closedBall c r' :=
      closedBall_subset_closedBall' (by linarith)
    exact freezing_step hα0 hα1 hK hKb hP hsymm hell haH hb hbH hv heq hV hM hH hρ hρ1 hsub4
      hS0 hT0 (fun z hz => hSbound z (hsub4' hz))
      (fun x' hx' y' hy' => hT x' (hsub2 hx') y' (hsub2 hy')) hGdef hMFdef hHFdef y hy
  -- far pairs: twice the sup bound
  have hfar : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r, ρ ≤ ‖x - y‖ →
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤
        2 * S * ρ ^ (-(α:ℝ)) * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy hxy
    have hsubr : closedBall c r ⊆ closedBall c (r + 4 * ρ) :=
      closedBall_subset_closedBall (by linarith)
    have h1 := hSbound x (hsubr hx)
    have h2 := hSbound y (hsubr hy)
    have hqxy : q ≤ ‖x - y‖ ^ (α:ℝ) := Real.rpow_le_rpow hρ.le hxy hαr.le
    calc ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖
        ≤ ‖fderiv ℝ (fderiv ℝ v) x‖ + ‖fderiv ℝ (fderiv ℝ v) y‖ := by
          rw [sub_eq_add_neg]
          exact (ContinuousLinearMap.opNorm_add_le _ _).trans
            (by rw [ContinuousLinearMap.opNorm_neg])
      _ ≤ 2 * S := by linarith
      _ = 2 * S * ρ ^ (-(α:ℝ)) * q := by
          rw [Real.rpow_neg hρ.le, ← hqdef]; field_simp
      _ ≤ 2 * S * ρ ^ (-(α:ℝ)) * ‖x - y‖ ^ (α:ℝ) :=
          mul_le_mul_of_nonneg_left hqxy (by positivity)
  -- the seminorm on `closedBall c r` is at most the sum of the two caps
  have hA0 : 0 ≤ C₀ * (V * ρ ^ (-(2:ℝ) - α) + MF * ρ ^ (-(α:ℝ)) + HF) := by
    have : 0 ≤ MF := by rw [hMFdef]; positivity
    have : 0 ≤ HF := by rw [hHFdef]; positivity
    positivity
  have hB0 : 0 ≤ 2 * S * ρ ^ (-(α:ℝ)) := by positivity
  have hcap : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤
        (C₀ * (V * ρ ^ (-(2:ℝ) - α) + MF * ρ ^ (-(α:ℝ)) + HF) + 2 * S * ρ ^ (-(α:ℝ))) *
          ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy
    have hd0 : 0 ≤ ‖x - y‖ ^ (α:ℝ) := by positivity
    by_cases hxy : ‖x - y‖ < ρ
    · have hy' : y ∈ ball x ρ := by rw [mem_ball, dist_comm, dist_eq_norm]; exact hxy
      exact (hnear x hx y hy').trans (mul_le_mul_of_nonneg_right (by linarith) hd0)
    · exact (hfar x hx y hy (not_lt.mp hxy)).trans
        (mul_le_mul_of_nonneg_right (by linarith) hd0)
  have hTr := hessianHolderSeminorm_le (add_nonneg hA0 hB0) hcap
  -- algebra
  have e1 : ρ ^ (-(2:ℝ) - α) = ρ⁻¹ ^ 2 * q⁻¹ := by
    rw [show -(2:ℝ) - α = -(2 + α) by ring, Real.rpow_neg hρ.le, hρ2α, mul_inv, inv_pow]
  have e2 : ρ ^ (-(α:ℝ)) = q⁻¹ := by rw [Real.rpow_neg hρ.le]
  have halg := recursion_algebra (n := (n:ℝ)) (K := K) (Kb := Kb) (C₀ := C₀) (Cε := Cε) (V := V)
    (M := M) (H := H) (T' := T') (ρ := ρ) (q := q) (p := ρ⁻¹) (qi := q⁻¹) (w := (2 * ρ) ^ (α:ℝ))
    (S := S) (G := G) (MF := MF) (HF := HF) (Nat.cast_nonneg n) hK hKb hC₀ hCε hV0 hT0 hρ hρ1
    hq0 hq1 hρq (mul_inv_cancel₀ hρ.ne') (mul_inv_cancel₀ hq0.ne') hw
    (hsmall ρ hρ hρρ₀) hSdef hGdef hMFdef hHFdef
  rw [e1, e2] at hTr ⊢
  calc hessianHolderSeminorm v α c r ≤ _ := hTr
    _ ≤ _ := halg
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- **GT 2001 Theorem 6.2, interior a priori form on balls.** For `n ≥ 2`, `0 < α < 1`,
`0 < λ ≤ Λ` and `K, Kb ≥ 0` there is `C > 0` such that for every centre `c`, radius `0 < R ≤ 1`,
symmetric `(λ, Λ)`-elliptic principal coefficients `a` with `α`-Hölder cap `K`, first-order
coefficients `b` bounded by `Kb` with `α`-Hölder cap `Kb`, all on `closedBall c (2R)`, and every
`C²` function `v` with finite Hessian bound and Hessian Hölder bound on `closedBall c (2R)` solving
`Σ_{ij} aⁱʲ D_{ij} v + Σ_i bⁱ D_i v + v = g` there with `|v| ≤ V`, `|g| ≤ M`, `[g]_α ≤ H`, one has
`‖D²v‖ ≤ C (V R⁻² + M + H)` and `‖D²v(x) - D²v(y)‖ ≤ C (V R^(-2-α) + M R^(-α) + H) ‖x - y‖^α`
on `ball c R`. The constant depends only on `(n, α, λ, Λ, K, Kb)`; the a priori bounds `N`, `N2`
of the Hessian are hypotheses only. -/
theorem variable_coefficient_interior_hessian_holder {n : ℕ} (hn : 2 ≤ n) {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α < 1) {lam Lam K Kb : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (hK : 0 ≤ K)
    (hKb : 0 ≤ Kb) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → R ≤ 1 →
      ∀ (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
        (b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x ∈ closedBall c (2 * R), ∀ i j, a i j x = a j i x) →
      (∀ x ∈ closedBall c (2 * R), ∀ ξ : EuclideanSpace ℝ (Fin n),
        lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j ∧
          ∑ i, ∑ j, a i j x * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, ∀ x ∈ closedBall c (2 * R), ∀ y ∈ closedBall c (2 * R),
        |a i j x - a i j y| ≤ K * ‖x - y‖ ^ (α:ℝ)) →
      (∀ i, ∀ x ∈ closedBall c (2 * R), |b i x| ≤ Kb) →
      (∀ i, ∀ x ∈ closedBall c (2 * R), ∀ y ∈ closedBall c (2 * R),
        |b i x - b i y| ≤ Kb * ‖x - y‖ ^ (α:ℝ)) →
      ∀ (v g : EuclideanSpace ℝ (Fin n) → ℝ) (V N N2 M : ℝ) (H : ℝ≥0),
      ContDiff ℝ 2 v →
      (∀ x ∈ closedBall c (2 * R), ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ N) →
      (∀ x ∈ closedBall c (2 * R), ∀ y ∈ closedBall c (2 * R),
        ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ N2 * ‖x - y‖ ^ (α:ℝ)) →
      (∀ x ∈ closedBall c (2 * R), (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ v) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
          (∑ i, b i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i)) + v x = g x) →
      (∀ x ∈ closedBall c (2 * R), |v x| ≤ V) → (∀ x ∈ closedBall c (2 * R), |g x| ≤ M) →
      HolderOnWith H α g (closedBall c (2 * R)) →
      (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ C * (V * R ^ (-(2:ℝ)) + M + H)) ∧
      ∀ x ∈ ball c R, ∀ y ∈ ball c R,
        ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤
          C * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
  have hαr : (0:ℝ) < α := hα0
  have hα1r : (α:ℝ) ≤ 1 := by exact_mod_cast hα1.le
  -- the constants: GT Lemma 6.1, interpolation with `ε = 1/8`, the freezing threshold `ρ₀`,
  -- the absorption constant
  obtain ⟨C₀, hC₀, hP⟩ := constant_coefficient_interior_hessian_holder hn hα0 hα1 hlam hLam
  obtain ⟨Cε, hCε, hI⟩ := exists_hessian_interpolation_constant (E := EuclideanSpace ℝ (Fin n))
    (α:ℝ) hαr (1 / 8) (by norm_num)
  obtain ⟨ρ₀, hρ₀, hρ₀1, hsmall⟩ := exists_small_freezing_radius (ι := Unit) (α:ℝ) hαr (1 / 4)
    (by norm_num) (C₀ * (1 + n * Kb + 3 * (n:ℝ) ^ 2 * K)) (by positivity)
  have hsmall' : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      C₀ * (1 + n * Kb + 3 * (n:ℝ) ^ 2 * K) * ρ ^ (α:ℝ) ≤ 1 / 4 := by
    intro ρ h1 h2
    have := hsmall ρ h1 h2
    rwa [Fintype.card_unit, Nat.cast_one, one_mul] at this
  obtain ⟨cA, hcA, habs⟩ := exists_absorption_constant (θ := 1 / 2) (by norm_num) (by norm_num)
    (k := 2 + (α:ℝ)) (by positivity)
  set ΓV : ℝ := C₀ * (6 + 2 * n * Kb + 3 * (n:ℝ) ^ 2 * K) * (1 + 4 * Cε) + 2 * Cε with hΓVdef
  have hΓV : 0 < ΓV := by positivity
  set κ : ℝ := 2 / ρ₀ + 8 with hκdef
  have hκ : 0 < κ := by positivity
  set C' : ℝ := cA * (64 * κ ^ (2 + (α:ℝ)) * ΓV + 256 * κ ^ (α:ℝ) * C₀ + 8 * C₀) with hC'def
  have hC' : 0 < C' := by positivity
  refine ⟨4 * Cε + C', by positivity, ?_⟩
  intro c R hR hR1 a b hsymm hell haH hb hbH v g V _N N2 M H hv _hN hN2 heq hV hM hH
  have hc : c ∈ closedBall c (2 * R) := mem_closedBall_self (by linarith)
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV c hc)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c hc)
  have hH0 : (0:ℝ) ≤ H := H.coe_nonneg
  -- the seminorm function and the absorption function `A r = r^(2+α) T r`
  set T : ℝ → ℝ := hessianHolderSeminorm v α c with hTdef
  have hT0 : ∀ r, 0 ≤ T r := fun r => hessianHolderSeminorm_nonneg v α c r
  set A : ℝ → ℝ := fun r => r ^ (2 + (α:ℝ)) * T r with hAdef
  set B : ℝ := (2 * R) ^ (2 + (α:ℝ)) *
    (κ ^ (2 + (α:ℝ)) * ΓV * V + κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M) with hBdef
  set Cc : ℝ := (2 * R) ^ (2 + (α:ℝ)) * C₀ * H with hCcdef
  -- the recursion
  have hrec : ∀ r r' : ℝ, 0 < r → r < r' → r' ≤ 2 * R →
      A r ≤ 1 / 2 * A r' + B / (r' - r) ^ (2 + (α:ℝ)) + Cc := by
    intro r r' hr hrr' hr'R
    have hs0 : 0 < r' - r := by linarith
    have hs2 : r' - r ≤ 2 * R := by linarith
    set ρ : ℝ := min ρ₀ ((r' - r) / 8) with hρdef
    have hρ0 : 0 < ρ := lt_min hρ₀ (by positivity)
    have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
    have h8 : 8 * ρ ≤ r' - r := by
      have := min_le_right ρ₀ ((r' - r) / 8)
      linarith
    have hTr := seminorm_recursion hα0 hα1 hK hKb hC₀ hCε hP hI hρ₀1 hsmall' hsymm hell haH hb
      hbH hv heq hV hM hH hN2 hr hr'R hρ0 hρρ₀ h8
    -- `ρ⁻¹ ≤ κ / (r' - r)`
    have hsκ : r' - r ≤ κ * ρ := by
      by_cases hcase : ρ₀ ≤ (r' - r) / 8
      · rw [hρdef, min_eq_left hcase]
        have : κ * ρ₀ = 2 + 8 * ρ₀ := by rw [hκdef]; field_simp
        rw [this]; linarith
      · rw [hρdef, min_eq_right (not_le.mp hcase).le]
        have : κ * ((r' - r) / 8) = (r' - r) / (4 * ρ₀) + (r' - r) := by
          rw [hκdef]; field_simp; ring
        rw [this]
        have : 0 ≤ (r' - r) / (4 * ρ₀) := by positivity
        linarith
    have hinv : ρ⁻¹ ≤ κ / (r' - r) := by
      rw [le_div_iff₀ hs0, inv_mul_le_iff₀ hρ0]
      linarith
    have hp1 : ρ ^ (-(2:ℝ) - α) ≤ κ ^ (2 + (α:ℝ)) / (r' - r) ^ (2 + (α:ℝ)) := by
      rw [show -(2:ℝ) - α = -(2 + α) by ring, Real.rpow_neg hρ0.le, ← Real.inv_rpow hρ0.le,
        ← Real.div_rpow hκ.le hs0.le]
      exact Real.rpow_le_rpow (inv_nonneg.2 hρ0.le) hinv (by positivity)
    have hp2 : ρ ^ (-(α:ℝ)) ≤ κ ^ (α:ℝ) * (2 * R) ^ 2 / (r' - r) ^ (2 + (α:ℝ)) := by
      have h1 : ρ ^ (-(α:ℝ)) ≤ κ ^ (α:ℝ) / (r' - r) ^ (α:ℝ) := by
        rw [Real.rpow_neg hρ0.le, ← Real.inv_rpow hρ0.le, ← Real.div_rpow hκ.le hs0.le]
        exact Real.rpow_le_rpow (inv_nonneg.2 hρ0.le) hinv hαr.le
      have h2 : (r' - r) ^ (2 + (α:ℝ)) = (r' - r) ^ 2 * (r' - r) ^ (α:ℝ) := by
        rw [Real.rpow_add hs0, Real.rpow_two]
      have h3 : 0 < (r' - r) ^ (α:ℝ) := Real.rpow_pos_of_pos hs0 _
      calc ρ ^ (-(α:ℝ)) ≤ κ ^ (α:ℝ) / (r' - r) ^ (α:ℝ) := h1
        _ = κ ^ (α:ℝ) * (r' - r) ^ 2 / (r' - r) ^ (2 + (α:ℝ)) := by
            rw [h2]; field_simp
        _ ≤ κ ^ (α:ℝ) * (2 * R) ^ 2 / (r' - r) ^ (2 + (α:ℝ)) := by
            gcongr
    have hr2α : r ^ (2 + (α:ℝ)) ≤ r' ^ (2 + (α:ℝ)) :=
      Real.rpow_le_rpow hr.le hrr'.le (by positivity)
    have hr2R : r ^ (2 + (α:ℝ)) ≤ (2 * R) ^ (2 + (α:ℝ)) :=
      Real.rpow_le_rpow hr.le (by linarith) (by positivity)
    have hr0 : 0 ≤ r ^ (2 + (α:ℝ)) := by positivity
    have hTr'0 := hT0 r'
    have hs2α : 0 < (r' - r) ^ (2 + (α:ℝ)) := Real.rpow_pos_of_pos hs0 _
    have h1 : r ^ (2 + (α:ℝ)) * (ΓV * V * ρ ^ (-(2:ℝ) - α)) ≤
        (2 * R) ^ (2 + (α:ℝ)) * (ΓV * V * (κ ^ (2 + (α:ℝ)) / (r' - r) ^ (2 + (α:ℝ)))) :=
      mul_le_mul hr2R (mul_le_mul_of_nonneg_left hp1 (by positivity)) (by positivity)
        (by positivity)
    have h2 : r ^ (2 + (α:ℝ)) * (C₀ * M * ρ ^ (-(α:ℝ))) ≤
        (2 * R) ^ (2 + (α:ℝ)) * (C₀ * M * (κ ^ (α:ℝ) * (2 * R) ^ 2 / (r' - r) ^ (2 + (α:ℝ)))) :=
      mul_le_mul hr2R (mul_le_mul_of_nonneg_left hp2 (by positivity)) (by positivity)
        (by positivity)
    have h3 : r ^ (2 + (α:ℝ)) * (C₀ * H) ≤ (2 * R) ^ (2 + (α:ℝ)) * (C₀ * H) :=
      mul_le_mul_of_nonneg_right hr2R (by positivity)
    have h4 : r ^ (2 + (α:ℝ)) * T r' ≤ r' ^ (2 + (α:ℝ)) * T r' :=
      mul_le_mul_of_nonneg_right hr2α hTr'0
    calc A r = r ^ (2 + (α:ℝ)) * T r := rfl
      _ ≤ r ^ (2 + (α:ℝ)) * (1 / 2 * T r' + ΓV * V * ρ ^ (-(2:ℝ) - α) + C₀ * M * ρ ^ (-(α:ℝ)) +
          C₀ * H) := mul_le_mul_of_nonneg_left hTr hr0
      _ = 1 / 2 * (r ^ (2 + (α:ℝ)) * T r') + r ^ (2 + (α:ℝ)) * (ΓV * V * ρ ^ (-(2:ℝ) - α)) +
          r ^ (2 + (α:ℝ)) * (C₀ * M * ρ ^ (-(α:ℝ))) + r ^ (2 + (α:ℝ)) * (C₀ * H) := by ring
      _ ≤ 1 / 2 * (r' ^ (2 + (α:ℝ)) * T r') +
          (2 * R) ^ (2 + (α:ℝ)) * (ΓV * V * (κ ^ (2 + (α:ℝ)) / (r' - r) ^ (2 + (α:ℝ)))) +
          (2 * R) ^ (2 + (α:ℝ)) * (C₀ * M * (κ ^ (α:ℝ) * (2 * R) ^ 2 / (r' - r) ^ (2 + (α:ℝ)))) +
          (2 * R) ^ (2 + (α:ℝ)) * (C₀ * H) := by linarith
      _ = 1 / 2 * A r' + B / (r' - r) ^ (2 + (α:ℝ)) + Cc := by
          rw [hBdef, hCcdef]; field_simp; ring
  -- the absorption lemma on `(0, 2R]`
  have hA0 : ∀ r ∈ Set.Ioc (0:ℝ) (2 * R), 0 ≤ A r := fun r hr =>
    mul_nonneg (Real.rpow_nonneg hr.1.le _) (hT0 r)
  have hAbd : ∃ Bd : ℝ, ∀ r ∈ Set.Ioc (0:ℝ) (2 * R), A r ≤ Bd := by
    refine ⟨(2 * R) ^ (2 + (α:ℝ)) * max N2 0, fun r hr => ?_⟩
    have hsub : closedBall c r ⊆ closedBall c (2 * R) := closedBall_subset_closedBall hr.2
    have hTle : T r ≤ max N2 0 := hessianHolderSeminorm_le (le_max_right _ _)
      (fun x hx y hy => (hN2 x (hsub hx) y (hsub hy)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    exact mul_le_mul (Real.rpow_le_rpow hr.1.le hr.2 (by positivity)) hTle (hT0 r) (by positivity)
  have hB0 : 0 ≤ B := by positivity
  have hCc0 : 0 ≤ Cc := by positivity
  have hmain := habs (2 * R) (by positivity) A B Cc hB0 hCc0 hA0 hAbd hrec (3 * R / 2)
    ⟨by positivity, by linarith⟩
  -- the bound of `T (3R/2)`
  set u : ℝ := R ^ (α:ℝ) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hR _
  have hu1 : u ≤ 1 := Real.rpow_le_one hR.le hR1 hαr.le
  have hR2α : R ^ (2 + (α:ℝ)) = R ^ 2 * u := by rw [Real.rpow_add hR, Real.rpow_two]
  have hs3 : (1:ℝ) ≤ (3 / 2) ^ (2 + (α:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hs2 : (2:ℝ) ^ (2 + (α:ℝ)) ≤ 8 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by linarith : 2 + (α:ℝ) ≤ 3)
    rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast] at this
    norm_num at this
    exact this
  have hsh : (1 / 8 : ℝ) ≤ (1 / 2) ^ (2 + (α:ℝ)) := by
    have := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ) < 1 / 2) (by norm_num)
      (by linarith : 2 + (α:ℝ) ≤ 3)
    rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast] at this
    norm_num at this
    exact this
  have hsh0 : (0:ℝ) < (1 / 2) ^ (2 + (α:ℝ)) := by positivity
  have hT32 : T (3 * R / 2) ≤ C' * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) := by
    have e1 : (3 * R / 2) ^ (2 + (α:ℝ)) = (3 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u) := by
      rw [show 3 * R / 2 = 3 / 2 * R by ring, Real.mul_rpow (by norm_num) hR.le, hR2α]
    have e2 : (2 * R) ^ (2 + (α:ℝ)) = 2 ^ (2 + (α:ℝ)) * (R ^ 2 * u) := by
      rw [Real.mul_rpow (by norm_num) hR.le, hR2α]
    have e3 : (2 * R - 3 * R / 2) ^ (2 + (α:ℝ)) = (1 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u) := by
      rw [show 2 * R - 3 * R / 2 = 1 / 2 * R by ring, Real.mul_rpow (by norm_num) hR.le, hR2α]
    have e4 : R ^ (-(2:ℝ) - α) = (R ^ 2 * u)⁻¹ := by
      rw [show -(2:ℝ) - α = -(2 + α) by ring, Real.rpow_neg hR.le, hR2α]
    have e5 : R ^ (-(α:ℝ)) = u⁻¹ := by rw [Real.rpow_neg hR.le]
    have hmain' := hmain
    simp only [hAdef, hBdef, hCcdef] at hmain'
    rw [e1, e2, e3] at hmain'
    -- `hmain' : s₃ R² u T ≤ cA ((s₂ R² u (…)) / (sh R² u) + s₂ R² u C₀ H)`
    have hRu : 0 < R ^ 2 * u := by positivity
    have hq1 : 2 ^ (2 + (α:ℝ)) * (R ^ 2 * u) * (κ ^ (2 + (α:ℝ)) * ΓV * V +
        κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M) / ((1 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u)) ≤
        64 * (κ ^ (2 + (α:ℝ)) * ΓV * V + κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M) := by
      rw [div_le_iff₀ (by positivity)]
      have hX0 : 0 ≤ κ ^ (2 + (α:ℝ)) * ΓV * V + κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M := by positivity
      calc 2 ^ (2 + (α:ℝ)) * (R ^ 2 * u) * (κ ^ (2 + (α:ℝ)) * ΓV * V +
            κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M)
          ≤ 8 * (R ^ 2 * u) * (κ ^ (2 + (α:ℝ)) * ΓV * V + κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M) := by
            gcongr
        _ = 64 * (κ ^ (2 + (α:ℝ)) * ΓV * V + κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M) *
            (1 / 8 * (R ^ 2 * u)) := by ring
        _ ≤ 64 * (κ ^ (2 + (α:ℝ)) * ΓV * V + κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M) *
            ((1 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u)) := by gcongr
    have hq2 : 2 ^ (2 + (α:ℝ)) * (R ^ 2 * u) * C₀ * H ≤ 8 * (R ^ 2 * u) * C₀ * H := by
      gcongr
    have hbound : (3 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u) * T (3 * R / 2) ≤
        C' * (V + R ^ 2 * M + R ^ 2 * u * H) := by
      calc (3 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u) * T (3 * R / 2) ≤ _ := hmain'
        _ ≤ cA * (64 * (κ ^ (2 + (α:ℝ)) * ΓV * V + κ ^ (α:ℝ) * (2 * R) ^ 2 * C₀ * M) +
            8 * (R ^ 2 * u) * C₀ * H) := by gcongr
        _ = cA * (64 * κ ^ (2 + (α:ℝ)) * ΓV) * V + cA * (256 * κ ^ (α:ℝ) * C₀) * (R ^ 2 * M) +
            cA * (8 * C₀) * (R ^ 2 * u * H) := by ring
        _ ≤ C' * V + C' * (R ^ 2 * M) + C' * (R ^ 2 * u * H) := by
            rw [hC'def]
            have hc1 : cA * (64 * κ ^ (2 + (α:ℝ)) * ΓV) ≤
                cA * (64 * κ ^ (2 + (α:ℝ)) * ΓV + 256 * κ ^ (α:ℝ) * C₀ + 8 * C₀) := by
              gcongr; linarith [show 0 ≤ 256 * κ ^ (α:ℝ) * C₀ + 8 * C₀ by positivity]
            have hc2 : cA * (256 * κ ^ (α:ℝ) * C₀) ≤
                cA * (64 * κ ^ (2 + (α:ℝ)) * ΓV + 256 * κ ^ (α:ℝ) * C₀ + 8 * C₀) := by
              gcongr; linarith [show 0 ≤ 64 * κ ^ (2 + (α:ℝ)) * ΓV + 8 * C₀ by positivity]
            have hc3 : cA * (8 * C₀) ≤
                cA * (64 * κ ^ (2 + (α:ℝ)) * ΓV + 256 * κ ^ (α:ℝ) * C₀ + 8 * C₀) := by
              gcongr; linarith [show 0 ≤ 64 * κ ^ (2 + (α:ℝ)) * ΓV + 256 * κ ^ (α:ℝ) * C₀ by
                positivity]
            have := mul_le_mul_of_nonneg_right hc1 hV0
            have := mul_le_mul_of_nonneg_right hc2 (by positivity : 0 ≤ R ^ 2 * M)
            have := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ R ^ 2 * u * H)
            linarith
        _ = _ := by ring
    rw [e4, e5]
    have hpos : 0 < (3 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u) := by positivity
    apply le_of_mul_le_mul_left _ hpos
    calc (3 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u) * T (3 * R / 2)
        ≤ C' * (V + R ^ 2 * M + R ^ 2 * u * H) := hbound
      _ ≤ (3 / 2) ^ (2 + (α:ℝ)) * (C' * (V + R ^ 2 * M + R ^ 2 * u * H)) :=
          le_mul_of_one_le_left (by positivity) hs3
      _ = (3 / 2) ^ (2 + (α:ℝ)) * (R ^ 2 * u) * (C' * (V * (R ^ 2 * u)⁻¹ + M * u⁻¹ + H)) := by
          field_simp
  -- the Hölder conclusion on `ball c R`
  have hsub32 : ball c R ⊆ closedBall c (3 * R / 2) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hsub32' : closedBall c (3 * R / 2) ⊆ closedBall c (2 * R) :=
    closedBall_subset_closedBall (by linarith)
  have hcap32 : ∀ x ∈ closedBall c (3 * R / 2), ∀ y ∈ closedBall c (3 * R / 2),
      ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ T (3 * R / 2) * ‖x - y‖ ^ (α:ℝ) :=
    fun x hx y hy => le_hessianHolderSeminorm hαr
      (fun x hx y hy => hN2 x (hsub32' hx) y (hsub32' hy)) hx hy
  have hdata0 : 0 ≤ V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H := by positivity
  have hC'le : C' ≤ 4 * Cε + C' := by linarith
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · -- the sup bound by interpolation on `closedBall x (R/2) ⊆ closedBall c (3R/2)`
    have hxsub : closedBall x (R / 2) ⊆ closedBall c (3 * R / 2) :=
      closedBall_subset_closedBall' (by rw [mem_ball] at hx; linarith)
    have hdv : ∀ z, HasFDerivAt v (fderiv ℝ v z) z := fun z =>
      ((hv.differentiable (by norm_num)) z).hasFDerivAt
    have hddv : ∀ z, HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) z) z := fun z =>
      (((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z).hasFDerivAt
    have h := hI (R / 2) (by positivity) v (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v)) hdv hddv x V
      (T (3 * R / 2)) (hT0 _) (fun z hz => hV z (hsub32' (hxsub hz)))
      (fun z hz => hcap32 z (hxsub hz) x (hxsub (mem_closedBall_self (by positivity))))
    have hR2 : (R / 2) ^ (2 + (α:ℝ)) = (R / 2) ^ 2 * (R / 2) ^ (α:ℝ) := by
      rw [Real.rpow_add (by positivity), Real.rpow_two]
    have hhalf : (R / 2) ^ (α:ℝ) ≤ u := Real.rpow_le_rpow (by positivity) (by linarith) hαr.le
    have hTu : T (3 * R / 2) * u ≤ C' * (V * R ^ (-(2:ℝ)) + M + H) := by
      have e4 : R ^ (-(2:ℝ) - α) = (R ^ 2 * u)⁻¹ := by
        rw [show -(2:ℝ) - α = -(2 + α) by ring, Real.rpow_neg hR.le, hR2α]
      have e5 : R ^ (-(α:ℝ)) = u⁻¹ := by rw [Real.rpow_neg hR.le]
      have e6 : R ^ (-(2:ℝ)) = (R ^ 2)⁻¹ := by rw [Real.rpow_neg hR.le, Real.rpow_two]
      rw [e4, e5] at hT32
      rw [e6]
      calc T (3 * R / 2) * u ≤ C' * (V * (R ^ 2 * u)⁻¹ + M * u⁻¹ + H) * u :=
            mul_le_mul_of_nonneg_right hT32 hu0.le
        _ = C' * (V * (R ^ 2)⁻¹ + M + H * u) := by field_simp
        _ ≤ C' * (V * (R ^ 2)⁻¹ + M + H) := by gcongr; exact mul_le_of_le_one_right hH0 hu1
    have hR2pos : 0 < (R / 2) ^ 2 := by positivity
    have h' : ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ 4 * Cε * V * (R ^ 2)⁻¹ +
        1 / 8 * (T (3 * R / 2) * (R / 2) ^ (α:ℝ)) := by
      rw [hR2] at h
      have hR2' : (R / 2) ^ 2 * (R ^ 2)⁻¹ = 1 / 4 := by field_simp; ring
      have : (R / 2) ^ 2 * (4 * Cε * V * (R ^ 2)⁻¹ + 1 / 8 * (T (3 * R / 2) * (R / 2) ^ (α:ℝ))) =
          Cε * V + 1 / 8 * T (3 * R / 2) * ((R / 2) ^ 2 * (R / 2) ^ (α:ℝ)) := by
        linear_combination (4 * Cε * V) * hR2'
      rw [← this] at h
      exact le_of_mul_le_mul_left h hR2pos
    have e6 : R ^ (-(2:ℝ)) = (R ^ 2)⁻¹ := by rw [Real.rpow_neg hR.le, Real.rpow_two]
    rw [e6]
    rw [e6] at hTu
    have hTR : T (3 * R / 2) * (R / 2) ^ (α:ℝ) ≤ T (3 * R / 2) * u :=
      mul_le_mul_of_nonneg_left hhalf (hT0 _)
    have hVR : 0 ≤ V * (R ^ 2)⁻¹ := by positivity
    have hd0 : 0 ≤ V * (R ^ 2)⁻¹ + M + H := by positivity
    calc ‖fderiv ℝ (fderiv ℝ v) x‖
        ≤ 4 * Cε * V * (R ^ 2)⁻¹ + 1 / 8 * (T (3 * R / 2) * (R / 2) ^ (α:ℝ)) := h'
      _ ≤ 4 * Cε * (V * (R ^ 2)⁻¹ + M + H) + 1 / 8 * (C' * (V * (R ^ 2)⁻¹ + M + H)) := by
          have h1 : 4 * Cε * V * (R ^ 2)⁻¹ ≤ 4 * Cε * (V * (R ^ 2)⁻¹ + M + H) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h2 : T (3 * R / 2) * (R / 2) ^ (α:ℝ) ≤ C' * (V * (R ^ 2)⁻¹ + M + H) :=
            hTR.trans hTu
          linarith
      _ ≤ (4 * Cε + C') * (V * (R ^ 2)⁻¹ + M + H) := by
          have : 1 / 8 * (C' * (V * (R ^ 2)⁻¹ + M + H)) ≤ C' * (V * (R ^ 2)⁻¹ + M + H) := by
            have : 0 ≤ C' * (V * (R ^ 2)⁻¹ + M + H) := by positivity
            linarith
          linarith
  · calc ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖
        ≤ T (3 * R / 2) * ‖x - y‖ ^ (α:ℝ) := hcap32 x (hsub32 hx) y (hsub32 hy)
      _ ≤ C' * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) :=
          mul_le_mul_of_nonneg_right hT32 (by positivity)
      _ ≤ (4 * Cε + C') * (V * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
          gcongr

end FunctionalInequalities.Analysis
