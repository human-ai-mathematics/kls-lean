module

public import FunctionalInequalities.Analysis.IteratedDerivative.Interpolation

/-!
# Freezing the principal coefficients of a second-order operator

Supports the coefficient-freezing step in the proof of the interior Schauder estimate of
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7), Theorem 6.2, pp. 90–92, equations (6.17)–(6.19): the equation is rewritten
with the coefficients frozen at a center `c`, and the error `(a(c) - a(x)) D²u(x)` is made small in
the scaled Hölder norm by shrinking the radius.

The principal part is taken along a fixed finite family of direction pairs `(v i, w i)` of norm at
most one, with coefficients `a i` and an arbitrary bilinear field `B` (an actual second derivative
when the interpolation theorem is invoked):

* `principalPart`, `freezingError`, `freezing_identity`: the frozen principal part is the variable
  one plus the freezing error;
* `freezing_bounds`: if every coefficient has `α`-Hölder cap `K` on `closedBall c r`, `‖B‖ ≤ N` and
  `B` has `α`-Hölder cap `H` there, then the error is at most `card ι · K r^α N` in sup norm and has
  `α`-Hölder cap `card ι · K (N + r^α H)`;
* `exists_uniform_hessian_constant`: the Hessian interpolation constant of
  `exists_hessian_interpolation_constant` applies at every point of `closedBall c r` with data on
  `closedBall c (2r)`;
* `exists_small_freezing_radius`: a radius `ρ ∈ (0, 1]` with `card ι · K r^α ≤ η` for `r ≤ ρ`,
  chosen
  before any function data;
* `exists_freezing_absorption_constants`: for `0 < r ≤ ρ`, `r² |error| ≤ C M + η H r^{2+α}` and the
  scaled `α`-Hölder difference bound with the same right-hand side, where `M` bounds `|f|` and `H`
  is the `α`-Hölder cap of `D²f` on `closedBall c (2r)`; `C` and `ρ` are chosen after `E`, `ι`, `α`,
  `η` and `K` only, before the radius, coefficients, directions, function and center.

The Hölder cap `H` of the Hessian is an input. This module proves no Schauder estimate for
solutions of an elliptic equation, no lower-order terms and no ellipticity statement.
-/

@[expose] public section

noncomputable section
open Set Metric
namespace FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

/-- The actual principal part in a fixed finite family of directions. -/
def principalPart (a : ι → E → ℝ) (v w : ι → E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∑ i, a i x * B x (v i) (w i)

/-- Difference of the frozen and variable principal parts. -/
def freezingError (a : ι → E → ℝ) (v w : ι → E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (c x : E) : ℝ :=
  ∑ i, (a i c - a i x) * B x (v i) (w i)

/-- Freezing identity: the frozen principal part equals the variable principal part plus the
freezing error. -/
theorem freezing_identity (a : ι → E → ℝ) (v w : ι → E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (c x : E) :
    principalPart (fun i _ => a i c) v w B x =
      principalPart a v w B x + freezingError a v w B c x := by
  simp only [principalPart, freezingError, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem abs_eval_le (B : E →L[ℝ] E →L[ℝ] ℝ) {v w : E}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) : |B v w| ≤ ‖B‖ := by
  simpa only [Real.norm_eq_abs, mul_one] using B.le_of_opNorm₂_le_of_le le_rfl hv hw

/-- Genuine local product estimate: one coefficient increment times one Hessian. -/
theorem freezing_bounds
    {a : ι → E → ℝ} {v w : ι → E} {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    {c : E} {r α K N H : ℝ} (hr : 0 ≤ r) (hα : 0 ≤ α)
    (hK : 0 ≤ K)
    (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1)
    (ha : ∀ i, ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      |a i x - a i y| ≤ K * ‖x - y‖ ^ α)
    (hB : ∀ x ∈ closedBall c r, ‖B x‖ ≤ N)
    (hBH : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖B x - B y‖ ≤ H * ‖x - y‖ ^ α) :
    (∀ x ∈ closedBall c r, |freezingError a v w B c x| ≤
      Fintype.card ι * K * r ^ α * N) ∧
    (∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      |freezingError a v w B c x - freezingError a v w B c y| ≤
        Fintype.card ι * K * (N + r ^ α * H) * ‖x - y‖ ^ α) := by
  have hcoef (i : ι) (x : E) (hx : x ∈ closedBall c r) :
      |a i c - a i x| ≤ K * r ^ α := by
    have hb : ‖c - x‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hx
    exact (ha i c (mem_closedBall_self hr) x hx).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hb hα) hK)
  have hsum (g : ι → ℝ) (T : ℝ) (hg : ∀ i, |g i| ≤ T) :
      |∑ i, g i| ≤ Fintype.card ι * T := by
    calc
      _ ≤ ∑ i, |g i| := by simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ g
      _ ≤ ∑ _i : ι, T := Finset.sum_le_sum fun i _ => hg i
      _ = _ := by simp
  constructor
  · intro x hx
    have h := hsum (fun i => (a i c - a i x) * B x (v i) (w i)) (K * r ^ α * N)
      (fun i => by
        rw [abs_mul]
        exact mul_le_mul (hcoef i x hx) ((abs_eval_le _ (hv i) (hw i)).trans (hB x hx))
          (abs_nonneg _) (by positivity))
    simpa only [freezingError, mul_assoc] using h
  · intro x hx y hy
    have he (i : ι) :
        (a i c - a i x) * B x (v i) (w i) - (a i c - a i y) * B y (v i) (w i) =
        (a i y - a i x) * B x (v i) (w i) +
          (a i c - a i y) * (B x - B y) (v i) (w i) := by
      simp only [sub_apply]
      ring
    have h := hsum (fun i => (a i c - a i x) * B x (v i) (w i) -
        (a i c - a i y) * B y (v i) (w i))
      (K * (N + r ^ α * H) * ‖x - y‖ ^ α) (fun i => by
        rw [he]
        calc
          _ ≤ |(a i y - a i x) * B x (v i) (w i)| +
              |(a i c - a i y) * (B x - B y) (v i) (w i)| := by
            simpa only [Real.norm_eq_abs] using norm_add_le
              ((a i y - a i x) * B x (v i) (w i))
              ((a i c - a i y) * (B x - B y) (v i) (w i))
          _ ≤ (K * ‖x - y‖ ^ α) * N + (K * r ^ α) * (H * ‖x - y‖ ^ α) := by
            rw [abs_mul, abs_mul]
            apply add_le_add
            · apply mul_le_mul
              · simpa only [norm_sub_rev] using ha i y hy x hx
              · exact (abs_eval_le _ (hv i) (hw i)).trans (hB x hx)
              · exact abs_nonneg _
              · positivity
            · exact mul_le_mul (hcoef i y hy)
                ((abs_eval_le _ (hv i) (hw i)).trans (hBH x hx y hy))
                (abs_nonneg _) (by positivity)
          _ = _ := by ring)
    simpa only [freezingError, ← Finset.sum_sub_distrib, mul_assoc] using h

/-- The Hessian interpolation constant is uniform at every center of the smaller ball, with data
on the doubled ball. -/
theorem exists_uniform_hessian_constant (α : ℝ) (hα : 0 < α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (r : ℝ),
          0 < r →
            ∀ (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (B : E → E →L[ℝ] E →L[ℝ] ℝ),
              (∀ z, HasFDerivAt f (f' z) z) →
                (∀ z, HasFDerivAt f' (B z) z) →
                  ∀ (c : E) (M H : ℝ),
                    0 ≤ H →
                      (∀ z ∈ closedBall c (2 * r), |f z| ≤ M) →
                        (∀ x ∈ closedBall c (2 * r),
                            ∀ y ∈ closedBall c (2 * r), ‖B x - B y‖ ≤ H * ‖x - y‖ ^ α) →
                          ∀ x ∈ closedBall c r, r ^ 2 * ‖B x‖ ≤ C * M + ε * H * r ^ (2 + α) := by
  obtain ⟨C, hC, hI⟩ :=
    FunctionalInequalities.Analysis.exists_hessian_interpolation_constant (E := E) α hα ε hε
  refine ⟨C, hC, ?_⟩
  intro r hr f f' B hf hf' c M H hH hM hBH x hx
  have hs : closedBall x r ⊆ closedBall c (2 * r) :=
    closedBall_subset_closedBall' (by rw [mem_closedBall] at hx; linarith)
  have hx2 : x ∈ closedBall c (2 * r) := hs (mem_closedBall_self hr.le)
  exact
    hI r hr f f' B hf hf' x M H hH (fun z hz => hM z (hs hz)) (fun z hz => hBH z (hs hz) x hx2)

/-- A positive radius making the coefficient-oscillation factor `card ι · K r^α` at most `η` can be
chosen before any function or seminorm data. -/
theorem exists_small_freezing_radius (α : ℝ) (hα : 0 < α) (η : ℝ) (hη : 0 < η)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ ρ →
      (Fintype.card ι : ℝ) * K * r ^ α ≤ η := by
  let A : ℝ := Fintype.card ι * K + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let ρ : ℝ := min 1 ((η / A) ^ α⁻¹)
  have hρ : 0 < ρ := lt_min zero_lt_one (Real.rpow_pos_of_pos (div_pos hη hA) _)
  refine ⟨ρ, hρ, min_le_left _ _, ?_⟩
  intro r hr hrρ
  have hra : r ^ α ≤ η / A := by
    have h := Real.rpow_le_rpow hr.le (hrρ.trans (min_le_right _ _)) hα.le
    rwa [Real.rpow_inv_rpow (div_nonneg hη.le hA.le) hα.ne'] at h
  calc
    _ ≤ A * r ^ α := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (by positivity)
    _ ≤ A * (η / A) := mul_le_mul_of_nonneg_left hra hA.le
    _ = η := by field_simp

/-- Scaled frozen-principal-part errors have an arbitrarily small Hessian-seminorm
coefficient. Both constants and the permitted radius are selected before `f`, `M`, `H`.
The seminorm cap `H` itself remains an input; no PDE Schauder conclusion is assumed. -/
theorem exists_freezing_absorption_constants
    (α : ℝ) (hα : 0 < α) (η : ℝ) (hη : 0 < η) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ (r : ℝ), 0 < r → r ≤ ρ →
      ∀ (a : ι → E → ℝ) (v w : ι → E)
        (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (B : E → E →L[ℝ] E →L[ℝ] ℝ),
      (∀ z, HasFDerivAt f (f' z) z) → (∀ z, HasFDerivAt f' (B z) z) →
      (∀ i, ‖v i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) →
      ∀ (c : E) (M H : ℝ), 0 ≤ H →
      (∀ z ∈ closedBall c (2 * r), |f z| ≤ M) →
      (∀ x ∈ closedBall c (2 * r), ∀ y ∈ closedBall c (2 * r),
        ‖B x - B y‖ ≤ H * ‖x - y‖ ^ α) →
      (∀ i, ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
        |a i x - a i y| ≤ K * ‖x - y‖ ^ α) →
      (∀ x ∈ closedBall c r, r ^ 2 * |freezingError a v w B c x| ≤
        C * M + η * H * r ^ (2 + α)) ∧
      (∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
        r ^ (2 + α) * |freezingError a v w B c x - freezingError a v w B c y| ≤
          (C * M + η * H * r ^ (2 + α)) * ‖x - y‖ ^ α) := by
    obtain ⟨D, hD, hI⟩ := exists_uniform_hessian_constant (E := E) α hα 1 zero_lt_one
    obtain ⟨ρ, hρ, hρ1, hsmall⟩ :=
      exists_small_freezing_radius (ι := ι) α hα (η / 2) (by positivity) K hK
    let m : ℝ := Fintype.card ι * K
    have hm : 0 ≤ m := by dsimp [m]; positivity
    refine ⟨m * D + 1, ρ, by positivity, hρ, hρ1, ?_⟩
    intro r hr hrρ a v w f f' B hf hf' hv hw c M H hH hM hBH ha
    have hr1 : r ≤ 1 := hrρ.trans hρ1
    have hM0 : 0 ≤ M :=
      (abs_nonneg (f c)).trans (hM c (mem_closedBall_self (by linarith)))
    have hra : r ^ α ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow hr.le hr1 hα.le
    have hmr : m * r ^ α ≤ η / 2 := hsmall r hr hrρ
    have hpow : r ^ (2 + α) = r ^ 2 * r ^ α := by rw [Real.rpow_add hr, Real.rpow_two]
    let N : ℝ := D * M / r ^ 2 + H * r ^ α
    have hcap : ∀ x ∈ closedBall c r, ‖B x‖ ≤ N := by
      intro x hx
      have h := hI r hr f f' B hf hf' c M H hH hM hBH x hx
      simp only [one_mul] at h
      have he : N * r ^ 2 = D * M + H * r ^ (2 + α) := by
        dsimp [N]
        rw [hpow]
        field_simp
      apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hr)).mp
      nlinarith [h, he]
    have hball : closedBall c r ⊆ closedBall c (2 * r) :=
      closedBall_subset_closedBall (by linarith)
    obtain ⟨hb, hh⟩ :=
      freezing_bounds hr.le hα.le hK hv hw ha hcap
        (fun x hx y hy => hBH x (hball hx) y (hball hy))
    have hmain : r ^ 2 * (m * r ^ α * N) ≤ (m * D + 1) * M + η * H * r ^ (2 + α) := by
      have he :
        r ^ 2 * (m * r ^ α * N) = m * r ^ α * D * M + (m * r ^ α) * H * r ^ (2 + α) := by
        dsimp [N]
        rw [hpow]
        field_simp
      rw [he]
      have h1 : m * r ^ α * D * M ≤ m * D * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hra hm)
            hD.le)
          hM0
      have h2 : (m * r ^ α) * H * r ^ (2 + α) ≤ η * H * r ^ (2 + α) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : m * r ^ α ≤ η) hH) (by positivity)
      nlinarith
    have hmainH :
      r ^ (2 + α) * (m * (N + r ^ α * H)) ≤ (m * D + 1) * M + η * H * r ^ (2 + α) := by
      have he :
        r ^ (2 + α) * (m * (N + r ^ α * H)) =
          m * r ^ α * D * M + (2 * (m * r ^ α)) * H * r ^ (2 + α) := by
        dsimp [N]
        rw [hpow]
        field_simp
        ring
      rw [he]
      have h1 : m * r ^ α * D * M ≤ m * D * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hra hm)
            hD.le)
          hM0
      have h2 : (2 * (m * r ^ α)) * H * r ^ (2 + α) ≤ η * H * r ^ (2 + α) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : 2 * (m * r ^ α) ≤ η) hH)
          (by positivity)
      nlinarith
    constructor
    · intro x hx
      exact (mul_le_mul_of_nonneg_left (hb x hx) (sq_nonneg r)).trans hmain
    · intro x hx y hy
      calc
        _ ≤ r ^ (2 + α) * (m * (N + r ^ α * H) * ‖x - y‖ ^ α) :=
          mul_le_mul_of_nonneg_left (hh x hx y hy) (by positivity)
        _ = (r ^ (2 + α) * (m * (N + r ^ α * H))) * ‖x - y‖ ^ α := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmainH (by positivity)

end FunctionalInequalities.Analysis
