module

public import FunctionalInequalities.Analysis.OrthonormalPair
public import FunctionalInequalities.Analysis.LogRadial.Gradient
public import FunctionalInequalities.Analysis.LogRadial.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import FunctionalInequalities.Analysis.Matrix.Positivity
public import FunctionalInequalities.Analysis.LogRadial.Calculus
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The two-plane log/radial barrier operator margin (CNS1984 Lemma 5.1, barrier display p. 386)

In `ℝ²` with `s = x₀ - β`, `x₁ > 0` and `r = √(s² + x₁²)`, the radial/log part of the CNS barrier is
`φ = (r + s - ε x₁ log r²) / 2`. For a coefficient matrix `A`, not assumed symmetric, with
`ℓ ‖v‖² ≤ ∑ Aᵢⱼ vᵢ vⱼ ≤ Λ ‖v‖²` and `ε ≤ ℓ / (24 Λ)`, the contraction of `A` with the actual Fréchet
Hessian
of `φ` is at least `ℓ / (4 r)`. The constant `24` is a conservative derived support constant, not a
numbered
constant of the source.

Proof: the shared constructed-profile producer `contDiffAt_fderiv_fderiv_log_radial_profile` gives
smoothness and
the actual second derivative (radial and logarithmic pieces, affine part zero).
Only `A₀₀`, `A₁₁` and `A₀₁ + A₁₀` enter the trace against the symmetric Hessian, and the quadratic
bounds control
exactly these: the radial contraction is `Q_A(x₁, -s) / r³ ≥ ℓ / r`, and the logarithmic one has
size at most
`12 Λ / r`.

Scope: ambient `ℝ²` only; no drift or zeroth-order term, comparison, modulus or existence statement.
-/

@[expose] public section

section
open Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- The coordinate quadratic form of a `2 × 2` matrix at `(a, b)`. -/
private lemma quadratic_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) :
    (∑ i, ∑ j, A i j * (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)) i *
      (WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2)) j) =
      A 0 0 * a ^ 2 + (A 0 1 + A 1 0) * a * b + A 1 1 * b ^ 2 := by
  simp [Fin.sum_univ_two]
  ring

private lemma norm_sq_fin_two (a b : ℝ) :
    ‖(WithLp.toLp 2 ![a, b] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, sq_abs]

open scoped Matrix.Norms.Elementwise in
/--
**Coefficient control from the raw quadratic bounds**: the diagonal entries and the symmetric
off-diagonal
sum (never a raw off-diagonal entry), plus the lower bound at an arbitrary vector `(a, b)`. -/
private lemma coefficient_bounds (A : Matrix (Fin 2) (Fin 2) ℝ) {ell Λ : ℝ} (hell_pos : 0 < ell)
    (hell :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        ell * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, A i j * v i * v j) ∧
          (∑ i, ∑ j, A i j * v i * v j) ≤ Λ * ‖v‖ ^ 2)
    (a b : ℝ) :
    (0 ≤ A 0 0 ∧ A 0 0 ≤ Λ) ∧
      (0 ≤ A 1 1 ∧ A 1 1 ≤ Λ) ∧
        |A 0 1 + A 1 0| ≤ 2 * Λ ∧
          ell * (a ^ 2 + b ^ 2) ≤ A 0 0 * a ^ 2 + (A 0 1 + A 1 0) * a * b + A 1 1 * b ^ 2 := by
  have h :
    ∀ a b : ℝ,
      ell * (a ^ 2 + b ^ 2) ≤ A 0 0 * a ^ 2 + (A 0 1 + A 1 0) * a * b + A 1 1 * b ^ 2 ∧
        A 0 0 * a ^ 2 + (A 0 1 + A 1 0) * a * b + A 1 1 * b ^ 2 ≤ Λ * (a ^ 2 + b ^ 2) :=
    fun a b => by
    have := hell (WithLp.toLp 2 ![a, b])
    rwa [quadratic_fin_two, norm_sq_fin_two] at this
  obtain ⟨h10l, h10u⟩ := h 1 0
  obtain ⟨h01l, h01u⟩ := h 0 1
  norm_num at h10l h10u h01l h01u
  have hΛ0 : 0 ≤ Λ := by linarith
  have hn : ∀ w : Fin 2 → ℝ, 0 ≤ ∑ i, ∑ j, A i j * w i * w j := by
    intro w
    exact le_trans (mul_nonneg hell_pos.le (sq_nonneg _)) (hell (WithLp.toLp 2 w)).1
  have hu : ∀ w : Fin 2 → ℝ, (∑ i, ∑ j, A i j * w i * w j) ≤ Λ * ∑ i, w i ^ 2 := by
    intro w
    simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using
      (hell (WithLp.toLp 2 w)).2
  have hnS := norm_symmetricPart_le_of_quadratic_le A hΛ0 hn hu
  have hentry := (Matrix.norm_le_iff hΛ0).mp hnS (0 : Fin 2) (1 : Fin 2)
  have hsum : |A 0 1 + A 1 0| ≤ 2 * Λ := by
    have hhalf : (1 / 2 : ℝ) * |A 0 1 + A 1 0| ≤ Λ := by
      simpa only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul,
        Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hentry
    linarith
  exact ⟨⟨by linarith, h10u⟩, ⟨by linarith, h01u⟩, hsum, (h a b).1⟩

/--
**The scalar margin**: the radial contraction `Q / r³ ≥ ℓ / r`, the logarithmic numerator is at
least
`-12 Λ r³`, and `24 Λ ε ≤ ℓ`. -/
private lemma margin_arith {a00 a11 m ell Λ ε s y : ℝ} (hell_pos : 0 < ell) (hΛ : 0 < Λ)
    (hε : 0 ≤ ε) (hεcap : ε ≤ ell / (24 * Λ)) (hy : 0 < y) (h00 : 0 ≤ a00 ∧ a00 ≤ Λ)
    (h11 : 0 ≤ a11 ∧ a11 ≤ Λ) (hm : |m| ≤ 2 * Λ)
    (hQ : ell * (y ^ 2 + (-s) ^ 2) ≤ a00 * y ^ 2 + m * y * (-s) + a11 * (-s) ^ 2) :
    ell / (4 * Real.sqrt (s ^ 2 + y ^ 2)) ≤
      ((y ^ 2 * a00 - s * y * m + s ^ 2 * a11) / Real.sqrt (s ^ 2 + y ^ 2) ^ 3 +
          ε *
            ((2 * y * (s ^ 2 - y ^ 2) * a00 + 2 * s * (y ^ 2 - s ^ 2) * m -
                2 * y * (3 * s ^ 2 + y ^ 2) * a11) /
              (s ^ 2 + y ^ 2) ^ 2)) /
        2 := by
  have hS : 0 < s ^ 2 + y ^ 2 := by positivity
  set r := Real.sqrt (s ^ 2 + y ^ 2) with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hS
  have hr2 : r ^ 2 = s ^ 2 + y ^ 2 := Real.sq_sqrt hS.le
  have hsr : |s| ≤ r := Real.abs_le_sqrt (by nlinarith)
  have hyr : |y| ≤ r := Real.abs_le_sqrt (by nlinarith)
  have hdiff : |s ^ 2 - y ^ 2| ≤ r ^ 2 := by
    rw [hr2, abs_le]
    constructor <;> nlinarith
  have hdiff' : |y ^ 2 - s ^ 2| ≤ r ^ 2 := by rw [abs_sub_comm]; exact hdiff
  have hsum3 : |3 * s ^ 2 + y ^ 2| ≤ 3 * r ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have ha00 : |a00| ≤ Λ := abs_le.mpr ⟨by linarith [h00.1], h00.2⟩
  have ha11 : |a11| ≤ Λ :=
    abs_le.mpr
      ⟨by linarith [h11.1], h11.2⟩
  -- radial: `Q / r³ ≥ ℓ / r`

  have hQ' : ell * r ^ 2 ≤ y ^ 2 * a00 - s * y * m + s ^ 2 * a11 := by
    rw [hr2]
    nlinarith
  have hTR : ell / r ≤ (y ^ 2 * a00 - s * y * m + s ^ 2 * a11) / r ^ 3 := by
    rw [div_le_div_iff₀ hr (by positivity)]
    nlinarith
  -- logarithmic: numerator at least `-12 Λ r³`

  have t1 : |2 * y * (s ^ 2 - y ^ 2) * a00| ≤ 2 * r * r ^ 2 * Λ := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    gcongr
  have t2 : |2 * s * (y ^ 2 - s ^ 2) * m| ≤ 2 * r * r ^ 2 * (2 * Λ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    gcongr
  have t3 : |2 * y * (3 * s ^ 2 + y ^ 2) * a11| ≤ 2 * r * (3 * r ^ 2) * Λ := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    gcongr
  have hN :
    -(12 * Λ * r ^ 3) ≤
      2 * y * (s ^ 2 - y ^ 2) * a00 + 2 * s * (y ^ 2 - s ^ 2) * m -
        2 * y * (3 * s ^ 2 + y ^ 2) * a11 := by
    have := (abs_le.mp t1).1
    have := (abs_le.mp t2).1
    have := (abs_le.mp t3).2
    nlinarith
  have hTL :
    -(12 * Λ) / r ≤
      (2 * y * (s ^ 2 - y ^ 2) * a00 + 2 * s * (y ^ 2 - s ^ 2) * m -
          2 * y * (3 * s ^ 2 + y ^ 2) * a11) /
        (s ^ 2 + y ^ 2) ^ 2 := by
    rw [← hr2, div_le_div_iff₀ hr (by positivity)]
    nlinarith
  have hεΛ : 24 * Λ * ε ≤ ell := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 24 * Λ)).mp hεcap
    linarith
  have hεTL :
    -(ell / (2 * r)) ≤
      ε *
        ((2 * y * (s ^ 2 - y ^ 2) * a00 + 2 * s * (y ^ 2 - s ^ 2) * m -
            2 * y * (3 * s ^ 2 + y ^ 2) * a11) /
          (s ^ 2 + y ^ 2) ^ 2) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hTL hε)
    rw [mul_div_assoc', le_div_iff₀ hr]
    field_simp
    nlinarith
  have hsplit : ell / (4 * r) = (ell / r - ell / (2 * r)) / 2 := by
    field_simp
    ring
  rw [hsplit]
  linarith

theorem plane_log_radial_barrier_trace_lower
    (A : Matrix (Fin 2) (Fin 2) ℝ) {ell Λ ε : ℝ}
    (hell_pos : 0 < ell) (hΛ : 0 < Λ) (hε : 0 ≤ ε) (hεcap : ε ≤ ell / (24 * Λ))
    (hell : ∀ v : EuclideanSpace ℝ (Fin 2),
      ell * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, A i j * v i * v j) ∧
        (∑ i, ∑ j, A i j * v i * v j) ≤ Λ * ‖v‖ ^ 2)
    (β : ℝ) {x : EuclideanSpace ℝ (Fin 2)} (hx : 0 < x 1) :
    let φ : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
      (Real.sqrt ((y 0 - β) ^ 2 + (y 1) ^ 2) + (y 0 - β) -
        ε * y 1 * Real.log ((y 0 - β) ^ 2 + (y 1) ^ 2)) / 2
    ContDiffAt ℝ ∞ φ x ∧
      ell / (4 * Real.sqrt ((x 0 - β) ^ 2 + (x 1) ^ 2)) ≤
        Matrix.trace (A * ((Matrix.of fun i j => fderiv ℝ (fderiv ℝ φ) x
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))) :
          Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro φ
  set p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 0 with hp
  set q : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 1 with hq
  have hqx : 0 < q x := hx
  -- the shared constructed-profile producer: smoothness and the actual second derivative
  obtain ⟨hC, hH⟩ := contDiffAt_fderiv_fderiv_log_radial_profile p q β ε hqx
  have hφ : φ = fun y => (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
      ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) / 2 := rfl
  refine ⟨hφ ▸ hC, ?_⟩
  · rw [hφ]
    have hp0 : p (EuclideanSpace.single 0 1) = 1 := by simp [hp]
    have hp1 : p (EuclideanSpace.single 1 1) = 0 := by simp [hp]
    have hq0 : q (EuclideanSpace.single 0 1) = 0 := by simp [hq]
    have hq1 : q (EuclideanSpace.single 1 1) = 1 := by simp [hq]
    have hpx : p x = x 0 := rfl
    have hqx' : q x = x 1 := rfl
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, hH,
      hp0, hp1, hq0, hq1, hpx, hqx']
    obtain ⟨h00, h11, hm, hQ⟩ := coefficient_bounds A hell_pos hell (x 1) (-(x 0 - β))
    refine (margin_arith hell_pos hΛ hε hεcap hx h00 h11 hm hQ).trans_eq ?_
    ring

end FunctionalInequalities.Analysis

end


/-!
# The ambient tangent–normal barrier operator (CNS1984 Lemma 5.1, barrier display p. 386)

In `ℝ^{m+2}` (`m ≥ 0`), take a unit tangent vector `ζ` (`ζₙ = 0`) and the standard last normal `ν =
eₙ`. The CNS
barrier profile in the plane of `ζ` and `ν` is
`φ(y) = (√((⟨ζ, y⟩ - β)² + yₙ²) + (⟨ζ, y⟩ - β) - ε yₙ log((⟨ζ, y⟩ - β)² + yₙ²)) / 2`.
For a coefficient matrix `A` (not assumed symmetric) with `ℓ ‖v‖² ≤ ∑ Aᵢⱼ vᵢ vⱼ ≤ Λ ‖v‖²` and `ε ≤ ℓ
/ (24 Λ)`,
the contraction of `A` with the actual ambient Fréchet Hessian of `φ` is at least `ℓ / (4 r)`.

Proof:
* `ζ, ν` is orthonormal, so `J v = v₀ ζ + v₁ ν` is an isometry `ℝ² → ℝ^{m+2}`.
* The compressed matrix `Bₐ_b = ∑ Aᵢⱼ (fₐ)ᵢ (f_b)ⱼ` (`f₀ = ζ`, `f₁ = ν`) has `Q_B(v) = Q_A(J v)`,
  hence the SAME `ℓ`
  and `Λ`.
* The shared profile producer gives both Hessians in the normal form
  `a·pv·pw + b·(pv·qw + qv·pw) + c·qv·qw`, with the same `a, b, c`: the ambient one (`p = ⟨ζ, ·⟩`,
  `q = yₙ`, at
  `x`) and the planar one (`p = y₀`, `q = y₁`, at `(⟨ζ, x⟩, xₙ)`). Hence
  `tr(A·H_amb) = a B₀₀ + b (B₀₁ + B₁₀) + c B₁₁ = tr(B·H₂)`.
* The planar margin `plane_log_radial_barrier_trace_lower` is then applied to `B`.

Scope: ambient dimension `m + 2 ≥ 2` only; no drift or zeroth-order term, comparison, modulus or
existence.
-/

section
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The profile Hessian formula in the normal form `a·pv·pw + b·(pv·qw + qv·pw) + c·qv·qw`. -/
private lemma profile_formula_normal (s t ε pv qv pw qw : ℝ) :
    ((t ^ 2 * pv * pw - s * t * (pv * qw + qv * pw) + s ^ 2 * qv * qw) /
            (Real.sqrt (s ^ 2 + t ^ 2)) ^ 3 +
          ε *
            ((2 * t * (s ^ 2 - t ^ 2) * pv * pw +
                  2 * s * (t ^ 2 - s ^ 2) * (pv * qw + qv * pw) -
                2 * t * (3 * s ^ 2 + t ^ 2) * qv * qw) /
              ((s ^ 2 + t ^ 2) ^ 2))) /
        2 =
      ((t ^ 2 / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 +
                ε * (2 * t * (s ^ 2 - t ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
              2) *
            (pv * pw) +
          ((-(s * t) / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 +
                ε * (2 * s * (t ^ 2 - s ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
              2) *
            (pv * qw + qv * pw) +
        ((s ^ 2 / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 -
              ε * (2 * t * (3 * s ^ 2 + t ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
            2) *
          (qv * qw) := by
  ring

/-- The frame `v ↦ v₀ ζ + v₁ eₙ` is an isometry: `ζ` is a unit vector orthogonal to `eₙ`. -/
private lemma frame_norm_sq {m : ℕ} (zeta : EuclideanSpace ℝ (Fin (m + 2)))
    (hznorm : ‖zeta‖ = 1) (hztan : zeta (Fin.last (m + 1)) = 0) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖v 0 • zeta + v 1 • EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)‖ ^ 2 = ‖v‖ ^ 2 := by
  have hin : ⟪zeta, EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)⟫ = 0 := by
    rw [EuclideanSpace.inner_single_right]
    simp [hztan]
  have h :=
    orthogonal_pair_norm_sq hznorm
      (show ‖EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ)‖ = 1 by simp) hin (v 0) (v 1)
  simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, PiLp.toLp_apply] using h

/--
**Compression**: the quadratic form of `Bₐ_b = ∑ Aᵢⱼ (fₐ)ᵢ (f_b)ⱼ` is that of `A` on `v₀ f₀ + v₁
f₁`. -/
private lemma quadratic_compress {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
    (f : Fin 2 → EuclideanSpace ℝ (Fin (m + 2))) (v : EuclideanSpace ℝ (Fin 2)) :
    (∑ a,
        ∑ b,
          (Matrix.of fun a b => ∑ i, ∑ j, A i j * f a i * f b j : Matrix (Fin 2) (Fin 2) ℝ) a
                b *
              v a *
            v b) =
      ∑ i, ∑ j, A i j * (v 0 • f 0 + v 1 • f 1) i * (v 0 • f 0 + v 1 • f 1) j := by
  simp only [Fin.sum_univ_two, Matrix.of_apply, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Trace of a normal-form Hessian** against `A`, in terms of the compressed entries. -/
private lemma trace_normal_form {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
    (u w : EuclideanSpace ℝ (Fin (m + 2))) (a b c : ℝ) :
    (∑ i, ∑ j, A i j * (a * (u j * u i) + b * (u j * w i + w j * u i) + c * (w j * w i))) =
      a * (∑ i, ∑ j, A i j * u i * u j) +
        b * ((∑ i, ∑ j, A i j * u i * w j) + (∑ i, ∑ j, A i j * w i * u j)) +
        c * (∑ i, ∑ j, A i j * w i * w j) := by
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tangent_normal_log_radial_barrier_trace_lower {m : ℕ}
    (zeta : EuclideanSpace ℝ (Fin (m + 2))) (hznorm : ‖zeta‖ = 1)
    (hztan : zeta (Fin.last (m + 1)) = 0) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
    {ell Λ ε : ℝ} (hell_pos : 0 < ell) (hΛ : 0 < Λ) (hε : 0 ≤ ε) (hεcap : ε ≤ ell / (24 * Λ))
    (hell :
      ∀ v : EuclideanSpace ℝ (Fin (m + 2)),
        ell * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, A i j * v i * v j) ∧
          (∑ i, ∑ j, A i j * v i * v j) ≤ Λ * ‖v‖ ^ 2)
    (β : ℝ) {x : EuclideanSpace ℝ (Fin (m + 2))} (hx : 0 < x (Fin.last (m + 1))) :
    let φ : EuclideanSpace ℝ (Fin (m + 2)) → ℝ := fun y =>
      (Real.sqrt (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last (m + 1))) ^ 2) +
            ((∑ i, zeta i * y i) - β) -
          ε * y (Fin.last (m + 1)) *
            Real.log (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last (m + 1))) ^ 2)) /
        2
    ContDiffAt ℝ ∞ φ x ∧
      ell / (4 * Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2)) ≤
        Matrix.trace
          (A *
            ((Matrix.of fun i j =>
                fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                  (EuclideanSpace.single j (1 : ℝ))) :
              Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) := by
  intro φ
  set ν : EuclideanSpace ℝ (Fin (m + 2)) :=
    EuclideanSpace.single (Fin.last (m + 1)) (1 : ℝ) with hν
  set p : EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ] ℝ := innerSL ℝ zeta with hp
  set q : EuclideanSpace ℝ (Fin (m + 2)) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last (m + 1)) with
    hq
  have hpy : ∀ y, p y = ∑ i, zeta i * y i := fun y => by simp [hp, PiLp.inner_apply, mul_comm]
  have hqy : ∀ y, q y = y (Fin.last (m + 1)) := fun _ => rfl
  have hqx : 0 < q x :=
    hx
  -- the shared constructed-profile producer, ambient instance

  obtain ⟨hC, hH⟩ := contDiffAt_fderiv_fderiv_log_radial_profile p q β ε hqx
  have hφ :
    φ = fun y =>
      (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
          ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) /
        2 := by
    funext y
    simp only [φ, hpy, hqy]
  refine
    ⟨hφ ▸ hC, ?_⟩
  -- the orthonormal frame `ζ, ν`, the compressed matrix and its SAME ellipticity bounds

  set f : Fin 2 → EuclideanSpace ℝ (Fin (m + 2)) := ![zeta, ν] with hf
  set B : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun a b => ∑ i, ∑ j, A i j * f a i * f b j with
    hB
  have hellB :
    ∀ v : EuclideanSpace ℝ (Fin 2),
      ell * ‖v‖ ^ 2 ≤ (∑ a, ∑ b, B a b * v a * v b) ∧
        (∑ a, ∑ b, B a b * v a * v b) ≤ Λ * ‖v‖ ^ 2 := by
    intro v
    have hJ : v 0 • f 0 + v 1 • f 1 = v 0 • zeta + v 1 • ν := by simp [hf]
    rw [hB, quadratic_compress, hJ, ← frame_norm_sq zeta hznorm hztan v]
    exact
      hell
        _
  -- the planar point and the planar margin for `B`

  set x2 : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![p x, q x] with hx2
  have hx2_1 : 0 < x2 1 := by simpa [hx2] using hqx
  have hBO := (plane_log_radial_barrier_trace_lower B hell_pos hΛ hε hεcap hellB β hx2_1).2
  have hx20 : (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x2 = p x := by
    simp [hx2]
  have hx21 : (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x2 = q x := by
    simp [hx2]
  -- both Hessians in normal form with the SAME coefficients

  set s := p x - β with hs
  set t := q x with ht
  have hHn :
    ∀ v w,
      fderiv ℝ
          (fderiv ℝ
            (fun y =>
              (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
                  ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) /
                2))
          x v w =
        ((t ^ 2 / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 +
                  ε * (2 * t * (s ^ 2 - t ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
                2) *
              (p v * p w) +
            ((-(s * t) / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 +
                  ε * (2 * s * (t ^ 2 - s ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
                2) *
              (p v * q w + q v * p w) +
          ((s ^ 2 / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 -
                ε * (2 * t * (3 * s ^ 2 + t ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
              2) *
            (q v * q w) :=
    fun v w => (hH v w).trans (profile_formula_normal s t ε _ _ _ _)
  have hp2 :
    (0 : ℝ) < (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x2 := hx2_1
  obtain ⟨-, hH2⟩ :=
    contDiffAt_fderiv_fderiv_log_radial_profile (EuclideanSpace.proj (0 : Fin 2))
      (EuclideanSpace.proj (1 : Fin 2)) β ε hp2
  have hH2n :
    ∀ v w : EuclideanSpace ℝ (Fin 2),
      fderiv ℝ
          (fderiv ℝ
            (fun y : EuclideanSpace ℝ (Fin 2) =>
              (Real.sqrt ((y 0 - β) ^ 2 + (y 1) ^ 2) + (y 0 - β) -
                  ε * y 1 * Real.log ((y 0 - β) ^ 2 + (y 1) ^ 2)) /
                2))
          x2 v w =
        ((t ^ 2 / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 +
                  ε * (2 * t * (s ^ 2 - t ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
                2) *
              (v 0 * w 0) +
            ((-(s * t) / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 +
                  ε * (2 * s * (t ^ 2 - s ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
                2) *
              (v 0 * w 1 + v 1 * w 0) +
          ((s ^ 2 / Real.sqrt (s ^ 2 + t ^ 2) ^ 3 -
                ε * (2 * t * (3 * s ^ 2 + t ^ 2)) / (s ^ 2 + t ^ 2) ^ 2) /
              2) *
            (v 1 * w 1) := by
    intro v w
    have h := hH2 v w
    rw [hx20, hx21] at h
    exact h.trans (profile_formula_normal s t ε _ _ _ _)
  have hpe : ∀ j, p (EuclideanSpace.single j (1 : ℝ)) = zeta j := fun j => by
    rw [hpy]
    simp
  have hqe : ∀ j, q (EuclideanSpace.single j (1 : ℝ)) = ν j := fun j => by
    simp [hq, hν, eq_comm]
  -- the ambient trace equals the compressed planar trace

  have hamb :
    Matrix.trace
        (A *
          ((Matrix.of fun i j =>
              fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single j (1 : ℝ))) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) =
      Matrix.trace
        (B *
          ((Matrix.of fun a b =>
              fderiv ℝ
                (fderiv ℝ
                  (fun y : EuclideanSpace ℝ (Fin 2) =>
                    (Real.sqrt ((y 0 - β) ^ 2 + (y 1) ^ 2) + (y 0 - β) -
                        ε * y 1 * Real.log ((y 0 - β) ^ 2 + (y 1) ^ 2)) /
                      2))
                x2 (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ))) :
            Matrix (Fin 2) (Fin 2) ℝ)) := by
    rw [hφ]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, hHn, hpe, hqe,
      hH2n, Fin.sum_univ_two]
    rw [trace_normal_form]
    simp [hB, hf]
    ring
  have hLHS : (∑ i, zeta i * x i) = x2 0 := by
    rw [← hpy]
    exact hx20.symm
  have hlast : x (Fin.last (m + 1)) = x2 1 := hx21.symm
  rw [hLHS, hlast, hamb]
  exact hBO

end FunctionalInequalities.Analysis

end


/-!
# Small-radius drift margin of the CNS radial/log barrier profile (CNS1984 Lemma 5.1, p. 386)

For ellipticity constants `ℓ, Λ`, `0 ≤ ε ≤ ℓ / (24 Λ)` and a drift bound `B ≥ 0`, one radius `ρ ∈
(0, 1)` is
generated before every dimension, coefficient matrix, drift vector, unit tangent, shift and point.
Within
distance `r < ρ` of the singular set, the radial/log barrier profile `φ` satisfies
`ℓ / (8 r) ≤ tr(A D²φ) + Dφ(b)`. The constant `8` is a derived support constant.

Proof:
* The ambient trace bound `tangent_normal_log_radial_barrier_trace_lower` gives
  `tr(A D²φ) ≥ ℓ / (4 r)`.
* The first-derivative bound `tangent_normal_log_radial_profile_fderiv_norm_le` gives
  `‖Dφ‖ ≤ 2 + ε (|log r²| + 2)`, so `Dφ(b) ≥ -‖Dφ‖ ‖b‖`.
* The radius makes `r B (2 + ε (|log r²| + 2)) ≤ ℓ / 8`, because `r log r → 0` (Mathlib
  `Real.continuous_mul_log`).

Scope: only the radial/log part with bounded drift; no polynomial part, zeroth-order term or
comparison.
-/

section
open Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/--
**Generated small radius** (numeric budget): `r B (2 + ε (|log r²| + 2)) ≤ ℓ / 8` for all `0 < r <
ρ`. -/
theorem exists_log_radial_drift_budget_radius {ell ε B : ℝ} (hell_pos : 0 < ell) (hε : 0 ≤ ε)
    (hB : 0 ≤ B) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        ρ < 1 ∧ ∀ r : ℝ, 0 < r → r < ρ → r * B * (2 + ε * (|Real.log (r ^ 2)| + 2)) ≤ ell / 8 := by
  set η : ℝ := ell / (16 * (2 * B * ε + 1)) with hη
  have hBε : 0 ≤ 2 * B * ε := by positivity
  have hη0 : 0 < η := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp Real.continuous_mul_log.continuousAt η hη0
  set K : ℝ := B * (2 + 2 * ε) with hK
  have hK0 : 0 ≤ K := by positivity
  refine
    ⟨min (1 / 2) (min δ (ell / (16 * (K + 1)))),
      lt_min (by norm_num) (lt_min hδ0 (by positivity)),
      lt_of_le_of_lt (min_le_left _ _) (by norm_num), fun r hr hrρ => ?_⟩
  have hrδ : r < δ := lt_of_lt_of_le hrρ ((min_le_right _ _).trans (min_le_left _ _))
  have hrK : r < ell / (16 * (K + 1)) :=
    lt_of_lt_of_le hrρ ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : |Real.log (r ^ 2)| = 2 * |Real.log r| := by
    rw [Real.log_pow, abs_mul]
    norm_num
  have hrl : |r * Real.log r| < η := by
    have h := hδ (x := r) (by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact hrδ)
    simpa [Real.dist_eq] using h
  have hrl' : r * |Real.log r| ≤ η := by
    rw [abs_mul, abs_of_pos hr] at hrl
    exact hrl.le
  have e :
    r * B * (2 + ε * (|Real.log (r ^ 2)| + 2)) = r * K + 2 * B * ε * (r * |Real.log r|) := by
    rw [hlog, hK]
    ring
  have h1 : r * K ≤ ell / 16 := by
    calc
      r * K ≤ ell / (16 * (K + 1)) * K := mul_le_mul_of_nonneg_right hrK.le hK0
      _ ≤ ell / 16 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have h2 : 2 * B * ε * (r * |Real.log r|) ≤ ell / 16 := by
    calc
      2 * B * ε * (r * |Real.log r|) ≤ 2 * B * ε * η := mul_le_mul_of_nonneg_left hrl' hBε
      _ ≤ ell / 16 := by
        rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  rw [e]
  linarith

theorem exists_log_radial_drift_margin_radius {ell Λ ε B : ℝ} (hell_pos : 0 < ell) (hΛ : 0 < Λ)
    (hε : 0 ≤ ε) (hεcap : ε ≤ ell / (24 * Λ)) (hB : 0 ≤ B) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        ρ < 1 ∧
          ∀ (m : ℕ) (zeta : EuclideanSpace ℝ (Fin (m + 2))) (_hznorm : ‖zeta‖ = 1)
            (_hztan : zeta (Fin.last (m + 1)) = 0) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
            (_hell :
              ∀ v : EuclideanSpace ℝ (Fin (m + 2)),
                ell * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, A i j * v i * v j) ∧
                  (∑ i, ∑ j, A i j * v i * v j) ≤ Λ * ‖v‖ ^ 2)
            (b : EuclideanSpace ℝ (Fin (m + 2))) (_hb : ‖b‖ ≤ B) (β : ℝ)
            (x : EuclideanSpace ℝ (Fin (m + 2))) (_hx : 0 < x (Fin.last (m + 1)))
            (_hr : Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) < ρ),
            let φ : EuclideanSpace ℝ (Fin (m + 2)) → ℝ := fun y =>
              (Real.sqrt (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last (m + 1))) ^ 2) +
                    ((∑ i, zeta i * y i) - β) -
                  ε * y (Fin.last (m + 1)) *
                    Real.log (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last (m + 1))) ^ 2)) /
                2
            ell / (8 * Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2)) ≤
              Matrix.trace
                  (A *
                    ((Matrix.of fun i j =>
                        fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                          (EuclideanSpace.single j (1 : ℝ))) :
                      Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) +
                (fderiv ℝ φ x) b := by
  -- the radius is generated from `ℓ, ε, B` only

  obtain ⟨ρ, hρ0, hρ1, hsmall⟩ := exists_log_radial_drift_budget_radius (B := B) hell_pos hε hB
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro m zeta hznorm hztan A hell b hb β x hx hr
    φ
  -- ambient Hessian trace bound on the SAME `φ`

  have hAM :
    ell / (4 * Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2)) ≤
      Matrix.trace
        (A *
          ((Matrix.of fun i j =>
              fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single j (1 : ℝ))) :
            Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) :=
    (tangent_normal_log_radial_barrier_trace_lower zeta hznorm hztan A hell_pos hΛ hε hεcap hell
        β hx).2
  -- first-derivative bound on the SAME `φ`

  have hBD :
    ‖fderiv ℝ φ x‖ ≤
      2 + ε * (|Real.log (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2)| + 2) :=
    tangent_normal_log_radial_profile_fderiv_norm_le (m := m + 1) zeta hznorm.le β ε hε hx
  have hS0 : 0 < ((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2 := by positivity
  set r := Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hS0
  have hS : ((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2 = r ^ 2 :=
    (Real.sq_sqrt hS0.le).symm
  rw [hS] at hBD
  -- the directional derivative along the drift

  have hdir : -(‖fderiv ℝ φ x‖ * ‖b‖) ≤ (fderiv ℝ φ x) b := by
    have h := (fderiv ℝ φ x).le_opNorm b
    rw [Real.norm_eq_abs] at h
    exact neg_le_of_abs_le h
  have hcap0 : 0 ≤ 2 + ε * (|Real.log (r ^ 2)| + 2) := by positivity
  have hDb : ‖fderiv ℝ φ x‖ * ‖b‖ ≤ ell / (8 * r) := by
    have hsm := hsmall r hr0 hr
    calc
      ‖fderiv ℝ φ x‖ * ‖b‖ ≤ (2 + ε * (|Real.log (r ^ 2)| + 2)) * B :=
        mul_le_mul hBD hb (norm_nonneg _) hcap0
      _ ≤ ell / (8 * r) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
  have hsplit : ell / (4 * r) = ell / (8 * r) + ell / (8 * r) := by
    field_simp
    ring
  linarith

end FunctionalInequalities.Analysis

end


/-!
# Zeroth-order margin of the CNS radial/log barrier profile (CNS1984 Lemma 5.1, p. 386)

For ellipticity constants `ℓ, Λ`, `0 ≤ ε ≤ ℓ / (24 Λ)`, a drift bound `B ≥ 0` and a zeroth-order
bound `C ≥ 0`, one
radius `ρ ∈ (0, 1)` is generated before every dimension, coefficient, drift, zeroth-order
coefficient
`a ∈ [-C, 0]`, unit tangent, shift and point. Within distance `r < ρ` of the singular set, the
radial/log profile
`φ` is nonnegative and `ℓ / (16 r) ≤ tr(A D²φ) + Dφ(b) + a φ`. The constant `16` is a derived
support constant.

Proof:
* `ρ = min ρ₁ ρ₂`, where `ρ₁` is the drift-margin radius (`ℓ / (8 r) ≤ tr(A D²φ) + Dφ(b)`) and `ρ₂`
  is
  the shared numeric budget radius at `(ℓ / 2, C)`.
* With `s = ⟨ζ, x⟩ - β`, `y = xₙ > 0` and `r = √(s² + y²) < 1`: `|s|, y ≤ r` and `log r² < 0`. Hence
  `0 ≤ φ(x) = (r + s - ε y log r²) / 2 ≤ r (1 + (ε/2) |log r²|)`.
* The budget gives `r C φ(x) ≤ ℓ / 16`, so `a φ(x) ≥ -C φ(x) ≥ -ℓ / (16 r)`.
-/

section
open Filter
open scoped Topology ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- **Scalar zeroth-order step.** With `r² = s² + y²`, `0 < y`, `0 < r < 1`, the profile value
`v = (r + s - ε y log r²) / 2` satisfies `0 ≤ v ≤ r (1 + (ε/2) |log r²|)`; under the budget at
`(ℓ/2, C)` and a
drift margin `ℓ / (8 r) ≤ M`, every `a ∈ [-C, 0]` gives `ℓ / (16 r) ≤ M + a v`. -/
private lemma zeroth_margin_scalar {ell ε C a s y r M : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (ha : -C ≤ a ∧ a ≤ 0) (hy : 0 < y) (hr0 : 0 < r) (hr2 : r ^ 2 = s ^ 2 + y ^ 2) (hr1 : r < 1)
    (hbud : r * C * (2 + ε * (|Real.log (r ^ 2)| + 2)) ≤ ell / 2 / 8) (hm : ell / (8 * r) ≤ M) :
    0 ≤ (r + s - ε * y * Real.log (r ^ 2)) / 2 ∧
      ell / (16 * r) ≤ M + a * ((r + s - ε * y * Real.log (r ^ 2)) / 2) := by
  obtain ⟨hv0, hvle⟩ := log_radial_profile_value_bounds hε hy hr0 hr2 hr1
  set L := |Real.log (r ^ 2)| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  have hεL : 0 ≤ ε * L := mul_nonneg hε hL0
  have h1 : r * (1 + ε / 2 * L) ≤ 2 + ε * (L + 2) := by nlinarith
  have hrCv : r * C * ((r + s - ε * y * Real.log (r ^ 2)) / 2) ≤ ell / 16 := by
    calc
      r * C * ((r + s - ε * y * Real.log (r ^ 2)) / 2) ≤ r * C * (r * (1 + ε / 2 * L)) :=
        mul_le_mul_of_nonneg_left hvle (by positivity)
      _ ≤ r * C * (2 + ε * (L + 2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ell / 2 / 8 := hbud
      _ = ell / 16 := by ring
  have hCv : C * ((r + s - ε * y * Real.log (r ^ 2)) / 2) ≤ ell / (16 * r) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hav :
    -(C * ((r + s - ε * y * Real.log (r ^ 2)) / 2)) ≤
      a * ((r + s - ε * y * Real.log (r ^ 2)) / 2) := by
    nlinarith [ha.1]
  have hsplit : ell / (8 * r) = ell / (16 * r) + ell / (16 * r) := by
    field_simp
    ring
  exact ⟨hv0, by linarith⟩

theorem exists_log_radial_zeroth_margin_radius {ell Λ ε B C : ℝ} (hell_pos : 0 < ell)
    (hΛ : 0 < Λ) (hε : 0 ≤ ε) (hεcap : ε ≤ ell / (24 * Λ)) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        ρ < 1 ∧
          ∀ (m : ℕ) (zeta : EuclideanSpace ℝ (Fin (m + 2))) (_hznorm : ‖zeta‖ = 1)
            (_hztan : zeta (Fin.last (m + 1)) = 0) (A : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
            (_hell :
              ∀ v : EuclideanSpace ℝ (Fin (m + 2)),
                ell * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, A i j * v i * v j) ∧
                  (∑ i, ∑ j, A i j * v i * v j) ≤ Λ * ‖v‖ ^ 2)
            (b : EuclideanSpace ℝ (Fin (m + 2))) (_hb : ‖b‖ ≤ B) (a : ℝ) (_ha : -C ≤ a ∧ a ≤ 0)
            (β : ℝ) (x : EuclideanSpace ℝ (Fin (m + 2))) (_hx : 0 < x (Fin.last (m + 1)))
            (_hr : Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) < ρ),
            let φ : EuclideanSpace ℝ (Fin (m + 2)) → ℝ := fun y =>
              (Real.sqrt (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last (m + 1))) ^ 2) +
                    ((∑ i, zeta i * y i) - β) -
                  ε * y (Fin.last (m + 1)) *
                    Real.log (((∑ i, zeta i * y i) - β) ^ 2 + (y (Fin.last (m + 1))) ^ 2)) /
                2
            0 ≤ φ x ∧
              ell /
                  (16 *
                    Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2)) ≤
                Matrix.trace
                      (A *
                        ((Matrix.of fun i j =>
                            fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                              (EuclideanSpace.single j (1 : ℝ))) :
                          Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) +
                    (fderiv ℝ φ x) b +
                  a * φ x := by
  -- both radii are generated from the numerical data only

  obtain ⟨ρ₁, h₁0, h₁1, hBP⟩ := exists_log_radial_drift_margin_radius hell_pos hΛ hε hεcap hB
  obtain ⟨ρ₂, h₂0, -, hbud⟩ :=
    exists_log_radial_drift_budget_radius (ell := ell / 2) (B := C) (by positivity) hε hC
  refine ⟨min ρ₁ ρ₂, lt_min h₁0 h₂0, lt_of_le_of_lt (min_le_left _ _) h₁1, ?_⟩
  intro m zeta hznorm hztan A hell b hb a ha β x hx hr φ
  have hr₁ := lt_of_lt_of_le hr (min_le_left _ _)
  have hr₂ :=
    lt_of_lt_of_le hr
      (min_le_right _ _)
  -- the drift margin on the SAME `φ`

  have hm :
    ell / (8 * Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2)) ≤
      Matrix.trace
          (A *
            ((Matrix.of fun i j =>
                fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                  (EuclideanSpace.single j (1 : ℝ))) :
              Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) +
        (fderiv ℝ φ x) b :=
    hBP m zeta hznorm hztan A hell b hb β x hx
      hr₁
  -- scalar data of the point: `r = √(s² + y²)`, `0 < r < 1`

  have hS0 : 0 < ((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2 := by positivity
  have hr0 : 0 < Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) :=
    Real.sqrt_pos.mpr hS0
  have hr2 :=
    Real.sq_sqrt
      hS0.le
  -- the actual value of the SAME profile at `x`

  have hφx :
    φ x =
      (Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) +
            ((∑ i, zeta i * x i) - β) -
          ε * x (Fin.last (m + 1)) *
            Real.log
              (Real.sqrt (((∑ i, zeta i * x i) - β) ^ 2 + (x (Fin.last (m + 1))) ^ 2) ^ 2)) /
        2 := by
    rw [hr2]
  rw [hφx]
  exact zeroth_margin_scalar hε hC ha hx hr0 hr2 (hr₁.trans h₁1) (hbud _ hr0 hr₂) hm

end FunctionalInequalities.Analysis

end
