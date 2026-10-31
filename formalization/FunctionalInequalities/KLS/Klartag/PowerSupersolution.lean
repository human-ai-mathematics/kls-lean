module

public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Trace
public import FunctionalInequalities.Analysis.LocalExtension
public import FunctionalInequalities.Analysis.Matrix.Positivity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv


/-!
# Power supersolution for the dual moment-measure potential

Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, Lemma 5.2, in the
dual (transport onto `K`) form of Section 5. For `φ` smooth on an open set `K` with positive
definite Hessian, `ρ` convex and `C²` on `K`, and the dual transport equation (66)
`det ∇²φ(x) = exp(x·∇φ(x) - φ(x) - ρ(x))` on `K`, written as
`log det ∇²φ = ⟪x, ∇φ x⟫ - φ x - ρ x`, the function `f = ⟪(∇²φ)⁻¹θ, θ⟫` satisfies
`L(f^ε) + ε f^ε ≥ 0` on `K` for every `θ` and every `ε > 0`, where
`L u = Σ φ^{ij} u_ij - Σ x^i u_i` is the operator (67)
(`MomentMeasure.inverseHessian_rpow_supersolution`). Klartag takes `θ = e₁`.

The proof follows (69)–(73): the twice differentiated equation gives
`Lf = tr(AMAM) - f + wᵀ∇²ρ w ≥ tr(AMAM) - f` with `A = (∇²φ)⁻¹`, `w = Aθ`,
`M = ∂³φ(w, ·, ·)`; the Hilbert–Schmidt versus rank-one bound `Γ(f) ≤ tr(AMAM) f` and the
power rule for `t ↦ t^ε` close the estimate. Regularity is localized by germ transfer to a
globally smooth function (`exists_contDiff_eventuallyEq_germ` and the `_congr_of_eventuallyEq`
lemmas), so the existing global Hessian calculus applies at each point of `K`. The first and second
derivatives of (66) near a point (`dualTransport_first_derivative`,
`dualTransport_second_derivative`) are public for Lemma 5.1.

Scope: a conditional statement for a GIVEN `φ` satisfying (66) on `K`. Existence and
regularity of the moment-map potential, Lemma 5.1, the diffusion of Section 5 and
Theorem 1.1 are not provided. No boundedness of `K` or of `ρ` is used.

The pointwise chain and power rules for `nondivergenceOperator`, the
matrix inequality `(Wx)ᵀA(Wx) ≤ tr(AWAWᵀ)·xᵀA⁻¹x` and the germ-transfer lemmas are generic.
-/

@[expose] public section

noncomputable section
section MatrixPart

open Matrix
open scoped MatrixOrder

namespace FunctionalInequalities.Analysis

variable {ι : Type*} [Fintype ι]

/-- The quartic form `tr(A P A Pᵀ)` is nonnegative for positive semidefinite `A`
(Schur product theorem). -/
private theorem sum_quartic_nonneg {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (P : Matrix ι ι ℝ) :
    0 ≤ ∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * P a c * P p q := by
  have h := (posSemidef_weightedGram A hA (fun _ : Unit => P)).diag_nonneg (i := ())
  simp only [Matrix.of_apply] at h
  exact h.trans_eq (Finset.sum_congr rfl fun a _ => Finset.sum_comm)

/-- The symmetric bilinear form `tr(A P A Qᵀ)` written as a fourfold sum. -/
private def quarticForm (A P Q : Matrix ι ι ℝ) : ℝ :=
  ∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * P a c * Q p q

private theorem quarticForm_sub_smul (A W Q : Matrix ι ι ℝ) (t : ℝ) :
    quarticForm A (W - t • Q) (W - t • Q) =
      quarticForm A W W - t * quarticForm A W Q - t * quarticForm A Q W +
        t ^ 2 * quarticForm A Q Q := by
  unfold quarticForm
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun q _ => ?_
  ring

variable [DecidableEq ι]

/-- **Hilbert–Schmidt versus rank one** in the metric of a positive definite `A`
(Klartag arXiv:1309.2767v1, (73)): for every matrix `W` and vector `x`,
`(Wx)ᵀ A (Wx) ≤ tr(A W A Wᵀ) · xᵀ A⁻¹ x`. No symmetry of `W` is needed. -/
private theorem sum_mul_mulVec_le_quartic_mul_inv {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (W : Matrix ι ι ℝ) (x : ι → ℝ) :
    ∑ a, ∑ p, A a p * (∑ c, W a c * x c) * (∑ q, W p q * x q) ≤
      (∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * W a c * W p q) *
        ∑ i, ∑ j, A⁻¹ i j * x i * x j := by
  by_cases hx : x = 0
  · subst hx
    simp
  set u : ι → ℝ := fun a => ∑ c, W a c * x c with hu
  set v : ι → ℝ := A⁻¹ *ᵥ x with hv
  have hAsymm (i j : ι) : A i j = A j i := by
    simpa using congrFun (congrFun hA.isHermitian j) i
  have hAv : A *ᵥ v = x := by
    rw [hv, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det A).mp hA.isUnit),
      one_mulVec]
  have hAv' (c : ι) : ∑ q, A c q * v q = x c := by
    simpa [mulVec, dotProduct] using congrFun hAv c
  let Q : Matrix ι ι ℝ := Matrix.of fun a c => u a * v c
  have hWQ : quarticForm A W Q = ∑ a, ∑ p, A a p * u a * u p := by
    unfold quarticForm
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
    have : ∑ c, ∑ q, A a p * A c q * W a c * Q p q =
        A a p * u p * ∑ c, W a c * ∑ q, A c q * v q := by
      simp only [Q, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [this]
    simp only [hAv', hu]
    ring
  have hQW : quarticForm A Q W = quarticForm A W Q := by
    unfold quarticForm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hAsymm p a, hAsymm q c]
    ring
  have hQQ : quarticForm A Q Q =
      (∑ a, ∑ p, A a p * u a * u p) * ∑ i, ∑ j, A⁻¹ i j * x i * x j := by
    have hvx : ∑ c, ∑ q, A c q * v c * v q = ∑ i, ∑ j, A⁻¹ i j * x i * x j := by
      have h1 : ∑ c, ∑ q, A c q * v c * v q = ∑ c, v c * x c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← hAv' c, Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
      rw [h1]
      simp only [hv, mulVec, dotProduct, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [← hvx]
    unfold quarticForm
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Q, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  set Γ := ∑ a, ∑ p, A a p * u a * u p with hΓ
  set G := ∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * W a c * W p q with hG
  set h := ∑ i, ∑ j, A⁻¹ i j * x i * x j with hh
  have hGW : quarticForm A W W = G := rfl
  have hΓ0 : 0 ≤ Γ := by
    have := hA.posSemidef.dotProduct_mulVec_nonneg u
    simpa [hΓ, dotProduct, mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using this
  have hh0 : 0 < h := by
    have := hA.inv.dotProduct_mulVec_pos hx
    simpa [hh, dotProduct, mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using this
  have hq := sum_quartic_nonneg hA.posSemidef (W - h⁻¹ • Q)
  change 0 ≤ quarticForm A (W - h⁻¹ • Q) (W - h⁻¹ • Q) at hq
  rw [quarticForm_sub_smul, hQW, hWQ, hQQ, hGW] at hq
  have key : Γ ≤ G * h := by
    have h2 : 0 ≤ G - h⁻¹ * Γ := by
      have e : G - h⁻¹ * Γ - h⁻¹ * Γ + h⁻¹ ^ 2 * (Γ * h) = G - h⁻¹ * Γ := by
        field_simp
        ring
      linarith [e]
    have h3 : h⁻¹ * Γ ≤ G := by linarith
    calc Γ = h * (h⁻¹ * Γ) := by field_simp
      _ ≤ h * G := mul_le_mul_of_nonneg_left h3 hh0.le
      _ = G * h := mul_comm _ _
  exact key

end FunctionalInequalities.Analysis

end MatrixPart

namespace FunctionalInequalities.Analysis

variable {ι : Type*} [Fintype ι]

private theorem sum4_swap (F : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
  calc ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ i, ∑ a, ∑ j, ∑ b, F i j a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, F i j a b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, F i j a b := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ∑ j, F i j a b :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm

private theorem sum3_perm (F : ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ i, ∑ j, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm

/-- Index algebra of Klartag arXiv:1309.2767v1, Lemma 5.2, (69)–(71): with `w = Aθ`,
`M_ac = Σ_i w_i ∂_i φ_ac`, the first and second derivatives of `f = θᵀAθ` and the twice
differentiated dual transport equation give `Lf = tr(AMAM) - f + wᵀ∇²ρ w`. -/
private theorem dual_generator_algebra (A : ι → ι → ℝ) (T : ι → ι → ι → ℝ)
    (Q : ι → ι → ι → ι → ℝ) (H R : ι → ι → ℝ) (w x : ι → ℝ) (f : ℝ) (δ : ι → ι → ℝ)
    (D1 : ι → ℝ) (D2 : ι → ι → ℝ)
    (hA : ∀ a b, A a b = A b a)
    (hT1 : ∀ a b k, T a b k = T b a k) (hT2 : ∀ a b k, T a b k = T k b a)
    (hδ : ∀ (j : ι) (F : ι → ℝ), ∑ k, δ j k * F k = F j)
    (hD1 : ∀ k, D1 k = -∑ a, ∑ b, w a * T a b k * w b)
    (hD2 : ∀ k l, D2 k l = -∑ a, ∑ b, ((-∑ p, ∑ q, A a p * T p q k * w q) * T a b l * w b +
      w a * Q a b k l * w b + w a * T a b l * (-∑ p, ∑ q, A b p * T p q k * w q)))
    (hEq : ∀ i j, (∑ a, ∑ c, A a c * Q i j a c) -
      ∑ a, ∑ c, ∑ p, ∑ q, A a p * A c q * T a c i * T p q j =
        ∑ k, (δ j k * H k i + x k * T k i j) - R j i)
    (hf : ∑ i, ∑ j, w i * w j * H j i = f) :
    (∑ k, ∑ l, A k l * D2 k l) - ∑ k, x k * D1 k =
      (∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * (∑ i, w i * T a c i) * (∑ i, w i * T p q i)) - f +
        ∑ i, ∑ j, w i * w j * R j i := by
  set M : ι → ι → ℝ := fun a c => ∑ i, w i * T a c i with hM
  have hT3 (a b k : ι) : T a b k = T a k b := by rw [hT2, hT1, hT2]
  have hMs (a c : ι) : M a c = M c a := by
    simp only [hM]; exact Finset.sum_congr rfl fun i _ => by rw [hT1]
  have hTw (a l : ι) : ∑ b, T a b l * w b = M a l := by
    simp only [hM]; exact Finset.sum_congr rfl fun b _ => by rw [hT3]; ring
  have hwT (b l : ι) : ∑ a, w a * T a b l = M b l := by
    simp only [hM]; exact Finset.sum_congr rfl fun a _ => by rw [hT1, hT3]
  have hAM (a k : ι) : ∑ p, ∑ q, A a p * T p q k * w q = ∑ p, A a p * M p k := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hTw p k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  -- second derivative in terms of `M`
  have hD2' (k l : ι) : D2 k l = 2 * ∑ a, ∑ p, A a p * M p k * M a l -
      ∑ a, ∑ b, w a * w b * Q a b k l := by
    rw [hD2]
    simp only [hAM]
    have h1 : ∑ a, ∑ b, (-∑ p, A a p * M p k) * T a b l * w b =
        -∑ a, ∑ p, A a p * M p k * M a l := by
      calc ∑ a, ∑ b, (-∑ p, A a p * M p k) * T a b l * w b
          = ∑ a, (-∑ p, A a p * M p k) * ∑ b, T a b l * w b := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by ring
        _ = ∑ a, (-∑ p, A a p * M p k) * M a l := by simp only [hTw]
        _ = -∑ a, ∑ p, A a p * M p k * M a l := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [neg_mul, Finset.sum_mul]
    have h3 : ∑ a, ∑ b, w a * T a b l * (-∑ p, A b p * M p k) =
        -∑ a, ∑ p, A a p * M p k * M a l := by
      calc ∑ a, ∑ b, w a * T a b l * (-∑ p, A b p * M p k)
          = ∑ b, ∑ a, w a * T a b l * (-∑ p, A b p * M p k) := Finset.sum_comm
        _ = ∑ b, (∑ a, w a * T a b l) * (-∑ p, A b p * M p k) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.sum_mul]
        _ = ∑ b, M b l * (-∑ p, A b p * M p k) := by simp only [hwT]
        _ = -∑ a, ∑ p, A a p * M p k * M a l := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [mul_neg, neg_inj, Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => by ring
    have h2 : ∑ a, ∑ b, w a * Q a b k l * w b = ∑ a, ∑ b, w a * w b * Q a b k l :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [Finset.sum_add_distrib]
    rw [h1, h2, h3]
    ring
  -- the contracted twice differentiated equation
  have hS : ∑ i, ∑ j, w i * w j *
      (∑ a, ∑ c, ∑ p, ∑ q, A a p * A c q * T a c i * T p q j) =
      ∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * M a c * M p q := by
    have inner (a c p q : ι) : ∑ i, ∑ j, w i * w j * (A a p * A c q * T a c i * T p q j) =
        A a p * A c q * M a c * M p q := by
      simp only [hM]
      rw [mul_assoc (A a p * A c q), Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    calc ∑ i, ∑ j, w i * w j * (∑ a, ∑ c, ∑ p, ∑ q, A a p * A c q * T a c i * T p q j)
        = ∑ i, ∑ j, ∑ a, ∑ c, ∑ p, ∑ q, w i * w j * (A a p * A c q * T a c i * T p q j) := by
          simp only [Finset.mul_sum]
      _ = ∑ a, ∑ c, ∑ i, ∑ j, ∑ p, ∑ q, w i * w j * (A a p * A c q * T a c i * T p q j) :=
          sum4_swap _
      _ = ∑ a, ∑ c, ∑ p, ∑ q, ∑ i, ∑ j, w i * w j * (A a p * A c q * T a c i * T p q j) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => sum4_swap _
      _ = ∑ a, ∑ c, ∑ p, ∑ q, A a p * A c q * M a c * M p q := by simp only [inner]
      _ = ∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * M a c * M p q :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hcontract := congrArg (fun F : ι → ι → ℝ => ∑ i, ∑ j, w i * w j * F i j)
    (funext fun i => funext fun j => hEq i j)
  simp only [mul_sub, Finset.sum_sub_distrib, hS] at hcontract
  have hH : ∑ i, ∑ j, w i * w j * ∑ k, (δ j k * H k i + x k * T k i j) =
      f + ∑ k, x k * ∑ a, ∑ b, w a * T a b k * w b := by
    rw [← hf]
    have e1 (i j : ι) : ∑ k, (δ j k * H k i + x k * T k i j) =
        H j i + ∑ k, x k * T k i j := by
      rw [Finset.sum_add_distrib, hδ j (fun k => H k i)]
    simp only [e1, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum]
    rw [sum3_perm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [(hT3 k i j).trans (hT2 i j k).symm]
    ring
  rw [hH] at hcontract
  have hQ : ∑ k, ∑ l, A k l * (∑ a, ∑ b, w a * w b * Q a b k l) =
      ∑ i, ∑ j, w i * w j * ∑ a, ∑ c, A a c * Q i j a c := by
    simp only [Finset.mul_sum]
    rw [sum4_swap]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hTwo : ∑ k, ∑ l, A k l * (2 * ∑ a, ∑ p, A a p * M p k * M a l) =
      2 * ∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * M a c * M p q := by
    simp only [Finset.mul_sum]
    rw [sum4_swap]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [hA k l]; ring
  have hL2 : ∑ k, ∑ l, A k l * D2 k l =
      2 * (∑ a, ∑ p, ∑ c, ∑ q, A a p * A c q * M a c * M p q) -
        ∑ i, ∑ j, w i * w j * ∑ a, ∑ c, A a c * Q i j a c := by
    simp only [hD2', mul_sub, Finset.sum_sub_distrib, hTwo, hQ]
  have hL1 : ∑ k, x k * D1 k = -∑ k, x k * ∑ a, ∑ b, w a * T a b k * w b := by
    simp only [hD1, mul_neg, Finset.sum_neg_distrib]
  rw [hL2, hL1]
  linarith

end FunctionalInequalities.Analysis


open Filter Topology
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem nondivergenceOperator_comp_at
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (b : E → Fin (Module.finrank ℝ E) → ℝ) {f : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h (f x)) :
    nondivergenceOperator A b (fun y => h (f y)) x =
      deriv h (f x) * nondivergenceOperator A b f x +
        deriv (deriv h) (f x) * ∑ i, ∑ j, A x i j *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ f x (stdOrthonormalBasis ℝ E j) := by
  have hf_ev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hh_ev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 h (f y) :=
    hf.continuousAt.eventually (hh.eventually (by simp))
  have hfirst_ev : ∀ᶠ y in 𝓝 x,
      fderiv ℝ (fun z => h (f z)) y = deriv h (f y) • fderiv ℝ f y := by
    filter_upwards [hf_ev, hh_ev] with y hfy hhy
    exact ((hhy.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y
      (hfy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hfirst : fderiv ℝ (fun z => h (f z)) x = deriv h (f x) • fderiv ℝ f x :=
    hfirst_ev.self_of_nhds
  have hh' : ContDiffAt ℝ 1 (deriv h) (f x) := by
    have h1 := hh.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun t => fderiv ℝ h t 1) (f x) :=
      h1.clm_apply contDiffAt_const
    exact h2
  have hdh : DifferentiableAt ℝ (fun y => deriv h (f y)) x :=
    (hh'.differentiableAt (by norm_num)).comp x (hf.differentiableAt (by norm_num))
  have hcomp : ContDiffAt ℝ 2 (fun y => h (f y)) x := hh.comp x hf
  have hsecond (v w : E) :
      bilinearIteratedFDerivTwo ℝ (fun y => h (f y)) x v w =
        deriv h (f x) * bilinearIteratedFDerivTwo ℝ f x v w +
          deriv (deriv h) (f x) * fderiv ℝ f x v * fderiv ℝ f x w := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply_at hcomp v w,
      bilinearIteratedFDerivTwo_eq_fderiv_apply_at hf v w]
    have hfun : (fun y => fderiv ℝ (fun z => h (f z)) y w) =ᶠ[𝓝 x]
        (fun y => deriv h (f y) * fderiv ℝ f y w) := by
      filter_upwards [hfirst_ev] with y hy
      simp [hy]
    rw [hfun.fderiv_eq]
    have hfw : DifferentiableAt ℝ (fun y => fderiv ℝ f y w) x :=
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
        (differentiableAt_const w)
    have hdh' : fderiv ℝ (fun y => deriv h (f y)) x =
        deriv (deriv h) (f x) • fderiv ℝ f x :=
      ((hh'.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt x
        (hf.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    rw [fderiv_fun_mul hdh hfw, hdh']
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp only [nondivergenceOperator, hsecond, hfirst, smul_apply, smul_eq_mul]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [mul_left_comm, mul_comm]
  ring

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The power rule for a nondivergence operator at a point where `f > 0`:
`L(f^ε) = ε f^(ε-1) Lf + ε(ε-1) f^(ε-2) Σ A_ij ∂_i f ∂_j f`. -/
private theorem nondivergenceOperator_rpow_at
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (b : E → Fin (Module.finrank ℝ E) → ℝ) {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hfx : 0 < f x) (ε : ℝ) :
    nondivergenceOperator A b (fun y => f y ^ ε) x =
      ε * f x ^ (ε - 1) * nondivergenceOperator A b f x +
        ε * (ε - 1) * f x ^ (ε - 2) * ∑ i, ∑ j, A x i j *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ f x (stdOrthonormalBasis ℝ E j) := by
  have hh : ContDiffAt ℝ 2 (fun t : ℝ => t ^ ε) (f x) :=
    Real.contDiffAt_rpow_const_of_ne hfx.ne'
  rw [nondivergenceOperator_comp_at A b hf hh]
  have h1 : deriv (fun t : ℝ => t ^ ε) = fun t => ε * t ^ (ε - 1) :=
    funext fun t => Real.deriv_rpow_const t ε
  have h2 : deriv (fun t : ℝ => ε * t ^ (ε - 1)) (f x) = ε * ((ε - 1) * f x ^ (ε - 2)) := by
    rw [deriv_const_mul _ (Real.differentiableAt_rpow_const_of_ne _ hfx.ne'),
      Real.deriv_rpow_const]
    norm_num [sub_sub]
  rw [h1, h2]
  ring

/-- Scalar closing step of Klartag arXiv:1309.2767v1, Lemma 5.2, after (71)–(73):
`Lf ≥ S - f`, `0 ≤ Γ ≤ S f` and `f > 0` give
`ε f^(ε-1) Lf + ε(ε-1) f^(ε-2) Γ + ε f^ε ≥ 0` for `ε > 0`. -/
private theorem rpow_generator_add_nonneg {ε f Lf Γ S : ℝ} (hε : 0 < ε) (hf : 0 < f)
    (hL : S - f ≤ Lf) (hΓ0 : 0 ≤ Γ) (hΓ : Γ ≤ S * f) :
    0 ≤ ε * f ^ (ε - 1) * Lf + ε * (ε - 1) * f ^ (ε - 2) * Γ + ε * f ^ ε := by
  have hP : 0 < f ^ (ε - 2) := Real.rpow_pos_of_pos hf _
  have e1 : f ^ (ε - 1) = f ^ (ε - 2) * f := by
    rw [← Real.rpow_add_one hf.ne']; ring_nf
  have e0 : f ^ ε = f ^ (ε - 2) * f ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hf]; ring_nf
  rw [e1, e0]
  have key : 0 ≤ f * Lf + (ε - 1) * Γ + f ^ 2 := by nlinarith
  have := mul_nonneg (mul_nonneg hε.le hP.le) key
  nlinarith [this]

end FunctionalInequalities.Analysis.BakryEmery


open Filter Topology
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "dimE" => Module.finrank ℝ E
local notation "e" => stdOrthonormalBasis ℝ E

omit [FiniteDimensional ℝ E] in
private theorem sum4_perm {ι : Type*} [Fintype ι] (F : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ a, ∑ b, ∑ j, ∑ i, F i j a b := by
  calc ∑ i, ∑ j, ∑ a, ∑ b, F i j a b = ∑ i, ∑ a, ∑ b, ∑ j, F i j a b := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ b, ∑ j, F i j a b := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ j, ∑ i, F i j a b := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- The quadratic form `θᵀ (∇²φ)⁻¹ θ` in standard coordinates. -/
private def invHessQuad (φ : E → ℝ) (c : Fin dimE → ℝ) (y : E) : ℝ :=
  ∑ i, ∑ j, c i * c j * inverseHessianEntry φ e y i j

/-- The vector `(∇²φ)⁻¹ θ` in standard coordinates. -/
private def invHessVec (φ : E → ℝ) (c : Fin dimE → ℝ) (y : E) (a : Fin dimE) : ℝ :=
  ∑ j, inverseHessianEntry φ e y a j * c j

private theorem fderiv_invHessQuad {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : Fin dimE → ℝ) {y : E}
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v) (k : Fin dimE) :
    fderiv ℝ (invHessQuad φ c) y (e k) =
      -∑ a, ∑ b, invHessVec φ c y a * stdHessianMatrixDeriv φ y k a b * invHessVec φ c y b := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd (i j : Fin dimE) : DifferentiableAt ℝ (fun z => inverseHessianEntry φ e z i j) y :=
    (contDiffAt_inverseHessianEntry e hφ y hPD i j).differentiableAt (by simp)
  have hdij (i j : Fin dimE) :
    fderiv ℝ (fun z => c i * c j * inverseHessianEntry φ e z i j) y (e k) =
      c i * c j *
        -(∑ a,
            ∑ b,
              inverseHessianEntry φ e y i a * stdHessianMatrixDeriv φ y k a b *
                inverseHessianEntry φ e y b j) := by
    rw [fderiv_const_mul (hd i j), smul_apply, smul_eq_mul,
      fderiv_inverseHessianEntry_apply e hφ y hPD]
    rfl
  have hdi (i : Fin dimE) :
    fderiv ℝ (fun z => ∑ j, c i * c j * inverseHessianEntry φ e z i j) y (e k) =
      ∑ j,
        c i * c j *
          -(∑ a,
              ∑ b,
                inverseHessianEntry φ e y i a * stdHessianMatrixDeriv φ y k a b *
                  inverseHessianEntry φ e y b j) := by
    rw [fderiv_sum_apply Finset.univ (fun j _ => (hd i j).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => hdij i j
  have hq : invHessQuad φ c = fun z => ∑ i, ∑ j, c i * c j * inverseHessianEntry φ e z i j :=
    rfl
  rw [hq,
    fderiv_sum_apply Finset.univ
      (fun i _ => DifferentiableAt.fun_sum fun j _ => (hd i j).const_mul _)]
  simp_rw [hdi]
  unfold invHessVec
  have hsymm (i a : Fin dimE) : inverseHessianEntry φ e y i a = inverseHessianEntry φ e y a i :=
    inverseHessianEntry_symm e h2 y i a
  simp only [Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [sum4_perm]
  refine
    Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hsymm i a]
  ring

private theorem fderiv_invHessVec {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : Fin dimE → ℝ) {y : E}
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v) (a k : Fin dimE) :
    fderiv ℝ (fun z => invHessVec φ c z a) y (e k) =
      -∑ p,
          ∑ q,
            inverseHessianEntry φ e y a p * stdHessianMatrixDeriv φ y k p q *
              invHessVec φ c y q := by
  have hd (i j : Fin dimE) : DifferentiableAt ℝ (fun z => inverseHessianEntry φ e z i j) y :=
    (contDiffAt_inverseHessianEntry e hφ y hPD i j).differentiableAt (by simp)
  unfold invHessVec
  rw [fderiv_sum_apply Finset.univ (fun j _ => (hd a j).mul_const _)]
  simp_rw [fderiv_mul_const (hd a _), smul_apply, smul_eq_mul,
    fderiv_inverseHessianEntry_apply e hφ y hPD]
  unfold stdHessianMatrixDeriv hessianMatrixIn
  simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem contDiff_third_apply {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (a b k : Fin dimE) :
    ContDiff ℝ ∞ (fun y => stdHessianMatrixDeriv φ y k a b) := by
  unfold stdHessianMatrixDeriv hessianMatrixIn
  have h := contDiff_bilinearIteratedFDerivTwo_apply hφ (e a) (e b)
  have h' : ContDiff ℝ ∞ (fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e a) (e b))) :=
    h.fderiv_right (by simp)
  exact h'.clm_apply contDiff_const

private theorem contDiffAt_invHessVec {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : Fin dimE → ℝ) {y : E}
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v) (a : Fin dimE) :
    ContDiffAt ℝ ∞ (fun z => invHessVec φ c z a) y := by
  unfold invHessVec
  exact ContDiffAt.sum fun j _ => (contDiffAt_inverseHessianEntry e hφ y hPD a j).mul
    contDiffAt_const

private theorem contDiffAt_invHessQuad {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : Fin dimE → ℝ) {y : E}
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v) :
    ContDiffAt ℝ ∞ (invHessQuad φ c) y := by
  unfold invHessQuad
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => contDiffAt_const.mul
    (contDiffAt_inverseHessianEntry e hφ y hPD i j)

/-- Second derivative of `θᵀ(∇²φ)⁻¹θ` at a point near which the Hessian is positive definite. -/
private theorem bilinear_invHessQuad {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : Fin dimE → ℝ)
    {x : E} (hPD : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (k l : Fin dimE) :
    bilinearIteratedFDerivTwo ℝ (invHessQuad φ c) x (e k) (e l) =
      -∑ a,
          ∑ b,
            ((-∑ p,
                        ∑ q,
                          inverseHessianEntry φ e x a p * stdHessianMatrixDeriv φ x k p q *
                            invHessVec φ c x q) *
                    stdHessianMatrixDeriv φ x l a b *
                  invHessVec φ c x b +
                invHessVec φ c x a *
                    bilinearIteratedFDerivTwo ℝ
                      (fun y => bilinearIteratedFDerivTwo ℝ φ y (e a) (e b)) x (e k) (e l) *
                  invHessVec φ c x b +
              invHessVec φ c x a * stdHessianMatrixDeriv φ x l a b *
                (-∑ p,
                    ∑ q,
                      inverseHessianEntry φ e x b p * stdHessianMatrixDeriv φ x k p q *
                        invHessVec φ c x q)) := by
  have hx := hPD.self_of_nhds
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply_at
      ((contDiffAt_invHessQuad hφ c hx).of_le (WithTop.coe_le_coe.mpr le_top))]
  have hev :
    (fun y => fderiv ℝ (invHessQuad φ c) y (e l)) =ᶠ[𝓝 x]
      (fun y =>
        -∑ a, ∑ b, invHessVec φ c y a * stdHessianMatrixDeriv φ y l a b * invHessVec φ c y b) := by
    filter_upwards [hPD] with y hy
    exact fderiv_invHessQuad hφ c hy l
  rw [hev.fderiv_eq]
  have hw (a : Fin dimE) : DifferentiableAt ℝ (fun z => invHessVec φ c z a) x :=
    (contDiffAt_invHessVec hφ c hx a).differentiableAt (by simp)
  have hT (a b : Fin dimE) : DifferentiableAt ℝ (fun z => stdHessianMatrixDeriv φ z l a b) x :=
    (contDiff_third_apply hφ a b l).contDiffAt.differentiableAt (by simp)
  have hprod (a b : Fin dimE) :
    DifferentiableAt ℝ
      (fun z => invHessVec φ c z a * stdHessianMatrixDeriv φ z l a b * invHessVec φ c z b) x :=
    ((hw a).mul (hT a b)).mul (hw b)
  rw [fderiv_fun_neg, neg_apply,
    fderiv_sum_apply Finset.univ (fun a _ => DifferentiableAt.fun_sum fun b _ => hprod a b)]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_sum_apply Finset.univ (fun b _ => hprod a b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hH :
    HasFDerivAt
      (fun z => invHessVec φ c z a * stdHessianMatrixDeriv φ z l a b * invHessVec φ c z b)
      ((invHessVec φ c x a * stdHessianMatrixDeriv φ x l a b) •
          fderiv ℝ (fun z => invHessVec φ c z b) x +
        invHessVec φ c x b •
          (invHessVec φ c x a • fderiv ℝ (fun z => stdHessianMatrixDeriv φ z l a b) x +
            stdHessianMatrixDeriv φ x l a b • fderiv ℝ (fun z => invHessVec φ c z a) x))
      x :=
    (((hw a).hasFDerivAt.mul (hT a b).hasFDerivAt).mul (hw b).hasFDerivAt)
  rw [hH.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_invHessVec hφ c hx a k, fderiv_invHessVec hφ c hx b k]
  have h4 :
    fderiv ℝ (fun z => stdHessianMatrixDeriv φ z l a b) x (e k) =
      bilinearIteratedFDerivTwo ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e a) (e b)) x (e k)
        (e l) := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply
        ((contDiff_bilinearIteratedFDerivTwo_apply hφ (e a) (e b)).of_le
          (WithTop.coe_le_coe.mpr le_top))]
    rfl
  rw [h4]
  ring

/-- Derivative of the right-hand side `⟪y, ∇φ y⟫ - φ y - ρ y` of the dual transport equation. -/
theorem fderiv_dualTransport_rhs {φ ρ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {y : E}
    (hρ : DifferentiableAt ℝ ρ y) (v : E) :
    fderiv ℝ (fun z => ⟪z, gradient φ z⟫ - φ z - ρ z) y v =
      ⟪y, hessianOperator φ y v⟫ - fderiv ℝ ρ y v := by
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hgr : HasFDerivAt (gradient φ) (hessianOperator φ y) y :=
    (hg.differentiable (by simp) y).hasFDerivAt
  have hφd : HasFDerivAt φ (fderiv ℝ φ y) y := (hφ.differentiable (by simp) y).hasFDerivAt
  have hall : HasFDerivAt (fun z => ⟪z, gradient φ z⟫ - φ z - ρ z)
      ((fderivInnerCLM ℝ (y, gradient φ y)).comp
        ((ContinuousLinearMap.id ℝ E).prod (hessianOperator φ y)) - fderiv ℝ φ y -
          fderiv ℝ ρ y) y :=
    (((hasFDerivAt_id y).inner ℝ hgr).sub hφd).sub hρ.hasFDerivAt
  rw [hall.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.id_apply]
  have hgv : ⟪v, gradient φ y⟫ = fderiv ℝ φ y v := by
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  rw [hgv]
  ring

/-- `⟪y, ∇²φ(y) eᵢ⟫` in standard coordinates. -/
private theorem inner_hessianOperator_eq_sum {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (y : E)
    (i : Fin dimE) :
    ⟪y, hessianOperator φ y (e i)⟫ =
      ∑ k, ⟪y, e k⟫ * bilinearIteratedFDerivTwo ℝ φ y (e k) (e i) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [← (e).sum_inner_mul_inner y (hessianOperator φ y (e i))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bilinearIteratedFDerivTwo_symm h2, bilinearIteratedFDerivTwo_eq_inner_hessianOperator h2]
  congr 1
  exact real_inner_comm _ _

/-- The first derivative of the dual transport equation in coordinates, near `x`:
`Σ_ac φ^{ac} ∂_i φ_ac = Σ_k y_k φ_ki - ρ_i`. -/
theorem dualTransport_first_derivative {φ ρ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : E}
    (hPD : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hρ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ρ y)
    (hEq : ∀ᶠ y in 𝓝 x, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y) (i : Fin dimE) :
    ∀ᶠ y in 𝓝 x, ∑ a, ∑ c, inverseHessianEntry φ e y a c * stdHessianMatrixDeriv φ y i a c =
      ∑ k, ⟪y, e k⟫ * bilinearIteratedFDerivTwo ℝ φ y (e k) (e i) - fderiv ℝ ρ y (e i) := by
  filter_upwards [hPD, hρ, hEq.eventually_nhds] with y hy hρy hyeq
  have hfun : logDetHessian φ e =ᶠ[𝓝 y] fun z => ⟪z, gradient φ z⟫ - φ z - ρ z := hyeq
  have h := fderiv_logDetHessian_eq_sum e hφ y hy (e i)
  rw [hfun.fderiv_eq, fderiv_dualTransport_rhs hφ hρy, inner_hessianOperator_eq_sum hφ] at h
  unfold stdHessianMatrixDeriv hessianMatrixIn
  exact h.symm

/-- The twice differentiated dual transport equation at `x`. -/
theorem dualTransport_second_derivative {φ ρ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : E}
    (hPD : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hρ : ContDiffAt ℝ 2 ρ x)
    (hEq : ∀ᶠ y in 𝓝 x, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y) (i j : Fin dimE) :
    (∑ a,
          ∑ c,
            inverseHessianEntry φ e x a c *
              bilinearIteratedFDerivTwo ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e i) (e j))
                x (e a) (e c)) -
        ∑ a,
          ∑ c,
            ∑ p,
              ∑ q,
                inverseHessianEntry φ e x a p * inverseHessianEntry φ e x c q *
                    stdHessianMatrixDeriv φ x i a c *
                  stdHessianMatrixDeriv φ x j p q =
      ∑ k,
          (⟪e j, e k⟫ * bilinearIteratedFDerivTwo ℝ φ x (e k) (e i) +
            ⟪x, e k⟫ * stdHessianMatrixDeriv φ x j k i) -
        bilinearIteratedFDerivTwo ℝ ρ x (e j) (e i) := by
  have hx := hPD.self_of_nhds
  have hρd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ρ y := by
    filter_upwards [hρ.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hlhs := fderiv_mongeAmpere_first_lhs e hφ x hx i j
  have hev :
    (fun y => ∑ a, ∑ c, inverseHessianEntry φ e y a c * stdHessianMatrixDeriv φ y i a c) =ᶠ[𝓝 x]
      (fun y =>
        ∑ k, ⟪y, e k⟫ * bilinearIteratedFDerivTwo ℝ φ y (e k) (e i) - fderiv ℝ ρ y (e i)) :=
    dualTransport_first_derivative hφ hPD hρd hEq i
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L (e j)) (hev.fderiv_eq (𝕜 := ℝ))
  unfold stdHessianMatrixDeriv hessianMatrixIn at hd
  rw [hlhs] at hd
  unfold stdHessianMatrixDeriv hessianMatrixIn
  rw [hd]
  have hH (k : Fin dimE) :
    DifferentiableAt ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e k) (e i)) x :=
    ((contDiff_bilinearIteratedFDerivTwo_apply hφ (e k) (e i)).differentiable (by simp)) x
  have hprod (k : Fin dimE) :
    HasFDerivAt (fun y => ⟪y, e k⟫ * bilinearIteratedFDerivTwo ℝ φ y (e k) (e i))
      (⟪x, e k⟫ • fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e k) (e i)) x +
        bilinearIteratedFDerivTwo ℝ φ x (e k) (e i) •
          (fderivInnerCLM ℝ (x, e k)).comp ((ContinuousLinearMap.id ℝ E).prod 0))
      x :=
    ((hasFDerivAt_id x).inner ℝ (hasFDerivAt_const (e k) x)).mul (hH k).hasFDerivAt
  have hρ1 : DifferentiableAt ℝ (fun y => fderiv ℝ ρ y (e i)) x :=
    ((hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const _)
  have hsum :
    HasFDerivAt (fun y => ∑ k, ⟪y, e k⟫ * bilinearIteratedFDerivTwo ℝ φ y (e k) (e i))
      (∑ k,
        (⟪x, e k⟫ • fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e k) (e i)) x +
          bilinearIteratedFDerivTwo ℝ φ x (e k) (e i) •
            (fderivInnerCLM ℝ (x, e k)).comp ((ContinuousLinearMap.id ℝ E).prod 0)))
      x :=
    HasFDerivAt.fun_sum fun k _ => hprod k
  have hall :
    HasFDerivAt
      (fun y =>
        ∑ k, ⟪y, e k⟫ * bilinearIteratedFDerivTwo ℝ φ y (e k) (e i) - fderiv ℝ ρ y (e i))
      ((∑ k,
          (⟪x, e k⟫ • fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e k) (e i)) x +
            bilinearIteratedFDerivTwo ℝ φ x (e k) (e i) •
              (fderivInnerCLM ℝ (x, e k)).comp ((ContinuousLinearMap.id ℝ E).prod 0))) -
        fderiv ℝ (fun y => fderiv ℝ ρ y (e i)) x)
      x :=
    hsum.sub hρ1.hasFDerivAt
  rw [hall.fderiv, bilinearIteratedFDerivTwo_eq_fderiv_apply_at hρ (e j) (e i)]
  simp only [sub_apply, sum_apply, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.id_apply, zero_apply, inner_zero_right]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem third_symm₁ {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (y : E) (a b k : Fin dimE) :
    stdHessianMatrixDeriv φ y k a b = stdHessianMatrixDeriv φ y k b a := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  unfold stdHessianMatrixDeriv hessianMatrixIn
  have : (fun z => bilinearIteratedFDerivTwo ℝ φ z (e a) (e b)) =
      fun z => bilinearIteratedFDerivTwo ℝ φ z (e b) (e a) :=
    funext fun z => bilinearIteratedFDerivTwo_symm h2 z _ _
  rw [this]

private theorem third_symm₂ {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (y : E) (a b k : Fin dimE) :
    stdHessianMatrixDeriv φ y k a b = stdHessianMatrixDeriv φ y a k b :=
  fderiv_bilinearIteratedFDerivTwo_comm hφ y (e a) (e b) (e k)

private theorem sum_inner_stdBasis_mul (j : Fin dimE) (F : Fin dimE → ℝ) :
    ∑ k, ⟪e j, e k⟫ * F k = F j := by
  classical
  simp [(e).inner_eq_ite]

private theorem posDef_hessianMatrixIn {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {x : E}
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    (hessianMatrixIn φ e x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, hessianMatrixIn]
    exact bilinearIteratedFDerivTwo_symm hφ x _ _
  · have hne : (∑ i, v i • e i) ≠ 0 := by
      intro h0
      apply hv
      have := (Fintype.linearIndependent_iff.mp (e).toBasis.linearIndependent) v
      funext i
      simpa using this (by simpa using h0) i
    have h := hPD _ hne
    rw [bilinear_sum_smul_sum_smul] at h
    simpa [dotProduct, Matrix.mulVec, hessianMatrixIn, Finset.mul_sum, mul_comm, mul_left_comm,
      mul_assoc] using h

private theorem sum_invHessVec_hessian {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {x : E}
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (c : Fin dimE → ℝ) :
    ∑ i, ∑ j, invHessVec φ c x i * invHessVec φ c x j *
      bilinearIteratedFDerivTwo ℝ φ x (e j) (e i) = invHessQuad φ c x := by
  have hHA (i b : Fin dimE) : ∑ j, bilinearIteratedFDerivTwo ℝ φ x (e i) (e j) *
      inverseHessianEntry φ e x j b = if b = i then 1 else 0 := by
    rw [← sum_inverseHessianEntry_mul_hessian e hφ x hPD b i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inverseHessianEntry_symm e hφ x j b, bilinearIteratedFDerivTwo_symm hφ x (e i) (e j)]
    ring
  have hrow (i : Fin dimE) : ∑ j, invHessVec φ c x j *
      bilinearIteratedFDerivTwo ℝ φ x (e j) (e i) = c i := by
    unfold invHessVec
    calc ∑ j, (∑ b, inverseHessianEntry φ e x j b * c b) *
          bilinearIteratedFDerivTwo ℝ φ x (e j) (e i)
        = ∑ b, (∑ j, bilinearIteratedFDerivTwo ℝ φ x (e i) (e j) *
            inverseHessianEntry φ e x j b) * c b := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
          rw [bilinearIteratedFDerivTwo_symm hφ x (e j) (e i)]
          ring
      _ = c i := by simp [hHA]
  calc ∑ i, ∑ j, invHessVec φ c x i * invHessVec φ c x j *
        bilinearIteratedFDerivTwo ℝ φ x (e j) (e i)
      = ∑ i, invHessVec φ c x i * c i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hrow i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = invHessQuad φ c x := by
        unfold invHessVec invHessQuad
        simp only [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [inverseHessianEntry_symm e hφ x i j]
        ring

/-- **Klartag arXiv:1309.2767v1, Lemma 5.2, pointwise core** for a globally smooth `φ`:
near `x` the Hessian is positive definite and the dual transport equation
`log det ∇²φ(y) = ⟪y, ∇φ y⟫ - φ y - ρ y` holds, `ρ` is `C²` at `x` with positive semidefinite
Hessian there. Then for `f = θᵀ(∇²φ)⁻¹θ` and every `ε > 0`, `L(f^ε) + ε f^ε ≥ 0` at `x`, where
`L u = Σ φ^{ij} u_ij - Σ x^i u_i`. -/
private theorem invHessQuad_rpow_generator_nonneg_core {φ ρ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {x : E} (hPD : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hρ : ContDiffAt ℝ 2 ρ x) (hρpsd : ∀ v, 0 ≤ bilinearIteratedFDerivTwo ℝ ρ x v v)
    (hEq : ∀ᶠ y in 𝓝 x, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y) (c : Fin dimE → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    0 ≤
      nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫)
          (fun y => invHessQuad φ c y ^ ε) x +
        ε * invHessQuad φ c x ^ ε := by
  classical
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hx := hPD.self_of_nhds
  by_cases hc : c = 0
  · subst hc
    have h0 : (fun y => invHessQuad φ 0 y ^ ε) = fun _ => (0 : ℝ) := by
      funext y;
      simp [invHessQuad, Real.zero_rpow hε.ne']
    rw [h0]
    simp [nondivergenceOperator, invHessQuad, Real.zero_rpow hε.ne', bilinearIteratedFDerivTwo]
  -- the inverse Hessian as a positive definite matrix

  set Amat : Matrix (Fin dimE) (Fin dimE) ℝ :=
    Matrix.of fun i j => inverseHessianEntry φ e x i j with hAmat
  have hHpd := posDef_hessianMatrixIn h2 hx
  have hAinv : (hessianMatrixIn φ e x)⁻¹ = Amat := inv_hessianMatrixIn e h2 x hx
  have hApd : Amat.PosDef := hAinv ▸ hHpd.inv
  have hAinv' : Amat⁻¹ = hessianMatrixIn φ e x := by
    rw [← hAinv,
      Matrix.nonsing_inv_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.isUnit hHpd))]
  -- positivity of f

  have hfx : 0 < invHessQuad φ c x := by
    have := hApd.dotProduct_mulVec_pos hc
    simpa [invHessQuad, dotProduct, Matrix.mulVec, hAmat, Finset.mul_sum, mul_comm,
      mul_left_comm, mul_assoc] using this
  rw [nondivergenceOperator_rpow_at _ _
      ((contDiffAt_invHessQuad hφ c hx).of_le (WithTop.coe_le_coe.mpr le_top)) hfx ε]
  set f := invHessQuad φ c x with hf
  set w := invHessVec φ c x with hw
  set M : Fin dimE → Fin dimE → ℝ := fun a b => ∑ i, w i * stdHessianMatrixDeriv φ x i a b with
    hM
  set S :=
    ∑ a,
      ∑ p,
        ∑ b,
          ∑ q,
            inverseHessianEntry φ e x a p * inverseHessianEntry φ e x b q *
                (∑ i, w i * stdHessianMatrixDeriv φ x i a b) *
              (∑ i, w i * stdHessianMatrixDeriv φ x i p q) with
    hS
  -- the generator of f

  have hLf :=
    dual_generator_algebra (fun i j => inverseHessianEntry φ e x i j)
      (fun a b k => stdHessianMatrixDeriv φ x k a b)
      (fun a b k l =>
        bilinearIteratedFDerivTwo ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e a) (e b)) x
          (e k) (e l))
      (fun i j => bilinearIteratedFDerivTwo ℝ φ x (e i) (e j))
      (fun i j => bilinearIteratedFDerivTwo ℝ ρ x (e i) (e j)) w (fun k => ⟪x, e k⟫) f
      (fun j k => ⟪e j, e k⟫) (fun k => fderiv ℝ (invHessQuad φ c) x (e k))
      (fun k l => bilinearIteratedFDerivTwo ℝ (invHessQuad φ c) x (e k) (e l))
      (fun a b => inverseHessianEntry_symm e h2 x a b) (third_symm₁ hφ x) (third_symm₂ hφ x)
      sum_inner_stdBasis_mul (fun k => fderiv_invHessQuad hφ c hx k)
      (fun k l => bilinear_invHessQuad hφ c hPD k l)
      (fun i j => dualTransport_second_derivative hφ hPD hρ hEq i j)
      (sum_invHessVec_hessian h2 hx c)
  have hLf' :
    nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫)
        (invHessQuad φ c) x =
      S - f + ∑ i, ∑ j, w i * w j * bilinearIteratedFDerivTwo ℝ ρ x (e j) (e i) :=
    hLf
  have hR : 0 ≤ ∑ i, ∑ j, w i * w j * bilinearIteratedFDerivTwo ℝ ρ x (e j) (e i) := by
    have h := hρpsd (∑ i, w i • e i)
    rw [bilinear_sum_smul_sum_smul] at h
    refine le_of_le_of_eq h (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
    rw [bilinearIteratedFDerivTwo_symm_at hρ]
  have hD1 (k : Fin dimE) : fderiv ℝ (invHessQuad φ c) x (e k) = -∑ b, M k b * w b := by
    rw [fderiv_invHessQuad hφ c hx k, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hM, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [third_symm₂ hφ x a b k]
  have hΓ0 :
    0 ≤
      ∑ i,
        ∑ j,
          inverseHessianEntry φ e x i j * fderiv ℝ (invHessQuad φ c) x (e i) *
            fderiv ℝ (invHessQuad φ c) x (e j) := by
    have :=
      hApd.posSemidef.dotProduct_mulVec_nonneg (fun k => fderiv ℝ (invHessQuad φ c) x (e k))
    simpa [dotProduct, Matrix.mulVec, hAmat, Finset.mul_sum, mul_comm, mul_left_comm,
      mul_assoc] using this
  have hΓ :
    ∑ i,
        ∑ j,
          inverseHessianEntry φ e x i j * fderiv ℝ (invHessQuad φ c) x (e i) *
            fderiv ℝ (invHessQuad φ c) x (e j) ≤
      S * f := by
    have h :=
      FunctionalInequalities.Analysis.sum_mul_mulVec_le_quartic_mul_inv hApd (Matrix.of M) w
    rw [hAinv'] at h
    have hquad : ∑ i, ∑ j, hessianMatrixIn φ e x i j * w i * w j = f := by
      rw [hf, ← sum_invHessVec_hessian h2 hx c, hw]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [hessianMatrixIn]
      rw [bilinearIteratedFDerivTwo_symm h2 x (e i) (e j)]
      ring
    rw [hquad] at h
    simp only [hD1, Matrix.of_apply, hAmat] at h ⊢
    convert h using 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  exact rpow_generator_add_nonneg hε hfx (by rw [hLf']; linarith) hΓ0 hΓ

/-- A nondivergence operator at `x` only sees the coefficients at `x` and the germ of `u`. -/
theorem nondivergenceOperator_congr
    {A A' : E → Fin dimE → Fin dimE → ℝ} {b : E → Fin dimE → ℝ} {u u' : E → ℝ} {x : E}
    (hA : A x = A' x) (hu : u =ᶠ[𝓝 x] u') :
    nondivergenceOperator A b u x = nondivergenceOperator A' b u' x := by
  unfold nondivergenceOperator bilinearIteratedFDerivTwo
  rw [hA, hu.fderiv_eq, hu.fderiv.fderiv_eq]

theorem hessianOperator_congr_of_eventuallyEq {φ ψ : E → ℝ} {y : E} (h : ψ =ᶠ[𝓝 y] φ) :
    hessianOperator ψ y = hessianOperator φ y := by
  unfold hessianOperator
  have hg : gradient ψ =ᶠ[𝓝 y] gradient φ := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
    unfold gradient
    rw [hz]
  exact hg.fderiv_eq

omit [FiniteDimensional ℝ E] in
theorem bilinearIteratedFDerivTwo_congr_of_eventuallyEq {φ ψ : E → ℝ} {y : E} (h : ψ =ᶠ[𝓝 y] φ) :
    bilinearIteratedFDerivTwo ℝ ψ y = bilinearIteratedFDerivTwo ℝ φ y := by
  unfold bilinearIteratedFDerivTwo
  rw [h.fderiv.fderiv_eq]

/-- `⟪(∇²φ)⁻¹θ, θ⟫` in standard coordinates. -/
private theorem inner_ringInverse_hessianOperator_eq_invHessQuad (φ : E → ℝ) (θ : E) (y : E) :
    ⟪Ring.inverse (hessianOperator φ y) θ, θ⟫ = invHessQuad φ (fun j => ⟪e j, θ⟫) y := by
  set R := Ring.inverse (hessianOperator φ y)
  have hθ : θ = ∑ j, ⟪e j, θ⟫ • e j := ((e).sum_repr' θ).symm
  conv_lhs => rw [hθ]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  unfold invHessQuad inverseHessianEntry operatorEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (e i) (R (e j))]
  ring

/-- Inverse-Hessian entries only depend on the germ of the function. -/
theorem inverseHessianEntry_congr_of_eventuallyEq {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ ψ : E → ℝ} {y : E} (h : ψ =ᶠ[𝓝 y] φ) :
    inverseHessianEntry ψ b y = inverseHessianEntry φ b y := by
  funext i j
  unfold inverseHessianEntry
  rw [hessianOperator_congr_of_eventuallyEq h]

omit [FiniteDimensional ℝ E] in
/-- `log det ∇²φ` only depends on the germ of the function. -/
theorem logDetHessian_congr_of_eventuallyEq {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ ψ : E → ℝ} {y : E} (h : ψ =ᶠ[𝓝 y] φ) :
    logDetHessian ψ b y = logDetHessian φ b y := by
  unfold logDetHessian hessianMatrixIn
  rw [bilinearIteratedFDerivTwo_congr_of_eventuallyEq h]

/-- **Germ transfer.** A function smooth on an open set agrees, on a neighbourhood of each of
its points, with a globally smooth function; at every point of that neighbourhood the two have
the same germ, hence the same Hessian, inverse-Hessian entries and `log det ∇²`. -/
theorem exists_contDiff_eventuallyEq_germ {K : Set E} (hK : IsOpen K) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ K) {x : E} (hx : x ∈ K) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ ∀ᶠ y in 𝓝 x, ψ =ᶠ[𝓝 y] φ := by
  obtain ⟨ψ, hψ, hψφ⟩ := FunctionalInequalities.Analysis.exists_contDiff_eventuallyEq
    (m := ⊤) hK hφ hx
  exact ⟨ψ, hψ, hψφ.eventuallyEq_nhds⟩

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "e" => stdOrthonormalBasis ℝ E

/-- **Klartag, Logarithmically-concave moment measures I, arXiv:1309.2767v1, Lemma 5.2**, in
the dual (transport-to-`K`) form of Section 5 with the regularity localized to `K`.
Let `K` be open and convex, `φ` smooth on `K` with positive definite Hessian there, `ρ` convex
and `C²` on `K`, and `det ∇²φ(x) = exp(x·∇φ(x) - φ(x) - ρ(x))` on `K`, (66), written as
`log det ∇²φ = ⟪x, ∇φ x⟫ - φ x - ρ x`. For every `θ` (Klartag: `θ = e₁`), with
`f = ⟪(∇²φ)⁻¹θ, θ⟫ = φ^{θθ}` and the operator `L u = φ^{ij} u_ij - x^i u_i` of (67),
`L(f^ε) + ε f^ε ≥ 0` on `K` for every `ε > 0`. -/
theorem inverseHessian_rpow_supersolution {K : Set E} (hK : IsOpen K) {φ ρ : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ K) (hρ : ContDiffOn ℝ 2 ρ K) (hρc : ConvexOn ℝ K ρ)
    (hPD : ∀ y ∈ K, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hEq : ∀ y ∈ K, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y) (θ : E) {ε : ℝ}
    (hε : 0 < ε) {x : E} (hx : x ∈ K) :
    0 ≤
      nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫)
          (fun y => ⟪Ring.inverse (hessianOperator φ y) θ, θ⟫ ^ ε) x +
        ε * ⟪Ring.inverse (hessianOperator φ x) θ, θ⟫ ^ ε := by
  obtain ⟨ψ, hψ, hloc⟩ := exists_contDiff_eventuallyEq_germ hK hφ hx
  have hKx : ∀ᶠ y in 𝓝 x, y ∈ K := hK.mem_nhds hx
  have hPD' : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ y v v := by
    filter_upwards [hloc, hKx] with y hy hyK
    rw [bilinearIteratedFDerivTwo_congr_of_eventuallyEq hy]
    exact hPD y hyK
  have hEq' : ∀ᶠ y in 𝓝 x, logDetHessian ψ e y = ⟪y, gradient ψ y⟫ - ψ y - ρ y := by
    filter_upwards [hloc, hKx] with y hy hyK
    have hg : gradient ψ y = gradient φ y := by
      unfold gradient
      rw [hy.fderiv_eq]
    rw [logDetHessian_congr_of_eventuallyEq _ hy, hg, hy.eq_of_nhds]
    exact hEq y hyK
  have hρx : ContDiffAt ℝ 2 ρ x := hρ.contDiffAt (hK.mem_nhds hx)
  have hρpsd : ∀ v, 0 ≤ bilinearIteratedFDerivTwo ℝ ρ x v v :=
    bilinearIteratedFDerivTwo_self_nonneg_of_convexOn_open hK hρ hρc hx
  have hcore :=
    invHessQuad_rpow_generator_nonneg_core hψ hPD' hρx hρpsd hEq' (fun j => ⟪e j, θ⟫) hε
  have hfun :
    (fun y => invHessQuad ψ (fun j => ⟪e j, θ⟫) y ^ ε) =ᶠ[𝓝 x]
      (fun y => ⟪Ring.inverse (hessianOperator φ y) θ, θ⟫ ^ ε) := by
    filter_upwards [hloc] with y hy
    rw [← inner_ringInverse_hessianOperator_eq_invHessQuad,
      hessianOperator_congr_of_eventuallyEq hy]
  have hAx : (fun y => inverseHessianEntry ψ e y) x = (fun y => inverseHessianEntry φ e y) x := by
    exact inverseHessianEntry_congr_of_eventuallyEq _ hloc.self_of_nhds
  have e1 := nondivergenceOperator_congr (b := fun y i => ⟪y, e i⟫) hAx hfun
  have e2 :
    invHessQuad ψ (fun j => ⟪e j, θ⟫) x ^ ε = ⟪Ring.inverse (hessianOperator φ x) θ, θ⟫ ^ ε :=
    hfun.self_of_nhds
  rw [e1, e2] at hcore
  exact hcore

end FunctionalInequalities.Probability.MomentMeasure
end
