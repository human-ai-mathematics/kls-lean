import FunctionalInequalities.Analysis.IteratedDerivative.CoefficientFreezing
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinate form of the coefficient-freezing error

Specializes `FunctionalInequalities.Analysis.freezingError` to the `n²` direction pairs
`(b i, b j)`, `(i, j) : Fin n × Fin n`, as in the operator `aⁱʲ Dᵢⱼ u` of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7),
Theorem 6.2, pp. 90–92, equations (6.17)–(6.19):

* `principalPart_coordinates`: the finite-direction principal part over `Fin n × Fin n` is the
  double coordinate sum `∑ᵢ ∑ⱼ aᵢⱼ(x) B x (b i) (b j)`;
* `coordinate_freezing_bounds`: the sup and `α`-Hölder bounds of `freezing_bounds` for the actual
  Fréchet Hessian `fderiv ℝ (fderiv ℝ f)` in a frame with `‖b i‖ ≤ 1`, with the factor exactly `n²`;
* `euclideanError`, `euclideanError_eq_sum`, `euclidean_freezing_bounds`: the same in
  `EuclideanSpace ℝ (Fin n)` with the standard orthonormal basis.

Only the principal part is treated; lower-order terms, ellipticity and the Schauder estimate
itself are not part of this module.
-/
noncomputable section
open Set Metric
namespace FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The finite-direction operator is exactly the double coordinate sum, not a
formal array of unrelated directional values. -/
theorem principalPart_coordinates {n : ℕ} (a : Fin n → Fin n → E → ℝ)
    (b : Fin n → E) (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    principalPart (fun p : Fin n × Fin n => a p.1 p.2)
      (fun p => b p.1) (fun p => b p.2) B x =
      ∑ i, ∑ j, a i j x * B x (b i) (b j) := by
  simp only [principalPart, Fintype.sum_prod_type]

/-- Source-coordinate specialization: n² actual Hessian entries in a normalized
coordinate frame. The standard Euclidean orthonormal basis satisfies hb. -/
theorem coordinate_freezing_bounds {n : ℕ}
    {a : Fin n → Fin n → E → ℝ} {b : Fin n → E}
    {f : E → ℝ} {c : E} {r α K N H : ℝ} (hr : 0 ≤ r) (hα : 0 ≤ α) (hK : 0 ≤ K)
    (hb : ∀ i, ‖b i‖ ≤ 1)
    (ha : ∀ i j, ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      |a i j x - a i j y| ≤ K * ‖x - y‖ ^ α)
    (hB : ∀ x ∈ closedBall c r, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ N)
    (hBH : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y‖ ≤ H * ‖x - y‖ ^ α) :
    (∀ x ∈ closedBall c r,
      |∑ i, ∑ j, (a i j c - a i j x) * fderiv ℝ (fderiv ℝ f) x (b i) (b j)| ≤
        (n : ℝ) ^ 2 * K * r ^ α * N) ∧
    (∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      |(∑ i, ∑ j, (a i j c - a i j x) * fderiv ℝ (fderiv ℝ f) x (b i) (b j)) -
        (∑ i, ∑ j, (a i j c - a i j y) * fderiv ℝ (fderiv ℝ f) y (b i) (b j))| ≤
        (n : ℝ) ^ 2 * K * (N + r ^ α * H) * ‖x - y‖ ^ α) := by
  have h := freezing_bounds (ι := Fin n × Fin n) hr hα hK
    (fun p => hb p.1) (fun p => hb p.2) (fun p => ha p.1 p.2) hB hBH
  simpa only [freezingError, Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, pow_two] using h

/-- Actual standard-coordinate freezing error, with all n² entries. -/
def euclideanError {n : ℕ} (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (c x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  freezingError (fun p : Fin n × Fin n => a p.1 p.2)
    (fun p => EuclideanSpace.basisFun (Fin n) ℝ p.1)
    (fun p => EuclideanSpace.basisFun (Fin n) ℝ p.2)
    (fderiv ℝ (fderiv ℝ u)) c x

/-- The Euclidean freezing error as the explicit double coordinate sum. -/
theorem euclideanError_eq_sum {n : ℕ}
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (c x : EuclideanSpace ℝ (Fin n)) :
    euclideanError a u c x = ∑ i, ∑ j, (a i j c - a i j x) *
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  simp only [euclideanError, freezingError, Fintype.sum_prod_type]

/-- The principal-error estimate on the actual canonical Fréchet Hessian and
standard orthonormal basis; the factor is exactly n². -/
theorem euclidean_freezing_bounds {n : ℕ}
    {a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)}
    {r α K N H : ℝ} (hr : 0 ≤ r) (hα : 0 ≤ α) (hK : 0 ≤ K)
    (ha : ∀ i j, ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      |a i j x - a i j y| ≤ K * ‖x - y‖ ^ α)
    (hB : ∀ x ∈ closedBall c r, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ N)
    (hBH : ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) :
    (∀ x ∈ closedBall c r, |euclideanError a u c x| ≤ (n : ℝ) ^ 2 * K * r ^ α * N) ∧
    (∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      |euclideanError a u c x - euclideanError a u c y| ≤
        (n : ℝ) ^ 2 * K * (N + r ^ α * H) * ‖x - y‖ ^ α) := by
  simpa only [euclideanError_eq_sum] using coordinate_freezing_bounds hr hα hK
    (fun i => ((EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i).le) ha hB hBH

end FunctionalInequalities.Analysis
