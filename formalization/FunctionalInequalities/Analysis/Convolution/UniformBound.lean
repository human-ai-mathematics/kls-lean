module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Uniform bound for convolution with an integrable kernel

Supporting the interior derivative estimates for harmonic functions in Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Theorem 2.10 /
estimate (2.31), as used in Theorem 4.6, p. 60:

* `norm_convolution_le_of_bound`: for an integrable kernel `f : ℝⁿ → F`, a continuous bilinear map
  `L : F →L ℝ →L G` and a scalar source with `|g| ≤ M` everywhere,
  `‖(f ⋆[L] g) x‖ ≤ (‖L‖ * ∫ ‖f‖) * M` at every point `x`.

The intended clients use fixed derivatives of a smooth compact annular kernel, so no derivative of
the harmonic source enters the constant. This is the elementary `L¹ × L∞` bound only; no
measurability or integrability of `g` is needed, since a non-integrable integrand has Bochner
integral `0`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Convolution
namespace FunctionalInequalities.Analysis
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A fixed L¹ kernel controls the actual bilinear convolution against a bounded
scalar source. No desired derivative or harmonic estimate is a premise. -/
theorem norm_convolution_le_of_bound {n : ℕ} (L : F →L[ℝ] ℝ →L[ℝ] G)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : Integrable f volume)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hg : ∀ y, |g y| ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(f ⋆[L, volume] g) x‖ ≤ (‖L‖ * ∫ y, ‖f y‖) * M := by
  rw [convolution_def]
  calc
    ‖∫ y, L (f y) (g (x - y))‖ ≤ ∫ y, ‖L‖ * ‖f y‖ * M := by
      apply norm_integral_le_of_norm_le ((hf.norm.const_mul ‖L‖).mul_const M)
      apply Eventually.of_forall
      intro y
      exact (L.le_opNorm₂ (f y) (g (x - y))).trans
        (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hg (x - y))
          (mul_nonneg (norm_nonneg L) (norm_nonneg (f y))))
    _ = (‖L‖ * ∫ y, ‖f y‖) * M := by
      rw [integral_mul_const, integral_const_mul]
end FunctionalInequalities.Analysis
