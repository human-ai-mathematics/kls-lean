import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder transport of bilinear fields under a linear map

Supporting the linear change of variables in the Schauder theory of Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 6.1,
p. 88, and Theorem 6.2, pp. 90–92, where Hölder seminorms of second derivatives are compared before
and after a linear transformation of coordinates.

* `norm_bilinearComp_self_le`: `‖B.bilinearComp T T‖ ≤ ‖B‖ ‖T‖²` in operator norm;
* `bilinear_field_holder_linear_transport`: if a bilinear field `H` satisfies
  `‖H x - H y‖ ≤ C ‖x - y‖^α` on `s` (`C, α ≥ 0`), then `x ↦ (H (T x)).bilinearComp T T` satisfies
  the same bound on `T ⁻¹' s` with constant `C ‖T‖² ‖T‖^α`.

The zero map and zero-dimensional spaces are included; neither positivity of `‖T‖` nor a
transformed Hölder estimate is a premise. This is a generic transport bound; it is independent of
the Hessian pullback identity and asserts no Schauder estimate.
-/
noncomputable section
namespace FunctionalInequalities.Analysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Operator-norm bound for composing a bilinear map with the same linear map in both slots. -/
theorem norm_bilinearComp_self_le
    (B : F →L[ℝ] F →L[ℝ] ℝ) (T : E →L[ℝ] F) :
    ‖B.bilinearComp T T‖ ≤ ‖B‖ * ‖T‖ ^ 2 := by
  calc
    ‖B.bilinearComp T T‖ = ‖(B.comp T).flip.comp T‖ :=
      ContinuousLinearMap.opNorm_flip _
    _ ≤ ‖(B.comp T).flip‖ * ‖T‖ :=
      (B.comp T).flip.opNorm_comp_le T
    _ = ‖B.comp T‖ * ‖T‖ := by
      rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ (‖B‖ * ‖T‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right (B.opNorm_comp_le T) (norm_nonneg T)
    _ = ‖B‖ * ‖T‖ ^ 2 := by
      rw [pow_two, mul_assoc]

/-- A Hölder-type difference bound of a bilinear field transports through `bilinearComp T T` with
the operator-norm factor `‖T‖² ‖T‖^α`. The zero map and zero-dimensional spaces are included. -/
theorem bilinear_field_holder_linear_transport
    {H : F → F →L[ℝ] F →L[ℝ] ℝ} {s : Set F} {C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hH : ∀ x ∈ s, ∀ y ∈ s, ‖H x - H y‖ ≤ C * ‖x - y‖ ^ α)
    (T : E →L[ℝ] F) :
    ∀ x ∈ T ⁻¹' s, ∀ y ∈ T ⁻¹' s,
      ‖(H (T x)).bilinearComp T T - (H (T y)).bilinearComp T T‖ ≤
        C * ‖T‖ ^ 2 * ‖T‖ ^ α * ‖x - y‖ ^ α := by
  intro x hx y hy
  have hsub :
      (H (T x)).bilinearComp T T - (H (T y)).bilinearComp T T =
        (H (T x) - H (T y)).bilinearComp T T := by
    ext v w
    rfl
  have hT : ‖T x - T y‖ ≤ ‖T‖ * ‖x - y‖ := by
    simpa only [map_sub] using T.le_opNorm (x - y)
  have hpow :
      ‖T x - T y‖ ^ α ≤ (‖T‖ * ‖x - y‖) ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) hT hα
  rw [hsub]
  calc
    ‖(H (T x) - H (T y)).bilinearComp T T‖
        ≤ ‖H (T x) - H (T y)‖ * ‖T‖ ^ 2 :=
      norm_bilinearComp_self_le _ T
    _ ≤ (C * ‖T x - T y‖ ^ α) * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hH (T x) hx (T y) hy) (sq_nonneg ‖T‖)
    _ ≤ (C * (‖T‖ * ‖x - y‖) ^ α) * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hC) (sq_nonneg ‖T‖)
    _ = C * ‖T‖ ^ 2 * ‖T‖ ^ α * ‖x - y‖ ^ α := by
      rw [Real.mul_rpow (norm_nonneg T) (norm_nonneg (x - y))]
      ac_rfl

end FunctionalInequalities.Analysis
