module

public import FunctionalInequalities.Analysis.LogRadial.Operator
public import examples.EllipticDrift

/-!
# Client of the zeroth-order radial/log margin

`skew_zeroth_margin_client`: for `ℓ = Λ = 1`, `ε = 1/24`, `B = 2`, `C = 3`, the radius `ρ` generated
by the main
theorem is chosen once. The point, tangent, drift and coefficient come from the shared client-only
fixture:
`x = (t, t)` with `t = ρ / (2 √2)`, `ζ = e₀`, `b = (1, -1) ≠ 0`, `r = ρ / 2 < ρ`, and the skew
coefficient
`[[1, k], [-k, 1]]` for an ARBITRARY `k`. With the nonzero zeroth-order coefficient `a = -3`, the
main theorem gives
`0 ≤ φ(x)` and `1 / (8 ρ) ≤ tr(A D²φ(x)) + Dφ(x) b - 3 φ(x)`.
-/

@[expose] public section

noncomputable section
open scoped ContDiff

namespace FunctionalInequalities.Analysis.LogRadialZerothClient

open FunctionalInequalities.Analysis

theorem skew_zeroth_margin_client (k : ℝ) :
    ∃ ρ : ℝ,
      0 < ρ ∧
        ρ < 1 ∧
          let zeta : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
          let x : EuclideanSpace ℝ (Fin 2) :=
            WithLp.toLp 2 ![ρ / (2 * Real.sqrt 2), ρ / (2 * Real.sqrt 2)]
          let b : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, -1]
          let φ : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
            (Real.sqrt (((∑ i, zeta i * y i) - 0) ^ 2 + (y 1) ^ 2) + ((∑ i, zeta i * y i) - 0) -
                1 / 24 * y 1 * Real.log (((∑ i, zeta i * y i) - 0) ^ 2 + (y 1) ^ 2)) /
              2
          b ≠ 0 ∧
            0 ≤ φ x ∧
              1 / (8 * ρ) ≤
                Matrix.trace
                      (CNSCoefficientScopeAudit.coefficient k *
                        ((Matrix.of fun i j =>
                            fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                              (EuclideanSpace.single j (1 : ℝ))) :
                          Matrix (Fin 2) (Fin 2) ℝ)) +
                    (fderiv ℝ φ x) b +
                  (-3 : ℝ) * φ x := by
  -- the radius is generated ONCE by the main theorem

  obtain ⟨ρ, hρ0, hρ1, hmain⟩ :=
    exists_log_radial_zeroth_margin_radius (ell := 1) (Λ := 1) (ε := 1 / 24) (B := 2) (C := 3)
      one_pos one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨ρ, hρ0, hρ1, ?_⟩
  intro zeta x b
    φ
      -- the generated point geometry from the shared client-only fixture

  have hfix := LogRadialDriftPointFixture.drift_point_geometry hρ0 k
  have hz : ‖zeta‖ = 1 := hfix.1
  have hztan : zeta (Fin.last 1) = 0 := hfix.2.1
  have hb0 : b ≠ 0 := hfix.2.2.1
  have hb : ‖b‖ ≤ 2 := hfix.2.2.2.1
  have hx : 0 < x (Fin.last 1) := hfix.2.2.2.2.1
  have hsq : Real.sqrt (((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2) = ρ / 2 :=
    hfix.2.2.2.2.2.2.1
  have hell :
    ∀ v : EuclideanSpace ℝ (Fin 2),
      1 * ‖v‖ ^ 2 ≤ (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ∧
        (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ≤ 1 * ‖v‖ ^ 2 :=
    hfix.2.2.2.2.2.2.2
  have hr : Real.sqrt (((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2) < ρ := by
    rw [hsq]
    linarith
  have h :
    0 ≤ φ x ∧
      1 / (16 * Real.sqrt (((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2)) ≤
        Matrix.trace
              (CNSCoefficientScopeAudit.coefficient k *
                ((Matrix.of fun i j =>
                    fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i (1 : ℝ))
                      (EuclideanSpace.single j (1 : ℝ))) :
                  Matrix (Fin 2) (Fin 2) ℝ)) +
            (fderiv ℝ φ x) b +
          (-3 : ℝ) * φ x :=
    hmain 0 zeta hz hztan (CNSCoefficientScopeAudit.coefficient k) hell b hb (-3)
      ⟨by norm_num, by norm_num⟩ 0 x hx hr
  obtain ⟨hφ0, hmarg⟩ := h
  rw [hsq] at hmarg
  refine ⟨hb0, hφ0, le_of_eq_of_le ?_ hmarg⟩
  field_simp
  ring

end FunctionalInequalities.Analysis.LogRadialZerothClient

#print axioms FunctionalInequalities.Analysis.LogRadialZerothClient.skew_zeroth_margin_client
