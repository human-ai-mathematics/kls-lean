module

public import examples.EllipticDrift

/-! The exact positive-radius drift-point contract, including its chosen vectors and coefficients.
-/

@[expose] public section
noncomputable section

example {ρ : ℝ} (hρ0 : 0 < ρ) (k : ℝ) :
    let zeta : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 0]
    let x : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 ![ρ / (2 * Real.sqrt 2), ρ / (2 * Real.sqrt 2)]
    let b : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, -1]
    ‖zeta‖ = 1 ∧
      zeta (Fin.last 1) = 0 ∧
        b ≠ 0 ∧
          ‖b‖ ≤ 2 ∧
            0 < x (Fin.last 1) ∧
              ((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2 = (ρ / 2) ^ 2 ∧
                Real.sqrt (((∑ i, zeta i * x i) - 0) ^ 2 + (x (Fin.last 1)) ^ 2) = ρ / 2 ∧
                  ∀ v : EuclideanSpace ℝ (Fin 2),
                    1 * ‖v‖ ^ 2 ≤
                        (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ∧
                      (∑ i, ∑ j, CNSCoefficientScopeAudit.coefficient k i j * v i * v j) ≤
                        1 * ‖v‖ ^ 2 :=
  FunctionalInequalities.Analysis.LogRadialDriftPointFixture.drift_point_geometry hρ0 k

#print axioms FunctionalInequalities.Analysis.LogRadialDriftPointFixture.drift_point_geometry
