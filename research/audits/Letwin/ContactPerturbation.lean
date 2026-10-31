module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace LetwinContactPerturbationAudit
open FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem unit_quadratic_C1 :
    ContDiff ℝ 1 (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : E) 0 (-1 / 2)) :=
  (contDiff_quadraticAt _ _ _ _).of_le (by norm_num)

/-- Actual unit-density quadratic reference geometry. No convexity assumption
on the C1 perturbation is supplied to obtain its interior supporting contacts. -/
theorem quadratic_reference_contacts :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ (w : E → ℝ),
          ContDiff ℝ 1 w →
            (∀ y ∈ closure (ball (0 : E) 1),
                |w y - quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2) y| ≤ ε) →
              ∀ z ∈ closedBall (0 : E) (1 / 2),
                ∃ x ∈ ball (0 : E) 1,
                  gradient w x =
                      gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)) z ∧
                    ∀ y ∈ closure (ball (0 : E) 1),
                      w x +
                          ⟪gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)) z,
                            y - x⟫ ≤
                        w y := by
  apply
    exists_contact_of_uniform_close (strictConvexOn_quadraticAt Matrix.PosDef.one _ _ _)
      unit_quadratic_C1 isOpen_ball isBounded_ball (isCompact_closedBall _ _)
  exact closedBall_subset_ball (by norm_num)

/-- The reference, its strictness, smoothness, boundary data and unit MA
measure are all constructed. Only the unknown solution supplies its genuine
MA equation and pointwise density error. Epsilon precedes that unknown data. -/
theorem quadratic_reference_residual_contacts (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ (u f : E → ℝ),
      ConvexOn ℝ univ u → ContDiff ℝ 1 u →
      (∀ x ∈ frontier (ball (0 : E) 1), u x = 0) →
      (∀ x ∈ ball (0 : E) 1, (1 - ε) ^ n ≤ f x ∧ f x ≤ (1 + ε) ^ n) →
      (∀ G : Set E, IsOpen G → G ⊆ ball (0 : E) 1 →
        volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y)) →
      ∀ z ∈ closedBall (0 : E) (1 / 2), ∃ x ∈ ball (0 : E) 1,
        gradient u x - (1 - δ) •
          gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)) x =
          δ • gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)) z ∧
        ∀ y ∈ closure (ball (0 : E) 1),
          u x - (1 - δ) * quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2) x +
            ⟪δ • gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)) z, y - x⟫ ≤
          u y - (1 - δ) * quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2) y := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let v : E → ℝ := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
    have hv0 : ∀ x ∈ frontier (ball (0 : E) 1), v x = 0 := by
      intro x hx
      rw [frontier_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hx
      have hnrm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
      dsimp [v, quadraticAt]
      simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, sub_zero, inner_zero_left]
      norm_num [real_inner_self_eq_norm_sq, hnrm]
    have hMAv :
      ∀ G : Set E,
        IsOpen G → G ⊆ ball (0 : E) 1 → volume (subgradientImage v G) = volume G := by
      intro G hG _
      change volume (subgradientImage (quadraticAt _ _ _ _) G) = volume G
      rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one, Matrix.det_one,
        ENNReal.ofReal_one, one_mul]
      exact hG.measurableSet
    obtain ⟨ε, hε, hε1, hcontact⟩ :=
      exists_residual_contact_of_alexandrov_density_close hn
        (strictConvexOn_quadraticAt Matrix.PosDef.one _ _ _) unit_quadratic_C1
        isOpen_ball isBounded_ball hv0 hMAv (isCompact_closedBall (0 : E) (1 / 2))
        (closedBall_subset_ball (by norm_num)) hδ
    refine ⟨ε, hε, hε1, ?_⟩
    intro u f hu huC1 hu0 hf hMA
    apply hcontact u hu huC1 hu0
    intro G hG hGO
    rw [hMA G hG hGO]
    constructor
    · rw [← setLIntegral_const G]
      apply setLIntegral_mono' hG.measurableSet
      intro y hy
      exact ENNReal.ofReal_le_ofReal (hf y (hGO hy)).1
    · rw [← setLIntegral_const G]
      apply setLIntegral_mono' hG.measurableSet
      intro y hy
      exact ENNReal.ofReal_le_ofReal (hf y (hGO hy)).2

end LetwinContactPerturbationAudit
#print axioms FunctionalInequalities.Analysis.gradient_tangent_gap_pos
#print axioms FunctionalInequalities.Analysis.exists_contact_of_uniform_close
#print axioms FunctionalInequalities.Analysis.exists_residual_contact_of_alexandrov_density_close
#print axioms LetwinContactPerturbationAudit.quadratic_reference_contacts
#print axioms LetwinContactPerturbationAudit.quadratic_reference_residual_contacts
#check LetwinContactPerturbationAudit.quadratic_reference_contacts (n := 0)
