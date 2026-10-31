module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace LetwinSectionComparisonAudit
open FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The comparison potential and its MA equation are constructed, rather than supplied:
a unit-density quadratic on the unit ball. The unknown Dirichlet solution has only
convexity, its boundary values and density bounds. -/
theorem quadratic_reference_stability (hn : 0 < n) {u f : E → ℝ}
    (hu : ConvexOn ℝ univ u) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hu0 : ∀ x ∈ frontier (ball (0 : E) 1), u x = 0)
    (hf : ∀ x ∈ ball (0 : E) 1, (1 - ε) ^ n ≤ f x ∧ f x ≤ (1 + ε) ^ n)
    (hMA : ∀ G : Set E, IsOpen G → G ⊆ ball (0 : E) 1 →
      volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y)) :
    ∀ x ∈ ball (0 : E) 1,
      |u x - quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2) x| ≤
        ε * |quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2) x| := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let v : E → ℝ := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
  have hv : ConvexOn ℝ univ v := convexOn_quadraticAt Matrix.PosSemidef.one 0 0 _
  have hv0 : ∀ x ∈ frontier (ball (0 : E) 1), v x = 0 := by
    intro x hx
    rw [frontier_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hx
    have hnrm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    dsimp [v, quadraticAt]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, sub_zero, inner_zero_left]
    norm_num [real_inner_self_eq_norm_sq, hnrm]
  apply abs_sub_le_of_alexandrov_density_close hn hu hv isOpen_ball isBounded_ball hu0 hv0 hε hε1
  · intro G hG hGO
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
  · intro G hG _
    change volume (subgradientImage (quadraticAt _ _ _ _) G) = volume G
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one, Matrix.det_one,
      ENNReal.ofReal_one, one_mul]
    exact hG.measurableSet
end LetwinSectionComparisonAudit
#print axioms LetwinSectionComparisonAudit.quadratic_reference_stability
#print axioms FunctionalInequalities.Analysis.le_of_strict_alexandrov_bounds
#print axioms FunctionalInequalities.Analysis.bounds_of_alexandrov_density_bounds
#print axioms FunctionalInequalities.Analysis.abs_sub_le_of_alexandrov_density_close
