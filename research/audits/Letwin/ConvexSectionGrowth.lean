module

public import FunctionalInequalities.Analysis.Convex.Section.Growth

/-!
# Audit: the convex Hölder supports on the planar quadratic

Clients of `Analysis` on `u(x) = ‖x‖²` in the plane, with every hypothesis derived:
the tangent-plane growth is exactly `‖z − x‖²` (`α = 1`, `C = 1`), so
`exists_holder_gradient_of_growth` gives a
Lipschitz gradient on the closed unit ball; the sections `S_h(x) ⊇ closedBall x (h^{1/2})` feed
`growth_of_closedBall_subset_section` (`θ = 1/2`, exponent `2`); and the Alexandrov section estimate
applies at
`x = 0`, `p = 0`, where the section `{‖y‖² < h}` is bounded. `#print axioms` for the clients and the
producers.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace ConvexHolderAudit
open FunctionalInequalities.Analysis

abbrev E := EuclideanSpace ℝ (Fin 2)

/-- The planar quadratic. -/
def normSq (x : E) : ℝ := ‖x‖ ^ 2

theorem normSq_convex : ConvexOn ℝ Set.univ normSq :=
  convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2

theorem normSq_contDiff : ContDiff ℝ 1 normSq := (contDiff_norm_sq ℝ).of_le le_top

theorem normSq_continuous : Continuous normSq := normSq_contDiff.continuous

theorem gradient_normSq (x : E) : gradient normSq x = (2 : ℝ) • x := by
  have h0 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hder : (InnerProductSpace.toDual ℝ E) ((2 : ℝ) • x) = 2 • (innerSL ℝ) x := by
    ext v
    simp
  have h : HasFDerivAt normSq ((InnerProductSpace.toDual ℝ E) ((2 : ℝ) • x)) x := by
    rw [hder]
    exact h0
  exact (hasGradientAt_iff_hasFDerivAt.mpr h).gradient

/-- Exact tangent-plane growth: `u z − u x − ⟪∇u x, z − x⟫ = ‖z − x‖²`. -/
theorem normSq_growth (x z : E) :
    normSq z ≤ normSq x + ⟪gradient normSq x, z - x⟫ + 1 * ‖z - x‖ ^ ((1 : ℝ) + 1) := by
  rw [gradient_normSq, show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [normSq, inner_smul_left, RCLike.conj_to_real, one_mul]
  have : ‖z - x‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪x, z⟫ + ‖x‖ ^ 2 := by
    rw [@norm_sub_sq_real, real_inner_comm]
  rw [this, inner_sub_right]
  linarith [real_inner_self_eq_norm_sq x]

/-- The Hölder (here Lipschitz) gradient bound on the closed unit ball from the growth alone. -/
theorem normSq_holder_gradient :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖gradient normSq y - gradient normSq x‖ ≤ C' * ‖y - x‖ ^ (1 : ℝ) :=
  exists_holder_gradient_of_growth normSq_convex normSq_contDiff (isCompact_closedBall _ _)
    (C := 1) (α := 1) (r₀ := 1) zero_le_one zero_le_one one_pos
    (fun x _ z _ => normSq_growth x z)

/-- Sections of the quadratic contain the balls of radius `h^{1/2}`. -/
theorem normSq_section_ball (x : E) : ∀ h : ℝ, 0 < h → h ≤ 1 →
    closedBall x (1 * h ^ ((1 : ℝ) / 2)) ⊆
      {z | normSq z ≤ normSq x + ⟪gradient normSq x, z - x⟫ + h} := by
  intro h hh _ z hz
  rw [mem_closedBall, dist_eq_norm, one_mul] at hz
  have hzx : ‖z - x‖ ^ 2 ≤ h := by
    calc ‖z - x‖ ^ 2 ≤ (h ^ ((1 : ℝ) / 2)) ^ 2 := by gcongr
      _ = h := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]; norm_num
  change normSq z ≤ normSq x + ⟪gradient normSq x, z - x⟫ + h
  have := normSq_growth x z
  rw [show ((1 : ℝ) + 1) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  linarith

/-- The growth bound recovered from the section inclusion (exponent `(1/2)⁻¹ = 2`). -/
theorem normSq_growth_of_sections (x : E) : ∀ z, ‖z - x‖ ≤ 1 * (1 : ℝ) ^ ((1 : ℝ) / 2) →
    normSq z ≤ normSq x + ⟪gradient normSq x, z - x⟫ + (‖z - x‖ / 1) ^ ((1 : ℝ) / 2)⁻¹ :=
  growth_of_closedBall_subset_section one_pos (by norm_num) one_pos (normSq_section_ball x)

/-- The Alexandrov section estimate at the origin of the quadratic. -/
theorem normSq_section_estimate :
    ∃ c : ℝ,
      0 < c ∧
        ∀ h : ℝ,
          0 < h →
            ENNReal.ofReal (c * h ^ Module.finrank ℝ E) ≤
              (volume : Measure E)
                  (FunctionalInequalities.Analysis.subgradientImage normSq
                    {y | normSq y < normSq 0 + ⟪(0 : E), y - 0⟫ + h}) *
                ENNReal.ofReal
                  (diam {y | normSq y < normSq 0 + ⟪(0 : E), y - 0⟫ + h} ^
                      (Module.finrank ℝ E - 1) *
                    infDist 0 (frontier {y | normSq y < normSq 0 + ⟪(0 : E), y - 0⟫ + h})) := by
  obtain ⟨c, hc, hest⟩ := exists_section_alexandrov_estimate (E := E)
  refine ⟨c, hc, fun h hh => hest normSq normSq_convex normSq_continuous 0 0 h hh ?_⟩
  refine (Metric.isBounded_iff_subset_closedBall (0 : E)).mpr ⟨Real.sqrt h, fun y hy => ?_⟩
  change normSq y < normSq 0 + ⟪(0 : E), y - 0⟫ + h at hy
  simp only [normSq, norm_zero, inner_zero_left] at hy
  rw [mem_closedBall, dist_zero_right]
  exact Real.le_sqrt_of_sq_le (by linarith)
end ConvexHolderAudit

#print axioms ConvexHolderAudit.normSq_holder_gradient
#print axioms ConvexHolderAudit.normSq_growth_of_sections
#print axioms ConvexHolderAudit.normSq_section_estimate
#print axioms FunctionalInequalities.Analysis.norm_gradient_sub_le_of_growth
#print axioms FunctionalInequalities.Analysis.exists_holder_gradient_of_growth
#print axioms FunctionalInequalities.Analysis.growth_of_closedBall_subset_section
#print axioms FunctionalInequalities.Analysis.exists_section_alexandrov_estimate
#print axioms FunctionalInequalities.Analysis.exists_section_alexandrov_estimate_real
