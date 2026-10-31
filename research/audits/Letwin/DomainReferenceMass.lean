module

public import FunctionalInequalities.Analysis.Convex.ContactMeasure
@[expose] public section

noncomputable section
open Set MeasureTheory Metric
open scoped RealInnerProductSpace ENNReal
namespace DomainReferenceMassAudit
open FunctionalInequalities.Analysis
/-- Actual unit quadratic constructs its MA and local differentiation, in every
n including0 and on every open working domain. -/
theorem actual_unit_quadratic {n : ℕ} {Ω G : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hG : IsOpen G) (hGO : G ⊆ Ω) :
    volume G ≤
      volume (gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0) '' closure G) := by
  let q : EuclideanSpace ℝ (Fin n) → ℝ := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0
  have hq : ContDiff ℝ 1 q := (contDiff_quadraticAt _ _ _ _).of_le (by norm_num)
  have hc : ConvexOn ℝ univ q := convexOn_quadraticAt Matrix.PosDef.one.posSemidef _ _ _
  apply
    volume_le_gradient_image_closure_of_domain_alexandrov hΩ
      (hq.differentiable one_ne_zero).differentiableOn hG hGO
  intro U hU hUO
  rw [subgradientImageOn_eq_subgradientImage hc hΩ
      (hq.differentiable one_ne_zero).differentiableOn hUO]
  rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one _ _ _ hU.measurableSet,
    Matrix.det_one, ENNReal.ofReal_one, one_mul]

end DomainReferenceMassAudit
set_option pp.fullNames true in
#print axioms DomainReferenceMassAudit.actual_unit_quadratic
