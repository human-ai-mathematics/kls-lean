import FunctionalInequalities.Probability.Support.Convex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Audit clients for Cordero-Erausquin–Klartag (arXiv:1304.0630v1), Lemma 16 (`Probability/Support/Convex.lean`,
sections `EffectiveDomain`, `FiniteMeasureHalfspace`, `PointControl`). Section `PromotionClients`: the public
real-convexity helper and the point control in its module. Section `MassClients`:
a mass-two measure at the endpoints of `[-1, 1]` (not a probability measure, all mass outside the open support hull),
and the zero-dimensional halfspace bound for a mass-three Dirac measure. The probability bound (54) keeps its
existing clients in `research/audits/BKL/ConvexSupportAudit.lean`. -/

noncomputable section

section PromotionClients

namespace PromotionAPIClient
open Set FunctionalInequalities.Probability

/-- New external use: the previously private generic declaration is callable under its existing name. -/
theorem real_convexity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {φ : E → EReal} (hnn : ∀ x, 0 ≤ φ x)
    (hphi : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) :
    ConvexOn ℝ {x | φ x ≠ ⊤} (fun x => (φ x).toReal) :=
  real_convexOn_effective_domain hnn hphi

/-- The point control is available in its module. -/
theorem point_control {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.IsFiniteMeasure μ] (x : E)
    (hx : x ∈ interior (convexHull ℝ μ.support)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : E → EReal,
      (∀ y, 0 ≤ φ y) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
      AEMeasurable (fun y => (φ y).toENNReal) μ →
      (∫⁻ y, (φ y).toENNReal ∂μ) ≠ ⊤ →
      φ x ≤ ((C * (∫⁻ y, (φ y).toENNReal ∂μ).toReal : ℝ) : EReal) :=
  exists_pos_le_mul_lintegral_toReal_of_convex_epigraph μ x hx

end PromotionAPIClient

end PromotionClients

section MassClients

open MeasureTheory FunctionalInequalities.Probability

namespace CEKPointControlClients

private theorem mem_support_dirac (a : ℝ) : a ∈ (Measure.dirac a).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
  norm_num

/-- `0` is interior to the support hull of the endpoint measure, which has no mass in `(-1, 1)`. -/
theorem zero_mem_interior_endpoints :
    (0 : ℝ) ∈ interior (convexHull ℝ (Measure.dirac (-1 : ℝ) + Measure.dirac 1).support) := by
  have hends : ({-1, 1} : Set ℝ) ⊆ (Measure.dirac (-1 : ℝ) + Measure.dirac 1).support := by
    intro x hx
    rw [Measure.support_add]
    rcases hx with rfl | hx
    · exact Set.mem_union_left _ (mem_support_dirac (-1))
    · rw [Set.mem_singleton_iff.mp hx]
      exact Set.mem_union_right _ (mem_support_dirac 1)
  have hsubset := convexHull_mono (𝕜 := ℝ) hends
  rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)] at hsubset
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)) (Set.Ioo_subset_Icc_self.trans hsubset))

/-- Lemma 16 point control at `0` for the mass-two endpoint measure. -/
theorem endpoints_point_control :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : ℝ → EReal,
      (∀ x, 0 ≤ φ x) → Convex ℝ {p : ℝ × ℝ | φ p.1 ≤ (p.2 : EReal)} →
      AEMeasurable (fun x => (φ x).toENNReal) (Measure.dirac (-1 : ℝ) + Measure.dirac 1) →
      (∫⁻ x, (φ x).toENNReal ∂(Measure.dirac (-1 : ℝ) + Measure.dirac 1)) ≠ ⊤ →
        φ 0 ≤ ((C * (∫⁻ x, (φ x).toENNReal ∂(Measure.dirac (-1 : ℝ) + Measure.dirac 1)).toReal : ℝ) : EReal) :=
  exists_pos_le_mul_lintegral_toReal_of_convex_epigraph _ 0 zero_mem_interior_endpoints

/-- The finite-measure halfspace bound (54) for the endpoint measure: `m ≤ 2`, and every open halfspace through `0`
contains one endpoint. -/
theorem endpoints_halfspace :
    ∃ m : ℝ, 0 < m ∧ m ≤ 2 ∧ ∀ u : ℝ, ‖u‖ = 1 →
      m ≤ (Measure.dirac (-1 : ℝ) + Measure.dirac 1).real {x | 0 < inner ℝ u (x - 0)} := by
  obtain ⟨m, hm, hmass, hhalf⟩ :=
    exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure
      (Measure.dirac (-1 : ℝ) + Measure.dirac 1) zero_mem_interior_endpoints
  refine ⟨m, hm, ?_, hhalf⟩
  have htotal : (Measure.dirac (-1 : ℝ) + Measure.dirac 1).real Set.univ = 2 := by
    simp [measureReal_def]
    norm_num
  linarith

/-- Dimension zero with total mass three: the bound holds with `m ≤ 3`, and there is no unit direction. -/
theorem zeroDim_mass_three_halfspace :
    ∃ m : ℝ, 0 < m ∧ m ≤ 3 ∧ ∀ u : EuclideanSpace ℝ (Fin 0), ‖u‖ = 1 →
      m ≤ ((3 : ENNReal) • Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))).real
        {x | 0 < inner ℝ u (x - 0)} := by
  let μ : Measure (EuclideanSpace ℝ (Fin 0)) := (3 : ENNReal) • Measure.dirac 0
  have : IsFiniteMeasure μ := (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))).smul_finite (by norm_num)
  have hsupp : μ.support = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hx : (0 : EuclideanSpace ℝ (Fin 0)) ∈ U := (Subsingleton.elim x 0) ▸ mem_of_mem_nhds hU
    simp [μ, Measure.dirac_apply_of_mem hx]
  have h0 : (0 : EuclideanSpace ℝ (Fin 0)) ∈ interior (convexHull ℝ μ.support) := by simp [hsupp]
  obtain ⟨m, hm, hmass, hhalf⟩ :=
    exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure μ h0
  refine ⟨m, hm, ?_, hhalf⟩
  have htotal : μ.real Set.univ = 3 := by
    simp [μ, measureReal_def]
  linarith

end CEKPointControlClients

end MassClients

#print axioms PromotionAPIClient.real_convexity
#print axioms PromotionAPIClient.point_control
#print axioms CEKPointControlClients.zero_mem_interior_endpoints
#print axioms CEKPointControlClients.endpoints_point_control
#print axioms CEKPointControlClients.endpoints_halfspace
#print axioms CEKPointControlClients.zeroDim_mass_three_halfspace
#print axioms FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top
#print axioms FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support_of_isFiniteMeasure
#print axioms FunctionalInequalities.Probability.real_convexOn_effective_domain
#print axioms FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph
