module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology
namespace LetwinDomainMAImageAudit
open FunctionalInequalities.Analysis
private def v (x : ℝ) : ℝ := if x ∈ Ioo (-2 : ℝ) 2 then |x| else 0
private lemma cv : ConvexOn ℝ (Ioo (-2 : ℝ) 2) v := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a * x + b * y ∈ Ioo (-2 : ℝ) 2 := by
    simpa only [smul_eq_mul] using (convex_Ioo (-2 : ℝ) 2) hx hy ha hb hab
  have h := abs_add_le (a * x) (b * y)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at h
  simpa [v, hx, hy, hz, smul_eq_mul] using h
private lemma ct : ContinuousOn v (Ioo (-2 : ℝ) 2) := by
  apply continuous_abs.continuousOn.congr
  intro x hx
  simp [v, hx]

theorem actual_piecewise_abs_open :
    MeasurableSet (subgradientImageOn v (Ioo (-2 : ℝ) 2) (Ioo (-1 : ℝ) 1)) ∧
      let G : Bool → Set ℝ := fun b => if b then Ioo 0 1 else Ioo (-1) 0
      (volume : Measure ℝ) (subgradientImageOn v (Ioo (-2 : ℝ) 2) (⋃ b, G b)) =
        ∑' b, (volume : Measure ℝ) (subgradientImageOn v (Ioo (-2 : ℝ) 2) (G b)) := by
  constructor
  · apply measurableSet_subgradientImageOn_of_isOpen isOpen_Ioo cv ct isOpen_Ioo
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · dsimp only
    apply volume_subgradientImageOn_iUnion_of_pairwise_disjoint_open isOpen_Ioo cv ct
    · intro b
      cases b <;> exact isOpen_Ioo
    · intro b x hx
      cases b <;> constructor <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx <;>
        linarith [hx.1, hx.2]
    · have hsep : Disjoint (Ioo (-1 : ℝ) 0) (Ioo 0 1) := by
        apply Set.disjoint_left.mpr
        intro x hx hy
        exact lt_asymm hx.2 hy.1
      intro i j hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact hsep
      · exact hsep.symm
      · exact (hij rfl).elim

theorem actual_zero_dimensional_open :
    MeasurableSet (subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ))
      Set.univ Set.univ) := by
  exact measurableSet_subgradientImageOn_of_isOpen isOpen_univ
    (convexOn_const 0 convex_univ) continuous_const.continuousOn isOpen_univ (subset_refl _)

theorem actual_piecewise_abs_compact :
    IsCompact (subgradientImageOn v (Ioo (-2 : ℝ) 2) (Icc (-1 : ℝ) 1)) := by
  apply isCompact_subgradientImageOn_of_isCompact isOpen_Ioo cv ct isCompact_Icc
  intro x hx
  constructor <;> linarith [hx.1, hx.2]

theorem actual_zero_dimensional_compact :
    IsCompact (subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ))
      Set.univ ({0} : Set (EuclideanSpace ℝ (Fin 0)))) := by
  exact isCompact_subgradientImageOn_of_isCompact isOpen_univ
    (convexOn_const 0 convex_univ) continuous_const.continuousOn
    isCompact_singleton (subset_univ _)

theorem actual_piecewise_abs_analytic :
    AnalyticSet (subgradientImageOn v (Ioo (-2 : ℝ) 2) (Ioo (-1 : ℝ) 1 \ {0})) := by
  apply
    analyticSet_subgradientImageOn isOpen_Ioo ct
      (isOpen_Ioo.measurableSet.diff (measurableSet_singleton 0))
  intro x hx
  constructor <;> linarith [hx.1.1, hx.1.2]

theorem actual_zero_dimensional_analytic :
    AnalyticSet (subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ))
      Set.univ ({0} : Set (EuclideanSpace ℝ (Fin 0)))) := by
  exact analyticSet_subgradientImageOn isOpen_univ continuous_const.continuousOn
    (measurableSet_singleton 0) (subset_univ _)

theorem generic_constant_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {D K : Set E} : IsClosed {q : K × E | ∀ y ∈ D, (0 : ℝ) + ⟪q.2, y - q.1.val⟫ ≤ 0} := by
  exact isClosed_subgradient_graphOn continuousOn_const

end LetwinDomainMAImageAudit
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.isClosed_subgradient_graphOn
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.isCompact_subgradientImageOn_of_isCompact
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.analyticSet_subgradientImageOn
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.measurableSet_subgradientImageOn_of_isOpen
set_option pp.fullNames true in
#print axioms
  FunctionalInequalities.Analysis.volume_subgradientImageOn_iUnion_of_pairwise_disjoint_open
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_piecewise_abs_open
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_zero_dimensional_open
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_piecewise_abs_compact
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_zero_dimensional_compact
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_piecewise_abs_analytic
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_zero_dimensional_analytic
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.generic_constant_graph

namespace LetwinDomainMAImageAudit
open FunctionalInequalities.Analysis

theorem actual_piecewise_abs_borel_null :
    NullMeasurableSet (subgradientImageOn v (Ioo (-2 : ℝ) 2) (Icc (-1 / 2 : ℝ) (1 / 2)))
      volume := by
  apply nullMeasurableSet_subgradientImageOn_of_measurableSet isOpen_Ioo cv ct measurableSet_Icc
  intro x hx
  constructor <;> linarith [hx.1, hx.2]

theorem actual_zero_dimensional_borel_null :
    NullMeasurableSet (subgradientImageOn
      (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) univ
      ({0} : Set (EuclideanSpace ℝ (Fin 0)))) volume := by
  exact nullMeasurableSet_subgradientImageOn_of_measurableSet isOpen_univ
    (convexOn_const 0 convex_univ) continuous_const.continuousOn
    (measurableSet_singleton 0) (subset_univ _)
end LetwinDomainMAImageAudit
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_piecewise_abs_borel_null
set_option pp.fullNames true in
#print axioms LetwinDomainMAImageAudit.actual_zero_dimensional_borel_null
