import FunctionalInequalities.KLS.Geometry.Cheeger.BVIdentification
import FunctionalInequalities.KLS.LogConcave.Line.Poincare

/-! Independent full-signature clients for the closed-support BV Cheeger constants and the
log-concave intrinsic frontend. Checks: the trace and image correspondences (measurability, mass,
perimeter), equality of the half-mass and symmetric BV constants of a law with convex closed
support and of its closed-support law, the proper convex support of the uniform law on `[0, 1]`
(all constants agree with the Minkowski constant), the singleton support of `dirac 0` (empty
admissible family: all constants `⊤`), and the frontend
`intrinsicHalfConstant μ = Isoperimetry.constant μ` for finite-dimensional log-concave laws,
instantiated for an actual log-concave law (a Dirac law on `ℝ`). Nonconvex supports, the
literature test-class equivalence and general metric-measure comparisons are not claimed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MetricBVIntrinsicIdentificationAudit

open FunctionalInequalities.KLS
open FunctionalInequalities.KLS.MetricBV

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem traceMass (ν : ProbabilityMeasure E) (B : Set E) :
    (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B) =
      (ν : Measure E) B := by
  exact closedSupportLaw_preimage ν B

theorem imageCorrespondence (ν : ProbabilityMeasure E) (hconv : Convex ℝ (ν : Measure E).support)
    {A : Set (ν : Measure E).support} (hA : MeasurableSet A) :
    MeasurableSet (Subtype.val '' A) ∧
      (ν : Measure E) (Subtype.val '' A) =
        (closedSupportLaw ν : Measure (ν : Measure E).support) A ∧
      perimeter (ν : Measure E) (Subtype.val '' A) =
        perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) A := by
  exact image_closedSupportLaw ν hconv hA

theorem symmetricTransfer (ν : ProbabilityMeasure E) (hconv : Convex ℝ (ν : Measure E).support) :
    symmetricConstant (closedSupportLaw ν) = symmetricConstant ν := by
  exact symmetricConstant_closedSupportLaw_eq ν hconv

theorem halfTransfer (ν : ProbabilityMeasure E) (hconv : Convex ℝ (ν : Measure E).support) :
    halfConstant (closedSupportLaw ν) = halfConstant ν := by
  exact halfConstant_closedSupportLaw_eq ν hconv

/-- On a convex closed support, all four BV constants equal the Minkowski constant. -/
theorem allConstants (ν : ProbabilityMeasure E) (hconv : Convex ℝ (ν : Measure E).support) :
    halfConstant (closedSupportLaw ν) = Isoperimetry.minkowskiConstant ν ∧
      symmetricConstant (closedSupportLaw ν) = Isoperimetry.minkowskiConstant ν :=
  ⟨(halfConstant_closedSupportLaw_eq ν hconv).trans (halfConstant_eq_minkowskiConstant ν),
    (symmetricConstant_closedSupportLaw_eq ν hconv).trans
      (symmetricConstant_eq_minkowskiConstant ν)⟩

end Generic

section Frontend

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

theorem frontendOfConvex (μ : ProbabilityMeasure E)
    (hconv : Convex ℝ (FunctionalInequalities.Probability.intrinsicMeasure μ :
      Measure (FunctionalInequalities.Probability.affineSupport μ).direction).support) :
    intrinsicHalfConstant μ = Isoperimetry.constant μ := by
  exact intrinsicHalfConstant_eq_constant_of_convex μ hconv

theorem frontendLogConcave (μ : ProbabilityMeasure E) (hμ : LogConcave μ) :
    intrinsicHalfConstant μ = Isoperimetry.constant μ := by
  exact intrinsicHalfConstant_eq_constant μ hμ

theorem frontendSymmetric (μ : ProbabilityMeasure E) (hμ : LogConcave μ) :
    symmetricConstant (intrinsicClosedSupportLaw μ) = Isoperimetry.constant μ := by
  exact symmetricConstant_intrinsicClosedSupportLaw_eq_constant μ hμ

end Frontend

/-- The uniform law on `[0, 1]`. -/
def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Set.Icc 0 1), ⟨by simp⟩⟩

theorem uniformInterval_support :
    (uniformInterval : Measure ℝ).support = Set.Icc 0 1 := by
  change ((volume : Measure ℝ).restrict (Set.Icc 0 1)).support = Set.Icc 0 1
  refine subset_antisymm
    (Measure.support_subset_of_isClosed isClosed_Icc (ae_restrict_mem measurableSet_Icc)) ?_
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ ((volume : Measure ℝ).restrict (Set.Icc 0 1)).support := by
    have h := Measure.interior_inter_support (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    rwa [interior_Icc, Measure.support_eq_univ, Set.inter_univ] at h
  calc Set.Icc (0 : ℝ) 1 = closure (Set.Ioo 0 1) := (closure_Ioo zero_ne_one).symm
    _ ⊆ _ := closure_minimal hsub Measure.isClosed_support

/-- A proper convex support: the BV constants of the closed-support law on `[0, 1]` equal those
of the law on `ℝ` and the Minkowski constant. -/
theorem uniformIntervalConstants :
    halfConstant (closedSupportLaw uniformInterval) = halfConstant uniformInterval ∧
      symmetricConstant (closedSupportLaw uniformInterval) =
        Isoperimetry.minkowskiConstant uniformInterval := by
  have hconv : Convex ℝ (uniformInterval : Measure ℝ).support := by
    rw [uniformInterval_support]
    exact convex_Icc 0 1
  exact ⟨halfConstant_closedSupportLaw_eq _ hconv, (allConstants _ hconv).2⟩

/-- The Dirac law at `0` on `ℝ`. -/
def diracZero : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

theorem diracZero_support : (diracZero : Measure ℝ).support = {0} := by
  change (Measure.dirac (0 : ℝ)).support = {0}
  refine subset_antisymm (Measure.support_subset_of_isClosed isClosed_singleton ?_) ?_
  · rw [mem_ae_iff, Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl]
    simp
  · rintro x rfl
    refine (Measure.mem_support_iff_forall _).2 fun U hU => ?_
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
    exact zero_lt_one

/-- Singleton support: the admissible families are empty on the one-point support, so the
closed-support constants are `⊤`, and the transfer gives `⊤` for the law on `ℝ` as well. -/
theorem diracConstantsTop :
    symmetricConstant (closedSupportLaw diracZero) = ⊤ ∧ symmetricConstant diracZero = ⊤ ∧
      halfConstant diracZero = ⊤ := by
  have hconv : Convex ℝ (diracZero : Measure ℝ).support := by
    rw [diracZero_support]
    exact convex_singleton 0
  have hS : Subsingleton (diracZero : Measure ℝ).support := by
    rw [diracZero_support]
    infer_instance
  have htop : symmetricConstant (closedSupportLaw diracZero) = ⊤ :=
    symmetricConstant_eq_top_of_subsingleton _
  have h2 : symmetricConstant diracZero = ⊤ :=
    (symmetricConstant_closedSupportLaw_eq _ hconv).symm.trans htop
  exact ⟨htop, h2, (halfConstant_eq_symmetricConstant _).trans h2⟩

/-- The log-concave frontend for an actual log-concave law: a Dirac law on `ℝ`. -/
theorem diracFrontend (a : ℝ) :
    intrinsicHalfConstant (FunctionalInequalities.Probability.ofMeasure (Measure.dirac a)) =
      Isoperimetry.constant (FunctionalInequalities.Probability.ofMeasure (Measure.dirac a)) :=
  intrinsicHalfConstant_eq_constant _ (logConcave_dirac a)

#print axioms traceMass
#print axioms imageCorrespondence
#print axioms symmetricTransfer
#print axioms halfTransfer
#print axioms allConstants
#print axioms frontendOfConvex
#print axioms frontendLogConcave
#print axioms frontendSymmetric
#print axioms uniformInterval_support
#print axioms uniformIntervalConstants
#print axioms diracZero_support
#print axioms diracConstantsTop
#print axioms diracFrontend

end MetricBVIntrinsicIdentificationAudit
