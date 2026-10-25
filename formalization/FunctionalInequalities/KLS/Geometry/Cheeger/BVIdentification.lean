import FunctionalInequalities.KLS.Geometry.Cheeger.BVConstant
import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.KLS.Geometry.Perimeter.MetricBVMinkowski
import FunctionalInequalities.KLS.Geometry.Perimeter.ConvexSupport
import FunctionalInequalities.KLS.LogConcave.Transport
import FunctionalInequalities.KLS.Geometry.Perimeter.TestClassRelaxation

/-!
# Identification of the metric BV and Minkowski Cheeger constants

For every probability law on a normed group with Borel structure, the symmetric metric BV Cheeger
constant `MetricBV.symmetricConstant` equals the Minkowski Cheeger constant
`Isoperimetry.minkowskiConstant` (`symmetricConstant_eq_minkowskiConstant`), and so does the
half-mass constant (`halfConstant_eq_minkowskiConstant`). Both are infima over the same admissible
family of measurable sets of mass strictly between `0` and `1`; empty families give `⊤` on both
sides. One inequality is termwise (`perimeter ≤ content`); the other bounds the Minkowski infimum
by each BV quotient, which is `⊤` at infinite perimeter and, at finite perimeter, the limit of the
Minkowski quotients of the eventually admissible Minkowski recovery sets. This is an equality of
infima, not of the perimeter and content of individual sets.

For the intrinsic coordinate law of a probability measure on a finite-dimensional inner-product
space, both BV constants equal the isoperimetric constant `Isoperimetry.constant`
(`symmetricConstant_intrinsicMeasure_eq_constant`).

On a real Hilbert space, for a probability law with convex closed support, the half-mass and
symmetric BV constants of the law equal those of its closed-support law
(`halfConstant_closedSupportLaw_eq`, `symmetricConstant_closedSupportLaw_eq`): traces and images
of measurable sets correspond with equal masses and, by `perimeter_eq_closedSupportLaw_of_convex`,
equal perimeters. Consequently, for a finite-dimensional log-concave probability law, the BV
constant `intrinsicHalfConstant` on the closed intrinsic support equals `Isoperimetry.constant`
(`intrinsicHalfConstant_eq_constant`); the underlying structural hypothesis is convexity of the
intrinsic support (`intrinsicHalfConstant_eq_constant_of_convex`).

On the closed intrinsic support of every finite-dimensional probability law, the perimeter of the
closed-support law is the relaxation over globally Lipschitz approximants and, the support being
proper, over locally Lipschitz approximants with global `L¹` convergence
(`lipschitzRelaxation_intrinsicClosedSupportLaw`,
`locallyLipschitzRelaxation_intrinsicClosedSupportLaw`); this test-class identity needs neither
convexity nor log-concavity and is distinct from the identification of the constant with
`Isoperimetry.constant`. The compact-local `L¹` relaxation also equals this perimeter on the
proper closed intrinsic support (`compactLocallyLipschitzRelaxation_intrinsicClosedSupportLaw`).
Nonconvex supports for the constant identification and general metric-measure comparisons
remain outside these results.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace FunctionalInequalities.KLS.MetricBV

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

omit [BorelSpace V] in
/-- An admissible set bounds the Minkowski Cheeger infimum by its Minkowski quotient. -/
theorem minkowskiConstant_le_div (ν : ProbabilityMeasure V) {A : Set V} (hA : MeasurableSet A)
    (h0 : 0 < (ν : Measure V) A) (h1 : (ν : Measure V) A < 1) :
    Isoperimetry.minkowskiConstant ν ≤
      Isoperimetry.minkowskiContent (ν : Measure V) A / min ((ν : Measure V) A) (1 - (ν : Measure V) A) := by
  unfold Isoperimetry.minkowskiConstant
  exact iInf_le_of_le A (iInf_le_of_le hA (iInf_le_of_le h0 (iInf_le _ h1)))

/-- The BV Cheeger constant is at most the Minkowski one: perimeter is at most content. -/
theorem symmetricConstant_le_minkowskiConstant (ν : ProbabilityMeasure V) :
    symmetricConstant ν ≤ Isoperimetry.minkowskiConstant ν := by
  unfold symmetricConstant Isoperimetry.minkowskiConstant
  exact iInf_mono fun B => iInf_mono fun hB => iInf_mono fun _ => iInf_mono fun _ =>
    ENNReal.div_le_div_right (perimeter_le_minkowskiContent (ν : Measure V) hB) _

/-- The Minkowski Cheeger constant is at most the BV one: each admissible BV quotient is either
`⊤` (infinite perimeter, positive finite denominator) or the limit of Minkowski quotients of the
eventually admissible recovery sets. -/
theorem minkowskiConstant_le_symmetricConstant (ν : ProbabilityMeasure V) :
    Isoperimetry.minkowskiConstant ν ≤ symmetricConstant ν := by
  unfold symmetricConstant
  refine le_iInf fun B => le_iInf fun hBm => le_iInf fun h0 => le_iInf fun h1 => ?_
  rcases eq_or_ne (perimeter (ν : Measure V) B) ⊤ with htop | hfin
  · have hmin : min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_right _ _).trans tsub_le_self)
    rw [htop, ENNReal.top_div_of_ne_top hmin]
    exact le_top
  · have hB : perimeter (ν : Measure V) B < ⊤ := lt_top_iff_ne_top.2 hfin
    refine ge_of_tendsto (tendsto_minkowskiContent_div_min_minkowskiRecoverySet ν hBm hB h0 h1) ?_
    filter_upwards [eventually_measure_minkowskiRecoverySet_mem_Ioo ν hBm hB h0 h1] with n hn
    exact minkowskiConstant_le_div ν (measurableSet_minkowskiRecoverySet (ν : Measure V) hB n) hn.1 hn.2

/-- BV--Minkowski Cheeger identification: the symmetric metric BV constant equals the Minkowski
Cheeger constant for every probability law on a normed group. -/
theorem symmetricConstant_eq_minkowskiConstant (ν : ProbabilityMeasure V) :
    symmetricConstant ν = Isoperimetry.minkowskiConstant ν :=
  le_antisymm (symmetricConstant_le_minkowskiConstant ν) (minkowskiConstant_le_symmetricConstant ν)

/-- The half-mass metric BV constant equals the Minkowski Cheeger constant. -/
theorem halfConstant_eq_minkowskiConstant (ν : ProbabilityMeasure V) :
    halfConstant ν = Isoperimetry.minkowskiConstant ν :=
  (halfConstant_eq_symmetricConstant ν).trans (symmetricConstant_eq_minkowskiConstant ν)

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- Frontend form: the symmetric BV constant of the intrinsic coordinate law is the isoperimetric
constant of `def:isoperimetric-cheeger-scale`. -/
theorem symmetricConstant_intrinsicMeasure_eq_constant (μ : ProbabilityMeasure E) :
    symmetricConstant (Probability.intrinsicMeasure μ) = Isoperimetry.constant μ :=
  (symmetricConstant_eq_minkowskiConstant _).trans
    (Isoperimetry.constant_eq_minkowskiConstant_intrinsic μ).symm

/-- Frontend form for the half-mass BV constant of the intrinsic coordinate law. -/
theorem halfConstant_intrinsicMeasure_eq_constant (μ : ProbabilityMeasure E) :
    halfConstant (Probability.intrinsicMeasure μ) = Isoperimetry.constant μ :=
  (halfConstant_eq_symmetricConstant _).trans (symmetricConstant_intrinsicMeasure_eq_constant μ)

end Intrinsic

section ClosedSupport

section MeasurableSpace

variable {X : Type*}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- An admissible set bounds the symmetric BV constant by its quotient. -/
theorem symmetricConstant_le_div
    (ν : ProbabilityMeasure X) {A : Set X} (hA : MeasurableSet A) (h0 : 0 < (ν : Measure X) A)
    (h1 : (ν : Measure X) A < 1) :
    symmetricConstant ν ≤
      perimeter (ν : Measure X) A / min ((ν : Measure X) A) (1 - (ν : Measure X) A) := by
  unfold symmetricConstant
  exact iInf_le_of_le A (iInf_le_of_le hA (iInf_le_of_le h0 (iInf_le _ h1)))

/-- An admissible set bounds the half-mass BV constant by its quotient. -/
theorem halfConstant_le_div
    (ν : ProbabilityMeasure X) {A : Set X} (hA : MeasurableSet A) (h0 : 0 < (ν : Measure X) A)
    (h1 : (ν : Measure X) A ≤ 1 / 2) :
    halfConstant ν ≤ perimeter (ν : Measure X) A / (ν : Measure X) A := by
  unfold halfConstant
  exact iInf_le_of_le A (iInf_le_of_le hA (iInf_le_of_le h0 (iInf_le _ h1)))

end MeasurableSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The image of a measurable subset of the support is measurable, has the same mass, and has
the same perimeter as the subset (its trace is the subset itself). -/
theorem image_closedSupportLaw (ν : ProbabilityMeasure E)
    (hconv : Convex ℝ (ν : Measure E).support) {A : Set (ν : Measure E).support}
    (hA : MeasurableSet A) :
    MeasurableSet (Subtype.val '' A) ∧
      (ν : Measure E) (Subtype.val '' A) =
        (closedSupportLaw ν : Measure (ν : Measure E).support) A ∧
      perimeter (ν : Measure E) (Subtype.val '' A) =
        perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) A := by
  refine ⟨MeasurableSet.subtype_image Measure.isClosed_support.measurableSet hA,
    (closedSupportLaw_apply ν A).symm, ?_⟩
  rw [perimeter_eq_closedSupportLaw_of_convex ν hconv, Subtype.val_injective.preimage_image]

/-- On a convex closed support, the symmetric BV constant of the law equals that of its
closed-support law. -/
theorem symmetricConstant_closedSupportLaw_eq (ν : ProbabilityMeasure E)
    (hconv : Convex ℝ (ν : Measure E).support) :
    symmetricConstant (closedSupportLaw ν) = symmetricConstant ν := by
  apply le_antisymm
  · refine le_iInf fun B => le_iInf fun hB => le_iInf fun h0 => le_iInf fun h1 => ?_
    have hm := closedSupportLaw_preimage ν B
    calc symmetricConstant (closedSupportLaw ν)
        ≤ perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B) /
            min ((closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B))
              (1 - (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B)) :=
          symmetricConstant_le_div _ (measurable_subtype_coe hB) (by rw [hm]; exact h0)
            (by rw [hm]; exact h1)
      _ = perimeter (ν : Measure E) B / min ((ν : Measure E) B) (1 - (ν : Measure E) B) := by
          rw [hm, ← perimeter_eq_closedSupportLaw_of_convex ν hconv B]
  · refine le_iInf fun A => le_iInf fun hA => le_iInf fun h0 => le_iInf fun h1 => ?_
    obtain ⟨hAm, hm, hp⟩ := image_closedSupportLaw ν hconv hA
    calc symmetricConstant ν
        ≤ perimeter (ν : Measure E) (Subtype.val '' A) /
            min ((ν : Measure E) (Subtype.val '' A)) (1 - (ν : Measure E) (Subtype.val '' A)) :=
          symmetricConstant_le_div ν hAm (by rw [hm]; exact h0) (by rw [hm]; exact h1)
      _ = _ := by rw [hm, hp]

/-- On a convex closed support, the half-mass BV constant of the law equals that of its
closed-support law. -/
theorem halfConstant_closedSupportLaw_eq (ν : ProbabilityMeasure E)
    (hconv : Convex ℝ (ν : Measure E).support) :
    halfConstant (closedSupportLaw ν) = halfConstant ν := by
  apply le_antisymm
  · refine le_iInf fun B => le_iInf fun hB => le_iInf fun h0 => le_iInf fun h1 => ?_
    have hm := closedSupportLaw_preimage ν B
    calc halfConstant (closedSupportLaw ν)
        ≤ perimeter (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B) /
            (closedSupportLaw ν : Measure (ν : Measure E).support) (Subtype.val ⁻¹' B) :=
          halfConstant_le_div _ (measurable_subtype_coe hB) (by rw [hm]; exact h0)
            (by rw [hm]; exact h1)
      _ = perimeter (ν : Measure E) B / (ν : Measure E) B := by
          rw [hm, ← perimeter_eq_closedSupportLaw_of_convex ν hconv B]
  · refine le_iInf fun A => le_iInf fun hA => le_iInf fun h0 => le_iInf fun h1 => ?_
    obtain ⟨hAm, hm, hp⟩ := image_closedSupportLaw ν hconv hA
    calc halfConstant ν
        ≤ perimeter (ν : Measure E) (Subtype.val '' A) / (ν : Measure E) (Subtype.val '' A) :=
          halfConstant_le_div ν hAm (by rw [hm]; exact h0) (by rw [hm]; exact h1)
      _ = _ := by rw [hm, hp]

end ClosedSupport

section IntrinsicClosedSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- Structural frontend: if the intrinsic coordinate law has convex closed support, the BV
constant on the closed intrinsic support equals the isoperimetric constant. -/
theorem intrinsicHalfConstant_eq_constant_of_convex (μ : ProbabilityMeasure E)
    (hconv : Convex ℝ (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    intrinsicHalfConstant μ = Isoperimetry.constant μ := by
  unfold intrinsicHalfConstant intrinsicClosedSupportLaw
  rw [halfConstant_closedSupportLaw_eq _ hconv]
  exact halfConstant_intrinsicMeasure_eq_constant μ

/-- Log-concave frontend: for a finite-dimensional log-concave probability law, the metric BV
Cheeger constant on the closed intrinsic support equals the isoperimetric constant. -/
theorem intrinsicHalfConstant_eq_constant (μ : ProbabilityMeasure E) (hμ : LogConcave μ) :
    intrinsicHalfConstant μ = Isoperimetry.constant μ :=
  intrinsicHalfConstant_eq_constant_of_convex μ hμ.intrinsicMeasure.convex_support

/-- The symmetric BV constant on the closed intrinsic support of a finite-dimensional
log-concave probability law equals the isoperimetric constant. -/
theorem symmetricConstant_intrinsicClosedSupportLaw_eq_constant (μ : ProbabilityMeasure E)
    (hμ : LogConcave μ) :
    symmetricConstant (intrinsicClosedSupportLaw μ) = Isoperimetry.constant μ :=
  (intrinsicHalfConstant_eq_symmetricConstant μ).symm.trans (intrinsicHalfConstant_eq_constant μ hμ)

end IntrinsicClosedSupport

section IntrinsicTestClass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- On the closed intrinsic support, the perimeter is the relaxation over globally Lipschitz
approximants; no convexity or log-concavity is used. -/
theorem lipschitzRelaxation_intrinsicClosedSupportLaw (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    lipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B =
      perimeter (intrinsicClosedSupportLaw μ : Measure _) B :=
  lipschitzRelaxation_closedSupportLaw _ B

/-- On the closed intrinsic support, which is proper as a closed subset of the
finite-dimensional direction space, the perimeter is also the relaxation over locally Lipschitz
approximants with global `L¹` convergence; no convexity or log-concavity is used. -/
theorem locallyLipschitzRelaxation_intrinsicClosedSupportLaw (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    locallyLipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B =
      perimeter (intrinsicClosedSupportLaw μ : Measure _) B :=
  locallyLipschitzRelaxation_closedSupportLaw _ B

/-- On the closed intrinsic support, the perimeter is also the relaxation over locally Lipschitz
approximants converging on every compact set; no convexity or log-concavity is used. -/
theorem compactLocallyLipschitzRelaxation_intrinsicClosedSupportLaw (μ : ProbabilityMeasure E)
    (B : Set (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support) :
    compactLocallyLipschitzRelaxation (intrinsicClosedSupportLaw μ : Measure _) B =
      perimeter (intrinsicClosedSupportLaw μ : Measure _) B :=
  compactLocallyLipschitzRelaxation_closedSupportLaw _ B

end IntrinsicTestClass

end FunctionalInequalities.KLS.MetricBV
