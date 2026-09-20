import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `lem:covariance-core-closure`

For a compact-set log-concave probability law `ν` with nonempty support interior on a
finite-dimensional Euclidean space `V`, every Haar measure `m` and every continuous linear
`B : V →L[ℝ] V` (the Blueprint's `Σ^{1/2}`, with `Σ = B†B`), the operator `g ↦ B ∘ ∇g` on globally
Lipschitz `L²(ν)` tests is densely defined and closable; its closure equals the closure of its
restriction to every core between the smooth compactly supported classes and the full domain, in
particular to `ℝ + C_c^∞(V)`; and the sequential relaxation of `‖B ∇g‖²` equals `‖T̄ f‖²` on the
domain of the closure and `⊤` outside it. Typed applications cover the intrinsic law of every
log-concave law on `EuclideanSpace ℝ (Fin n)`, the zero-dimensional direction space, and the
identification with the affine covariance relaxation of `def:affine-poincare-constant`.
No Poincaré, translation-invariance, whitening or KLS statement is packaged here.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.LemCovarianceCoreClosure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The complete closable-gradient statement of the Blueprint for a full-dimensional log-concave
law: dense domain, closability, core independence of the closure, and the identification of the
sequential relaxation with the squared norm of the closure. -/
theorem certificate (ν : ProbabilityMeasure V) (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) (m : Measure V) [m.IsAddHaarMeasure]
    (B : V →L[ℝ] V) :
    Dense ((hν.weightedOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) ∧
    (hν.weightedOperator m B hi).IsClosable ∧
    (∀ S : Submodule ℝ (Lp ℝ 2 (ν : Measure V)), FunctionalInequalities.Energy.WeightedGradient.smoothCore ν ≤ S →
      S ≤ (hν.weightedOperator m B hi).domain →
      ((hν.weightedOperator m B hi).domRestrict S).closure = (hν.weightedOperator m B hi).closure) ∧
    (∀ f : (hν.weightedOperator m B hi).closure.domain,
      (Energy.PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).sequentialRelaxation f =
        (‖(hν.weightedOperator m B hi).closure f‖₊ ^ 2 : NNReal)) ∧
    (∀ f : Lp ℝ 2 (ν : Measure V), f ∉ (hν.weightedOperator m B hi).closure.domain →
      (Energy.PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).sequentialRelaxation f = ⊤) :=
  ⟨hν.dense_domain_weightedOperator m B hi, hν.weightedOperator_isClosable m B hi,
    fun _ hS hS' ↦ hν.closure_domRestrict_eq_of_smoothCore_le m B hi hS hS',
    fun f ↦ hν.weighted_relaxation_of_mem m B hi f,
    fun _ hf ↦ hν.weighted_relaxation_of_notMem m B hi hf⟩

/-- The intrinsic law of every log-concave law on a Euclidean space of any dimension is
full-dimensional on its direction space, so the certificate applies there. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure]
    (B : (Probability.affineSupport μ).direction →L[ℝ] (Probability.affineSupport μ).direction) :
    (hμ.intrinsicWeightedOperator m B).IsClosable ∧
      Dense ((hμ.intrinsicWeightedOperator m B).domain : Set (Lp ℝ 2
        (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction))) :=
  ⟨(certificate _ hμ.intrinsicMeasure hμ.interior_intrinsic_support_nonempty m B).2.1,
    (certificate _ hμ.intrinsicMeasure hμ.interior_intrinsic_support_nonempty m B).1⟩

/-- Dimension zero: the intrinsic operator vanishes and its domain is all of `L²`. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (hμ : KLS.LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure]
    (B : (Probability.affineSupport μ).direction →L[ℝ] (Probability.affineSupport μ).direction) :
    (∀ f : (hμ.intrinsicWeightedOperator m B).domain, hμ.intrinsicWeightedOperator m B f = 0) ∧
      (hμ.intrinsicWeightedOperator m B).domain = ⊤ :=
  ⟨fun f ↦ FunctionalInequalities.Energy.WeightedGradient.operator_apply_eq_zero_of_subsingleton _ B _ f,
    FunctionalInequalities.Energy.WeightedGradient.domain_operator_eq_top_of_subsingleton _ B _⟩

/-- The affine covariance relaxation of the definition node is the operator relaxation for any
square root `B` of the intrinsic covariance. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure]
    (B : (Probability.affineSupport μ).direction →L[ℝ] (Probability.affineSupport μ).direction)
    (hB : ∀ v, inner ℝ (Covariance.operator
      (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) v) v =
        ‖B v‖ ^ 2) :
    FunctionalInequalities.Energy.CovarianceGradient.Intrinsic.energy μ =
      (Energy.PreEnergy.ofLinearPMap (hμ.intrinsicWeightedOperator m B)).sequentialRelaxation :=
  hμ.intrinsicCovariance_energy_eq_operator m B hB

end Solutions.LemCovarianceCoreClosure

/--
info: 'Solutions.LemCovarianceCoreClosure.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.LemCovarianceCoreClosure.certificate

/--
info: 'FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.exists_mem_of_isClosed_of_frequently_norm_le

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_mem

/--
info: 'FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_notMem'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.PreEnergy.sequentialRelaxation_ofLinearPMap_of_notMem

/--
info: 'FunctionalInequalities.Energy.IsClosable.closure_domRestrict_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.IsClosable.closure_domRestrict_eq

/--
info: 'FunctionalInequalities.Energy.Euclidean.integral_mul_inner_gradient'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.Euclidean.integral_mul_inner_gradient

/--
info: 'FunctionalInequalities.Energy.WeightedGradient.operator_isClosable'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.WeightedGradient.operator_isClosable

/--
info: 'FunctionalInequalities.Energy.WeightedGradient.dense_domain_operator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.WeightedGradient.dense_domain_operator

/--
info: 'FunctionalInequalities.Energy.WeightedGradient.closure_domRestrict_smoothCore'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.WeightedGradient.closure_domRestrict_smoothCore

/--
info: 'FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap

/--
info: 'FunctionalInequalities.KLS.LogConcave.locallyDominates'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.locallyDominates

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_energy_eq_operator'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsicCovariance_energy_eq_operator
