import FunctionalInequalities.KLS.LogConcave.Borel
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `thm:compact-borell-logconcavity-equivalence`

Compact-set log-concavity of a Borel probability law on a finite-dimensional real normed space
is equivalent to Bobkov's Borel/inner-measure formulation. Singular laws, null sets, proper
affine supports and the zero space are included. No density, full-dimensional support,
positive-dimension or second-moment hypothesis is added. This is the bridge to the cited
literature formulation, not a Borell density representative and not a KLS bound.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmCompactBorellLogconcavityEquivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The complete compact/Borel equivalence from the Blueprint. -/
theorem certificate (μ : ProbabilityMeasure E) :
    KLS.LogConcave μ ↔ KLS.BorelLogConcave μ :=
  KLS.LogConcave.borel_iff μ

/-- Typed applications cover the exact Euclidean family in Conjecture, including dimension zero. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    KLS.LogConcave μ ↔ KLS.BorelLogConcave μ := certificate μ

example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) :
    KLS.LogConcave μ ↔ KLS.BorelLogConcave μ := certificate μ

/-- The Borel formulation is available as a consequence of the compact-set definition. -/
example (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ) : KLS.BorelLogConcave μ :=
  (certificate μ).1 hμ

end Solutions.ThmCompactBorellLogconcavityEquivalence

/--
info: 'Solutions.ThmCompactBorellLogconcavityEquivalence.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmCompactBorellLogconcavityEquivalence.certificate

/--
info: 'FunctionalInequalities.KLS.LogConcave.borel_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.borel_iff

/--
info: 'FunctionalInequalities.KLS.innerMeasure_eq_of_measurableSet'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.innerMeasure_eq_of_measurableSet

/--
info: 'FunctionalInequalities.KLS.isCompact_combination'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.isCompact_combination
