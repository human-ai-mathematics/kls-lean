import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Lean certificate: `thm:borell-logconcave-density`

The intrinsic law of a compact-set log-concave probability on a finite-dimensional Euclidean
space has, relative to every additive Haar measure on the direction of its affine support, an
upper semicontinuous log-concave Borel density representative; every such representative is
positive and continuous on the interior of the support and has positive two-sided bounds on its
compact subsets; the support is its own closed convex hull; the law has no mass outside the interior of
its support; and it has an exponential moment, hence finite moments of every order. Singular
ambient laws and zero-dimensional affine supports are included. No Poincaré, Cheeger, Dirichlet
or KLS conclusion is packaged here.
-/

noncomputable section

open MeasureTheory FunctionalInequalities

namespace Solutions.ThmBorellLogconcaveDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
/-- The complete Borell representation from the Blueprint, for every Haar reference measure on
the direction of the affine support. -/
theorem certificate (μ : ProbabilityMeasure E) (hμ : KLS.LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure] :
    (∃ ρ : (Probability.affineSupport μ).direction → ℝ,
        KLS.IsBorellDensity (Probability.intrinsicMeasure μ).toMeasure m ρ ∧
        (∀ x ∈ interior (Probability.intrinsicMeasure μ).toMeasure.support, 0 < ρ x) ∧
        ∀ K : Set (Probability.affineSupport μ).direction, IsCompact K →
          K ⊆ interior (Probability.intrinsicMeasure μ).toMeasure.support →
            ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ K, a ≤ ρ x ∧ ρ x ≤ b) ∧
    closure (convexHull ℝ (Probability.intrinsicMeasure μ).toMeasure.support) =
      (Probability.intrinsicMeasure μ).toMeasure.support ∧
    (Probability.intrinsicMeasure μ).toMeasure
      (interior (Probability.intrinsicMeasure μ).toMeasure.support)ᶜ = 0 ∧
    (∃ t : ℝ, 0 < t ∧
      Integrable (fun v ↦ Real.exp (t * ‖v‖)) (Probability.intrinsicMeasure μ).toMeasure) ∧
    ∀ p : ℕ, Integrable (fun v ↦ ‖v‖ ^ p) (Probability.intrinsicMeasure μ).toMeasure := by
  obtain ⟨ρ, hρ⟩ := hμ.exists_isBorellDensity m
  refine ⟨⟨ρ, hρ, fun _ hx ↦ hρ.pos_of_mem_interior_support hx,
    fun _ hK hKΩ ↦ hρ.exists_bounds_of_isCompact hK hKΩ⟩,
    hμ.closure_convexHull_intrinsic_support, hμ.intrinsic_interior_support_compl,
    hμ.intrinsic_integrable_exp_norm, hμ.intrinsic_integrable_norm_pow⟩

/-- Typed applications cover the exact Euclidean family of the KLS statement. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure] :
    ∃ ρ, KLS.IsBorellDensity (Probability.intrinsicMeasure μ).toMeasure m ρ :=
  ((certificate μ hμ m).1).imp fun _ h ↦ h.1

/-- Dimension zero is included: the direction space is trivial and the law is a Dirac mass. -/
example (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0))) (hμ : KLS.LogConcave μ)
    (m : Measure (Probability.affineSupport μ).direction) [m.IsAddHaarMeasure] :
    ∃ ρ, KLS.IsBorellDensity (Probability.intrinsicMeasure μ).toMeasure m ρ :=
  ((certificate μ hμ m).1).imp fun _ h ↦ h.1

/-- The second moment of the intrinsic law, the one used by the KLS statement. -/
example (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hμ : KLS.LogConcave μ) :
    Integrable (fun v ↦ ‖v‖ ^ 2) (Probability.intrinsicMeasure μ).toMeasure :=
  hμ.intrinsic_integrable_norm_pow 2

end Solutions.ThmBorellLogconcaveDensity

/--
info: 'Solutions.ThmBorellLogconcaveDensity.certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmBorellLogconcaveDensity.certificate

/--
info: 'FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity

/--
info: 'FunctionalInequalities.KLS.IsBorellDensity.pos_of_mem_interior_support'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.IsBorellDensity.pos_of_mem_interior_support

/--
info: 'FunctionalInequalities.KLS.IsBorellDensity.continuousOn_interior_support'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.IsBorellDensity.continuousOn_interior_support

/--
info: 'FunctionalInequalities.KLS.IsBorellDensity.exists_bounds_of_isCompact'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.IsBorellDensity.exists_bounds_of_isCompact

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_exp_norm'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_exp_norm

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_norm_pow'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_integrable_norm_pow

/--
info: 'FunctionalInequalities.KLS.LogConcave.closure_convexHull_intrinsic_support'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.closure_convexHull_intrinsic_support

/--
info: 'FunctionalInequalities.KLS.LogConcave.intrinsic_interior_support_compl'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.intrinsic_interior_support_compl

/--
info: 'FunctionalInequalities.KLS.BorelLogConcave.exists_integrable_exp_norm'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.BorelLogConcave.exists_integrable_exp_norm

/--
info: 'FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_interior_support_nonempty'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_interior_support_nonempty
