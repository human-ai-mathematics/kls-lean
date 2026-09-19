import FunctionalInequalities.Energy.LocalSlope.Gradient
import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison
import FunctionalInequalities.KLS.LogConcave.AbsoluteContinuity

/-!
# Route statements for the literature-Poincaré clause of `thm:klartag-density-frontend-identification`

**This file contains only `#check`s.  A proposition that type-checks is not a proof.**  It declares
nothing, proves nothing, and introduces no placeholder axiom.  Each proposition below is an
obligation of the route recorded in
`research/decisions/2026-09-19-klartag-literature-poincare-route.md`, and **at the time of this
route snapshot none of `Q0`–`Q3` had been proved**.  No work-in-progress module is imported; there
are none left in the repository.

## The target

`thm:klartag-density-frontend-identification` has three conclusions.  The two isoperimetric ones,
`h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν`, are already Lean-certified through
`lem:relative-perimeter-cheeger-infimum` (`Solutions.LemRelativePerimeterCheegerInfimum.intrinsic`,
the 25th certificate).  The **third clause is not certified**, which is why the node carries no
`\leanok`: that `C_P^lit(μ)` equals the infimum of the finite `C ≥ 0` for which

  `Var_ν(g) ≤ C ∫_V ‖∇g‖² dν`

holds for every locally Lipschitz `g ∈ L²(ν)` with `∫_V ‖∇g‖² dν < ∞`, where `ν` is the intrinsic
law on `V = (affineSupport μ).direction` and `inf ∅ = +∞`.

The content is the **gradient** description of the test energy.  `C_P^lit` is defined in
`def:literature-poincare-constant` through the **local metric slope** `|D f|`
(`Energy.LocalSlope.apply`), not through `‖∇g‖`; the clause asserts that the two descriptions cut
out the same admissible class and the same energy, hence the same optimal constant.  The Buser
half of `thm:logconcave-cheeger-poincare-comparison` is **not** in scope here and stays imported
mathematics.

## The route

This is an assembly round, not a new analytic argument.  All four analytic steps already exist and
are proved in `Energy/LocalSlope/Gradient.lean`, certified under
`thm:smooth-lipschitz-constant-equivalence`:

* `apply_eq_norm_gradient` — pointwise, at any point of differentiability;
* `apply_ae_eq_norm_gradient` — Rademacher plus `ν ≪ m` give the almost-everywhere identity for
  locally Lipschitz tests;
* `energy_eq_lintegral_gradient` — the two extended energies agree, infinite values included;
* `admissible_iff_memLp_gradient` — the existing admissible class is exactly
  `LocallyLipschitz g ∧ MemLp g 2 ν ∧ MemLp (gradient g) 2 ν`.

What is missing is only the transport of these to the optimal constant: the predicate
`Poincare.LocalSlope.Holds` is stated with `Energy.LocalSlope.energy`, so rewriting it in gradient
form (`Q1`) and taking the infimum over valid constants (`Q2`) gives the clause for any
absolutely continuous law; `LogConcave.intrinsic_absolutelyContinuous` supplies the hypothesis for
every finite-dimensional log-concave law, which is `Q0`.

The Haar reference measure follows the established convention of
`Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope`: `m` is an explicit parameter of the theorem carrying
`[m.IsAddHaarMeasure]`, not a field of a definition, so no measure needs to be chosen on the
direction submodule.

## What is already there

`Energy.LocalSlope.energy_eq_lintegral_gradient`, `Energy.LocalSlope.admissible_iff_memLp_gradient`,
`Poincare.LocalSlope.Holds`, `Poincare.LocalSlope.Intrinsic.constant`,
`Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope`, `KLS.LogConcave.intrinsic_absolutelyContinuous`,
`Probability.intrinsicMeasure`, `Probability.affineSupport_intrinsicMeasure`.  Mathlib supplies
`MemLp`, `evariance` and the Rademacher theorem already used by `Gradient.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set FunctionalInequalities
  FunctionalInequalities.KLS
open scoped ENNReal NNReal

/-! ### Proved inputs, for reference -/

#check @FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient
#check @FunctionalInequalities.Energy.LocalSlope.apply_ae_eq_norm_gradient
#check @FunctionalInequalities.Energy.LocalSlope.energy_eq_lintegral_gradient
#check @FunctionalInequalities.Energy.LocalSlope.admissible_iff_memLp_gradient
#check @FunctionalInequalities.Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope
#check @FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous

/-! ### Q1 — the two descriptions of validity agree

For an absolutely continuous law, a finite constant is valid in the local-slope sense exactly when
it is valid in the gradient sense.  Immediate from `energy_eq_lintegral_gradient` and
`admissible_iff_memLp_gradient`; no new analysis. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) (m : Measure V) [Measure.IsAddHaarMeasure m],
    (ν : Measure V) ≪ m → ∀ C : NNReal,
      Poincare.LocalSlope.Holds ν C ↔
        ∀ g : V → ℝ, LocallyLipschitz g → MemLp g 2 (ν : Measure V) →
          MemLp (gradient g) 2 (ν : Measure V) →
          evariance g (ν : Measure V) ≤
            (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2 ∂(ν : Measure V))

/-! ### Q2 — the optimal constant in gradient form, for any absolutely continuous intrinsic law

Taking the infimum over valid finite constants on both sides of `Q1`, applied to the intrinsic
law.  No log-concavity yet. -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) (m : Measure (Probability.affineSupport μ).direction)
    [Measure.IsAddHaarMeasure m],
    (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) ≪ m →
      Poincare.LocalSlope.Intrinsic.constant μ =
        ⨅ C : {C : NNReal //
            ∀ g : (Probability.affineSupport μ).direction → ℝ, LocallyLipschitz g →
              MemLp g 2 (Probability.intrinsicMeasure μ :
                Measure (Probability.affineSupport μ).direction) →
              MemLp (gradient g) 2 (Probability.intrinsicMeasure μ :
                Measure (Probability.affineSupport μ).direction) →
              evariance g (Probability.intrinsicMeasure μ :
                  Measure (Probability.affineSupport μ).direction) ≤
                (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2
                  ∂(Probability.intrinsicMeasure μ :
                    Measure (Probability.affineSupport μ).direction)},
          (C.1 : ENNReal))

/-! ### Q0 — the target: the literature-Poincaré clause for log-concave laws

`Q2` with the absolute continuity every finite-dimensional log-concave law has
(`LogConcave.intrinsic_absolutelyContinuous`).  This is the uncertified clause of
`thm:klartag-density-frontend-identification`; with it the node becomes fully Lean-proved. -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
      Poincare.LocalSlope.Intrinsic.constant μ =
        ⨅ C : {C : NNReal //
            ∀ g : (Probability.affineSupport μ).direction → ℝ, LocallyLipschitz g →
              MemLp g 2 (Probability.intrinsicMeasure μ :
                Measure (Probability.affineSupport μ).direction) →
              MemLp (gradient g) 2 (Probability.intrinsicMeasure μ :
                Measure (Probability.affineSupport μ).direction) →
              evariance g (Probability.intrinsicMeasure μ :
                  Measure (Probability.affineSupport μ).direction) ≤
                (C : ENNReal) * ∫⁻ x, (ENNReal.ofReal ‖gradient g x‖) ^ 2
                  ∂(Probability.intrinsicMeasure μ :
                    Measure (Probability.affineSupport μ).direction)},
          (C.1 : ENNReal))

/-! ### Q3 — origin independence, a bookkeeping obligation

The Blueprint sentence "these quantities do not depend on the affine origin `a`" is about the
statement of the node, not about its analysis: `Probability.intrinsicMeasure` is already defined
without a choice of origin, so this is expected to be discharged by the existing definition rather
than proved.  It is listed so that the implementation round records explicitly which of the two it
turned out to be. -/

#check @FunctionalInequalities.Probability.affineSupport_intrinsicMeasure
