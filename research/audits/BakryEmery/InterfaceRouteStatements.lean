module

public import FunctionalInequalities.KLS.LogConcave.Poincare
public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov
public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.Basic
public import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Energy
public import FunctionalInequalities.Analysis.BakryEmery.Calculus
public import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
public import FunctionalInequalities.Analysis.BakryEmery.Gamma
public import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
public import FunctionalInequalities.Analysis.Semigroup.AdjointClosure
public import FunctionalInequalities.Energy.Cheeger.Identification
public import FunctionalInequalities.Poincare.LocalSlope.Gradient
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Route statements: generator identification and the Bakry--Émery interface

This file contains only `#check`s.  A proposition that type-checks is not a proof.  The anonymous
propositions below are the obligations for the smooth-potential starting point of the
Bakry–Émery route; no axiom, theorem, definition, or placeholder proof is introduced here.

The current semigroup acts on `L²(μ)`.  In particular, none of the statements below asserts an
independent semigroup on all of `L¹`, and a classical gradient is used only for explicitly smooth
functions.  The fixed `stdOrthonormalBasis` in `B3` makes the Hilbert--Schmidt square typeable with
the current API; basis independence is a separate obligation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

/-! ## Existing proved interfaces -/

#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator
#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.generator_limit
#check @FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq
#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.positive
#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.one
#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.subMarkov
#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.integral
#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.abs_le
#check @FunctionalInequalities.KLS.LogConcave.HeatSemigroup.abs_le_const
#check @FunctionalInequalities.KLS.LogConcave.weighted_relaxation_of_mem
#check @FunctionalInequalities.KLS.LogConcave.exists_smoothGradient_localDensity
#check @FunctionalInequalities.KLS.LogConcave.weightedRelaxation_id_eq_smoothGradient
#check @FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_energy_eq_smoothGradient
#check @FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_energy_eq_two_mul_cheeger
#check @FunctionalInequalities.KLS.LogConcave.closure_domRestrict_eq_of_smoothCore_le
#check @FunctionalInequalities.Energy.WeightedGradient.apply_id
#check @FunctionalInequalities.Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport
#check @FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_two_mul_cheeger
#check @FunctionalInequalities.Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger
#check @FunctionalInequalities.Poincare.LocalSlope.holds_iff_memLp_gradient
#check @FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant_eq_iInf_gradient_of_logConcave
#check @FunctionalInequalities.Analysis.Semigroup.adjointComp_apply
#check @FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm
#check @FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian
#check @FunctionalInequalities.Analysis.BakryEmery.integral_mul_inner_gradient_eq_neg
#check @FunctionalInequalities.Analysis.BakryEmery.integral_inner_gradient_tilted
#check @FunctionalInequalities.Analysis.BakryEmery.memLp_weightedLaplacian
#check @FunctionalInequalities.Analysis.Semigroup.inner_eq_inner_closure_apply
#check @FunctionalInequalities.Analysis.Semigroup.adjoint_closure_apply_eq_of_forall
#check @FunctionalInequalities.KLS.LogConcave.integral_inner_gradient_eq
#check @FunctionalInequalities.KLS.LogConcave.integral_weightedLaplacian_eq_zero
#check @FunctionalInequalities.KLS.LogConcave.memLp_neg_weightedLaplacian
#check @FunctionalInequalities.KLS.LogConcave.inner_toLp_neg_weightedLaplacian_eq
#check @FunctionalInequalities.KLS.LogConcave.toLp_mem_adjointComp_domain
#check @FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_eq
#check @FunctionalInequalities.Analysis.BakryEmery.gamma
#check @FunctionalInequalities.Analysis.BakryEmery.gamma_self
#check @FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_mul
#check @FunctionalInequalities.Analysis.BakryEmery.gamma_eq_weightedLaplacian
#check @FunctionalInequalities.Analysis.BakryEmery.gammaTwo
#check @FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_expanded
#check @FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn
#check @FunctionalInequalities.Analysis.BakryEmery.fderiv_apply_comm
#check @FunctionalInequalities.Analysis.BakryEmery.fderiv_fderiv_fderiv_apply_comm
#check @FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis
#check @FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add
#check @FunctionalInequalities.Analysis.BakryEmery.bochner_stdBasis
#check @FunctionalInequalities.Analysis.BakryEmery.gammaTwo_nonneg
#check @FunctionalInequalities.Analysis.BakryEmery.bochner_nonneg_stdBasis
#check @InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
#check @integral_bilinear_fderiv_right_eq_neg_left_of_integrable
#check @MeasureTheory.isProbabilityMeasure_tilted

/-! ## N0 -- normalized smooth convex-potential model

The potential is named `U` to avoid collision with the ambient type `E`.  Integrability is explicit:
convexity alone does not normalize `exp (-U)`.  The desired package includes the actual tilted
probability, log-concavity, and full support; none of these is inferred merely from a name.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (m : Measure E) [m.IsAddHaarMeasure] (U : E → ℝ),
    ContDiff ℝ ∞ U → ConvexOn ℝ Set.univ U →
    Integrable (fun x => Real.exp (-U x)) m →
    0 < ∫ x, Real.exp (-U x) ∂m ∧
      ∃ μ : ProbabilityMeasure E,
        (μ : Measure E) = m.tilted (-U) ∧
        KLS.LogConcave μ ∧ (μ : Measure E).support = Set.univ)

/-! ## G0 -- weighted integration by parts on compactly supported smooth tests

This is the weak identity that must feed the adjoint definition.  A pointwise computation of the
differential expression alone is not enough for `D(T* T)`.

This exact proposition is discharged by
`Analysis.BakryEmery.integral_inner_gradient_tilted` (Haar form
`Analysis.BakryEmery.integral_mul_inner_gradient_eq_neg`; probability form
`KLS.LogConcave.integral_inner_gradient_eq`), with `C¹` potential, `C²` test `f` and `C¹` test
`g` without compact support; see `research/audits/BakryEmery/GeneratorIdentificationAudit.lean`
(`route_G0`).
The anonymous form is retained as a signature audit.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (m : Measure E) [m.IsAddHaarMeasure] (U f g : E → ℝ) (μ : ProbabilityMeasure E),
    (μ : Measure E) = m.tilted (-U) → ContDiff ℝ ∞ U →
    ContDiff ℝ ∞ f → HasCompactSupport f →
    ContDiff ℝ ∞ g → HasCompactSupport g →
    (∫ x, inner ℝ (gradient f x) (gradient g x) ∂(μ : Measure E)) =
      ∫ x, (-(Laplacian.laplacian f x - inner ℝ (gradient U x) (gradient f x))) * g x
        ∂(μ : Measure E))

/-! ## G1 -- identify `A = T* T` with `-ℒ` on `C_c^∞`

The existential `hLf` records the required `L²(μ)` membership of the differential expression.
The conclusion is only test-function inclusion and equality; it does not call `C_c^∞` an operator
core and does not assert equality of the full closed operators.

This exact proposition is discharged by `KLS.LogConcave.memLp_neg_weightedLaplacian`,
`KLS.LogConcave.toLp_mem_adjointComp_domain` and `KLS.LogConcave.adjointComp_toLp_eq`
(`KLS/LogConcave/HeatSemigroup/Generator/Basic.lean`), through the weak identity
`KLS.LogConcave.inner_toLp_neg_weightedLaplacian_eq` on all of `D(T̄)` and the closure lemma
`Analysis.Semigroup.inner_eq_inner_closure_apply`; see
`research/audits/BakryEmery/GeneratorIdentificationAudit.lean` (`route_G1`).  The four layers above
are still
distinct: only the first is proved.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure] (U : E → ℝ)
    (hμ : KLS.LogConcave μ) (hi : (interior (μ : Measure E).support).Nonempty),
    (μ : Measure E) = m.tilted (-U) → ContDiff ℝ ∞ U →
    ∀ (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
      ∃ hLf : MemLp
          (fun x => -(Laplacian.laplacian f x - inner ℝ (gradient U x) (gradient f x)))
          2 (μ : Measure E),
        ∃ hfA :
            (Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport μ hf hfc).toLp f ∈
              (adjointComp (hμ.closedWeightedOperator m (ContinuousLinearMap.id ℝ E) hi)).domain,
          adjointComp (hμ.closedWeightedOperator m (ContinuousLinearMap.id ℝ E) hi)
              ⟨(Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport μ hf hfc).toLp f,
                hfA⟩ =
            hLf.toLp
              (fun x => -(Laplacian.laplacian f x -
                inner ℝ (gradient U x) (gradient f x))))

/-! ## B0 -- the carré-du-champ product identity for the diffusion sign convention

This exact proposition is discharged by `Analysis.BakryEmery.gamma_eq_weightedLaplacian`
(`Analysis/BakryEmery/Gamma.lean`), with `Γ(f, g) = ⟪∇f, ∇g⟫` defined geometrically
(`Analysis.BakryEmery.gamma`) and no regularity assumed on `U`; see
`research/audits/BakryEmery/BochnerAudit.lean` (`route_B0`).  The anonymous form is retained as a
signature audit.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U f g : E → ℝ),
    ContDiff ℝ 2 U → ContDiff ℝ 2 f → ContDiff ℝ 2 g → ∀ x,
      ((Laplacian.laplacian (fun y => f y * g y) x -
          inner ℝ (gradient U x) (gradient (fun y => f y * g y) x)) -
        f x * (Laplacian.laplacian g x - inner ℝ (gradient U x) (gradient g x)) -
        g x * (Laplacian.laplacian f x - inner ℝ (gradient U x) (gradient f x))) / 2 =
      inner ℝ (gradient f x) (gradient g x))

/-! ## B1 -- convexity gives a positive-semidefinite Hessian

This exact proposition is discharged by
`Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn`
(`Analysis/BakryEmery/Bochner/Basic.lean`),
through the line restriction `t ↦ U (x + t v)`, `ConvexOn.monotoneOn_deriv` and
`Monotone.deriv_nonneg`; see `research/audits/BakryEmery/BochnerAudit.lean` (`route_B1`).
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U : E → ℝ),
    ContDiff ℝ 2 U → ConvexOn ℝ Set.univ U → ∀ x v,
      0 ≤ bilinearIteratedFDerivTwo ℝ U x v v)

/-! ## B2 -- symmetry of the Hessian / mixed derivatives

This proposition is discharged by `Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm`; the
anonymous form is retained to audit the exact intended signature.  It is restated as `route_B2` in
`research/audits/BakryEmery/BochnerAudit.lean`; its directional form is
`Analysis.BakryEmery.fderiv_apply_comm`.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (f : E → ℝ),
    ContDiff ℝ 2 f → ∀ x v w,
      bilinearIteratedFDerivTwo ℝ f x v w =
        bilinearIteratedFDerivTwo ℝ f x w v)

/-! ## B3 -- coordinate form of the Bochner identity

The first double sum is the Hilbert--Schmidt square in the fixed standard orthonormal basis.
This contract uses the coordinate expression and does not assert basis independence.

This exact proposition is discharged by `Analysis.BakryEmery.bochner_stdBasis`
(`Analysis/BakryEmery/Bochner/Basic.lean`; `Γ₂` form
`Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add`,
which needs only `C²` for `U`), with the double sum named `Analysis.BakryEmery.hessianSqStdBasis`
and **expressed in the standard basis**; see `research/audits/BakryEmery/BochnerAudit.lean`
(`route_B3`).  The third-order terms cancel through
`Analysis.BakryEmery.fderiv_fderiv_fderiv_apply_comm`; no basis independence is claimed.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U f : E → ℝ),
    ContDiff ℝ 3 U → ContDiff ℝ 3 f → ∀ x,
      (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
          inner ℝ (gradient U x) (gradient (fun y => ‖gradient f y‖ ^ 2) x)) / 2 -
        inner ℝ (gradient f x)
          (gradient (fun y => Laplacian.laplacian f y -
            inner ℝ (gradient U y) (gradient f y)) x) =
      (∑ i, ∑ j,
          (bilinearIteratedFDerivTwo ℝ f x
            (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2) +
        bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x))

/-! ## B4 -- the local `Γ₂ ≥ 0` consequence

This exact proposition is discharged by `Analysis.BakryEmery.bochner_nonneg_stdBasis`
(`Γ₂` form `Analysis.BakryEmery.gammaTwo_nonneg`), from `B3`, `B1` and the nonnegativity of the
Hessian square; see `research/audits/BakryEmery/BochnerAudit.lean` (`route_B4`).  It is a pointwise
statement: no semigroup estimate follows from it without the `S0` interfaces below.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U f : E → ℝ),
    ContDiff ℝ 3 U → ConvexOn ℝ Set.univ U → ContDiff ℝ 3 f → ∀ x,
      0 ≤
        (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
            inner ℝ (gradient U x) (gradient (fun y => ‖gradient f y‖ ^ 2) x)) / 2 -
          inner ℝ (gradient f x)
            (gradient (fun y => Laplacian.laplacian f y -
              inner ℝ (gradient U y) (gradient f y)) x))

/-! ## S0 -- square and `L¹` gradient interchange are distinct obligations

These are stated for smooth compactly supported input and require a classical representative `u`
of the `L²` class `P_t[f]`.  The existence and regularity of that representative are deliberately
part of the conclusion instead of silently taking `gradient` of an arbitrary `L²` representative.
-/

#check
  (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure] (U : E → ℝ)
    (hμ : KLS.LogConcave μ) (hi : (interior (μ : Measure E).support).Nonempty),
    (μ : Measure E) = m.tilted (-U) →
      ContDiff ℝ ∞ U →
        ConvexOn ℝ Set.univ U →
          ∀ (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (t : ℝ) (ht : 0 < t),
            ∃ (u : E → ℝ) (hu : MemLp u 2 (μ : Measure E)),
              FunctionalInequalities.KLS.LogConcave.HeatSemigroup.operator m
                    (ContinuousLinearMap.id ℝ E) hμ hi ht.le
                    ((Energy.WeightedGradient.memLp_of_contDiff_hasCompactSupport μ hf hfc).toLp
                      f) =
                  hu.toLp u ∧
                ContDiff ℝ ∞ u)

/-! The actual semigroup gradient estimates are recorded only after explicitly binding a
representative and every `L²` proof needed to feed the current `L²` semigroup. -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {μ : ProbabilityMeasure E}
    (P : Lp ℝ 2 (μ : Measure E) →L[ℝ] Lp ℝ 2 (μ : Measure E))
    (f u : E → ℝ) (hf : MemLp f 2 (μ : Measure E)) (hu : MemLp u 2 (μ : Measure E))
    (hgradSq : MemLp (fun y => ‖gradient f y‖ ^ 2) 2 (μ : Measure E)),
    P (hf.toLp f) = hu.toLp u →
      (∀ᵐ x ∂(μ : Measure E), ‖gradient u x‖ ^ 2 ≤
        P (hgradSq.toLp (fun y => ‖gradient f y‖ ^ 2)) x))

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] {μ : ProbabilityMeasure E}
    (P : Lp ℝ 2 (μ : Measure E) →L[ℝ] Lp ℝ 2 (μ : Measure E))
    (f u : E → ℝ) (hf : MemLp f 2 (μ : Measure E)) (hu : MemLp u 2 (μ : Measure E))
    (hgrad : MemLp (fun y => ‖gradient f y‖) 2 (μ : Measure E)),
    P (hf.toLp f) = hu.toLp u →
      (∀ᵐ x ∂(μ : Measure E), ‖gradient u x‖ ≤
        P (hgrad.toLp (fun y => ‖gradient f y‖)) x))

/-! ## E0 -- the identity-weight bridge to the canonical energy

This exact proposition is discharged by
`KLS.LogConcave.closedWeightedOperator_id_energy_eq_smoothGradient`.  It remains below as an
anonymous signature audit, not as an additional declaration.
-/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    (hμ : KLS.LogConcave μ) (hi : (interior (μ : Measure E).support).Nonempty),
    Energy.PreEnergy.normSqEnergy
        (hμ.closedWeightedOperator m (ContinuousLinearMap.id ℝ E) hi) =
      Energy.SmoothGradient.relaxation μ)
