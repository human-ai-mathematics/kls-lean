module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.BakryEmery.TestClass
public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.FormRange

/-!
# The heat-test class for arbitrary positive-time heat data

Let `ν = m.tilted (-U)` be a full-dimensional log-concave probability law with a smooth convex
potential and unit weight. Let `T̄` be the closed gradient, `A = T̄†T̄` and `P_t = exp (-t A)`. For
**arbitrary** `g ∈ L²(ν)`, `r > 0`, nonnegative `φ ∈ C_c^∞(V)` and `s ≥ 0`, put `F = P_r g` and
`ψ = P_s[φ]`. Then both pairings are integrable, and

`0 ≤ -(1/2) ∫ (Aψ) Γ(T̄F, T̄F) dν + ∫ ψ Γ(T̄F, T̄(AF)) dν`

(`integral_weakGamma_operator_nonneg`), with `Γ` the weak carré du champ of `L²` fields.

The proof applies the conditional two-field transfer
`integral_weakGamma_nonneg_of_mem_domain_of_tendsto` of `TestClass.lean`. Its two convergence
obligations are supplied by the two-field smooth core `exists_seq_smooth_tendsto_two_fields`
(`HeatSemigroup/Generator/FormRange.lean`), which rests on the finite-wave-splitting density of
`(I + A) C_c^∞` in the form domain. `F ∈ D(A)` and `AF ∈ D(T̄)` hold by positive-time
regularization. The bounds of
`ψ` and `Aψ` come from the Markov contraction of smooth data. The statement carries no wave,
core, residual, sequence or regularity premise.

No time interpolation `s ↦ ∫ (P_s φ) Γ(T̄(P_{t-s} f)) dν`, no gradient estimate and no Buser
or KLS statement is made.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff

namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup

open Energy Energy.WeightedGradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure]
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **The heat-test frontend for arbitrary heat data.** For `ν = m.tilted (-U)` with a smooth
convex potential, arbitrary `g ∈ L²(ν)`, `r > 0`, nonnegative `φ ∈ C_c^∞(V)` and `s ≥ 0`, with
`F = P_r g` and `ψ = P_s[φ]`: the pairings `(Aψ) Γ(T̄F, T̄F)` and `ψ Γ(T̄F, T̄(AF))` are
integrable and `0 ≤ -(1/2) ∫ (Aψ) Γ(T̄F, T̄F) dν + ∫ ψ Γ(T̄F, T̄(AF)) dν`. -/
theorem integral_weakGamma_operator_nonneg (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) (hconv : ConvexOn ℝ Set.univ U) (g : Lp ℝ 2 (ν : Measure V)) {r : ℝ}
    (hr : 0 < r) {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {s : ℝ} (hs : 0 ≤ s) :
    Integrable
        (fun x =>
          (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
                ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hs
                    ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
                  preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
                    ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hφ hφc⟩
                    hs⟩)
              x *
            WeakGamma.apply
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨_,
                  mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi
                    g hr⟩)
              (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                ⟨_,
                  mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi
                    g hr⟩)
              x)
        (ν : Measure V) ∧
      Integrable
          (fun x =>
            operator m (ContinuousLinearMap.id ℝ V) hν hi hs
                ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
              WeakGamma.apply
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                  ⟨_,
                    mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν
                      hi g hr⟩)
                (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                  ⟨adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
                      ⟨_,
                        mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                          hr⟩,
                    mem_closedWeightedOperator_domain_adjointComp_of_pos m
                      (ContinuousLinearMap.id ℝ V) hν hi g hr _⟩)
                x)
          (ν : Measure V) ∧
        0 ≤
          -(∫ x,
                  (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
                        ⟨operator m (ContinuousLinearMap.id ℝ V) hν hi hs
                            ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ),
                          preserves_domain m (ContinuousLinearMap.id ℝ V) hν hi
                            ⟨_,
                              hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hφ
                                hφc⟩
                            hs⟩)
                      x *
                    WeakGamma.apply
                      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                        ⟨_,
                          mem_closedWeightedOperator_domain_of_pos m
                            (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
                      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                        ⟨_,
                          mem_closedWeightedOperator_domain_of_pos m
                            (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
                      x ∂(ν : Measure V)) /
              2 +
            ∫ x,
              operator m (ContinuousLinearMap.id ℝ V) hν hi hs
                  ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x *
                WeakGamma.apply
                  (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                    ⟨_,
                      mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν
                        hi g hr⟩)
                  (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
                    ⟨adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
                        ⟨_,
                          mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g
                            hr⟩,
                      mem_closedWeightedOperator_domain_adjointComp_of_pos m
                        (ContinuousLinearMap.id ℝ V) hν hi g hr _⟩)
                  x ∂(ν : Measure V) := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by decide)
  obtain ⟨hint₁, -⟩ :=
    integrable_operator_toLp_weakGamma m hν hi hνU hU1 hφ hφc hs
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩,
          mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V) hν
            hi g hr _⟩)
  obtain ⟨-, hint₂⟩ :=
    integrable_operator_toLp_weakGamma m hν hi hνU hU1 hφ hφc hs
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, mem_closedWeightedOperator_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩)
  refine ⟨hint₂, hint₁, ?_⟩
  obtain ⟨C, D, hC, hD, hb⟩ := exists_bounds_operator_toLp m hν hi hνU hU1 hφ hφc
  obtain ⟨q, hq, hqc, -, c₂, -, c₄⟩ :=
    hν.exists_seq_smooth_tendsto_two_fields hνU hU
      ⟨_, mem_adjointComp_domain_of_pos m (ContinuousLinearMap.id ℝ V) hν hi g hr⟩
      (mem_closedWeightedOperator_domain_adjointComp_of_pos m (ContinuousLinearMap.id ℝ V) hν hi
        g hr _)
  have hψ :
    ∀ᵐ x ∂(ν : Measure V),
      0 ≤
        operator m (ContinuousLinearMap.id ℝ V) hν hi hs
          ((memLp_of_contDiff_hasCompactSupport ν hφ hφc).toLp φ) x := by
    apply ae_nonneg_operator m (ContinuousLinearMap.id ℝ V) hν hi hs
    filter_upwards [(memLp_of_contDiff_hasCompactSupport ν hφ hφc).coeFn_toLp] with x hx
    rw [hx]
    exact hφ0 x
  refine
    integral_weakGamma_nonneg_of_mem_domain_of_tendsto m hν hi hνU hU hconv _ hψ hC hD
      (hb s hs).1 (hb s hs).2 hq hqc
      (fun n =>
        (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) (hq n) (hqc n)).coeFn_toLp)
      (fun n => ?_) (tendsto_iff_norm_sub_tendsto_zero.mp c₂)
      (tendsto_iff_norm_sub_tendsto_zero.mp c₄)
  filter_upwards [(memLp_gradient_of_contDiff_hasCompactSupport (ν := ν)
        (contDiff_weightedLaplacian hU (hq n) (by decide) (by decide)).neg
        (hasCompactSupport_weightedLaplacian U (hqc n)).neg).coeFn_toLp] with
    x hx
  rw [hx, gradient_neg]

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
