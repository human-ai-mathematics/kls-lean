module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.InteriorRegularity
public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Inverse
public import FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate
public import FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
public import FunctionalInequalities.Analysis.Semigroup.VonNeumann
public import FunctionalInequalities.Analysis.Semigroup.Resolvent.Form

/-!
# Route statements: the operator route to BKL Theorem 3.1, step 1

This file contains only `#check`s. A proposition that type-checks is not a proof. The anonymous
propositions below are the step-1 obligations of the operator route to Bizeul–Klartag–Lehec
(arXiv:2610.05474v1,
Theorem 3.1). The iterates `h_i` of the source are built in `L²(ν)` from the operator domain of
`A = T̄†T̄ = -ℒ` instead of the class `𝒜`, and the first eigenfunction of (19) is replaced by an
approximate eigenfunction at `λ = 1 / C_P`. These obligations supply, on `D(A)`:

* `O1`: approximate eigenvectors at the bottom `λ` of `A` on `(ker T)ᗮ`, for an abstract closed
  densely defined `T`, with explicit errors;
* `O2`: its heat-model form, `‖A f - C_P⁻¹ f‖ ≤ C_P⁻¹ η` for centered unit `f` and every `η > 0`;
* `O3`: the weak Hessian of `F ∈ D(A)` (the components `∂_i F = ⟪e_i, T̄F⟫` lie in `D(T̄)`),
  its symmetry, and the curvature form of the Bochner identity (16) used in Lemma 3.4;
* `O4`: the tilt identity (48) and `O5`: Lemma 3.6, `T_{d+1}(A F) = S_{d+1} T_d(T̄ F)`, on `D(A)`.

This file does not construct the iterates or state Theorem 3.1 itself. Those contracts are in
`research/audits/BKL/IterateRouteStatements.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

/-! ## Existing proved interfaces -/

#check @FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp
#check @FunctionalInequalities.KLS.LogConcave.adjointComp_toLp_eq
#check @FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_toLp_eq
#check @FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq
#check @FunctionalInequalities.KLS.LogConcave.literatureConstant_le_of_gap
#check @FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_gap_of_literature_le
#check @FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_apply
#check @FunctionalInequalities.Analysis.Semigroup.inner_adjointComp_self
#check @FunctionalInequalities.Analysis.Semigroup.existsUnique_weakResolvent
#check @FunctionalInequalities.Analysis.BakryEmery.integral_hessianSq_add_le_of_hasTemperateGrowth
#check @FunctionalInequalities.Analysis.BakryEmery.taylorTensor_neg_weightedLaplacian
#check @FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le
#check @FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add
#check @FunctionalInequalities.Analysis.BakryEmery.taylorTensor_const_mul

/-! ## `O1`: approximate eigenvectors at the bottom of `T†T` on `(ker T)ᗮ` (abstract)

If `λ ‖y‖² ≤ ‖T y‖²` on `D(T) ∩ (ker T)ᗮ` and a unit `y` there has `‖T y‖² ≤ λ (1 + η)`, then the
solution `z ∈ D(T†T)` of `(T†T + λ) z = 2 λ y` is orthogonal to `ker T`, lies within `√(η / 8)` of
`y`, and satisfies `‖T†T z - λ z‖ ≤ λ √(η / 2)`. -/

#check (∀ {H₀ H₁ : Type} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → Dense (T.domain : Set H₀) →
    ∀ {lam η : ℝ}, 0 < lam → 0 ≤ η →
    (∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      lam * ‖(y : H₀)‖ ^ 2 ≤ ‖T y‖ ^ 2) →
    ∀ y : T.domain, (∀ k : T.domain, T k = 0 → ⟪(y : H₀), (k : H₀)⟫ = 0) →
      ‖(y : H₀)‖ = 1 → ‖T y‖ ^ 2 ≤ lam * (1 + η) →
    ∃ z : (adjointComp T).domain,
      (∀ k : T.domain, T k = 0 → ⟪(z : H₀), (k : H₀)⟫ = 0) ∧
      ‖(y : H₀) - (z : H₀)‖ ≤ Real.sqrt (η / 8) ∧
      ‖adjointComp T z - lam • (z : H₀)‖ ≤ lam * Real.sqrt (η / 2))

/-! ## `O2`: approximate first eigenfunctions in the heat model

For `ν = m.tilted (-U)` with `U ∈ C²` and `0 < C_P(ν) = C < ∞`, every `η > 0` admits a centered
`f ∈ D(A)` with `‖f‖ = 1` and `‖A f - C⁻¹ f‖ ≤ C⁻¹ η`: the replacement for the source's (19). -/

#check (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν = (C : ENNReal) →
    ∀ {η : ℝ}, 0 < η →
    ∃ f : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain,
      L2.mean ν (f : Lp ℝ 2 (ν : Measure V)) = 0 ∧ ‖(f : Lp ℝ 2 (ν : Measure V))‖ = 1 ∧
      ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) f -
          (C : ℝ)⁻¹ • (f : Lp ℝ 2 (ν : Measure V))‖ ≤ (C : ℝ)⁻¹ * η)

/-! ## `O3`: the weak Hessian on `D(A)` and the curvature form of (16)

For `ν = m.tilted (-U)` with `U` of temperate growth, all exponential moments and `∇²U ≥ ρ`, and
`F ∈ D(A)`: each component `∂_i F = ⟪e_i, T̄ F⟫` (standard orthonormal basis) lies in `D(T̄)`; the
weak Hessian `⟪e_j, T̄ ∂_i F⟫` is symmetric in `i, j`; and
`Σ_i ‖T̄ ∂_i F‖² + ρ ‖T̄ F‖² ≤ ‖A F‖²`. -/

#check (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain),
      ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)

#check (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {ρ : ℝ}, (∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      (∀ i j, (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩) =
        (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD j⟩)) ∧
      ∑ i, ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩‖ ^ 2 +
          ρ * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩‖ ^ 2 ≤
        ‖adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F‖ ^ 2)

/-! ## `O4`, `O5`: the tilt identity (48) and Lemma 3.6 on `D(A)`

For `ν = m.tilted (-U)` with `U ∈ C¹` and all exponential moments, and `F ∈ D(A)`:
`F_{A F}(z) = ⟪z, F_{T̄ F}(z)⟫` for every `z`, and `T_{d+1}(A F) = S_{d+1} T_d(T̄ F)` for every `d`
(`A = -ℒ`; the functions are the `L²` classes' representatives). -/

#check (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → ContDiff ℝ 1 U →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (z : V),
      tiltAverage (ν : Measure V)
          (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) z =
        ⟪z, tiltAverage (ν : Measure V)
          (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) z⟫)

#check (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ},
    (ν : Measure V) = m.tilted (-U) → ContDiff ℝ 1 U →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (d : ℕ),
      taylorTensor (ν : Measure V)
          (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F))
          (d + 1) =
        symmetrizeML (appendInner (taylorTensor (ν : Measure V)
          (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) d)))
