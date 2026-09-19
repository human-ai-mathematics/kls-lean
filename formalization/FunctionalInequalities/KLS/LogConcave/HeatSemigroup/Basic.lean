import FunctionalInequalities.Analysis.Semigroup.Generated.Generator
import FunctionalInequalities.KLS.LogConcave.WeightedGradient
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The heat semigroup of a log-concave law

This module specialises the abstract semigroup construction of `Analysis/Semigroup/` (route
`S1`–`S8`, all proved) to the repository's energy operator. For a full-dimensional compact-set
log-concave probability `ν` on a finite-dimensional Euclidean space `V`, a Haar measure `m` and a
weight `B : V →L[ℝ] V`, the closable weighted gradient
`T = hν.weightedOperator m B hi : L²(ν) →ₗ.[ℝ] L²(ν; V)` (`KLS/LogConcave/WeightedGradient.lean`,
`g ↦ B ∘ ∇g` on Lipschitz tests) has a closure `T̄`, closed and densely defined. Feeding `T̄` to
`Analysis.Semigroup.semigroupCLM` gives

`P_t = heatSemigroup hν m B hi ht : L²(ν) →L[ℝ] L²(ν)`, formally `exp (-t T̄†T̄)`,

and every abstract law transfers by one `exact`: contraction, symmetry, `P_0 = 1`,
`P_{t+u} = P_t P_u`, strong continuity on `[0, ∞)`, and the generator identity
`(P_t f - f)/t → -T̄†T̄ f` on `D(T̄†T̄)`. The bridge to the energy is `inner_adjointComp_self_eq`:
`⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²`, which by `weighted_relaxation_of_mem` is the sequential relaxation of
`‖B ∇g‖²`, the repository's closed energy. The intrinsic version for an arbitrary log-concave law
on any finite-dimensional Euclidean space is `intrinsicHeatSemigroup`.

## What this is not

This closes **gap 1** of the Buser program recorded for
`thm:logconcave-cheeger-poincare-comparison` in `tasks.json` (generation of a symmetric contraction
semigroup from the closed energy form), for the concrete operator. It provides **no** Markov
property (positivity, `P_t 1 = 1`, `L^∞` contraction: gap 2), no Bakry–Émery `Γ`-calculus (gap 3),
no small-time heat estimate (gap 4), and no step of Buser's inequality; the node gains no progress
marker and the constant `π` is not approached. Nothing here uses log-concavity beyond the three
hypothesis lemmas that make the weighted gradient closable and densely defined.
-/

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

open Energy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

section FullDimensional

variable {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)

/-- The closed weighted gradient `T̄`: the closure of `g ↦ B ∘ ∇g` on `L²(ν)`. -/
abbrev closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V) :=
  (hν.weightedOperator m B hi).closure

/-- `T̄` is closed. -/
theorem closedWeightedOperator_isClosed (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    (hν.closedWeightedOperator m B hi).IsClosed :=
  (hν.weightedOperator_isClosable m B hi).closure_isClosed

/-- `T̄` is densely defined: its domain contains the dense domain of `T`. -/
theorem dense_domain_closedWeightedOperator (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Dense ((hν.closedWeightedOperator m B hi).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  (hν.dense_domain_weightedOperator m B hi).mono fun _ hx =>
    (LinearPMap.le_closure (hν.weightedOperator m B hi)).1 hx

/-- **The heat semigroup of `ν`**: `P_t = exp (-t T̄†T̄)` on `L²(ν)`, for `t ≥ 0`, obtained from the
abstract construction `Analysis.Semigroup.semigroupCLM` applied to the closed weighted gradient. -/
def heatSemigroup (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) : Lp ℝ 2 (ν : Measure V) →L[ℝ] Lp ℝ 2 (ν : Measure V) :=
  semigroupCLM (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht

variable (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- `P_t f` is the abstract `semigroupApply` of the closed weighted gradient. -/
theorem heatSemigroup_apply {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    hν.heatSemigroup m B hi ht f =
      semigroupApply (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
        (hν.dense_domain_closedWeightedOperator m B hi) t f := rfl

/-- `P_t` is a contraction of `L²(ν)`. -/
theorem norm_heatSemigroup_apply_le {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (ν : Measure V)) :
    ‖hν.heatSemigroup m B hi ht f‖ ≤ ‖f‖ :=
  norm_semigroupApply_le (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht f

/-- `P_t` is symmetric on `L²(ν)`. -/
theorem inner_heatSemigroup_left {t : ℝ} (ht : 0 ≤ t) (f g : Lp ℝ 2 (ν : Measure V)) :
    ⟪hν.heatSemigroup m B hi ht f, g⟫ = ⟪f, hν.heatSemigroup m B hi ht g⟫ :=
  inner_semigroupApply_left (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht f g

/-- `P_0 = 1`. -/
theorem heatSemigroup_zero_apply (f : Lp ℝ 2 (ν : Measure V)) :
    hν.heatSemigroup m B hi le_rfl f = f :=
  semigroupApply_zero (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f

/-- The semigroup law `P_{t+u} = P_t P_u`. -/
theorem heatSemigroup_add_apply {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (f : Lp ℝ 2 (ν : Measure V)) :
    hν.heatSemigroup m B hi (add_nonneg ht hu) f =
      hν.heatSemigroup m B hi ht (hν.heatSemigroup m B hi hu f) :=
  semigroupApply_add (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) ht hu f

/-- Strong continuity: `t ↦ P_t f` is continuous on `[0, ∞)`, expressed through the underlying
`semigroupApply` (which is defined for every real `t`). -/
theorem continuousOn_heatSemigroup (f : Lp ℝ 2 (ν : Measure V)) :
    ContinuousOn (fun t : ℝ => semigroupApply (hν.closedWeightedOperator m B hi)
      (hν.closedWeightedOperator_isClosed m B hi) (hν.dense_domain_closedWeightedOperator m B hi)
      t f) (Set.Ici 0) :=
  continuousOn_semigroupApply (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f

/-- The generator is `-T̄†T̄`: on `D(T̄†T̄)`, `(P_t f - f)/t → -T̄†T̄ f` as `t ↓ 0`. -/
theorem heatSemigroup_generator (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, ∀ ht : 0 < t, t < δ →
      ‖t⁻¹ • (hν.heatSemigroup m B hi ht.le f - f) +
        adjointComp (hν.closedWeightedOperator m B hi) f‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_norm_inv_smul_semigroupApply_sub_self_add_adjointComp_lt
    (hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f hε
  exact ⟨δ, hδ, fun t ht htδ => h t ht htδ⟩

/-- **The Dirichlet form of the heat semigroup is the closed energy**: for `f ∈ D(T̄†T̄)`,
`⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²`, and by `weighted_relaxation_of_mem` the right-hand side is the sequential
relaxation of `‖B ∇g‖²` at `f`. -/
theorem inner_adjointComp_self_eq (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) :
    ⟪adjointComp (hν.closedWeightedOperator m B hi) f, (f : Lp ℝ 2 (ν : Measure V))⟫ =
      ‖hν.closedWeightedOperator m B hi ⟨f, f.2.2⟩‖ ^ 2 := by
  rw [inner_adjointComp (hν.dense_domain_closedWeightedOperator m B hi) f f.2.2,
    real_inner_self_eq_norm_sq]

end FullDimensional

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : ProbabilityMeasure E} (m : Measure (Probability.affineSupport μ).direction)
  [m.IsAddHaarMeasure] (B : (Probability.affineSupport μ).direction →L[ℝ]
    (Probability.affineSupport μ).direction)

omit [CompleteSpace E] in
/-- The heat semigroup of the intrinsic law of an arbitrary log-concave law, on
`L²(intrinsicMeasure μ)`. Every theorem of the full-dimensional section applies to it verbatim,
since it is `heatSemigroup` of `hμ.intrinsicMeasure`. -/
def intrinsicHeatSemigroup (hμ : LogConcave μ) {t : ℝ} (ht : 0 ≤ t) :
    Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) →L[ℝ]
      Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (Probability.affineSupport μ).direction) :=
  hμ.intrinsicMeasure.heatSemigroup m B hμ.interior_intrinsic_support_nonempty ht

end Intrinsic

end FunctionalInequalities.KLS.LogConcave
