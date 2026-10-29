import FunctionalInequalities.Analysis.Semigroup.Generated.Laws
import FunctionalInequalities.Energy.Form.Dirichlet
import FunctionalInequalities.Energy.Relaxation.LinearPMap
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic

/-!
# Route statements: Markov property of the log-concave heat semigroup

**This file contains only `#check`s. A proposition that type-checks is not a proof.** It declares
nothing, proves nothing, and introduces no placeholder axiom. Each proposition below is an
obligation of the Markov-property step of `thm:logconcave-cheeger-poincare-comparison`;
`research/audits/HeatSemigroup/MarkovAudit.lean` restates and discharges `M1`--`M7`.

The route is Beurling--Deny through the resolvent. First mollify every normal contraction on the
real line and use the sequential relaxation to prove that the closed weighted-gradient energy is
Markovian (`M1`). The weak resolvent equation then identifies `J_s f` as the unique minimizer of
`u \mapsto ‖u-f‖²+s‖Tu‖²`, so positive-part and upper truncation competitors prove positivity and
the sub-Markov bound (`M2`, `M3`). Constants lie in the weighted-gradient core and have zero
gradient, hence are fixed by the resolvent and every Yosida exponential (`M4`). The Poisson-series
factorization of the exponential transfers positivity from `J_s` to `exp (-t L_s)` (`M5`), and
the strong Yosida limit transfers it to `P_t` (`M6`). Symmetry, linearity and preservation of one
then give preservation of the mean, the absolute-value domination, and the `L^infinity` bound
(`M7`).

This route proves only the Markov property. It contains no `Gamma` calculus, no small-time heat
estimate, and no step of Buser's inequality; completing it does not give the comparison node a
progress marker.
-/

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace

namespace FunctionalInequalities

/-! ### `M1` -- the weighted-gradient relaxation is Markovian -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
    (hν : KLS.LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty),
      Energy.Markovian (ν : Measure V)
        ((Energy.PreEnergy.ofLinearPMap (hν.weightedOperator m B hi)).sequentialRelaxation))

/-! ### `M2` -- a Markovian closed form has a positive resolvent

The proof uses the competitor `(J_s f) sup 0`. The normal-contraction hypothesis supplies domain
membership and the energy bound; the lattice inequality
`abs ((u sup 0) - (f sup 0)) <= abs (u-f)` supplies the distance bound. -/

#check (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) {s : ℝ} (hs : 0 < s),
      Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T) →
      ∀ f : Lp ℝ 2 (μ : Measure α), 0 ≤ f → 0 ≤ resolventCLM T hT hs f)

/-! ### `M3` -- the resolvent is sub-Markov -/

/-! Use the competitor `(J_s f) inf 1`, with `1 = L2.const mu 1`, exactly as in `M2`. -/

#check (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) {s : ℝ} (hs : 0 < s),
      Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T) →
      ∀ f : Lp ℝ 2 (μ : Measure α), f ≤ L2.const μ 1 →
        resolventCLM T hT hs f ≤ L2.const μ 1)

/-! ### `M4` -- constants are fixed by the resolvent and Yosida exponential -/

#check (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) {s : ℝ} (hs : 0 < s),
      ∀ (hone : L2.const μ 1 ∈ T.domain), T ⟨L2.const μ 1, hone⟩ = 0 →
        resolventCLM T hT hs (L2.const μ 1) = L2.const μ 1 ∧
        ∀ t : ℝ,
          NormedSpace.exp (-t • yosida T hT hs) (L2.const μ 1) = L2.const μ 1)

/-! ### `M5` -- the Yosida exponentials are positive and sub-Markov -/

#check (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) (_hM : Energy.Markovian (μ : Measure α)
      (Energy.PreEnergy.normSqEnergy T)) {s t : ℝ} (hs : 0 < s) (_ht : 0 ≤ t)
    (hone : L2.const μ 1 ∈ T.domain) (_hTone : T ⟨L2.const μ 1, hone⟩ = 0),
      (∀ f, 0 ≤ f → 0 ≤ NormedSpace.exp (-t • yosida T hT hs) f) ∧
      (∀ f, f ≤ L2.const μ 1 →
        NormedSpace.exp (-t • yosida T hT hs) f ≤ L2.const μ 1))

/-! ### `M6` -- the generated semigroup is Markov -/

#check (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2 (μ : Measure α))))
    (_hM : Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T))
    {t : ℝ} (_ht : 0 ≤ t) (hone : L2.const μ 1 ∈ T.domain)
    (_hTone : T ⟨L2.const μ 1, hone⟩ = 0),
      (∀ f, 0 ≤ f → 0 ≤ FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f) ∧
      (∀ f, f ≤ L2.const μ 1 → FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f ≤ L2.const μ 1) ∧
      FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (L2.const μ 1) = L2.const μ 1)

/-! ### `M7` -- mean preservation, absolute-value domination and the `L^infinity` bound -/

#check (∀ {α H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : ProbabilityMeasure α) (T : Lp ℝ 2 (μ : Measure α) →ₗ.[ℝ] H)
    (hT : T.IsClosed) (hd : Dense (T.domain : Set (Lp ℝ 2 (μ : Measure α))))
    (_hM : Energy.Markovian (μ : Measure α) (Energy.PreEnergy.normSqEnergy T))
    {t : ℝ} (_ht : 0 ≤ t) (hone : L2.const μ 1 ∈ T.domain)
    (_hTone : T ⟨L2.const μ 1, hone⟩ = 0) (f : Lp ℝ 2 (μ : Measure α)),
      L2.mean μ (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f) = L2.mean μ f ∧
      |FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f| ≤ FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t |f| ∧
      ∀ {C : ℝ}, 0 ≤ C → |f| ≤ C • L2.const μ 1 →
        |FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f| ≤ C • L2.const μ 1)

end FunctionalInequalities
