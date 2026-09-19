import FunctionalInequalities.Analysis.Graph.Area
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Egorov

/-! Weighted coarea route: TYPE CHECKS ONLY, no declaration, proof, or axiom.
All L0-L12 obligations below remain UNPROVED. T1-T3 preserve the original targets.
-/
open MeasureTheory Filter Topology FunctionalInequalities FunctionalInequalities.KLS
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

-- L0. Zero-dimensional base, including infinite weights.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Subsingleton V] (u : V → ℝ) {g : V → ℝ≥0∞}, Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) volume ∧
    (∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))

-- L1. Eilenberg measurable majorant. Arbitrary S, Lipschitz only on S; no circular measurability assumption.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Nontrivial V], ∃ C : ℝ≥0, 0 < C ∧
    ∀ {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzOnWith K u S →
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, KLS.surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ (C : ℝ≥0∞) * (K : ℝ≥0∞) * volume S)

-- L2. Null-set slicing. Volume nullity alone does not give this without Lipschitz slicing.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {N : Set V}, LipschitzOnWith K u N →
    (volume : Measure V) N = 0 →
    ∀ᵐ t ∂(volume : Measure ℝ), KLS.surfaceMeasure V (N ∩ {x | u x = t}) = 0)

-- L3. Compact fibers: Borel measurable, not a claim of upper semicontinuity of Hausdorff measure.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {S : Set V}, Continuous u → IsCompact S →
    Measurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t})))

-- L4. Borel-set fibers from compact exhaustion modulo a volume-null remainder.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzWith K u → MeasurableSet S →
    AEMeasurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t}))
      (volume : Measure ℝ))

-- L5. Weighted fiber measurability; S = univ is target 1.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ))

-- L6. Compact C1 Whitney extension of a compatible first-order jet. New infrastructure.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ Set.EqOn v f S ∧
      ∀ x ∈ S, fderiv ℝ v x = F x)

-- L7. Whitney-Lusin decomposition. Disjoint Borel pieces cover a.e.; exact jets, not approximation in norm.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ (S : ℕ → Set V) (v : ℕ → V → ℝ),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j ↦ Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x)

-- L8. Weighted graph area on an open parameter domain; localization of the existing global unweighted result.
#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : H →ₗᵢ[ℝ] V) {e : V}
    {O S : Set H} {v : H → ℝ} {g : V → ℝ≥0∞},
    ‖e‖ = 1 → (∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) →
    IsOpen O → ContDiffOn ℝ 1 v O → MeasurableSet S → S ⊆ O → Measurable g →
    (∫⁻ x in Analysis.graphMap ι e v '' S, g x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))) =
      ∫⁻ y in S, ENNReal.ofReal (Analysis.graphJacobian (gradient v y)) *
        g (Analysis.graphMap ι e v y) ∂(volume : Measure H))

-- L9. Regular open-domain C1 coarea; local graph/Jacobian calculation and countable disjoint gluing.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    IsOpen O → ContDiffOn ℝ 1 u O → (∀ x ∈ O, fderiv ℝ u x ≠ 0) →
    MeasurableSet S → S ⊆ O → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))

-- L10. Critical fibers are null a.e. for C1, NOT critical values null (C1 Sard).
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ}, ContDiff ℝ 1 u →
    ∀ᵐ t ∂(volume : Measure ℝ),
      KLS.surfaceMeasure V ({x | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0)

-- L11. Global C1 weighted coarea, no global Lipschitz bound needed for the auxiliary C1 pieces.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    ContDiff ℝ 1 u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))

-- L12. Recommended general theorem: Borel restriction, arbitrary ENNReal weight, Lipschitz u, every dimension.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))

-- L6a. Compact jet extraction from Rademacher, derivative measurability, regularity and uniform approximation.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ S : ℕ → Set V, (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      ∀ j, IsCompact (S j) ∧ (∀ x ∈ S j, DifferentiableAt ℝ u x) ∧
        ContinuousOn (fderiv ℝ u) (S j) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ x ∈ S j, ∀ y ∈ S j, ‖y - x‖ < δ →
            ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ ε * ‖y - x‖)

-- T1. Original target: original WIP type; proof-binder names anonymized only to avoid unused-variable lint.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (_ : LipschitzWith K u)
    {g : V → ℝ≥0∞} (_ : Measurable g) ,
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ))

-- T2. Original target: original WIP type; proof-binder names anonymized only to avoid unused-variable lint.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}
    (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))

-- T3. Original C1 target, including SecondCountableTopology.
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    {u : V → ℝ} (_ : ContDiff ℝ 1 u)
    {K : ℝ≥0} (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ))
