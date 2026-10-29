import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Scope audit for the Cheeger-equality module

`KLS/Geometry/Cheeger/Equality.lean` proves the smooth coarea bound
`Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`,
`h_S · ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν`, and the comparison
`Isoperimetry.smoothConstant_le_minkowskiConstant`, `h_S ≤ h_M`, of the smooth relative-perimeter
and Minkowski Cheeger infima.  This client discharges every proposition of the route file
`research/audits/Cheeger/InfimumRouteStatements.lean` from that module, through **named**
arguments, so a renamed binder or a reordered hypothesis would fail to elaborate here.

The propositions `K0`–`K13` of `InfimumRouteStatements.lean` are restated verbatim as
`route_K0` … `route_K13`, with one documented exception.

**`K7` as written in `InfimumRouteStatements.lean` is false.**  Mathlib's convention
`Metric.infDist x ∅ = 0` makes `distanceCutoff ∅ r` the constant function `1`, while
`Metric.thickening r ∅ = ∅`, so for `B = ∅` the left-hand side is `1` and the right-hand side is
`0`.  `route_K7` below therefore carries the extra hypothesis `B.Nonempty`, exactly as the proved
library lemma `Isoperimetry.lintegral_enorm_distanceCutoff_sub_indicator_le` does, and
`route_K7_empty_counterexample` exhibits the failure of the verbatim form on a Dirac law over
`EuclideanSpace ℝ (Fin 1)`.  Nothing downstream is affected: the comparison `h_S ≤ h_M` applies
the bound only to sets of positive mass, which are nonempty.

The boundary section records the zero-dimensional convention (both infima `⊤`), the `h_M = ⊤` and
`h_S = ⊤` transfers, and the degenerate affine support of a Dirac-type law, where the intrinsic
transports read `h_μ = ⊤` and `Ψ_KLS(μ) = 0`.

The axiom reports at the end cover every public declaration of the Cheeger-equality module and
every theorem of this client; each of them must list only `propext`, `Classical.choice` and
`Quot.sound`.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
  FunctionalInequalities.KLS.Isoperimetry
open scoped ENNReal NNReal ContDiff

namespace CheegerEqualityAudit

/-! ### The smooth coarea bound -/

/-- `h_S · ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν` for a smooth Lipschitz `[0,1]`-valued `u`. -/
theorem route_K0 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
      ∀ {u : V → ℝ}, ContDiff ℝ ∞ u → ∀ {K : ℝ≥0}, LipschitzWith K u →
      (∀ x, u x ∈ Set.Icc (0 : ℝ) 1) →
      smoothConstant ρ (interior (ν : Measure V).support) ν *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
        ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  intro V _ _ _ _ _ _ _ ν ρ hρ u hu K hK hu01
  exact smoothConstant_mul_lintegral_min_superlevel_le (ν := ν) (ρ := ρ) (u := u) (K := K)
    hρ hu hK hu01

/-! ### The multiplied infimum bound, for every smooth domain -/

/-- `h_S · m(ν U) ≤ P_ρ(U)`; the degenerate masses go through `⊤ * 0 = 0`. -/
theorem route_K1 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ρ : V → ℝ) (Ω : Set V) (ν : ProbabilityMeasure V) (U : SmoothDomain V),
      smoothConstant ρ Ω ν * min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) ≤
        relativePerimeter ρ Ω U := by
  intro V _ _ _ _ _ _ _ ρ Ω ν U
  exact smoothConstant_mul_min_le ρ Ω ν U

/-! ### The relative perimeter of a superlevel domain -/

/-- `P_ρ(U) ≤ ∫_{u = t} ρ dσ` when `U.carrier = {t < u}` for a continuous `u`. -/
theorem route_K2 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ρ : V → ℝ) (Ω : Set V) {u : V → ℝ}, Continuous u → ∀ {t : ℝ} (U : SmoothDomain V),
      U.carrier = {x | t < u x} →
      relativePerimeter ρ Ω U ≤ ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V) := by
  intro V _ _ _ _ _ _ _ ρ Ω u hu t U hU
  exact relativePerimeter_le_lintegral_levelSet (u := u) (t := t) ρ Ω hu U hU

/-! ### Almost every strict superlevel set is a smooth domain -/

/-- Smooth Sard, already proved in `Analysis/SmoothDomain/RegularSuperlevel.lean`. -/
theorem route_K3 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {u : V → ℝ}, ContDiff ℝ ∞ u →
      ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x} := by
  intro V _ _ _ _ _ _ _ u hu
  exact SmoothDomain.ae_exists_superlevel (u := u) hu

/-! ### The weighted coarea formula for the Borell density -/

/-- `∫ ‖∇u‖ dν = ∫ (∫_{u = t} ρ dσ) dt` for `ν = volume.withDensity (ofReal ∘ ρ)`. -/
theorem route_K4 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
      ∀ {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) =
        ∫⁻ t, ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V)
          ∂(volume : Measure ℝ) := by
  intro V _ _ _ _ _ _ _ ν ρ hρ u K hK
  exact lintegral_enorm_gradient_eq_lintegral_levelSet_density (ν := ν) (ρ := ρ) (u := u) (K := K)
    hρ hK

/-! ### The comparison `h_S ≤ h_M` -/

/-- The reverse comparison of the two Cheeger infima. -/
theorem route_K5 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
      smoothConstant ρ (interior (ν : Measure V).support) ν ≤ minkowskiConstant ν := by
  intro V _ _ _ _ _ _ _ ν ρ hρ
  exact smoothConstant_le_minkowskiConstant (ν := ν) (ρ := ρ) hρ

/-! ### The gradient integral of a distance cutoff -/

/-- Already proved in `KLS/Geometry/Cheeger/DistanceCutoff.lean`. -/
theorem route_K6 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure], (ν : Measure V) ≪ m →
      ∀ (B : Set V) {r : ℝ}, 0 < r →
      ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
        ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
          ENNReal.ofReal r := by
  intro V _ _ _ _ _ _ _ ν m _ hac B r hr
  exact lintegral_enorm_gradient_distanceCutoff_le (r := r) ν m hac B hr

/-! ### The `L¹` distance of a distance cutoff to the indicator

The route file states this for every measurable `B`.  That form is **false**: see
`route_K7_empty_counterexample`.  The hypothesis `B.Nonempty` is the repair, and it is the only
change; the comparison `h_S ≤ h_M` applies the bound to sets of positive mass, which are
nonempty. -/

/-- `‖w_r − 𝟙_B‖₁ ≤ ν(B^r) − ν B` for a **nonempty** measurable `B`. -/
theorem route_K7 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {B : Set V}, B.Nonempty → MeasurableSet B → ∀ {r : ℝ}, 0 < r →
      ∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
  intro V _ _ _ _ _ _ _ ν B hB hBm r hr
  exact lintegral_enorm_distanceCutoff_sub_indicator_le (B := B) (r := r) ν hB hBm hr

/-- The form for every measurable `B` fails for the empty set: `distanceCutoff ∅ r ≡ 1` because
`Metric.infDist x ∅ = 0`, while `Metric.thickening r ∅ = ∅`, so the bound reads `1 ≤ 0`. -/
theorem route_K7_empty_counterexample :
    ∃ (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)))
      (B : Set (EuclideanSpace ℝ (Fin 1))) (r : ℝ),
      MeasurableSet B ∧ 0 < r ∧
        ¬ (∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ
              ∂(ν : Measure (EuclideanSpace ℝ (Fin 1))) ≤
            (ν : Measure (EuclideanSpace ℝ (Fin 1))) (Metric.thickening r B) -
              (ν : Measure (EuclideanSpace ℝ (Fin 1))) B) := by
  refine ⟨⟨Measure.dirac 0, inferInstance⟩, ∅, 1, MeasurableSet.empty, one_pos, ?_⟩
  have hcut : ∀ x : EuclideanSpace ℝ (Fin 1), distanceCutoff (∅ : Set _) 1 x = 1 := by
    intro x
    simp [distanceCutoff]
  simp [hcut]

/-! ### The balance is `1`-Lipschitz in the set -/

/-- `m(ν B) ≤ ∫₀¹ m(ν{u > t}) dt + ‖u − 𝟙_B‖₁` for a measurable `[0,1]`-valued `u`. -/
theorem route_K8 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) {u : V → ℝ}, Measurable u → (∀ x, u x ∈ Set.Icc (0 : ℝ) 1) →
      ∀ {B : Set V}, MeasurableSet B →
      min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≤
        (∫⁻ t in Set.Ioo (0 : ℝ) 1,
            min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x})) +
          ∫⁻ x, ‖u x - B.indicator 1 x‖ₑ ∂(ν : Measure V) := by
  intro V _ _ _ _ _ _ _ ν u hu hu01 B hB
  exact min_measure_le_lintegral_min_superlevel_add (u := u) (B := B) ν hu hu01 hB

/-! ### Smooth replacements of Lipschitz `[0,1]`-valued functions -/

/-- Mollification (`Isoperimetry.exists_smooth_approximation_lipschitz`). -/
theorem route_K9 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
      (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure], (ν : Measure V) ≪ m →
      ∀ {w : V → ℝ} {K : ℝ≥0}, LipschitzWith K w → (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) →
      ∃ u : ℕ → V → ℝ,
        (∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K' : ℝ≥0, LipschitzWith K' (u j)) ∧
          ∀ x, u j x ∈ Set.Icc (0 : ℝ) 1) ∧
        Tendsto (fun j ↦ ∫⁻ x, ‖u j x - w x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
        Tendsto (fun j ↦ ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V)) atTop
          (𝓝 (∫⁻ x, ‖gradient w x‖ₑ ∂(ν : Measure V))) := by
  intro V _ _ _ _ _ _ ν m _ hac w K hw hw01
  exact exists_smooth_approximation_lipschitz (w := w) (K := K) ν m hac hw hw01

/-! ### `lem:relative-perimeter-cheeger-infimum`: the two infima agree -/

/-- `h_M = h_S` for every law with a Borell density relative to Lebesgue measure. -/
theorem route_K10 :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
      minkowskiConstant ν = smoothConstant ρ (interior (ν : Measure V).support) ν := by
  intro V _ _ _ _ _ _ _ ν ρ hρ
  exact minkowskiConstant_eq_smoothConstant (ν := ν) (ρ := ρ) hρ

/-! ### The intrinsic transports -/

/-- The affine-support isoperimetric constant is the Minkowski constant of the intrinsic law. -/
theorem route_K11 :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      (μ : ProbabilityMeasure E),
      Isoperimetry.constant μ = minkowskiConstant (Probability.intrinsicMeasure μ) := by
  intro E _ _ _ _ _ _ _ μ
  exact constant_eq_minkowskiConstant_intrinsic μ

/-- The `h_μ = h_ν^{sm,rel}` clause of `thm:klartag-density-frontend-identification`. -/
theorem route_K12 :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      {μ : ProbabilityMeasure E}, LogConcave μ →
      ∀ {ρ : (Probability.affineSupport μ).direction → ℝ},
      IsBorellDensity (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction) volume ρ →
      Isoperimetry.constant μ =
        smoothConstant ρ
          (interior (Probability.intrinsicMeasure μ :
            Measure (Probability.affineSupport μ).direction).support)
          (Probability.intrinsicMeasure μ) := by
  intro E _ _ _ _ _ _ _ μ hμ ρ hρ
  exact constant_eq_smoothConstant_intrinsic (μ := μ) (ρ := ρ) hμ hρ

/-- The `Ψ_KLS(μ) = ψ_ν` clause: inverse scales agree. -/
theorem route_K13 :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      {μ : ProbabilityMeasure E}, LogConcave μ →
      ∀ {ρ : (Probability.affineSupport μ).direction → ℝ},
      IsBorellDensity (Probability.intrinsicMeasure μ :
        Measure (Probability.affineSupport μ).direction) volume ρ →
      Isoperimetry.inverseScale μ =
        (smoothConstant ρ
          (interior (Probability.intrinsicMeasure μ :
            Measure (Probability.affineSupport μ).direction).support)
          (Probability.intrinsicMeasure μ))⁻¹ := by
  intro E _ _ _ _ _ _ _ μ hμ ρ hρ
  exact inverseScale_eq_inv_smoothConstant_intrinsic (μ := μ) (ρ := ρ) hμ hρ

/-! ### Boundary cases -/

/-- Dimension zero: no set and no smooth domain has intermediate mass, both infima are `⊤`, and
the equality `h_M = h_S` reads `⊤ = ⊤`. -/
theorem boundary_zero_dimensional :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      [Subsingleton V] (ρ : V → ℝ) (Ω : Set V) (ν : ProbabilityMeasure V),
      minkowskiConstant ν = ⊤ ∧ smoothConstant ρ Ω ν = ⊤ := by
  intro V _ _ _ _ _ _ _ _ ρ Ω ν
  exact ⟨minkowskiConstant_eq_top_of_subsingleton ν, smoothConstant_eq_top_of_subsingleton ρ Ω ν⟩

/-- Dimension zero, through the equality itself: both sides of `h_M = h_S` are `⊤`. -/
theorem boundary_zero_dimensional_eq :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      [Subsingleton V] {ν : ProbabilityMeasure V} {ρ : V → ℝ},
      IsBorellDensity (ν : Measure V) volume ρ →
      minkowskiConstant ν = ⊤ ∧
        smoothConstant ρ (interior (ν : Measure V).support) ν = ⊤ ∧
          minkowskiConstant ν = smoothConstant ρ (interior (ν : Measure V).support) ν := by
  intro V _ _ _ _ _ _ _ _ ν ρ hρ
  refine ⟨minkowskiConstant_eq_top_of_subsingleton ν,
    smoothConstant_eq_top_of_subsingleton _ _ ν, minkowskiConstant_eq_smoothConstant hρ⟩

/-- `h_M = ⊤` forces `h_S = ⊤`, and conversely: the equality transfers the degenerate value in
both directions, so neither infimum is assumed finite anywhere. -/
theorem boundary_top_transfer :
    ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
      [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
      {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
      (minkowskiConstant ν = ⊤ ↔ smoothConstant ρ (interior (ν : Measure V).support) ν = ⊤) := by
  intro V _ _ _ _ _ _ _ ν ρ hρ
  rw [minkowskiConstant_eq_smoothConstant hρ]

/-- A law whose affine support is a point — a Dirac law in particular — has a zero-dimensional
direction space, so `h_μ = ⊤`, `Ψ_KLS(μ) = 0`, and the smooth relative-perimeter infimum of the
intrinsic law is `⊤` as well. -/
theorem boundary_degenerate_affine_support :
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
      {μ : ProbabilityMeasure E},
      Module.finrank ℝ (Probability.affineSupport μ).direction = 0 →
      Isoperimetry.constant μ = ⊤ ∧ Isoperimetry.inverseScale μ = 0 ∧
        ∀ (_hμ : LogConcave μ) {ρ : (Probability.affineSupport μ).direction → ℝ},
          IsBorellDensity (Probability.intrinsicMeasure μ :
            Measure (Probability.affineSupport μ).direction) volume ρ →
          smoothConstant ρ
            (interior (Probability.intrinsicMeasure μ :
              Measure (Probability.affineSupport μ).direction).support)
            (Probability.intrinsicMeasure μ) = ⊤ := by
  intro E _ _ _ _ _ _ _ μ hdim
  have htop : Isoperimetry.constant μ = ⊤ := by
    unfold Isoperimetry.constant
    rw [if_pos hdim]
  refine ⟨htop, by rw [Isoperimetry.inverseScale, htop, ENNReal.inv_top], ?_⟩
  intro hμ ρ hρ
  rw [← constant_eq_smoothConstant_intrinsic hμ hρ, htop]

end CheegerEqualityAudit

/-! ### Axiom audit

Every public declaration of `KLS/Geometry/Cheeger/Equality.lean` and every theorem of this client.
Only `propext`, `Classical.choice` and `Quot.sound` may appear; in particular no placeholder-proof
axiom. -/

#print axioms FunctionalInequalities.KLS.Isoperimetry.exists_smooth_approximation_lipschitz
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_mul_min_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.relativePerimeter_le_lintegral_levelSet
#print axioms
  FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_gradient_eq_lintegral_levelSet_density
#print axioms
  FunctionalInequalities.KLS.Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le
#print axioms
  FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_distanceCutoff_sub_indicator_le
#print axioms FunctionalInequalities.KLS.Isoperimetry.min_measure_le_lintegral_min_superlevel_add
#print axioms FunctionalInequalities.KLS.Isoperimetry.smoothConstant_le_minkowskiConstant
#print axioms FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant
#print axioms FunctionalInequalities.KLS.Isoperimetry.constant_eq_minkowskiConstant_intrinsic
#print axioms FunctionalInequalities.KLS.Isoperimetry.constant_eq_smoothConstant_intrinsic
#print axioms FunctionalInequalities.KLS.Isoperimetry.inverseScale_eq_inv_smoothConstant_intrinsic

#print axioms CheegerEqualityAudit.route_K0
#print axioms CheegerEqualityAudit.route_K1
#print axioms CheegerEqualityAudit.route_K2
#print axioms CheegerEqualityAudit.route_K3
#print axioms CheegerEqualityAudit.route_K4
#print axioms CheegerEqualityAudit.route_K5
#print axioms CheegerEqualityAudit.route_K6
#print axioms CheegerEqualityAudit.route_K7
#print axioms CheegerEqualityAudit.route_K7_empty_counterexample
#print axioms CheegerEqualityAudit.route_K8
#print axioms CheegerEqualityAudit.route_K9
#print axioms CheegerEqualityAudit.route_K10
#print axioms CheegerEqualityAudit.route_K11
#print axioms CheegerEqualityAudit.route_K12
#print axioms CheegerEqualityAudit.route_K13
#print axioms CheegerEqualityAudit.boundary_zero_dimensional
#print axioms CheegerEqualityAudit.boundary_zero_dimensional_eq
#print axioms CheegerEqualityAudit.boundary_top_transfer
#print axioms CheegerEqualityAudit.boundary_degenerate_affine_support
