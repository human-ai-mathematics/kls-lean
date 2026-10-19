import FunctionalInequalities.KLS.Geometry.Cheeger.Infimum
import FunctionalInequalities.KLS.Geometry.Cheeger.DistanceCutoff
import FunctionalInequalities.KLS.Geometry.SmoothDomain.RegularSuperlevel
import FunctionalInequalities.Analysis.Coarea.Lipschitz
import FunctionalInequalities.KLS.Isoperimetry
import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Route statements for Cheeger-infimum identification

**This file contains only `#check`s. A proposition that type-checks is not a proof.**
It preserves the Cheeger-infimum contracts `K0`–`K13`.
Current implementations of the smooth/Minkowski comparison and intrinsic transports are in
`KLS/Geometry/Cheeger/Equality.lean`, with the definitions in `KLS/Geometry/Cheeger/Infimum.lean`.
The anonymous statements below pin the route's hypotheses, constants and dimensional scope.

## The two comparison contracts

* `K0` — `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`: for a smooth Lipschitz
  `[0,1]`-valued `u`, `h_S · ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν`, where `h_S` is the smooth
  relative-perimeter Cheeger infimum and `m(s) = min(s, 1 − s)`;
* `K5` — `Isoperimetry.smoothConstant_le_minkowskiConstant`: `h_S ≤ h_M`.

Together with the proved `minkowskiConstant_le_smoothConstant` (`h_M ≤ h_S`,
`KLS/Geometry/Cheeger/Infimum.lean`) they give `lem:relative-perimeter-cheeger-infimum`, the
`h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν` clauses of `thm:klartag-density-frontend-identification`,
and supply the intrinsic transports `K11`–`K13`.

## The route

**`K0`.** For almost every `t` the strict superlevel set `{u > t}` is a smooth domain
(`SmoothDomain.ae_exists_superlevel`, smooth Sard, `K3`) whose frontier lies in the level set
`{u = t}` (`frontier_superlevel_subset`), so its relative perimeter is at most the level integral of
the density (`K2`); the multiplied infimum bound `h_S · m(ν U) ≤ P_ρ(U)` holds for every smooth
domain, the zero- and full-mass cases through `⊤ · 0 = 0` (`K1`); integrating over `t` and applying
the weighted `C¹` coarea formula for the density `ν = volume.withDensity ρ` (`K4`, from the proved
Lipschitz coarea `lintegral_enorm_gradient_mul_eq_lintegral_levelSet`) gives `∫ ‖∇u‖ dν`.  Nothing
requires measurability of `t ↦ ∫_{u=t} ρ`: `lintegral_mono_ae` does not ask for it.

**`K5`.** Take a Borel `B` of intermediate mass and finite Minkowski content, so that
`ν(closure B) = ν B`.  The distance cutoffs `w_r` have gradient integral at most
`(ν(B^r) − ν B)/r` (proved, `K6`) and `L¹` distance to `𝟙_B` at most `ν(B^r) − ν B` (`K7`); the
smooth replacements of `K9` satisfy the coarea bound `K0`; and the balance is `1`-Lipschitz in the
set: `m(ν B) ≤ ∫₀¹ m(ν{u > t}) dt + ‖u − 𝟙_B‖₁` (`K8`, from the proved
`lintegral_measure_symmDiff_superlevel` and `min_measure_le_add_measure_symmDiff`).  Subtract the
error from the balance rather than multiplying it into `h_S` — `h_S · (m(ν B) − e_r) ≤ q(r)` — so
that no finiteness of `h_S` is needed; let the mollification index tend to infinity, then take the
`liminf` along `r → 0⁺`, which is the Minkowski content.

## What is already there

`minkowskiConstant_le_smoothConstant`, `minkowskiConstant_mul_min_le`,
`lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff`,
`tendsto_lintegral_min_superlevel`, `SmoothDomain.ae_exists_superlevel`,
`frontier_superlevel_subset`, `lintegral_enorm_gradient_distanceCutoff_le`,
`tendsto_distanceCutoff_indicator`, `lintegral_enorm_gradient_mul_eq_lintegral_levelSet`,
`Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.KLS
  FunctionalInequalities.KLS.Isoperimetry
open scoped ENNReal NNReal ContDiff

/-! ### Proved inputs, for reference -/

#check @FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_le_smoothConstant
#check @FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_mul_min_le
#check @FunctionalInequalities.KLS.Isoperimetry.lintegral_measure_symmDiff_superlevel
#check @FunctionalInequalities.KLS.Isoperimetry.min_measure_le_add_measure_symmDiff
#check @FunctionalInequalities.KLS.SmoothDomain.ae_exists_superlevel
#check @FunctionalInequalities.KLS.SmoothDomain.frontier_superlevel_subset
#check @FunctionalInequalities.KLS.Isoperimetry.lintegral_enorm_gradient_distanceCutoff_le
#check @FunctionalInequalities.Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet

/-! ### K0 — the smooth coarea-bound contract, verbatim

`h_S · ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν` for smooth Lipschitz `[0,1]`-valued `u`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
    ∀ {u : V → ℝ}, ContDiff ℝ ∞ u → ∀ {K : ℝ≥0}, LipschitzWith K u →
    (∀ x, u x ∈ Set.Icc (0 : ℝ) 1) →
    smoothConstant ρ (interior (ν : Measure V).support) ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V))

/-! ### K1 — the multiplied infimum bound, for every smooth domain

`h_S · m(ν U) ≤ P_ρ(U)`.  For `0 < ν U < 1` this is the definition of the infimum; when the mass is
`0` or `1` the balance vanishes and `⊤ · 0 = 0`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ρ : V → ℝ) (Ω : Set V) (ν : ProbabilityMeasure V) (U : SmoothDomain V),
    smoothConstant ρ Ω ν * min ((ν : Measure V) U.carrier) (1 - (ν : Measure V) U.carrier) ≤
      relativePerimeter ρ Ω U)

/-! ### K2 — the relative perimeter of a superlevel domain is bounded by the level integral

If `U.carrier = {t < u}` for a continuous `u`, then `frontier U.carrier ⊆ {u = t}`, so
`P_ρ(U) ≤ ∫_{u = t} ρ dσ` for every `Ω` and every nonnegative `ρ`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ρ : V → ℝ) (Ω : Set V) {u : V → ℝ}, Continuous u → ∀ {t : ℝ} (U : SmoothDomain V),
    U.carrier = {x | t < u x} →
    relativePerimeter ρ Ω U ≤ ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V))

/-! ### K3 — almost every strict superlevel set is a smooth domain (proved) -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {u : V → ℝ}, ContDiff ℝ ∞ u →
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x})

/-! ### K4 — the weighted `C¹` coarea formula for the Borell density

With `ν = volume.withDensity (ofReal ∘ ρ)`, the proved Lipschitz coarea formula with weight
`ofReal ∘ ρ` reads `∫ ‖∇u‖ dν = ∫ (∫_{u = t} ρ dσ) dt`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
    ∀ {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, ENNReal.ofReal (ρ y) ∂(surfaceMeasure V) ∂(volume : Measure ℝ))

/-! ### K5 — the comparison contract, verbatim: `h_S ≤ h_M` -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
    smoothConstant ρ (interior (ν : Measure V).support) ν ≤ minkowskiConstant ν)

/-! ### K6 — the gradient integral of a distance cutoff (proved)

`∫ ‖∇ w_r‖ dν ≤ (ν(B^r) − ν(closure B)) / r` whenever `ν ≪ m` for a Haar measure `m`; a Borell
density gives `ν ≪ volume`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure], (ν : Measure V) ≪ m →
    ∀ (B : Set V) {r : ℝ}, 0 < r →
    ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r)

/-! ### K7 — the `L¹` distance of a distance cutoff to the indicator

`w_r = 1` on `B`, `0 ≤ w_r ≤ 1`, and `w_r = 0` off the open `r`-thickening, so
`‖w_r − 𝟙_B‖₁ ≤ ν(B^r) − ν B`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {B : Set V}, MeasurableSet B → ∀ {r : ℝ}, 0 < r →
    ∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B)

/-! ### K8 — the balance is `1`-Lipschitz in the set

`m(ν B) ≤ ∫₀¹ m(ν{u > t}) dt + ‖u − 𝟙_B‖₁` for measurable `[0,1]`-valued `u`: layer cake turns
the `L¹` distance into `∫₀¹ ν({u > t} △ B) dt`, and `m` is `1`-Lipschitz for the symmetric
difference. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {u : V → ℝ}, Measurable u → (∀ x, u x ∈ Set.Icc (0 : ℝ) 1) →
    ∀ {B : Set V}, MeasurableSet B →
    min ((ν : Measure V) B) (1 - (ν : Measure V) B) ≤
      (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x})) +
        ∫⁻ x, ‖u x - B.indicator 1 x‖ₑ ∂(ν : Measure V))

/-! ### K9 — smooth replacements (proved in the work-in-progress module; to be moved)

Mollification of a Lipschitz `[0,1]`-valued `w`: smooth Lipschitz `[0,1]`-valued approximants,
`L¹(ν)`-convergent with convergent gradient integrals, under `ν ≪ m` for a Haar measure `m`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure], (ν : Measure V) ≪ m →
    ∀ {w : V → ℝ} {K : ℝ≥0}, LipschitzWith K w → (∀ x, w x ∈ Set.Icc (0 : ℝ) 1) →
    ∃ u : ℕ → V → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K' : ℝ≥0, LipschitzWith K' (u j)) ∧
        ∀ x, u j x ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖u j x - w x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ ∫⁻ x, ‖gradient (u j) x‖ₑ ∂(ν : Measure V)) atTop
        (𝓝 (∫⁻ x, ‖gradient w x‖ₑ ∂(ν : Measure V))))

/-! ### K10 — `lem:relative-perimeter-cheeger-infimum`: the two infima agree

`le_antisymm` of the proved `h_M ≤ h_S` and `K5`.  Stated for every law with a Borell density
relative to Lebesgue measure — stronger than the Blueprint's full-dimensional log-concave scope. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} {ρ : V → ℝ}, IsBorellDensity (ν : Measure V) volume ρ →
    minkowskiConstant ν = smoothConstant ρ (interior (ν : Measure V).support) ν)

/-! ### K11–K13 — the intrinsic transports

`K11` identifies the affine-support isoperimetric constant of
`def:isoperimetric-cheeger-scale` is the Minkowski constant of the intrinsic law.  `K12` and `K13`
are the `h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν` clauses of
`thm:klartag-density-frontend-identification`. Their current source is
`KLS/Geometry/Cheeger/Equality.lean`. -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E),
    Isoperimetry.constant μ = minkowskiConstant (Probability.intrinsicMeasure μ))

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    ∀ {ρ : (Probability.affineSupport μ).direction → ℝ},
    IsBorellDensity (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) volume ρ →
    Isoperimetry.constant μ =
      smoothConstant ρ
        (interior (Probability.intrinsicMeasure μ :
          Measure (Probability.affineSupport μ).direction).support)
        (Probability.intrinsicMeasure μ))

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    ∀ {ρ : (Probability.affineSupport μ).direction → ℝ},
    IsBorellDensity (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction) volume ρ →
    Isoperimetry.inverseScale μ =
      (smoothConstant ρ
        (interior (Probability.intrinsicMeasure μ :
          Measure (Probability.affineSupport μ).direction).support)
        (Probability.intrinsicMeasure μ))⁻¹)
