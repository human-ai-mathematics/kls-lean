import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiConstant
import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison
import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Intrinsic
import FunctionalInequalities.KLS.Isoperimetry
import Mathlib.Probability.Moments.Variance

/-!
# Route statements for Cheeger's inequality `C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²`

**This file contains only `#check`s. A proposition that type-checks is not a proof.**
It preserves the Cheeger-inequality contracts `P0`–`P6`.
The coordinate inequality is in `KLS/Geometry/Cheeger/Inequality.lean`; the intrinsic log-concave
comparison is in `KLS/LogConcave/Poincare.lean`. These `#check`s introduce no proof or placeholder.

## The target

The **Cheeger half** of `thm:logconcave-cheeger-poincare-comparison`: for every finite-dimensional
log-concave law `μ`, `C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²`, where `C_P^lit` is the intrinsic local-slope
Poincaré constant of `def:literature-poincare-constant`
(`Poincare.LocalSlope.Intrinsic.constant`) and `Ψ_KLS = h_μ⁻¹` the inverse isoperimetric scale of
`def:isoperimetric-cheeger-scale` (`Isoperimetry.inverseScale`).  Dirac laws are included with both
sides `0`.  The **Buser half** `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` is **not** part of this route (`B1`
below). The general Buser comparison has the separate source
`KLS/LogConcave/Density/GaussianSmoothing/Buser.lean` and client
`research/audits/Density/GaussianBuserPassageAudit.lean`; this route concerns the Cheeger half.

## The route

Work on the coordinate space with an arbitrary Borel probability law `ν` and its Minkowski
constant `h_M = minkowskiConstant ν`; the log-concave statement is obtained at the end by
transport.  A median `m` of `g` exists (`P2`).  For a bounded `C¹` Lipschitz `g`,
`Var(g) ≤ ∫ (g − m)²`, which splits into the positive-part squares of `g − m` and `m − g`.  Each,
`v = (g − m)₊²`, is `C¹` (`t ↦ max t 0 ^ 2` is `C¹`), Lipschitz and supported on `{g > m}`, a set
of mass at most `1/2`, so on every superlevel set the balance `min(s, 1 − s)` is the mass itself
and the layer-cake formula with the multiplied Minkowski bound `minkowskiConstant_mul_min_le` and
the Minkowski coarea inequality `lintegral_minkowskiContent_superlevel_le` give the **`L¹`
Cheeger inequality** `h_M ∫ v ≤ ∫ ‖∇v‖` (`P3`).  The chain rule `∇v = 2 (g − m)₊ ∇g` and
Cauchy–Schwarz give `h_M² ∫ (g − m)₊² ≤ 4 ∫_{g > m} ‖∇g‖²` (`P4`); the two halves add up to
`h_M² Var(g) ≤ 4 ∫ ‖∇g‖²` (`P5`).  A general smooth test is cut off with a smooth bump `scaled R`:
the cutoff is bounded and Lipschitz, and its variance and gradient energy converge to those of the
test, giving the same bound for every admissible test (`P6`), hence
`C_P^smooth(ν) ≤ 4 / h_M²` (`P1`; when `h_M = 0` the right side is `⊤`).  Finally the
identification of the literature constant with the smooth-test constant of the intrinsic law
(`Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope`, under the absolute continuity
every log-concave law has) and `h_μ = h_M(ν)` (`Isoperimetry.constant_eq_minkowskiConstant_intrinsic`,
`K11` of `InfimumRouteStatements.lean`) transport `P1` to the target `P0`.

## What is already there

`minkowskiConstant_mul_min_le`, `lintegral_minkowskiContent_superlevel_le`,
`Poincare.SmoothTest.constant_le`, `Poincare.SmoothTest.Holds`,
`Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope`,
`LogConcave.intrinsic_absolutelyContinuous`, Mathlib's layer cake
`lintegral_eq_lintegral_meas_le`, `ENNReal.lintegral_mul_le_Lp_mul_Lq` (Hölder), `evariance` and
`variance`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set FunctionalInequalities
  FunctionalInequalities.KLS FunctionalInequalities.KLS.Isoperimetry
open scoped ENNReal NNReal ContDiff

/-! ### Proved inputs, for reference -/

#check @FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_mul_min_le
#check @FunctionalInequalities.KLS.Isoperimetry.lintegral_minkowskiContent_superlevel_le
#check @FunctionalInequalities.Poincare.SmoothTest.constant_le
#check @FunctionalInequalities.Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope
#check @FunctionalInequalities.KLS.LogConcave.intrinsic_absolutelyContinuous

/-! ### P0 — the target: Cheeger's inequality for log-concave laws

`C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²`, Dirac laws included with both sides `0`. -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * Isoperimetry.inverseScale μ ^ 2)

/-! ### P1 — Cheeger's inequality for the smooth-test constant of any Borel law

`C_P^smooth(ν) ≤ 4 / h_M(ν)²`; no density, no absolute continuity, no log-concavity. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V),
    Poincare.SmoothTest.constant (ν : Measure V) ≤ 4 / minkowskiConstant ν ^ 2)

/-! ### P2 — a median exists

Right and left continuity of the distribution function; the two half-mass bounds are the only
properties used. -/

#check (∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α → ℝ}, Measurable g →
    ∃ m : ℝ, μ {x | m < g x} ≤ 1 / 2 ∧ μ {x | g x < m} ≤ 1 / 2)

/-! ### P3 — the `L¹` Cheeger inequality for a nonnegative function of half mass

For `u ≥ 0` with `ν{u > 0} ≤ 1/2`, every superlevel set has mass at most `1/2`, so the balance is
the mass itself; layer cake, `minkowskiConstant_mul_min_le` and the Minkowski coarea inequality
give `h_M ∫ u dν ≤ ∫ ‖∇u‖ dν`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {u : V → ℝ}, ContDiff ℝ 1 u → ∀ {K : ℝ≥0}, LipschitzWith K u →
    (∀ x, 0 ≤ u x) → (ν : Measure V) {x | 0 < u x} ≤ 1 / 2 →
    minkowskiConstant ν * ∫⁻ x, ENNReal.ofReal (u x) ∂(ν : Measure V) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V))

/-! ### P4 — the positive-part square: `h_M² ∫ (g − m)₊² ≤ 4 ∫_{g > m} ‖∇g‖²`

`v = (g − m)₊²` is `C¹`, Lipschitz (for bounded `g`) and nonnegative with `{v > 0} = {g > m}`;
`P3` applies; `∇v = 2 (g − m)₊ ∇g` and Cauchy–Schwarz. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {g : V → ℝ}, ContDiff ℝ 1 g → ∀ {K : ℝ≥0}, LipschitzWith K g →
    ∀ {M : ℝ}, (∀ x, |g x| ≤ M) → ∀ (m : ℝ), (ν : Measure V) {x | m < g x} ≤ 1 / 2 →
    minkowskiConstant ν ^ 2 * ∫⁻ x, ENNReal.ofReal (max (g x - m) 0 ^ 2) ∂(ν : Measure V) ≤
      4 * ∫⁻ x in {x | m < g x}, ‖gradient g x‖ₑ ^ 2 ∂(ν : Measure V))

/-! ### P5 — Cheeger's inequality for bounded `C¹` Lipschitz functions

`h_M² Var(g) ≤ 4 ∫ ‖∇g‖²`: `Var(g) ≤ ∫ (g − m)²` at a median `m`, split into the two positive
parts, each handled by `P4`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {g : V → ℝ}, ContDiff ℝ 1 g → ∀ {K : ℝ≥0}, LipschitzWith K g →
    ∀ {M : ℝ}, (∀ x, |g x| ≤ M) →
    minkowskiConstant ν ^ 2 * evariance g (ν : Measure V) ≤
      4 * ∫⁻ x, ‖gradient g x‖ₑ ^ 2 ∂(ν : Measure V))

/-! ### P6 — every admissible smooth test

The cutoff `g · χ(·/R)` of an admissible test is bounded and Lipschitz; as `R → ∞` its variance
and gradient energy converge to those of the test (dominated convergence, `f ∈ L²`, finite
energy). -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {f : V → ℝ}, Poincare.SmoothTest.Admissible (ν : Measure V) f →
    minkowskiConstant ν ^ 2 * evariance f (ν : Measure V) ≤
      4 * ∫⁻ x, ‖gradient f x‖ₑ ^ 2 ∂(ν : Measure V))

/-! ### D1 — consequence: an infinite Minkowski constant forces a vanishing Poincaré constant

`4 / ⊤ = 0`; in particular in dimension zero, where `minkowskiConstant ν = ⊤`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V), minkowskiConstant ν = ⊤ →
    Poincare.SmoothTest.constant (ν : Measure V) = 0)

/-! ### B1 — the Buser half, stated and explicitly OUT of this route

`Ψ_KLS(μ)² ≤ π C_P^lit(μ)`; not an obligation here, recorded so the boundary is explicit. -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ)
