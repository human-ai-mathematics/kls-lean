import FunctionalInequalities.KLS.Geometry.Cheeger.Equality
import FunctionalInequalities.KLS.Geometry.Cheeger.Inequality
import FunctionalInequalities.KLS.LogConcave.Line.Hazard
import FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison
import FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Intrinsic
import FunctionalInequalities.Poincare.SmoothTest.Linear
import Mathlib.Probability.Moments.Variance

/-!
# Route statements for the Buser half `Ψ_KLS(μ)² ≤ π C_P^lit(μ)`

**This file contains only `#check`s. A proposition that type-checks is not a proof.**
It preserves the general comparison contract `B0` and the one-dimensional contracts `Q0`–`Q5`.
The current general log-concave comparison is
`KLS.LogConcave.inverseScale_sq_le_pi_literature` in
`KLS/LogConcave/Density/GaussianSmoothing/Buser.lean`, including every affine-support dimension.
The independent client is `research/audits/Density/GaussianBuserPassageAudit.lean`.

## The target and mathematical routes

`B0` is the Buser half of `thm:logconcave-cheeger-poincare-comparison`: for every finite-dimensional
log-concave law, `Ψ_KLS(μ)² ≤ π C_P^lit(μ)`, i.e. `λ₁ ≤ π h²`.
Classical semigroup arguments use the weighted heat semigroup and Bakry–Émery gradient bounds
(Ledoux; De Ponti–Mondino for the constant `π` on `RCD(0,∞)` spaces). A localization route uses
Lovász–Simonovits or Klartag needle decompositions and a transfer of Poincaré constants to needles.
These mathematical descriptions are distinct from the anonymous statement checks in this file.

## One-dimensional contracts, with an explicit constant

On the line everything needed already exists in this repository: a log-concave law with support of
nonempty interior has a Borell density `ρ` (`LineDensity`), a median `m`, and the hazard bounds
`2 ρ(m) F(x) ≤ ρ(x)` for `x ≤ m` and `2 ρ(m) (1 − F(x)) ≤ ρ(x)` for `x ≥ m`
(`KLS/LogConcave/Line/Hazard.lean`).  The route:

* `Q1` — **one-dimensional isoperimetry**: `h_M(ν) ≥ 2 ρ(m)`.  Through the certified equality
  `h_M = h_S` (`lem:relative-perimeter-cheeger-infimum`) it suffices to bound the smooth
  relative-perimeter infimum: a smooth domain of `ℝ` is an open set whose frontier is discrete, its
  relative perimeter is the sum of `ρ` over the frontier points in the interior of the support
  (`ℋ⁰` counts points), and the hazard bounds give, for the component containing the median,
  `ρ(a) + ρ(b) ≥ 2 ρ(m) (F(a) + 1 − F(b)) ≥ 2 ρ(m) (1 − ν U)`, and for every other component
  `ρ(endpoint) ≥ 2 ρ(m) ν(component)`; summing gives `2 ρ(m) · min(ν U, 1 − ν U) ≤ P_ρ(U)`.
* `Q2` — **the median is within a factor two of the mode**: `ρ(x) ≤ 2 ρ(m)` for every `x`.  With
  `κ` the slope of `log ρ` from the median towards the mode, log-concavity gives
  `ρ(x) ≤ ρ(m) e^{−κ(m − x)}` on the far side, so the far half-mass gives `κ ≤ 2 ρ(m)`, and the near
  half-mass gives `ρ(mode) ≤ ρ(m) + κ/2 ≤ 2 ρ(m)`.  Sharp for the exponential law.
* `Q3` — **a density bounded by `M` has variance at least `1/(12 M²)`** (no log-concavity): on each
  side of the mean the mass `p` resp. `1 − p` is spread with density `≤ M`, so the second moment on
  that side is at least that of the uniform distribution on an interval of length `p/M`, namely
  `p³/(3M²)`; `p³ + (1−p)³ ≥ 1/4`.
* `Q4` — **the linear test**: `Var(id) ≤ C_P^smooth(ν)` (the identity is a smooth test of unit
  gradient energy; `Poincare.SmoothTest.rayleigh_le_constant`).
* `Q5` / `Q0` — **assembly**: `Ψ² = h_M⁻² ≤ (2ρ(m))⁻² ≤ (ρ_max)⁻²/... ` precisely
  `h_M⁻² ≤ 1/(4 ρ(m)²) ≤ 1/(ρ_max²) ≤ 12 Var ≤ 12 C_P`, so `Ψ² ≤ 12 C_P^smooth(ν)` on the
  line, and through the literature identification `Ψ_KLS(μ)² ≤ 12 C_P^lit(μ)` whenever the affine
  support of `μ` has dimension at most one (`Q0'`; Dirac laws have both sides `0`).

The one-dimensional calculation gives `12`, which is larger than `π`; it does not by itself
establish the general comparison with `π`. The latter has the separate Gaussian-smoothing source
and full-signature client named above.

## General semigroup and localization descriptions

A semigroup argument uses the Markov semigroup of the Cheeger form, the Bakry–Émery gradient bound
`‖∇P_t f‖² ≤ P_t ‖∇f‖²`, and Ledoux's estimates
`‖f − P_t f‖₁ ≤ c √t · μ⁺(A)` and `‖P_t f − μ A‖₂ ≤ e^{−t/C_P}`.
A localization argument uses Lovász–Simonovits bisection, a needle limit and transfer of Poincaré
constants to needles. Neither description is a proof produced by a `#check` below.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set FunctionalInequalities
  FunctionalInequalities.KLS FunctionalInequalities.KLS.Isoperimetry
open FunctionalInequalities.Probability.Line (cdf)
open scoped ENNReal NNReal

/-! ### Proved inputs, for reference -/

#check @FunctionalInequalities.KLS.LineDensity.two_mul_cdf_le
#check @FunctionalInequalities.KLS.LineDensity.two_mul_measureReal_Ioi_le
#check @FunctionalInequalities.KLS.LineDensity.exists_median
#check @FunctionalInequalities.KLS.LogConcave.exists_lineDensity
#check @FunctionalInequalities.KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant
#check @FunctionalInequalities.Poincare.SmoothTest.rayleigh_le_constant
#check @FunctionalInequalities.KLS.LogConcave.literatureConstant_le_four_mul_inverseScale_sq

/-! ### B0 — the general Buser contract, every dimension, constant `π`

Recorded verbatim as the Blueprint states it; separate from the one-dimensional contracts `Q0`–`Q5`. -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    Isoperimetry.inverseScale μ ^ 2 ≤
      ENNReal.ofReal Real.pi * Poincare.LocalSlope.Intrinsic.constant μ)

/-! ### Q0 — one-dimensional target on the line: `Ψ² ≤ 12 C_P^smooth` -/

#check (∀ (ν : ProbabilityMeasure ℝ), LogConcave ν →
    (minkowskiConstant ν)⁻¹ ^ 2 ≤ 12 * Poincare.SmoothTest.constant (ν : Measure ℝ))

/-! ### Q0' — one-dimensional target in the Blueprint's variables: affine support of dimension at most one -/

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    {μ : ProbabilityMeasure E}, LogConcave μ →
    Module.finrank ℝ (Probability.affineSupport μ).direction ≤ 1 →
    Isoperimetry.inverseScale μ ^ 2 ≤ 12 * Poincare.LocalSlope.Intrinsic.constant μ)

/-! ### Q1 — one-dimensional isoperimetry: `2 ρ(m) ≤ h_M(ν)` -/

#check (∀ {ν : ProbabilityMeasure ℝ}, LogConcave ν →
    ∀ (_hi : (interior (ν : Measure ℝ).support).Nonempty) (d : LineDensity ν) {m : ℝ},
    cdf ν m = 1 / 2 → ENNReal.ofReal (2 * d.ρ m) ≤ minkowskiConstant ν)

/-! ### Q1' — the smooth-domain form that `Q1` reduces to through `h_M = h_S` -/

#check (∀ {ν : ProbabilityMeasure ℝ}, LogConcave ν →
    ∀ (_hi : (interior (ν : Measure ℝ).support).Nonempty) (d : LineDensity ν) {m : ℝ},
    cdf ν m = 1 / 2 → ∀ (U : SmoothDomain ℝ),
    ENNReal.ofReal (2 * d.ρ m) * min ((ν : Measure ℝ) U.carrier) (1 - (ν : Measure ℝ) U.carrier) ≤
      relativePerimeter d.ρ (interior (ν : Measure ℝ).support) U)

/-! ### Q2 — the density is at most twice its value at a median -/

#check (∀ {ν : ProbabilityMeasure ℝ}, LogConcave ν →
    ∀ (_hi : (interior (ν : Measure ℝ).support).Nonempty) (d : LineDensity ν) {m : ℝ},
    cdf ν m = 1 / 2 → ∀ x, d.ρ x ≤ 2 * d.ρ m)

/-! ### Q3 — a bounded density has variance at least `1 / (12 M²)` (no log-concavity) -/

#check (∀ (ν : ProbabilityMeasure ℝ) (d : LineDensity ν) {M : ℝ}, 0 < M → (∀ x, d.ρ x ≤ M) →
    ENNReal.ofReal (1 / (12 * M ^ 2)) ≤ evariance id (ν : Measure ℝ))

/-! ### Q4 — the linear test: the variance is at most the smooth-test Poincaré constant -/

#check (∀ (ν : ProbabilityMeasure ℝ), MemLp id 2 (ν : Measure ℝ) →
    evariance id (ν : Measure ℝ) ≤ Poincare.SmoothTest.constant (ν : Measure ℝ))

/-! ### Q5 — a log-concave law on the line has finite second moment -/

#check (∀ (ν : ProbabilityMeasure ℝ), LogConcave ν → MemLp id 2 (ν : Measure ℝ))

/-! ### D1 — comparison of the constants: `12` is not `π`

This chain does not give `π`: the chain `h_M ≥ 2ρ(m)`, `ρ_max ≤ 2ρ(m)`, `Var ≥ 1/(12 ρ_max²)` loses a
factor at each step, and the exponential law shows `Q2` and the one-dimensional Cheeger bound are
individually sharp.  Recorded as the (true, trivial) numerical statement that `π < 12`, so the
one-dimensional bound with `12` is weaker than the Blueprint's bound with `π`. -/

#check (Real.pi < 12)
