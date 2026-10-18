import FunctionalInequalities.Energy.Cheeger.Basic
import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Route statements for the singular-law Cheeger identification `𝓔^can = 2 Ch`

**This file contains only `#check`s. A proposition that type-checks is not a proof.**
It preserves `E0a`–`E0e` and the supporting `A1`–`A3`, `B1`–`B5`, `C1`–`C6` contracts.
The comparison, recovery and density sources are `Energy/Euclidean/Slope/Comparison.lean`,
`Energy/Euclidean/Slope/Recovery.lean` and `Energy/Euclidean/Slope/Density.lean`; the assembled
identification is in `Energy/Cheeger/Identification.lean`. Independent clients are
`research/audits/EnergySlopeComparisonAudit.lean`, `research/audits/EnergySlopeRecoveryAudit.lean`
and `research/audits/EnergySlopeDensityAudit.lean`.

## The five identification contracts and their structure

The contracts state, for every Borel probability law `ν` on a finite-dimensional
inner-product space: `E0a` the smooth-gradient relaxation is the relaxed squared local slope; `E0b`
the two Cheeger conventions relax to the same functional; `E0c` the two Cheeger energies agree; `E0d`
`𝓔 = 2 Ch` on the coordinate space; `E0e` the Blueprint identity
`thm:smooth-gradient-relaxation-two-cheeger` on the affine support.  The certified corollary
`cor:absolutely-continuous-relaxation-two-cheeger` proves all five under absolute continuity of `ν`
(`Energy/Cheeger/Basic.lean`).  **`E0a` is the substantive identification**: `E0b` follows from the sandwich
`LocalSlope.relaxation ≤ AsymptoticLipschitz.relaxation ≤ SmoothGradient.relaxation` (`A2`) once
`E0a` collapses its ends (`A3`), `E0c` is `E0b` halved, `E0d` is `Cheeger.two_mul_energy`, and `E0e`
is `E0a` on the intrinsic law transported as in the absolutely continuous corollary.
For singular laws the substantive step is **density of smooth tests in the local-slope energy**, i.e. the reverse inequality
`SmoothGradient.relaxation ≤ LocalSlope.relaxation` without a density (`C6`).

## The route

**A — the sandwich** (`Energy/Euclidean/Slope/Comparison.lean`).  A smooth test's asymptotic
Lipschitz constant is its gradient norm at every point (`A1`; lower bound from the one-moving-point
slope, upper bound by the mean value inequality on small balls), so smooth tests lie in the
asymptotic-Lipschitz test class with the same energy and `A2` follows by relaxing over the larger
class.  `A3` records the collapse.

**B — recovery for globally Lipschitz tests** (`Energy/Euclidean/Slope/Recovery.lean`).  Mollifying a
globally `K`-Lipschitz `g` at radius `2R` with the repository's kernel: the mollifier at `x` sees `g`
only within `2R`, so on the ball of radius `δ` it inherits the Lipschitz constant of `g` on the ball
of radius `δ + 2R`, whence `limsup_{R→0} ‖∇(g ⋆ ρ_R)(x)‖ ≤ Lip_a g (x)` pointwise; the global
constant `K` bounds the integrand uniformly, so reverse Fatou applies and
`SmoothGradient.relaxation ν (toLp g) ≤ AsymptoticLipschitz.energy ν g` (`B1`).  **A uniform
mollification radius is genuinely insufficient for general tests**: with `ν = Σ 2⁻ⁿ δ_n` and narrow
spikes of slope `4ⁿ` at distance `1/n` from the integers, `Lip_a g = 0` on the support but
`∫ Lip(g, B(·, r))² dν = ∞` for every fixed `r`.  Hence the reduction tools: a locally Lipschitz
function times a bounded globally Lipschitz one is locally Lipschitz (`B2`), locally Lipschitz and
vanishing outside a ball implies globally Lipschitz (`B3`), and the one-moving-point Leibniz bounds
for both slopes (`B4`, `B5`).

**C — density** (`Energy/Euclidean/Slope/Density.lean`).  `C1`: the local slope of a continuous
function is Borel, as the countable infimum over radii `1/(m+1)` of the lower-semicontinuous secant
suprema.  `C2`, the McShane patch: for a globally `L`-Lipschitz `f` and `α, δ > 0`, stratify the slope
into bands of width `α`, cut each band into small balls of a dense sequence and disjoint the family
into a Borel partition on which `f` is Lipschitz with constant within `2α` of its slope; inner
regularity gives finitely many disjoint compact cores carrying all but `δ` of the mass; extend `f` from
each core by McShane with the core's constant and glue with linear cutoffs at a scale below the
separation of the cores.  The patch `F` is globally Lipschitz with a constant `9L + 8α`
independent of `δ`, equals `f` on the cores, and its asymptotic Lipschitz constant on the cores is
within `2α` of the local slope of `f`.  `C4`: with `α = δ = 1/(n+1)`, the patches converge to `g` in
`L²(ν)`, `B1` bounds the relaxation at each patch by its asymptotic-Lipschitz energy, which is at most
`(1 + 4α) · LocalSlope.energy ν g + 4α + 4α² + M² δ` (no measurability of the asymptotic constant
needed: bound by a measurable majorant), and lower semicontinuity of the relaxation finishes.  `C5`:
a general admissible test is cut off with `scaled (n+1)`; `B2`, `B3` make the cutoff globally
Lipschitz, dominated convergence gives `L²` convergence, `B5` and Young's inequality
`(a + b)² ≤ (1+θ)a² + (1+θ⁻¹)b²` bound its energy by `(1+θ) · energy g + (1+θ⁻¹) N_n² ‖g‖₂²`; let
`n → ∞` then `θ → 0`.  `C6` is `C5` fed to `LocalSlope.le_relaxation_of_lowerSemicontinuous`.
Closest literature: S. Eriksson-Bique, *Density of Lipschitz functions in energy*, Calc. Var. PDE 62
(2023), Art. 60, Thm 1.1 (general metric measure spaces), of which this Euclidean argument is an
elementary special case; Ambrosio–Gigli–Savaré, Rev. Mat. Iberoam. 29 (2013) §8.3 reaches the same
conclusion through Hopf–Lax.

## What is already there

`LocalSlope.relaxation_le_asymptoticLipschitz`, `SmoothGradient.localSlope_relaxation_le`,
`LocalSlope.le_relaxation_of_lowerSemicontinuous`, `lowerSemicontinuous_relaxation`,
`Cheeger.two_mul_energy`, the mollifier (`kernel`, `mollify`, `hasFDerivAt_mollify`,
`norm_mollify_sub_le`), the smooth cutoff `scaled` with its Lipschitz bound,
`tendsto_eLpNorm_zero_of_dominated`, the certified absolutely continuous scope.  Mathlib has McShane
(`LipschitzOnWith.extend_real`), `Disjoint.exists_thickenings`, inner regularity
(`MeasurableSet.exists_isCompact_sdiff_lt`), reverse Fatou (`limsup_lintegral_le`), as the approximation and integration tools used by the route.
-/

noncomputable section

open MeasureTheory Filter Topology Set FunctionalInequalities FunctionalInequalities.Energy
open scoped ENNReal NNReal ContDiff

/-! ### Proved inputs, for reference -/

#check @FunctionalInequalities.Energy.LocalSlope.relaxation_le_asymptoticLipschitz
#check @FunctionalInequalities.Energy.SmoothGradient.localSlope_relaxation_le
#check @FunctionalInequalities.Energy.LocalSlope.le_relaxation_of_lowerSemicontinuous
#check @FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous
#check @FunctionalInequalities.Energy.Cheeger.two_mul_energy

/-! ### E0a–E0e — the identification contracts, verbatim -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V), SmoothGradient.relaxation ν = LocalSlope.relaxation ν)

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V), LocalSlope.relaxation ν = AsymptoticLipschitz.relaxation ν)

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V), Cheeger.energy ν = Cheeger.ofAsymptoticLipschitz ν)

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
    SmoothGradient.relaxation ν f = 2 * Cheeger.energy ν f)

#check (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
    (μ : ProbabilityMeasure E) (f : Lp ℝ 2 (μ : Measure E)),
    SmoothGradient.Intrinsic.energy μ f = 2 * Cheeger.Intrinsic.energy μ f)

/-! ### A1 — a smooth test's asymptotic Lipschitz constant is its gradient norm, pointwise -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} (f : SmoothGradient.Test ν) (x : V),
    AsymptoticLipschitz.apply f.toFun x = ‖gradient f.toFun x‖ₑ)

/-! ### A2 — the third side of the sandwich, for every law -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
    AsymptoticLipschitz.relaxation ν f ≤ SmoothGradient.relaxation ν f)

/-! ### A3 — the collapse: `E0a` implies `E0b` -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V), SmoothGradient.relaxation ν = LocalSlope.relaxation ν →
    LocalSlope.relaxation ν = AsymptoticLipschitz.relaxation ν)

/-! ### B1 — smooth recovery of a globally Lipschitz test -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {g : V → ℝ} {K : ℝ≥0}, LipschitzWith K g →
    ∀ (hg : MemLp g 2 (ν : Measure V)),
    SmoothGradient.relaxation ν (hg.toLp g) ≤ AsymptoticLipschitz.energy ν g)

/-! ### B2 — locally Lipschitz times bounded globally Lipschitz is locally Lipschitz -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {g h : V → ℝ} {N : ℝ≥0}, LocallyLipschitz g → LipschitzWith N h → (∀ x, |h x| ≤ 1) →
    LocallyLipschitz (fun x => g x * h x))

/-! ### B3 — locally Lipschitz and vanishing outside a ball is globally Lipschitz -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {g : V → ℝ} {R : ℝ}, LocallyLipschitz g → (∀ x, R ≤ ‖x‖ → g x = 0) →
    ∃ K : ℝ≥0, LipschitzWith K g)

/-! ### B4, B5 — the one-moving-point Leibniz bounds for the two slopes -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g h : V → ℝ) {N : ℝ≥0}, LipschitzWith N h → (∀ y, |h y| ≤ 1) → ∀ x : V,
    AsymptoticLipschitz.apply (fun y => g y * h y) x ≤
      AsymptoticLipschitz.apply g x + ENNReal.ofReal |g x| * N)

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g h : V → ℝ) {N : ℝ≥0}, LipschitzWith N h → (∀ y, |h y| ≤ 1) → ∀ x : V,
    LocalSlope.apply (fun y => g y * h y) x ≤ LocalSlope.apply g x + ENNReal.ofReal |g x| * N)

/-! ### C1 — the local slope of a continuous function is Borel -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {f : V → ℝ}, Continuous f → Measurable (LocalSlope.apply f))

/-! ### C2 — the McShane patch

For a globally `L`-Lipschitz `f` and `α, δ > 0`: a globally Lipschitz `F` with constant `9L + 8α`
(independent of `δ`), equal to `f` on a Borel set `K` of co-mass at most `δ`, whose asymptotic
Lipschitz constant on `K` is within `2α` of the local slope of `f`. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {f : V → ℝ} {L : ℝ≥0}, LipschitzWith L f →
    ∀ {α : ℝ≥0}, 0 < α → ∀ {δ : ℝ≥0∞}, 0 < δ →
    ∃ (F : V → ℝ) (K : Set V), LipschitzWith (9 * L + 8 * α) F ∧ MeasurableSet K ∧
      (ν : Measure V) Kᶜ ≤ δ ∧ (∀ x ∈ K, F x = f x) ∧
      ∀ x ∈ K, AsymptoticLipschitz.apply F x ≤ LocalSlope.apply f x + 2 * (α : ℝ≥0∞))

/-! ### C4 — density for globally Lipschitz tests -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {g : V → ℝ} {L : ℝ≥0}, LipschitzWith L g →
    ∀ (hg : MemLp g 2 (ν : Measure V)),
    SmoothGradient.relaxation ν (hg.toLp g) ≤ LocalSlope.energy ν g)

/-! ### C5 — density for every admissible local-slope test -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) {g : V → ℝ} (hg : LocalSlope.Admissible ν g),
    SmoothGradient.relaxation ν (hg.memLp_two.toLp g) ≤ LocalSlope.energy ν g)

/-! ### C6 — the reverse inequality, for every law -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    (ν : ProbabilityMeasure V) (f : Lp ℝ 2 (ν : Measure V)),
    SmoothGradient.relaxation ν f ≤ LocalSlope.relaxation ν f)

/-! ### D1 — diagnostic: the uniform-radius approach cannot work in general

Stated as the existence, on the line, of a probability law and a bounded locally Lipschitz `g` of
finite local-slope energy whose asymptotic-Lipschitz constant vanishes on the support while, for every
radius `r > 0`, the ball Lipschitz constant `Lip(g, B(·, r))` has infinite square integral.  Recorded
for the route record; proving it is not an obligation. -/

#check (∃ (ν : ProbabilityMeasure ℝ) (g : ℝ → ℝ), LocallyLipschitz g ∧
    LocalSlope.energy ν g = 0 ∧
    ∀ r : ℝ, 0 < r →
      ∫⁻ x, (⨆ (y : ℝ) (_ : dist y x < r) (z : ℝ) (_ : dist z x < r),
        ENNReal.ofReal (dist (g y) (g z) / dist y z)) ^ 2 ∂(ν : Measure ℝ) = ⊤)
