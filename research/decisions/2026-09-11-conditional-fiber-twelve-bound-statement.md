# 2026-09-11 — `cor:conditional-fiber-twelve-bound`: Infrastructure Verification and Statement Skeleton (Only one sorry)

## Decision

- In atlas order, after `lem:conditional-fiber-energy-comparison` registration, this inference becomes verifiable by `blocked`. Verification conclusion:
  Infrastructure **missing** (specific gaps see below), so under the statement-only process, only the statement skeleton is written, with no proof search.
- New file `formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean` (namespace
  `FunctionalInequalities.KLS.LogConcave`, log-concave inference invoked by the `hμ.` notation). **Only one `sorry`**:
  `ae_conditionalFiber_logConcave`. The other five are direct compositions of already-certified inputs (proof bodies consisting of a few lines of applications), compiled successfully.
- Not registered (not included in `FunctionalInequalities.lean` aggregation import, lakefile `Solutions` root, ledger, `CERTIFICATES`),
  Blueprint's `\lean{}`/`\leanok` are omitted; `tasks.json` this node is changed to `missing` and the gap and evidence hash are recorded.
  Not `git commit`, not `git push`.

## Lean Statement

```
theorem ae_conditionalFiber_logConcave (hμ : LogConcave μ) (hρ : Admissible μ ρ)
    (m : Measure E) [Measure.IsAddHaarMeasure m] (hac : (μ : Measure E) ≪ m) :
    ∀ᵐ b ∂baseLaw μ ρ, LogConcave (⟨kernel μ ρ b, inferInstance⟩ : ProbabilityMeasure ℝ)   -- sorry

theorem conditionalFiber_fiberBound_four … : FiberBound μ ρ 4
theorem conditionalFiber_energy_le_four_mul … (hf : Energy.LocalSlope.Admissible μ f) :
    energy μ ρ f ≤ 4 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤
theorem conditionalFiber_literatureConstant_le_four_mul … (hform : ∀ f ∈ domain μ ρ, ↑(L2.variance μ f) ≤ ↑C * form μ ρ f) :
    Poincare.LocalSlope.Intrinsic.constant μ ≤ 4 * ↑C
theorem conditionalFiber_energy_le_twelve_mul_of_four … : energy μ ρ f ≤ 12 * Energy.LocalSlope.energy μ f ∧ energy μ ρ f ≠ ⊤
theorem conditionalFiber_literatureConstant_le_twelve_mul_of_four … : Poincare.LocalSlope.Intrinsic.constant μ ≤ 12 * ↑C
```

`hμ`, `hρ` and `m`/`hac` follow the same parameter conventions as the comparison lemma; `κ` no longer appears, and the constants `4`/`12` are included in the names (`research/naming.md`:
"the constant 4 is included in the name, without additional parameters", "versions derived from 4 are annotated with the `_of_four` suffix").

## Sentence-by-sentence alignment (Blueprint ↔ Lean)

| Blueprint | Lean | Description |
|---|---|---|
| "For a full-dimensional log-concave law with finite second moment" | `hμ : LogConcave μ`, `hac : μ ≪ m` (Haar), second moment from `hρ : Admissible μ ρ` | "full-dimensional" is interpreted as absolutely continuous with respect to Haar (log-concave laws are equivalent to affine support being the entire space), matching the comparison lemma |
| "$\mathcal D_{\mu,\rho}(f)\le12\int|\nabla f|^2\,d\mu$ on the literature test domain" | `conditionalFiber_energy_le_twelve_mul_of_four` (`Energy.LocalSlope.energy` under `hac` equals `∫⁻ ‖∇f‖²`) | Uniform; Lean provides a stronger `4` version |
| "A finite form-gap bound $C$ therefore gives $\CPLit(\mu)\le12C$" | `conditionalFiber_literatureConstant_le_twelve_mul_of_four` | Consistent; Lean also provides `4C` |
| Proof: "conditional densities proportional to $t\mapsto\rho_\mu(z+t\theta)$ … These densities are log-concave. The remaining fibers are null" | `ae_conditionalFiber_logConcave` (**sorry**) | This is the sole analytic content |
| Proof: "finite second moment gives finite conditional variances almost everywhere" | Second field of `Nondegenerate` + `ConditionalFiber.ae_memLp_id` (`FiberBound` constrains only nondegenerate fibers, so no separate proof is needed) | Already included |
| Proof: "Apply thm:one-dimensional-logconcave-poincare and then the preceding comparison with κ=12" | `conditionalFiber_fiberBound_four` (using `hν.localSlope_constant_le_four_evariance`) + `energy_le_of_fiberBound`/`literatureConstant_le_of_fiberBound` | Consistent, and input is already proven 4 |
| "The same argument accepts any independently established smaller universal input" | Already demonstrated by parameterized `FiberBound μ ρ κ` | Consistent |

Blueprint inference is still written as `12`; Lean uses `4` as primary and `12` for inference, with Lean being stronger than Blueprint. Should the Blueprint statement be changed to `4C`
(the enhanced version previewed in the same-day `thm:one-dimensional-logconcave-poincare` record) is a statement change, left for the owner to decide; this change is not made.

## Infrastructure Gap (`tasks.json`: `missing`)

1. **One-dimensional Brunn–Minkowski / Prékopa–Leindler.** A probability measure on the real axis with log-concave Lebesgue density (`IsBorellDensity`) is
   Compact set log-concave (`KLS.LogConcave`). The pinned Mathlib lacks Brunn–Minkowski or Prékopa–Leindler ((`grep`) to the "Minkowski"
   All are gauge functionals, `Analysis/Convex/Gauge.lean`; the warehouse has only the reverse direction `LogConcave.exists_lineDensity`.
2. **Explicit decomposition along a line.** For each direction θ, the Haar measure along the orthogonal decomposition `E ≅ θ^⊥ × ℝθ` via Fubini's splitting (Mathlib has a fixed orthogonal basis coordinate)
   Measure preservation `OrthonormalBasis.measurePreserving_measurableEquiv`, without splitting depending on θ); normalize slice density
   Turn `t ↦ ρ_μ(z+tθ)` into a Markov kernel on the fixed product base `Direction E × E`; prove `baseLaw ⊗ₘ sliceKernel = jointLaw`.
   After being equal to the selected kernel a.e. given by the existing `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`
   (`ConditionalFiber.energyWithKernel_eq_energy` already used the same pattern).
3. **a.e. non-degenerate.** The slice variance is positive if the Borell density is positive within the support (`BorellRepresentation.pos_of_mem_interior_support`)
   Restricted to a line; finite second-order moment has been given by `ae_memLp_id`.

Possible routes around 1: directly prove "the condition law of log-concave laws is log-concave" (by direct definition for compact sets, without density), which still requires a Prékopa–Leindler-type argument; or prove the one-dimensional fact "log-concave density ⇒ log-concave on compact sets" using one-dimensional Brunn–Minkowski (`vol(A+B) ≥ vol(A)+vol(B)`, Mathlib also lacks this). Both are new work at the Mathlib level.

## Compilation

```
lake env lean FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean
```

Exactly 1 `declaration uses 'sorry'` (`ae_conditionalFiber_logConcave`), no other warnings.

## Not done / Future work

- Unproven `ae_conditionalFiber_logConcave`; not registered; Blueprint statement not modified (trade-off between `12` and `4C` left to owner).
- If gaps 1–3 are closed and proven: add this document to the aggregated import, issue `solutions/CorConditionalFiberTwelveBound.lean` certificate,
  ledger/`CERTIFICATES`/route sidecar/Blueprint `\lean{}` synchronized; at that time, the Blueprint inference block may be simultaneously changed to `4C`.
