# Vendored stochastic calculus

This directory holds third-party Lean libraries compiled as part of this package, so that the
Eldan localization of Bizeul–Klartag–Lehec Theorem 4.1 can build on an existing Brownian motion,
Itô integral, Itô formula and strong SDE solution instead of a new stochastic-calculus library.
The libraries are infrastructure only: no SDE, Itô, martingale or BKL statement of this project is
proved by adding them. Decision record:
[2026-10-12 LevyStochCalc adoption](../../research/decisions/2026-10-12-levystochcalc-adoption.md).

## Sources and pins

| Library (Lean root) | Upstream | Commit | Upstream toolchain | License | Modules here |
|---|---|---|---|---|---|
| `LevyStochCalc` | [cgarryZA/LevyStochCalc](https://github.com/cgarryZA/LevyStochCalc) | `984dbf0b790031eac05d56fe5a84b65e15e1e932` (2026-09-30) | v4.32.0, Mathlib `81a5d25` | Apache-2.0 | 196 |
| `BrownianMotion` | [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) | `4d52fa776130a29d4ad7d6eda2035a919c0b4696` | v4.32.0 | Apache-2.0 | 39 |
| `KolmogorovExtension4` | [RemyDegenne/kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4) | `f33cbc388e5d444606dffa7eec507a26b62c15bb` | v4.32.0 | Apache-2.0 | 3 |
| `MathFin` | [raphaelrrcoelho/formal-mathfin](https://github.com/raphaelrrcoelho/formal-mathfin) | `784a8311f75a1519a23717856df9982bd6a9a370` | v4.32.0 | Apache-2.0 | 1 |

The dependency commits are the exact revisions LevyStochCalc's `lake-manifest.json` pins. Each subdirectory keeps the upstream `LICENSE`, and
every source file keeps its upstream copyright header. The module paths and declaration names are
the upstream ones.

**Selection.** The 196 LevyStochCalc modules are those used by the stochastic-localization route of
the independent KLS500 development ([HongruZhao/KLS500](https://github.com/HongruZhao/KLS500) at
`c1a5099`): multidimensional Brownian motion, the L² Itô integral and its completion, vector Itô
processes and the Itô formula, cutoffs and locality, Picard strong solutions, exit times and the
continuous Doob inequality. The other three libraries contribute exactly the import closure of
those modules at the pinned revisions; seven further BrownianMotion files used by KLS500 itself are
not imported by LevyStochCalc and are omitted. No KLS500 source is included; its own port targets a different toolchain.

## Local changes

The sources were ported to this package's Lean v4.33.0 and Mathlib `db584cd` (tag v4.33.0). Twelve
files changed, by +29/−35 proof lines plus a two-line modification notice at the top of each:
[`port.patch`](port.patch) is the exact unified diff against the pinned upstream files and applies
with `patch -p1` from this directory. No declaration was renamed or restated, no option or axiom
was added, and no `sorry` was introduced.

| File | Change |
|---|---|
| `BrownianMotion/Auxiliary/Algebra.lean` | removed `Set.indicator_apply_apply`, now provided by Mathlib with the same equation |
| `BrownianMotion/StochasticIntegral/SimpleProcess.lean` | elaboration of one proof term |
| `KolmogorovExtension4/KolmogorovExtension.lean` | a `rw` replaced by `exact` |
| `LevyStochCalc/Brownian/{Martingale, MartingaleCondExp, ItoSimpleMoments, ItoL2CompletionIncrement}.lean` | Gaussian instance on `{r // 0 ≤ r}` arguments: Mathlib's `memLp_id_gaussianReal'` |
| `LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean` | a `rw` that matched the wrong occurrence |
| `LevyStochCalc/Brownian/SimplePredictableRefineAppend.lean` | a `simp only` that no longer makes progress |
| `LevyStochCalc/Brownian/{ItoAlgebraAssociativity, ItoPullOut, CrossVariation}.lean` | stale `Decidable` instance in `if` after `simp only`; goal restated with `show` |

Each library compiles with the upstream package options `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3` (see `../lakefile.toml`).

## Upstream holes

The pinned BrownianMotion revision contains four `sorry`s in
`BrownianMotion/StochasticIntegral/Quasimartingale/CadlagModification.lean`, on which exactly these
declarations depend:

- `ProbabilityTheory.uniformIntegrable_of_countable`
- `ProbabilityTheory.rightContModif_ae_eq_of_integral_tendsto`
- `ProbabilityTheory.cadlagModif_ae_eq_of_continuousWithinAt_integral`
- `MeasureTheory.Martingale.isRealQuasimartingale`
- `MeasureTheory.Martingale.cadlagModif_ae_eq`

No other vendored declaration uses them. `research/verify.py` lists them in
`VENDOR_UPSTREAM_SORRY` and its `vendor-axiom-audit` gate checks every vendored declaration: each
listed name must be found among the audited vendored declarations themselves (not a same-named
import) and still depend on `sorryAx`, and every other vendored declaration may depend only on
`propext`, `Classical.choice` and `Quot.sound`. A new hole, a new user of a listed declaration, or
an upstream fix therefore fails verification until this list is reviewed. The allowlist applies to
this gate only: the `local-declaration-audit` gate, run in both the full and the `--lean-only`
verification, checks every project-local declaration (public, private and generated, registered
or not), `KLS.kls` included and with no exclusion, for the three standard axioms, so no
local result can depend on these holes.

## Verification and updates

The four directories are `lean_lib`s of this package (`../lakefile.toml`), not a separate Lake
package: they share its toolchain, Mathlib pin and build directory. `research/verify.py` treats
their files as local sources: they are part of the source snapshot, built by the default
`lake build`, replayed by `leanchecker` and covered by the vendor axiom gate.

## Provenance lock

[`vendor-lock.json`](vendor-lock.json) records, for every file under the four directories, its
upstream path at the pinned commit, the upstream SHA-256 and Git blob id, the vendored SHA-256,
the module name and whether `port.patch` changes it, together with the SHA-256 of `port.patch`
and the pins. `python3 research/vendor_lock.py` checks it offline: the file inventory equals the
lock (no extra, missing or symlinked file), every vendored hash matches, the patched files are
exactly those whose hashes differ, and reverse-applying `port.patch` strictly (no fuzz or offset)
reproduces each upstream hash and blob id, the unpatched files being the upstream bytes. The full
`research/verify.py` runs the same check as its `vendor-provenance-lock` gate; the Lean-only CI
mode does not. `python3 research/vendor_lock.py --fetch` also compares every locked blob with the
upstream repositories at the pinned commits, and the pins of LevyStochCalc's `lake-manifest.json`
and each `lean-toolchain` with the lock (network access, not part of `verify.py`).

To update a library, change its pin here and in `PINS` of `research/vendor_lock.py`, re-copy the
modules from the new upstream revision, port and record the new diff in `port.patch`, keep the
modification notices, regenerate the lock with `python3 research/vendor_lock.py --write --fetch`,
and rerun the full verification. Do not edit these files for style; changes are limited to what the toolchain requires.
