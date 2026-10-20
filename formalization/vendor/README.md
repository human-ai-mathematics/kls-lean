# Vendored stochastic calculus

This directory holds third-party Lean libraries compiled as part of this package, so that the
Eldan localization of Bizeul–Klartag–Lehec Theorem 4.1 can build on an existing Brownian motion,
Itô integral, Itô formula and strong SDE solution instead of a new stochastic-calculus library.
The libraries are infrastructure only: no SDE, Itô, martingale or BKL statement of this project is
proved by adding them.

## Sources and pins

| Library (Lean root) | Upstream | Commit | Upstream toolchain | License | Modules here |
|---|---|---|---|---|---|
| `LevyStochCalc` | [cgarryZA/LevyStochCalc](https://github.com/cgarryZA/LevyStochCalc) | `984dbf0b790031eac05d56fe5a84b65e15e1e932` (2026-09-30) | v4.32.0, Mathlib `81a5d25` | Apache-2.0 | 196 |
| `BrownianMotion` | [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) | `a7ad7af662044313bc80a7c0756360fb3745f931` | v4.33.0-rc1, Mathlib `0434c03` | Apache-2.0 | 42 |
| `KolmogorovExtension4` | [RemyDegenne/kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4) | `f33cbc388e5d444606dffa7eec507a26b62c15bb` | v4.32.0 | Apache-2.0 | 3 |
| `MathFin` | [raphaelrrcoelho/formal-mathfin](https://github.com/raphaelrrcoelho/formal-mathfin) | `784a8311f75a1519a23717856df9982bd6a9a370` | v4.32.0 | Apache-2.0 | 1 |

KolmogorovExtension4 and MathFin retain LevyStochCalc's original dependency revisions.
BrownianMotion is an explicit override of its original `4d52fa7` dependency, synchronized
to the corrected regularization interfaces. BrownianMotion itself pins KolmogorovExtension4
to `7d76e18`; this package retains the tested `f33cbc3` revision. All libraries use this
package's unchanged Lean/Mathlib v4.33.0. The lock records these original upstream manifest
pins separately from the effective vendored commits; it does not claim that they agree.

Each subdirectory keeps the upstream `LICENSE`, and
every source file keeps its upstream copyright header. Public module paths and declaration names are
the upstream ones; the selected private helpers are documented below.

**Selection.** The 196 LevyStochCalc modules are those used by the stochastic-localization route of
the independent KLS500 development ([HongruZhao/KLS500](https://github.com/HongruZhao/KLS500) at
`c1a5099`): multidimensional Brownian motion, the L² Itô integral and its completion, vector Itô
processes and the Itô formula, cutoffs and locality, Picard strong solutions, exit times and the
continuous Doob inequality. The initial dependency selection was their import closure at LevyStochCalc's pinned revisions.
The BrownianMotion synchronization retains the original 39 modules and adds the required
`Auxiliary.Analysis`, `Auxiliary.Indistinguishable` and `Auxiliary.Jensen` modules.
The selected closure omits `StochasticIntegral.UniformIntegrable`, which carries unrelated
upstream placeholders. Three proved stability helpers from that file are private helpers in
its regularization consumer; their upstream proof bodies are retained in `port.patch`.
No KLS500 source is included; its own port targets a different toolchain.

## Local changes

The sources are ported to this package's Lean v4.33.0 and Mathlib `db584cd` (tag v4.33.0).
Thirteen files differ from their respective pinned upstream sources:
[`port.patch`](port.patch) is the exact unified diff and applies with `patch -p1` from this
directory. Modification notices identify every changed source. The BrownianMotion update
changes its upstream API; existing project and LevyStochCalc public contracts are retained.
No option, axiom or `sorry` is added by the local adaptations.

| File | Change |
|---|---|
| `BrownianMotion/Auxiliary/Algebra.lean` | removed `Set.indicator_apply_apply`, now provided by Mathlib with the same equation |
| `BrownianMotion/StochasticIntegral/Quasimartingale/CadlagModification.lean` | use Jensen and three proved private stability helpers instead of the broad UniformIntegrable import |
| `KolmogorovExtension4/KolmogorovExtension.lean` | a `rw` replaced by `exact` |
| `LevyStochCalc/Brownian/{Martingale, MartingaleCondExp, ItoSimpleMoments, ItoL2CompletionIncrement}.lean` | Gaussian instance on `{r // 0 ≤ r}` arguments: Mathlib's `memLp_id_gaussianReal'` |
| `LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean` | a `rw` that matched the wrong occurrence |
| `LevyStochCalc/Brownian/SimplePredictableRefineAppend.lean` | a `simp only` that no longer makes progress |
| `LevyStochCalc/Brownian/{ItoAlgebraAssociativity, ItoPullOut, CrossVariation}.lean` | stale `Decidable` instance in `if` after `simp only`; goal restated with `show` |
| `LevyStochCalc/Martingale/CadlagModification.lean` | migrate to the upstream `rightContModifReal` / `cadlagModifReal` names, retaining the existing hypotheses |

Each library compiles with the upstream package options `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3` (see `../lakefile.toml`).

## Upstream holes

The selected vendored closure has no accepted upstream holes. `VENDOR_UPSTREAM_SORRY` is
empty: the vendor and project-local declaration audits both permit only `propext`,
`Classical.choice` and `Quot.sound`, including private and generated declarations. Every new
`sorryAx` dependency fails verification. This concerns the selected files, not the entire
upstream repositories.

The former BrownianMotion pin had four placeholders affecting five declarations. The valid
martingale-to-quasimartingale result is now proved upstream. The overstrong general uniform
integrability interface was removed; expectation-based modification results were replaced by
submartingale results with a right-continuous filtration. The martingale modification also
explicitly requires a right-continuous filtration. No proof of the old stronger statements is
claimed. The [boundary client](../../research/audits/StochasticCalculus/Regularization.lean)
checks the corrected contracts, the retained LevyStochCalc client, absence of the obsolete
interfaces and exclusion of the unrelated UniformIntegrable module.

## Verification and updates

The four directories are `lean_lib`s of this package (`../lakefile.toml`), not a separate Lake
package: they share its toolchain, Mathlib pin and build directory. `research/verify.py` treats
their files as local sources: they are part of the source snapshot, built by the default
`lake build`, replayed by `leanchecker` and covered by the vendor axiom gate.

## Provenance lock

[`vendor-lock.json`](vendor-lock.json) records, for every file under the four directories, its
upstream path at the pinned commit, the upstream SHA-256 and Git blob id, the vendored SHA-256,
the module name and whether `port.patch` changes it, together with the SHA-256 of `port.patch`
and the pins. Schema 2 separately binds the recorded upstream dependency revisions, making
the tested overrides explicit. `python3 research/vendor_lock.py` checks it offline: the file inventory equals the
lock (no extra, missing or symlinked file), every vendored hash matches, the patched files are
exactly those whose hashes differ, and reverse-applying `port.patch` strictly (no fuzz or offset)
reproduces each upstream hash and blob id, the unpatched files being the upstream bytes. The full
`research/verify.py` runs the same check as its `vendor-provenance-lock` gate; the Lean-only CI
mode does not. `python3 research/vendor_lock.py --fetch` also compares every locked blob with the
upstream repositories at the pinned commits, and the recorded upstream dependency manifests
and each `lean-toolchain` with the lock (network access, not part of `verify.py`).

To update a library, change its pin here and in `PINS` of `research/vendor_lock.py`, re-copy the
modules from the new upstream revision, port and record the new diff in `port.patch`, keep the
modification notices, regenerate the lock with `python3 research/vendor_lock.py --write --fetch`,
and rerun the full verification. Record dependency overrides and the selected proved declaration closure explicitly, retain
original authorship, and check affected public contracts. Do not edit these files for style;
local changes serve toolchain compatibility, the documented proved dependency selection and
migration of existing consumers.
