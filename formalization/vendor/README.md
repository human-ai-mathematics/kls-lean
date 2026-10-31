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
package's Lean/Mathlib v4.35.0. The lock records these original upstream manifest
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

The sources are ported to this package's Lean v4.35.0 and Mathlib `56a0058` (tag v4.35.0) and to
the Lean module system. 219 files differ from their respective pinned upstream sources
(LevyStochCalc 196, BrownianMotion 20, KolmogorovExtension4 2, MathFin 1):
[`port.patch`](port.patch) is the exact unified diff and applies with `patch -p1` from this
directory. Modification notices identify every changed source. The BrownianMotion update
changes its upstream API; existing project and LevyStochCalc public contracts are retained,
except for the individually listed Mathlib v4.35.0 adaptations below.
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
| 43 further files, listed by `patch.files` in `vendor-lock.json` | apply Lean v4.33.0's recommended replacements for deprecated set aliases and proof-local `haveI`/`letI` bindings; each file has a dated modification notice |
| all 196 LevyStochCalc sources | Lean module system: `module` header, every `import` made `public import`, `@[expose] public section` (BrownianMotion, KolmogorovExtension4 and MathFin are already modules upstream); dated 2026-10-31 notice |
| LevyStochCalc and the other libraries, files listed in `port.patch` | Lean/Mathlib v4.35.0 drop-in replacements of deprecated names (for example `if_pos` → `ite_eq_left`, `.lipschitz` → `.lipschitzWith`); dated 2026-10-31 notice |
| `LevyStochCalc/Brownian/SimplePredictableRefineCommon.lean` | `mergedIdxMap_left/_right`: the private existence lemma is passed through a fully stated `show … by exact …`, so the exposed definition body does not reference a private proof; the lemmas stay private |
| `LevyStochCalc/Brownian/ItoL2CompletionMaster.lean` | `masterApprox`: the private `master_tol_pos n` is passed through `show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ by exact …` (the same proposition; the chosen data are unchanged) |
| LevyStochCalc and BrownianMotion files listed in `port.patch` | Mathlib v4.35.0 `eLpNorm`/`MemLp` API: `MemLp f p μ` is `eLpNorm f p μ < ∞`, triangle inequalities no longer take measurability arguments, norm formulas take an `AEStronglyMeasurable` argument; proofs pass existing witnesses (proof-only) |
| `LevyStochCalc/Probability/DoobContinuous.lean` | `LevyStochCalc.Probability.eLpNorm_two_eq` gains `(hf : AEStronglyMeasurable f μ)` after `f`: its unconditional statement is false for the v4.35.0 `eLpNorm`, which is `∞` off the a.e.-strongly-measurable branch |
| `LevyStochCalc/Poisson/CompensatedDensityLimit.lean`, `LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean`, `LevyStochCalc/Brownian/ItoIntegrandComplete.lean` | for the same reason, exactly four further norm-formula helpers gain one `AEStronglyMeasurable` premise after the function: `Poisson.Compensated.eLpNorm_two_rpow_eq_lintegral_sq`, `Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq`, `Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq`, `Brownian.Ito.eLpNorm_sq_eq_lintegral`; every caller passes an existing witness. No other public premise changes |
| `LevyStochCalc/Brownian/ItoDensityUnbounded.lean`, `LevyStochCalc/Brownian/ItoAlgebraAssociativity.lean` | private helpers only: two now-unused measurability binders renamed `_hf`/`_hg`/`_hfn` (types and order kept); private `eLpNorm_mul_le_of_bound` gains `(hcg : AEStronglyMeasurable (fun ω => c ω * g ω) P)` |
| `BrownianMotion/Auxiliary/HasLaw.lean` | removed `hasLaw_map`, now provided by Mathlib (`Probability/HasLaw`) with the same statement; Mathlib orders the implicit binders `{𝓧}` before `{mΩ}` |
| `BrownianMotion/Auxiliary/LeftLimWithin.lean` | removed `tendsto_atBot_of_mapClusterPt`, now provided by Mathlib (`Topology/Order/LeftRightLim`, generated from its `atTop` counterpart) with the same hypotheses |
| `BrownianMotion/Auxiliary/Indistinguishable.lean` | the module body is identical to Mathlib v4.35.0 `Probability/Process/Indistinguishable` (apart from Mathlib's module docstring); it now only re-exports that module, so the predicate, its `≡ᵐ[P]` notation and its lemmas keep their names and statements under Mathlib ownership |
| `BrownianMotion/StochasticIntegral/Cadlag.lean`, `BrownianMotion/Auxiliary/StoppedProcess.lean`, `LevyStochCalc/Martingale/CadlagModification.lean` | Mathlib v4.35.0 defines `IsRightContinuous` and `IsCadlag` (same predicates, fields `isRightContinuous`/`tendsto_nhdsLT`); the 29 colliding vendored declarations are removed in favour of Mathlib's and the vendored projections `IsCadlag.right_continuous`/`left_limit` are gone; the 16 other declarations keep their names and statements; callers use the Mathlib field names. Differences include `const_smul`/`fun_const_smul` generalised from `ℝ` with `ContinuousSMul` to any `R` with `ContinuousConstSMul` (scalar before the witness), `continuous_comp` taking the witness first, and `IsRightContinuous` a `def` instead of an `abbrev`. The project's migration review records every declaration, old and new type and caller; `research/tests/fixtures/mathlib435-semantics/` checks the predicate equivalence and recovers every old signature from Mathlib |

The warning maintenance changes proof scripts only. It preserves upstream pins, public
declarations, mathematical assumptions and non-theorem definitions. It adds no linter
suppression. The exact filenames and edits are recorded in the lock and `port.patch`.

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
original authorship, and check affected public contracts. Keep local maintenance limited to
toolchain compatibility, the documented proved dependency selection, migration of existing
consumers and compiler-reported warnings. Warning fixes use the compiler's recommended
substitutions and retain declaration interfaces; broader style rewrites remain outside this port.
