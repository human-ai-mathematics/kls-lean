# 2026-09-12 — Fix replay build scope in clean CI and audit the mathematical routes

The owner requested investigation of remote failures, an audit of the mathematical routes, and a commit of the current changes. This round includes prior unsynced research synchronization.

## Reasons for remote failure

The `d2f136f6633ddd2455b838a36732502978b37a56` was pushed to `origin/main`; this was not a commit or push failure.
[Lean certification running 34695539602](https://github.com/human-ai-mathematics/kls-lean/actions/runs/34695539602)
Python tests, default Lake builds, statement snapshots, and declaration audits have been executed; subsequently, an error occurred when preparing to replay inputs:

```text
Current source formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean has no built module
```

By default `lake build` only covers the root module and import closure of the library; WIP remaining in the source code but not formally imported via entry points does not need to be built.
The validator, however, requires replaying all current local source code. The development machine had previously built WIP separately, and existing cache masked this inconsistency.
The Blueprint CI succeeded for the same commit; the recent upstream check by Nicolas in this round also succeeded.

## Fix

`research/verify.py` uses the same `replay_sources` mapping to determine build and replay scope,
explicitly building all current modules to be replayed with `lake build +Module` before preparing replay inputs.
This checks that existing builds are current and covers modules absent from the default import closure in clean CI; it does not depend on `.olean` files happening to exist.
Retain default build gates, missing module failure checks, orphaned product filtering, and strict replay coverage set comparisons.
No modifications to default library entry points or certificate imports, no inclusion of WIP in certification closure, and no allowance for certificate usage of `sorryAx`.

New real Lake temporary project regression tests in cache-free environment proved:
Default build omits WIP not imported → old replay preparation fails → explicit scope build succeeds → formal root module still does not depend `sorryAx`.
Fixture contains both deleted paths and Dev scratch paths, which cannot enter replay scope.
All temporary builds and verification logs are not submitted.

## Mathematical Route Verification

This is a review of the current statement, normalization, dependencies, and upstream evidence boundaries, not a new proof of every upstream informal argument.
No new cyclic dependencies, treating open assumptions as conclusions, or mixing constant conventions, have been detected in this round of synchronization.
The objects under review are the Blueprint route chapter, route-composition, tasks, the current certificate, and the original records from fixed upstream sources.

| route | interface sufficient to advance to KLS | boundaries still requiring clarification |
| --- | --- | --- |
| conditional fiber | `Var ≤ C D` with certified `D ≤ 4 E` given to `C_P ≤ 4 C`, then affine/isotropic reduction | `C` lies outside dimension and measure quantifiers; the same frame is independent of test functions; covers the entire finite form domain. Quadratic polynomial computation cannot yield full `L²` conclusion |
| spectral localization | conditional sufficiency of universal-time full-damping occupation | Time and constant must consistently pass through regularization. The `log² n` window under Letwin input still depends on dimension; the universal-time gate cannot be closed |
| CMH recovery | A suitable `W₂` recovery sequence with uniform CMH control, via lower semicontinuity and reduction to KLS | Requires control of the full form and degenerate affine support; the weak column equation cannot serve as a strong operator domain equation; cone models, linear sector do not provide a uniform envelope |
| Eldan | tight-prefix absorption estimate and Riccati/survival/ geometric comparison chain | regular split class's screened supply does not cover all tangent sets; the refuted weighted package cannot be recovered into valid input |

A common geometric bridge has not yet been fully formalized in Lean: relative perimeter recovery, Cheeger infimum, and comparison of Cheeger–Buser bilateral constants.
The certified `E_can = 2 Ch` is energy identification, not a substitute for comparison of geometric isoperimetric and Poincaré constants.
The roadmap's lack of dependency cycles is merely a structural fact, insufficient to prove upstream mathematics is correct; the open roadmap still requires new mathematical input.

New literature follows `1/4 ≤ ψ²/C_P ≤ π`: Letwin's `ψ_n = O((log n)^(1/4))`
corresponds to `C_P = O(sqrt(log n))`; thin-shell itself still does not constitute dimension-free KLS proof.
Formal Lean certification consists of 24, with current WIP direct holes being 24; no changes to mathematical statements or proofs have been made in this round.

## Verification and commit boundary

Run the regression tests and the full `research/verify.py`, then commit after they pass. The final
verification receipt is referenced by `build/verification/latest.json` and must match the source
snapshot. A claim that remote CI passed requires evidence from an actual run after pushing;
local validation cannot replace it. The request in this round authorized a commit, not a push,
so only a local commit is created.
