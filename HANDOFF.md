# Current KLS handoff

Updated 2026-10-12. This file records the current state only. Earlier wording and detailed execution history are preserved verbatim in the [handoff baseline archive](research/decisions/2026-10-11-file-management-handoff-baseline.md). Dated records are historical context, not current task authorization. Exact theorem scopes, certificates and coverage remain in the [paper register](research/progress/LITERATURE.md) and [node register](research/progress/STATUS.md).

## State

- Local `main` is `7c0145c4028687dccc4837f3d46410477c14ebe6`; `origin/main` is `ca59365726bca899f26cdd889dcc62850089eb09`. Work described as uncommitted is in the working tree only: no commit, push, tag, or remote CI has been made for it. Remote Lean certification passed for `36e7c78` only; later work has local evidence only.
- There are 30 ledger certificates. The 30th is `prop:bkl-suspension` in `solutions/PropBklSuspension.lean`, Bizeul–Klartag–Lehec Proposition 7.1 in source form conditional on `CumulantBound d b`, in all dimensions. The 29th is `thm:bkl-taylor-criterion`. `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` remains the one intentional hole outside every certificate closure. Dimension-free KLS is open.
- Covered papers remain Ambrosio–Di Marino–Gigli Theorem 3.6 and Bakry–Gentil–Ledoux Corollary 4.8.2 (`⇑`). BKL and Letwin are not covered. BKL Theorem 1.1 is formalized only conditionally on the open Theorem 4.1/Eldan localization bound. Letwin Theorems 1.1–1.2 and the moment-map Stein kernel of an arbitrary law remain open; the Gaussian has the identity kernel.
- Verification is snapshot-specific. The integrated snapshot, including the 2026-10-11 Letwin A.4/A.5 source integration, is checked by `python3 research/verify.py` only after all proof and metadata edits. `build/verification/latest.json` is valid only while its status is `passed` and its snapshot hash matches the working tree. The full receipt `20261011T125323.381816Z` covers the integrated Stage 2A snapshot before file maintenance; `20261010T093056.948739Z` covers its earlier Stage 1 snapshot. This handoff edit does not create a fresh proof or verification receipt.
- Still open are the SDE/Itô dynamics, CEK essential continuity, Euler–Lagrange identification and Theorem 2, the regularity bridge (H2), the Letwin moment map, Theorem 2.5, Letwin Theorem 1.2, BKL Theorem 4.1, unconditional BKL Theorem 1.1, and `KLS.kls`.

## Current integrated work

The bounded Stage 2A was integrated and verified in receipt `20261011T125323.381816Z`; it is a completed supporting milestone. The subsequent path/filename maintenance requires its own matching full local receipt. It contains Letwin Lemma A.4 for every source-class potential and every real `R ≥ 1`, including the natural-index `C/(n+1)` form; Lemma A.5 for given cutoffs; and the nonconstant uniform-interval source-law client. It does not claim the arbitrary-law moment map, Letwin Theorems 2.5 or 1.1–1.2, BKL Lemma 4.2 without its hypothesis, Theorems 4.1/1.1, or `KLS.kls`.

The adopted source integration is represented by the reviewed candidate bundle in `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-w-final-integration-candidate-v1/`, with source SHA-256 prefix `6f70011e`, and by `build/reviews/2026-10-11-bkl-a4-goal-setup/STATE.json`. Its principal owners are `Analysis/Convex/Coercivity.lean`, `Analysis/Cutoff/Conservativity.lean`, `Analysis/BakryEmery/IntegrationByParts/InverseHessianCutoff.lean`, `Analysis/BakryEmery/UniformIntervalPotential.lean`, and `Analysis/BakryEmery/IntegrationByParts/UniformIntervalClient.lean`; the remaining A.4/A.5 declarations stay in their reviewed existing owners.

The adopted scalar cutoff, tail primitive, rescaling/positivity and real-exhaustion supports remain represented by their dated records and current source consumers. The separate [file-management goal](research/handoffs/2026-10-11-file-management-goal.md) reviews the Cutoff and Cumulant families; it does not replace the mathematical controller or advance proof status.

The current mathematical results retain their original scopes. Proposition 7.1 remains conditional on `CumulantBound d b` in all dimensions. The conditional BKL reduction uses `CumulantBound d ((d!)² K^d)` for every `d ≥ 2`, `K ≥ 1`, and gives `C_P ≤ 2·C_{3.1}·K`; the Section 2 Gaussian-smoothing, affine-normalization, weak-limit, posterior-response, cumulant, covariance, and cutoff results retain their existing hypotheses and public declarations. No dimension, constant, theorem status, certificate, API, or coverage claim is widened here.

Letwin Theorem 1.2 is the source of the quadratic-form bound with constant 8. That attribution is not assigned to Theorem 2.5. The current dependency remains A.4 → A.5 → Letwin Theorem 2.5 → Letwin Theorem 1.2, including its constant-8 quadratic-form bound → BKL Lemma 4.2 → Theorem 4.1 → Theorem 1.1. The bound is still an open prerequisite, not a proved result in this handoff.

## Controller and next steps

The current mathematical controller is Codex chat `01a128eb-e254-7d63-bd15-05abfcb7aaec`. The predecessor `01a12708-9c39-7f33-aa23-3b135e6d1de2` is historical. The bounded Stage 2A goal is [the 2026-10-11 BKL A.4 goal](research/handoffs/2026-10-11-bkl-a4-goal.md). Earlier controllers, idle predecessors, and superseded scheduling claims are historical. The authoritative packet handles remain in `build/reviews/2026-10-11-bkl-a4-goal-setup/STATE.json`.

The immediate mathematical next stage is Letwin Theorem 1.2, including the moment-map and regularity work, Proposition 2.8, Theorem 2.5, and the Stein-kernel identity (2.21), without assuming the desired estimate. Later stages are the Eldan localization/SDE/Itô/non-explosion argument, universal Theorem 4.1, unconditional Theorem 1.1, and `KLS.kls`. Existing Theorem 3.1, conditional Proposition 7.1, and the Section 2 reduction remain in scope as already recorded.

Codex coordinates and accepts; strong API models construct candidates; the reviewed Claude conversation remains the production integrator. No new proof, certificate, or coverage status is asserted by this handoff or by the file-management batch.

## Open owner decisions

- Decide whether to build stochastic calculus for Theorem 4.1 and priorities 5–6 here or build on external Lean efforts. The evidence and recommendation are in `research/decisions/2026-10-03-stochastic-calculus-options.md`.
- Decide whether to retain E. Milman Lemma 4.1 as `same`, although the real-infimum quantile differs from the paper's `−∞` in the degenerate case `f = 0`, `1 − ε < 0`, or relabel it.
- Decide whether to upstream generic infrastructure to Mathlib after API cleanup, including the `C^∞` symmetry of iterated derivatives.
- Decide the CI strategy: project build cache or a self-hosted runner while the repository is private.
- Decide whether the external stochastic closure, 339 StochLean modules at pin `e6741e18` and Apache-2.0 per the root audit, is adopted as a vendored separate Lake package or retained as evidence. The relevant records are `build/reviews/2026-10-07-bkl-continuous/reviews/STOCHASTIC-EXTERNAL-REUSE-SCHEME-20261008.md` and `build/reviews/2026-10-07-bkl-continuous/reviews/COEFFICIENT-SDE-MOMENTMAP-PROPOSALS-20261008.md`. The pinned closure has no SDE theorem; the Letwin moment-map producer remains out of reach at that pin and stays an explicit hypothesis.

## Local maintenance and delivery

The separate file-management goal covers reviewed reversible local storage management, inventory and research navigation. Publication, commit/push/tag actions, remote CI, and irrecoverable deletion or other destructive storage actions remain separate matters and are not authorized by this handoff. The inventory tool is read-only with respect to repository artifacts and writes candidates only under ignored `build/` output by default.

Follow [research/workflow.md](research/workflow.md). Stage canonical metadata and regenerate progress views only when proof or metadata work actually requires it. Preserve the broad dirty tree and actual Git index. Remote CI is Lean-only and requires separate owner authorization through manual dispatch or a `milestone/**` tag.

The 2026-10-12 filename map registers the Operator and BKL Suspension families and PosteriorCovariance; the [complete map](research/api-migration/2026-10-12-analysis-bkl-filename-map.json) records every owned declaration. File management retained all evidence paths and handled 1,708 compiled duplicate targets with recoverable COW. Its dynamic acceptance/receipt is in `build/file-management/COMPLETION.json`. After this round, resume the existing strong API proof-construction / reviewed Claude integration workflow; coordinate Claude's LevStochCalc introduction without concurrent canonical writers.
