# BKL primary formalization scope

Updated 2026-10-10 by the owner: BKL is the primary paper; other papers are worked on only for referenced results needed by its proof. This supersedes the standalone general CEK/Letwin paper goals. Previously accepted proofs and their evidence remain intact.

## Primary objective

Formalize Bizeul--Klartag--Lehec, *Presenting a proof of the Kannan--Lovasz--Simonovits conjecture*, arXiv:2610.05474v1, Theorem 1.1: a universal positive Poincare bound for every isotropic log-concave probability measure in every source dimension n >= 1. Preserve the source normalization and the connection to `KLS.Conjecture` / `KLS.kls`; a stronger zero-dimensional extension is supporting scope, not a replacement for the source theorem.

Pinned PDF: `../KLS-paper-sources/2026-10-07/2610.05474v1.pdf`, SHA-256 `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`. The source statement was checked on p. 2, the cumulant and Letwin dependencies on pp. 18-19, and the main assembly on p. 30.

Completion requires the unconditional main statement, standard axiom closure, its exact certificate, source mapping and a matching full local verification receipt. The conditional reduction and a supporting result do not complete BKL. Commit, push, tags and remote CI remain separate authorizations.

## Dependency filter and current priorities

| Work | Exact BKL consumer | Current boundary |
| --- | --- | --- |
| Universal all-order cumulant bounds, Theorem 4.1 (66), Sections 4-6 | Theorem 1.1, through Theorem 3.1 and Proposition 7.1, p. 30 | Main remaining BKL obligation. Preserve K^(m-1)((m-1)!)^2 and all source laws/orders. |
| Eldan's original inverse-covariance localization, (67)-(70), and subsequent Ito/cumulant energy arguments | BKL Theorem 4.1; p. 19 cites [14] and [12, Section 2.1 and Appendix A] | Deterministic posterior/coefficient supports do not supply the SDE, non-explosion, Ito or martingale proofs. |
| Letwin [29], Theorem 1.2 | BKL Lemma 4.2 on p. 18: R_3 <= 8 Id | Required cited theorem: variance <= 8 times Hilbert--Schmidt square for every symmetric matrix. Theorem 1.1 of Letwin and whole-paper coverage are not separate goals. |
| Necessary moment-potential, regularity, Stein, integration and approximation prerequisites of Letwin Theorem 1.2 | Explicit chain to Letwin Theorem 1.2, then BKL Lemma 4.2 | Record the precise immediate consumer and source locator before dispatch. A given potential or conditional kernel is not its producer. |
| Theorem 3.1, Proposition 7.1 and the regular-law reduction | BKL main assembly, p. 30 | Reuse accepted/certified results; Proposition 7.1 retains its genuine cumulant hypothesis until Theorem 4.1 discharges it. |

A bibliography entry alone is not a new work target. Every external task must have a reviewed source statement and a specific BKL consumer, including an explicit necessary prerequisite chain when indirect. Do not broaden an external source to full-paper coverage for convenience.

Cordero--Erausquin--Klartag is not a direct BKL bibliography entry in this pin. Its general Theorem 2 and uniqueness up to translation are no longer standalone completion requirements. Keep only results proved necessary for the cited moment-potential/Letwin input. In particular, standalone general uniqueness work is deferred. The already accepted Proposition 12, pointwise conjugate variation and other supporting results are retained.

The mapped-covariance interface has an explicit chain through the covariance step of the proof of Letwin Theorem 1.2 (p. 14, preceding (2.21)) to Theorem 1.2 and BKL Lemma 4.2. The newly prepared CEK density-variation packets remain unlaunched until their precise necessary consumer is reviewed. Their alternate mass/log-mass route concerns CEK functional (38); CEK (42) uses a fixed base density. Do not mislabel either expression.

## Execution and goal state

Codex coordinates mathematical scope, dependency selection, dispatch and final acceptance. Strong API models perform proof construction; no new Luna jobs, minimum GPT-5.6 Sol, no automatic weaker fallback. Preserve isolated scratch construction and one reviewed production integrator. Only completed, independently verified declarations may enter production or certificate closures. Preserve unrelated dirty work and the actual Git index.

The owner requested a new bounded goal on 2026-10-11 in controller `01a12708-9c39-7f33-aa23-3b135e6d1de2`: [Stage 2A, source Letwin A.4 and its A.5 client](2026-10-11-bkl-a4-goal.md). The predecessor's exact Stage 2 objective remains unfinished. Existing accepted artifacts and failed packets are retained; this goal setup is not a proof-status upgrade. This scope file governs the BKL dependency filter, and the new current-goal record governs execution.
