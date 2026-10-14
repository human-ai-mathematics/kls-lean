# Current KLS handoff

Updated 2026-10-14 at the documentation checkpoint. The previous handoff is preserved byte for byte in [the pre-checkpoint archive](research/decisions/2026-10-14-pre-documentation-checkpoint-handoff.md); earlier ones are listed in the [decision index](research/decisions/README.md). Exact statements and coverage belong to the [paper register](research/progress/LITERATURE.md); the main line is summarized in the [proof path](research/progress/PROOF-PATH.md).

## Active Goal

The owner's four-step roadmap is (1) Letwin constant 8, (2) stochastic localization, (3) BKL Theorem 4.1, (4) the KLS main theorem. Only step 1 is the active Goal ([Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md); control directory `build/reviews/2026-10-14-letwin-constant-eight-goal/`). Its endpoint is a proof of the frozen `letwinCompactBound : LetwinCompactBound` through the actual regular-class producer: for every n > 0 and every compactly supported isotropic log-concave probability measure on `EuclideanSpace ℝ (Fin n)`, every self-adjoint quadratic form, singular and indefinite ones included, has centered variance at most 8 times its squared Hilbert-Schmidt norm (Letwin arXiv:2607.24164v1, Theorem 1.2). Supports, conditional assemblies and documentation do not complete it. Steps 2-4 are queued; the existing conditional Theorem 4.1 and KLS assembly will be re-reviewed against exact sources and evidence, not re-proved.

Roles: Codex owns sources, frozen contracts, dependency order, placement review and independent acceptance; the existing Claude session runs the existing API loop (gpt-6-astra/high, existing script and provider configuration, max_rounds 4, max_queries 6, one candidate at a time) and is the sole canonical writer after Codex acceptance. No other worker or sub-controller; the old claude-kls heartbeat stays paused; the old eight large loops are not restarted.

## Current mathematical state

Dimension-free KLS remains open; `KLS.kls` in `KLS/Target.lean` is the intentional hole outside certificate closures. `KLS.BKL.Localization.conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture` and `theorem41` (KLS/BKL/Theorem41.lean) hold conditionally on `LetwinCompactBound`, which `letwinCompactBound_of_regularClass` reduces to the smooth uniformly convex regular class; that regular-class bound is still a premise.

Proved supports on the weak C^{1,1} route, each with its own scope: the bounded CEK moment-map producer and the R0 regular-class moment potential (`KLS/CEK/MomentRegularity.lean`); the pointwise Hessian identification and N11e weak third-derivative symmetry, which assumes the weak tensor (`Probability/Stein/HessianKernel.lean`); the N10b weak generator identities of Letwin (2.2) with their integrability (`Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`, `Analysis/Matrix/Piola.lean`); and the original N11b integrated Hessian-increment energy estimate `Analysis.integral_mul_hessian_increment_le` with its centered-difference, Hessian-entry and integrability supports (`Analysis/Convex/HessianIncrement.lean`, `Analysis/Convex/SecondDifference.lean`, `Probability/Stein/HessianKernel.lean`).

Still open: the actual local L2 weak third derivatives (N11d), local H1/chain-rule bridges, weak Hessian evolution and the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H^-1 transport, the spectral constant-8 assembly, full smooth Letwin Lemma 2.2, Letwin Theorems 1.1/1.2/2.5, unconditional BKL Theorems 4.1/1.1 and KLS. The 30 certificates and the covered ADM-G/BGL targets retain their scopes; no paper coverage changed.

## Evidence

- N11b integration: the full receipt `build/verification/20261014T080831.534453Z/report.json` passed (snapshot `6465861a5f7e4abd4ca9e027cab940daa0f8bc9ba8f79791bf802ce69d1edb36`), and Codex recorded `CODEX_CANONICAL_ACCEPT` for that snapshot (`build/reviews/2026-10-14-letwin-constant-eight-goal/canonical-independent/ACCEPTANCE.json`). Both cover the snapshot before this documentation checkpoint, not the later documentation.
- Earlier receipts cover only their own snapshots. No full verification of the post-checkpoint snapshot is claimed in this file; its evidence is recorded in the ignored checkpoint directory `build/reviews/2026-10-14-documentation-checkpoint/`.

## Documentation checkpoint authorization

On 2026-10-14 the owner prioritized a documentation cleanup and authorized one commit and an ordinary push to `origin/main` containing this documentation together with the independently accepted proof changes. This supersedes, for this checkpoint only, the earlier no-commit rule. Codex reviews, performs the final validation, stages, commits and pushes; Claude writes the documentation only. No tag, remote CI run or separate release is authorized beyond that ordinary push, and no new proof task is dispatched: the next contract N11d.1 is frozen but undispatched, and a frozen interface is not a proof acceptance.

The pre-existing dirty tree, the actual staged entries and flags of the real index and unrelated `.cursor/`/`.clinerules/` work are preserved; progress views are generated through a private temporary index.

## Next action

After the checkpoint, the next actual producer is N11d (local L2 weak third derivatives of the Hessian entries from the N11b difference-quotient bound and the canonical weak-derivative interfaces in `Analysis/WeakDerivative.lean`), beginning with the frozen N11d.1 contract when Codex dispatches it. The Goal endpoint remains `LetwinCompactBound`.
