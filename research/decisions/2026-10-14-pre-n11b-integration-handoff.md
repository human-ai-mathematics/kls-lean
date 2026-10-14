# Current KLS handoff

Updated 2026-10-14 when the step-1 Goal of the BKL roadmap was installed. The previous handoff (N10b integration) is preserved verbatim in [the pre-Goal archive](research/decisions/2026-10-14-pre-letwin-goal-handoff.md). Exact statements and coverage belong to the [paper register](research/progress/LITERATURE.md).

## Active Goal

The owner set the four-step mathematical roadmap (1) Letwin constant 8, (2) stochastic localization, (3) BKL Theorem 4.1, (4) the KLS main theorem, and installed only step 1 as the active Goal: [BKL step 1, the compact Letwin constant-eight theorem](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md) (control directory `build/reviews/2026-10-14-letwin-constant-eight-goal/`). Its endpoint is a proof of the original frozen `FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound`, through the actual regular-class producer rather than a supplied regular-class inequality: for every n > 0 and every compactly supported isotropic log-concave probability measure on `EuclideanSpace ℝ (Fin n)`, every self-adjoint quadratic form (singular and indefinite included) has centered variance at most 8 times its squared Hilbert-Schmidt norm. Mean/covariance normalization and the exact constant 8 are kept. N11b, other support units or a conditional assembly do not complete the Goal. Steps 2-4 are queued; the existing conditional Theorem 4.1 and KLS assembly will be reused and re-reviewed against exact source statements and axiom evidence, not re-proved blindly.

Roles: Codex owns source/version, frozen contracts, dependency order, placement review and independent acceptance; the existing Claude session runs the existing API loop (gpt-6-astra/high, existing script and provider configuration, max_rounds 4, max_queries 6, one candidate at a time) and is the sole canonical integrator after Codex acceptance and placement review. No new worker or sub-controller; the old claude-kls heartbeat stays paused; the old eight large loops are not restarted.

## Current mathematical state

Dimension-free KLS remains open. `KLS/Target.lean` contains the intentional `FunctionalInequalities.KLS.kls` hole outside certificate closures. The strongest BKL interface is `KLS.BKL.Localization.conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture`, through the conditional Theorem 4.1 and the certified Taylor/suspension reduction. Its compact constant-8 input is reduced by `letwinCompactBound_of_regularClass` to smooth uniformly convex regular laws `1_K exp(-W) dx`; that regular-class bound is still a premise.

The bounded isotropic CEK moment-map producer gives the actual gradient pushforward. R0 in `KLS/CEK/MomentRegularity.lean` gives, for the regular class, a convex Lipschitz normalized moment potential u with actual pushforward, C1 and 16/kappa-Lipschitz gradient, and a.e. positive definite Hessian, log-det equation and 16/kappa matrix cap. The pointwise bridge in `Probability/Stein/HessianKernel.lean` identifies the Hessian with D(gradient u) at gradient-differentiability points of a C1 potential, without global C2.

The weak C^{1,1} counterpart of Letwin (2.2) is canonical: `Analysis.integral_mul_generator_eq_neg_energy` and `Analysis.integral_mul_generator_eq_neg_energy'` in `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`, with the integrability interface `Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact` in `Analysis/Matrix/Piola.lean`.

N11b.1 (the centered second difference `u(x+h) + u(x-h) - 2u(x)` of a C1 potential with G-Lipschitz gradient is C1 with 4G-Lipschitz gradient, every finite dimension) has independent Codex acceptance (`build/reviews/2026-10-14-codex-claude-n11-controller/independent/N11b1/ACCEPTANCE.json`) but is not canonically integrated; it stays in scratch.

Full smooth Letwin Lemma 2.2, the N11b integrated Hessian-increment estimate, the weak third-derivative producer N11d, local H1/chain-rule bridges, weak Hessian evolution and the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H^-1 transport and the spectral constant-8 assembly remain open. Letwin Theorems 2.5/1.2, unconditional BKL Theorems 4.1/1.1 and KLS are not proved. The 30 certificates and covered ADM-G/BGL targets retain their scopes; no paper coverage changed.

## Verification and preservation

The canonical source and metadata before this Goal setup are the snapshot `6e7d5285ab6cf71f63ddabee4683387583242c24a672a57629395825be98661e`, covered by the passed full receipt `build/verification/20261013T181656.119706Z/report.json` (280 gates, 266 strict clients, 806 replayed modules) and Codex's canonical acceptance of the N10b integration. The Goal setup changed documentation only (this handoff, the Goal record, the archived handoff, the literature priority and one root-summary sentence, and regenerated progress views); that receipt does not verify the new documentation snapshot, and no new full verification is claimed. A fresh full `python3 research/verify.py` receipt, run without `GIT_INDEX_FILE`, is required once the Goal's proofs are integrated.

The baseline HEAD is `8ec28f68c8bf72f60ec195b6fbb0f0f48ea04a22`. The pre-existing dirty tree, the actual staged contents (index entries and flags) and unrelated `.cursor/`/`.clinerules/` work are preserved; progress views are regenerated through an isolated temporary index. No commit, push, tag, remote CI or publication is authorized.

## Next action

The immediate next contract is N11b.2: from the original convexity and upper-bound assumptions of N11b, the centered second difference satisfies `0 ≤ w ≤ D‖h‖²` together with the needed scalar nonnegativity. Codex freezes it and compiles its interface first; Claude dispatches it only after that. Then the precise compact weighted-integrability consumption and the unchanged original N11b assembly follow, one candidate at a time, before N11d and the later weak-route steps.
