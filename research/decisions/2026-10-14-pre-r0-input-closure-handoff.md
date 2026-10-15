# Current KLS handoff

Updated 2026-10-14 at the N11d integration. The previous handoff is preserved byte for byte in [the pre-N11d archive](2026-10-14-pre-n11d-integration-handoff.md); earlier ones are listed in the [decision index](README.md). Exact statements and coverage belong to the [paper register](../progress/LITERATURE.md); the main line is summarized in the [proof path](../progress/PROOF-PATH.md).

## Active Goal

The owner's four-step roadmap is (1) Letwin constant 8, (2) stochastic localization, (3) BKL Theorem 4.1, (4) the KLS main theorem. Only step 1 is the active Goal ([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md); control directory `build/reviews/2026-10-14-letwin-constant-eight-goal/`). Its endpoint is a proof of the frozen `letwinCompactBound : LetwinCompactBound` through the actual regular-class producer: for every n > 0 and every compactly supported isotropic log-concave probability measure on `EuclideanSpace ℝ (Fin n)`, every self-adjoint quadratic form, singular and indefinite ones included, has centered variance at most 8 times its squared Hilbert-Schmidt norm (Letwin arXiv:2607.24164v1, Theorem 1.2). Supports, conditional assemblies and documentation do not complete it. Steps 2-4 are queued; the existing conditional Theorem 4.1 and KLS assembly will be re-reviewed against exact sources and evidence, not re-proved.

Roles: Codex owns sources, frozen contracts, dependency order, placement review and independent acceptance; the existing Claude session runs the existing API loop (gpt-6-astra/high, existing script and provider configuration, max_rounds 4, max_queries 6, one candidate at a time) and is the sole canonical writer after Codex acceptance. No other worker or sub-controller; the old claude-kls heartbeat stays paused; the old eight large loops are not restarted. No commit, push, tag, remote CI or release is authorized for this integration; the earlier documentation checkpoint commit and push is history.

## Current mathematical state

Dimension-free KLS remains open; `KLS.kls` in `KLS/Target.lean` is the intentional hole outside certificate closures. `KLS.BKL.Localization.conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture` and `theorem41` (KLS/BKL/Theorem41.lean) hold conditionally on `LetwinCompactBound`, which `letwinCompactBound_of_regularClass` reduces to the smooth uniformly convex regular class; that regular-class bound is still a premise.

Proved supports on the weak C^{1,1} route, each with its own scope:
- the bounded CEK moment-map producer and the R0 regular-class moment potential (`KLS/CEK/MomentRegularity.lean`);
- the pointwise Hessian identification and N11e weak third-derivative symmetry, which assumes a given weak tensor (`Probability/Stein/HessianKernel.lean`);
- the N10b weak generator identities of Letwin (2.2) (`Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`, `Analysis/Matrix/Piola.lean`);
- the original N11b integrated Hessian-increment energy estimate (`Analysis/Convex/HessianIncrement.lean`, `Analysis/Convex/SecondDifference.lean`);
- **new:** the original N11d tensor `Analysis.exists_weak_third_derivative` (`Analysis/Convex/HessianRegularity.lean`). From the preserved original data it produces an actual tensor T: each Hessian entry has a weak derivative along each coordinate direction, L² on every compact set. The data are C¹ convex u with Lipschitz gradient, C¹ convex V, a global Lipschitz exponent −u + V(∇u), a.e. positive definite Hessian with the log-det equation and cap, and the global centered-difference bound, in all finite dimensions. Its supports are:
  - a uniform smooth compact majorant for translated cutoffs (`Analysis/Cutoff/Translation.lean`);
  - compact-local and cutoff-global L² of Hessian entries (`HessianKernel.lean`);
  - the cutoff difference-energy bound derived from N11b (`HessianIncrement.lean`).

  The tensor theorem has no cutoff or test-function input, and no given tensor, H¹ or cutoff square-difference-energy conclusion is assumed; the original global centered-difference bound is an input, distinct from the produced global L² translation bound ([N11d integration record](2026-10-14-n11d-weak-hessian-integration.md)).

Still open:
- **Next:** applying the N11d tensor to the actual R0 source law needs a proof of its two original inputs from R0 data: the global centered-difference bound and the global Lipschitz exponent. The current source has the 4/κ centered-difference bound only as an internal step of `lipschitzWith_gradient_of_map_gradient`, with no exported consumer.
- Local H¹/chain-rule bridges, weak Hessian evolution and the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H⁻¹ transport and the spectral constant-8 assembly.
- Full smooth Letwin Lemma 2.2, Letwin Theorems 1.1/1.2/2.5, unconditional BKL Theorems 4.1/1.1 and KLS.

The N11d result is the original weak, locally L² tensor support; it does not establish global C² or smooth regularity, the trace estimate, Theorem 2.5, Theorem 1.2 or compact constant 8. The 30 certificates and the covered ADM-G/BGL targets retain their scopes; no paper coverage changed.

## Evidence

- N11d.1-N11d.4 each have independent Codex acceptance (`independent/N11d1..4` in the control directory). The complete placement passed Codex's isolated prototype (`N11d-placement-prototype/RESULT.json`) and placement acceptance (`N11d-integration/PLACEMENT-ACCEPTANCE.json`). Local canonical checks (strict owners, aggregate and audit `research/audits/BKL/WeakHessianRegularityAudit.lean`, five complete types, thirteen standard axiom reports, four kernel replays) passed before the documentation freeze.
- At this freeze a fresh full verification of the post-integration snapshot is required and pending, and Codex's independent canonical acceptance is pending. Their results are recorded in the ignored `N11d-integration/CLAUDE-INTEGRATION-REPORT.md` and the Goal `STATE.json`, not in this file. Earlier receipts, including `build/verification/20261014T094923.736318Z/report.json` for the documentation checkpoint, cover only their own snapshots.

## Next action

After Codex's canonical acceptance, the next proof work closes the two R0 source-law inputs of the N11d tensor (the global centered-difference bound and the global Lipschitz exponent) from the actual regular-class data. Then come the local H¹/chain-rule and weak evolution/trace steps. Each is a separately frozen contract; none is dispatched by this integration. The Goal endpoint remains `LetwinCompactBound`.
