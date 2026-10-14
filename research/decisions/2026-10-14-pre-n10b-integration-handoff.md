# Current KLS handoff

Updated 2026-10-13 after the owner-authorized minimum R0 resume. The previous closeout/pause handoff is preserved verbatim in [the pre-resume archive](research/decisions/2026-10-13-pre-r0-resume-handoff.md). Exact statements and coverage belong to the [paper register](research/progress/LITERATURE.md).

## Current mathematical state

Dimension-free KLS remains open. `KLS/Target.lean` contains the intentional `FunctionalInequalities.KLS.kls` hole outside certificate closures. The strongest BKL interface is `KLS.BKL.Localization.conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture`, through the conditional Theorem 4.1 and the certified Taylor/suspension reduction. Its compact constant-8 input is reduced by `letwinCompactBound_of_regularClass` to smooth uniformly convex regular laws `1_K exp(-W) dx`; that regular-class bound is still a premise.

The bounded isotropic CEK moment-map producer gives the actual gradient pushforward. R0 is now assembled in `KLS/CEK/MomentRegularity.lean`: for n > 0, compact convex K with interior, globally smooth uniformly kappa-convex W, kappa > 0, and the isotropic source probability law, `Analysis.exists_regular_moment_potential` gives a convex Lipschitz normalized moment potential u, actual pushforward, C1 and 16/kappa-Lipschitz gradient, and a.e. positive definite Hessian, log-det equation and 16/kappa matrix cap. The original frozen declaration is unchanged.

The pointwise bridge in `Probability/Stein/HessianKernel.lean` requires C1 and gradient differentiability at x, with all finite dimensions allowed. It reuses the accepted N11e private coordinate/symmetry helpers, identifies the Hessian with D(gradient u), and proves Hermitian symmetry. It does not infer global C2 or require a weak third-derivative tensor.

Full smooth Letwin Lemma 2.2 (everywhere PD, smooth diffeomorphism and pointwise source package) remains open. So do generator symmetry, local H1/chain-rule bridges, weak Hessian evolution, the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H^-1 transport and final constant-8 assembly. Letwin Theorems 2.5/1.2, unconditional BKL Theorems 4.1/1.1 and KLS are not proved. The 30 certificates and covered ADM-G/BGL targets retain their scopes.

## Authorized work and acceptance

The owner authorized only the weak Hessian bridge, independent acceptance, then R0 assembly. These steps are complete. Other large tasks and the Claude-takeover heartbeat remain paused. No API loop was restarted, no new API worker or provider/model substitution was used, and no commit, push, tag, publication or remote CI was made.

The bridge passed strict production and frozen/actual-consumer clients, six standard-axiom reports and affected-module kernel replay before R0 assembly. R0 then passed strict production compilation, byte-identical frozen-header and full elaborated-type comparison, original-statement and actual derivative-norm clients, three standard-axiom reports and affected-module replay. See [the integration record](research/decisions/2026-10-13-r0-weak-hessian-integration.md).

The original eight loops ended naturally: N11e and W3b2a were accepted; N10b, N13c, N14a, W3b2b and R0 failed 18 rounds, LRF0 failed 20. Their failed sources/diagnostics remain unchanged. The [failure analysis](research/decisions/2026-10-13-letwin-loop-failure-analysis.md) remains historical evidence; this minimum resume supersedes R0's current unassembled status through a separate accepted source, without changing that history. N11e still assumes existence of the weak third-derivative tensor, and W3b2a still supplies convex-range mollification without the chain-rule limit.

## Verification and preservation

Current evidence is `build/reviews/2026-10-13-r0-weak-hessian-bridge/`; `STATE.json` tracks this resume and `COMPLETION.json`, when available, records the final complete verifier receipt and snapshot. Canonical clients are `BKL/WeakHessianIdentificationAudit.lean` and `BKL/RegularMomentPotentialAudit.lean` under `research/audits/`.

The baseline HEAD is `8ec28f68c8bf72f60ec195b6fbb0f0f48ea04a22`; the previous full receipt `20261013T122329.498795Z` covers the pre-resume tree, not these additions. Require a passed fresh `python3 research/verify.py` receipt matching the final source/metadata snapshot. Kernel replay, declaration/certificate axiom scopes and the intentional/upstream hole inventories remain separate trust statements.

The pre-existing dirty tree, actual staged contents and unrelated `.cursor/`/`.clinerules/` work are preserved. Progress views are regenerated through an isolated index containing the intended inherited and new changes. No source/layout move, old-name alias or checker weakening occurred.

## Next action

Finish verification of this narrow resume and stop. Other large tasks stay paused; further proof construction requires a new owner instruction. Keep BKL primary and the regular-class constant-8 bound as the open input.
