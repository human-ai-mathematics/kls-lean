# Current KLS handoff

Updated 2026-10-14 after the canonical integration of the N10b weak generator identities. The previous handoff (R0 resume) is preserved verbatim in [the pre-N10b archive](research/decisions/2026-10-14-pre-n10b-integration-handoff.md). Exact statements and coverage belong to the [paper register](research/progress/LITERATURE.md).

## Current mathematical state

Dimension-free KLS remains open. `KLS/Target.lean` contains the intentional `FunctionalInequalities.KLS.kls` hole outside certificate closures. The strongest BKL interface is `KLS.BKL.Localization.conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture`, through the conditional Theorem 4.1 and the certified Taylor/suspension reduction. Its compact constant-8 input is reduced by `letwinCompactBound_of_regularClass` to smooth uniformly convex regular laws `1_K exp(-W) dx`; that regular-class bound is still a premise.

The bounded isotropic CEK moment-map producer gives the actual gradient pushforward. R0 is assembled in `KLS/CEK/MomentRegularity.lean`: for n > 0, compact convex K with interior, globally smooth uniformly kappa-convex W, kappa > 0, and the isotropic source probability law, `Analysis.exists_regular_moment_potential` gives a convex Lipschitz normalized moment potential u, actual pushforward, C1 and 16/kappa-Lipschitz gradient, and a.e. positive definite Hessian, log-det equation and 16/kappa matrix cap.

The pointwise bridge in `Probability/Stein/HessianKernel.lean` requires C1 and gradient differentiability at x, with all finite dimensions allowed. It identifies the Hessian with D(gradient u) and proves Hermitian symmetry, without inferring global C2 or requiring a weak third-derivative tensor.

The weak C^{1,1} counterpart of Letwin (2.2) is now canonical. In the new `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`, `Analysis.integral_mul_generator_eq_neg_energy` and `Analysis.integral_mul_generator_eq_neg_energy'` prove the two original frozen N10b identities: for u in C1 with Lipschitz gradient, V in C1, Lipschitz exponent -u + V(gradient u) and det Hess u = exp(-u + V(gradient u)) almost everywhere, every w in C1 with Lipschitz gradient and every compactly supported eta in C2, `∫ eta (L w) e^{-u} = -∫ <(Hess u)^{-1} grad eta, grad w> e^{-u}`, and the same with eta and w exchanged inside L, in every dimension, with no C2 hypothesis on u or w. `Analysis.integrable_inv_hessianMatrix_mul_of_bounded_compact` in `Analysis/Matrix/Piola.lean` is the public integrability interface it uses; the four one-use supports (weighted test Lipschitz/support, its a.e. derivative, the a.e. Monge-Ampere exponent chain derivative, the finite inverse-matrix cancellation) are private in the new module.

Full smooth Letwin Lemma 2.2 (everywhere PD, smooth diffeomorphism and pointwise source package) remains open. So do local H1/chain-rule bridges, weak Hessian evolution, the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H^-1 transport and final constant-8 assembly. Letwin Theorems 2.5/1.2, unconditional BKL Theorems 4.1/1.1 and KLS are not proved. The 30 certificates and covered ADM-G/BGL targets retain their scopes; no paper coverage changed.

## Authorized work and acceptance

The owner authorized a Codex/Claude/API division of work for the minimal N10b chain: Codex froze six small contracts and accepted each candidate independently; Claude ran one existing gpt-6-astra/high loop per contract in ignored scratch and is the sole canonical writer after acceptance; no other large task was restarted. All six contracts (N10b.1-N10b.6) have independent Codex acceptance under `build/reviews/2026-10-13-codex-claude-n10-controller/independent/`, and Codex accepted the placement plan (`PLACEMENT.json`). Exactly six new small API loops were run, one per authorized contract, each with the existing `gpt_lean_loop.py` script and its existing gpt-6-astra/high configuration and bounded rounds; none of the old large loops was restarted or extended, and no additional worker, controller or Goal, provider/model substitution, commit, push, tag, publication or remote CI was made.

Canonical integration followed the placement plan: the N10b.4 interface was added to the existing weak inverse-divergence section of `Piola.lean` (prior text unchanged, existing cofactor helpers reused); the new module carries the accepted proof bodies verbatim, with the four one-use supports made private and the trailing N10b.3 client example and `#print` omitted. Elaborated types of all seven declarations match the accepted hashes; the full name/type map is `build/reviews/2026-10-13-codex-claude-n10-controller/integration/NAME-TYPE-MAP.json`. See [the integration record](research/decisions/2026-10-14-n10b-weak-generator-integration.md).

The original eight loops ended naturally: N11e and W3b2a were accepted; N10b, N13c, N14a, W3b2b and R0 failed 18 rounds, LRF0 failed 20. Their failed sources/diagnostics remain unchanged; R0 and N10b are now superseded by separately accepted sources without changing that history. N11e still assumes existence of the weak third-derivative tensor, and W3b2a still supplies convex-range mollification without the chain-rule limit.

## Verification and preservation

Evidence for this integration is `build/reviews/2026-10-13-codex-claude-n10-controller/` (`STATE.json`, `integration/`, `CLAUDE-INTEGRATION-REPORT.md`). The canonical client is `research/audits/BKL/WeakInverseHessianAudit.lean` (both original statements, the actual compact-test generator symmetry consumer, the integrability interface and a Lipschitz compact-test derivative consumer); the earlier `BKL/WeakHessianIdentificationAudit.lean` and `BKL/RegularMomentPotentialAudit.lean` remain.

The baseline HEAD is `8ec28f68c8bf72f60ec195b6fbb0f0f48ea04a22`; the receipt `20261013T133651.951876Z` covers the pre-integration snapshot `6547db40…`, not these additions. Require a passed fresh `python3 research/verify.py` receipt matching the final source/metadata snapshot. Kernel replay, declaration/certificate axiom scopes and the intentional/upstream hole inventories remain separate trust statements.

The pre-existing dirty tree, actual staged contents and unrelated `.cursor/`/`.clinerules/` work are preserved. Progress views are regenerated through an isolated index containing the intended inherited and new changes. No source/layout move, public rename, old-name alias or checker weakening occurred.

## Next action

Finish verification of this integration and stop for owner/Codex review. Other large tasks stay paused; further proof construction requires a new owner instruction. Keep BKL primary and the regular-class constant-8 bound as the open input.
