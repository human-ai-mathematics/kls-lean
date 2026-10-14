# Current KLS handoff

Updated 2026-10-13. This records the current closeout and pause. The previous handoff
is preserved verbatim in [the pre-closeout archive](research/decisions/2026-10-13-pre-closeout-handoff.md).
Exact source statements and coverage belong to the [paper register](research/progress/LITERATURE.md).

## Current mathematical state

- Dimension-free KLS remains open. `FunctionalInequalities.KLS.kls` in
  `KLS/Target.lean` is the intentional project-local hole, outside certificate closures.
- The strongest integrated BKL interface is
  `KLS.BKL.Localization.conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture`,
  through `theorem41` and the certified Taylor/suspension reduction. This is a
  conditional chain; unconditional BKL Theorems 4.1/1.1 and KLS are not proved.
- `LetwinCompactBound` is the constant-8 quadratic-form bound for compactly
  supported isotropic log-concave laws in positive dimension. It is now reduced by
  `letwinCompactBound_of_regularClass` to isotropic laws `1_K exp(-W) dx`, K compact
  convex with nonempty interior and W globally smooth and uniformly kappa-convex,
  kappa > 0. That regular-class bound is a retained premise, not a proof.
- Bounded isotropic moment-map existence and the actual gradient pushforward are
  integrated in `KLS/CEK/MomentMap.lean`. General unbounded/finite-mass existence
  and uniqueness are outside that producer. The weak source regularity package,
  the integrated PSD trace bound, weak Brascamp-Lieb, Stein/H^-1 transport and the
  final constant-8 assembly remain open. The full smooth source Lemma 2.2 is not
  proved by the C1 and 16/kappa-Lipschitz-gradient supports.
- The 30 existing certificates retain their exact scopes. BKL and Letwin are not
  covered papers. Paper coverage remains the registered ADM-G and BGL targets.

## This closeout

The owner requested that the eight existing tasks finish and then pause. Claude
exhausted its session allowance; the owner transferred closeout to Codex and
explicitly authorized disabling that window's automatic continuation. It was
visibly unchecked. No new task, retry, split, model/provider change or failed
proof repair was dispatched during this closeout.

All eight API loops ended naturally. N11e and W3b2a passed independent checking
and were integrated, with unchanged frozen public statements:

- `Analysis.ae_weak_third_derivative_symm` in
  `Probability/Stein/HessianKernel.lean`: a C1 potential with Lipschitz gradient
  has symmetric weak third derivatives **if the weak derivative tensor exists**.
  This does not construct that tensor.
- `Analysis.convolution_mem_of_ae_mem` in `Analysis/Mollification.lean`: normalized
  bump mollification preserves a closed convex range under the local a.e. range
  and integrability hypotheses. This is not the chain rule in the limit.
- The earlier T10f conditional compact approximation reduction remains in
  `KLS/BKL/LetwinApproximation.lean` and is included in this closeout.

N10b, N13c, N14a, W3b2b and R0 exhausted 18 rounds without acceptance; LRF0
exhausted 20. Their sources and diagnostics remain unchanged under
`build/reviews/2026-10-12-bkl-claude-goal/tasks/`. None of those failed candidates
is a production proof. The [failure analysis](research/decisions/2026-10-13-letwin-loop-failure-analysis.md)
distinguishes invalid candidate shortcuts, missing local analytic interfaces,
and oversized task assemblies; it is not a counterexample to the source route.

## Verification and preservation

Closeout evidence is in `build/reviews/2026-10-13-codex-takeover/`. `STATE.json`
tracks the lifecycle; `COMPLETION.json` records the final verifier outcome and
receipt when available. Independent candidate receipts, canonical source
integration maps and strict audit logs remain in that directory. Canonical
clients are `research/audits/BKL/{LetwinCompactApproximation,WeakHessianSymmetry,MollificationConvexRange}Audit.lean`.

The baseline HEAD is `8ec28f68c8bf72f60ec195b6fbb0f0f48ea04a22`; its full local
receipt is `20261013T074711.770167Z`. That earlier receipt does not cover the new
T10f source/import or this closeout. Full verification is snapshot-specific:
use `python3 research/verify.py`, and require a passed receipt matching the final
working tree. Kernel replay, standard-axiom audits, certificate scopes and the
intentional/upstream hole inventories remain separate trust statements.

The actual Git index and unrelated `.cursor/`/`.clinerules/` work are preserved.
Progress views are generated through an isolated index, containing only intended
proof and metadata changes. Codex has made no commit, push, tag, publication or
remote CI request in this closeout.

## Next authorized action

Pause after this closeout and its verification. Resume proof construction only
on a new owner instruction. Keep BKL primary and the Letwin compact bound as its
remaining input. The failure analysis proposes small, separately checkable
bridges for a future resume; those proposals are not active tasks.
