# Current KLS handoff

Updated 2026-10-18 for public-entry documentation and module-comment maintenance.

## Accepted result and open boundaries

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the finite-horizon cutoff
stochastic-localization route of BKL. Its target is unchanged: one finite covariance-normalized
literature Poincaré bound for every dimension and every log-concave probability law with
finite second moment, including dimension zero and singular affine supports.

The accepted chain is compact Letwin Theorem 1.2 (constant 8) → finite-horizon cutoff BKL (95)
→ source-form BKL Theorem 4.1 → source-form BKL Theorem 1.1 → KLS.
The [paper register](research/progress/LITERATURE.md) owns exact scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean and its certificates.
BKL's main theorem is covered. Letwin's noncompact Theorems 1.1/1.2, the uncut Eldan
construction and literal identities (68)–(73), and the separate uncut intermediate statements
remain open. The four exploratory routes retain their own statuses.

## Evidence and library use

The [recorded baseline](research/verification.md#recorded-baseline) is the stable summary of the
current evidence: commit `5d41bd7`, the completed full local verification and its binding to the
committed source, the separate three-client interface acceptance, and the remote-CI boundary.
Raw receipts and logs stay local in the ignored `build/` directory; publishing them is optional.

Use the [calling examples](examples/README.md), the [compiler API directory](formalization/API.md)
and the [short review checklist](research/workflow.md#review-after-mechanical-checks). The
[downstream runner](research/downstream.py) accepts one full Git commit, builds three narrow
clients in a fresh Lake project, audits their complete primary declaration closure and replays
the local compiled modules; it does not accept a working-tree overlay or renew a certificate,
and explicit third-party compiled caches remain trusted. Known
[vendor holes](formalization/vendor/README.md#upstream-holes) remain isolated.

## Next work

The current maintenance scope is public-entry documentation, targeted ignore rules and module
comments; the [delivery record](research/decisions/2026-10-18-comment-cleanup-delivery.md) records
the scope and preserves the preceding handoff. Original changed comments are kept in the
[comment archive](research/decisions/2026-10-18-migration-comment-history.md). Proofs, hypotheses
and all 34 certificate states are unchanged. Run the full local verifier on a frozen final
snapshot before committing this maintenance; receipts apply only to their recorded inputs.

Before public sharing, select the final commit for an owner-authorized remote Lean certification
run and review the disclosure scope of the preserved dated history and old branch. Source owners
are in the [module directory](formalization/MODULES.md); the
[maintenance register](research/technical-debt/remaining-families.md) retains deferred MetricBV
relocation.
