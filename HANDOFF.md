# Current KLS handoff

Updated 2026-10-18 for the final public-entry documentation corrections.

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

The [recorded baseline](research/verification.md#recorded-baseline) summarises the most recent
accepted snapshot: commit `904d1a5`, whose full local verification was completed, accepted and
pushed, with every committed blob matched to the frozen source of that run; `5d41bd7` remains the
separately tested three-client downstream pin; the recorded historical remote Lean run is
run 37516844384 for `36e7c78`. Receipts and logs stay local in the ignored `build/` directory; they
are dated evidence for their recorded snapshots, not a claim that every later prose commit was
reverified, and a later remote result is read from its own GitHub Actions run, not from this page.

Use the [calling examples](examples/README.md), the [compiler API directory](formalization/API.md),
the [audit client guide](research/audits/README.md) and the
[short review checklist](research/workflow.md#review-after-mechanical-checks). The
[downstream runner](research/downstream.py) accepts one full Git commit, builds three narrow
clients in a fresh Lake project, audits their complete primary declaration closure and replays
the local compiled modules; it does not accept a working-tree overlay or renew a certificate,
and explicit third-party compiled caches remain trusted. Known
[vendor holes](formalization/vendor/README.md#upstream-holes) remain isolated.

## Current work and next step

Maintenance at `904d1a5` (public-entry documentation, targeted ignore rules and the 43 module
comments) is delivered; the [delivery record](research/decisions/2026-10-18-comment-cleanup-delivery.md)
and [comment archive](research/decisions/2026-10-18-migration-comment-history.md) preserve its scope
and originals. The present batch is documentation only: two stale comment clauses, a concise audit
client guide, this handoff and the recorded baseline, with the replaced originals in the
[documentation history](research/decisions/2026-10-18-public-readiness-documentation-history.md).
Proofs, hypotheses and all 34 certificate states are unchanged.

Acceptance procedure for this batch: Codex accepts the candidates, commits and pushes, then runs
the owner's authorized remote Lean certification for that pushed commit. Its terminal result is
read from the GitHub Actions run whose `head_sha` is that exact SHA. That run has the Lean-only scope
described in the [verification guide](research/verification.md#change-appropriate-checks-and-remote-ci);
no outcome is assumed here, and the SHA is not written back into this text. The repository is
private until the owner decides
the disclosure scope of the preserved dated history and old branch and changes visibility
explicitly. Source owners are in the [module directory](formalization/MODULES.md); the
[maintenance register](research/technical-debt/remaining-families.md) retains deferred MetricBV
relocation.
