# Reproducible downstream acceptance runner

Date: 2026-10-18. This is verification-tool maintenance; mathematical statements, proofs,
hypotheses, the 34 existing certificate states and historical records are unchanged.

## Placement and scope

- Owner: downstream verification tooling in `research/downstream.py`, with standard-library
  regression tests in `research/tests/test_downstream.py`; extend the existing example and
  verification guides. No Lean module, mathematical namespace or public theorem API changes.
- Inputs: one full Git commit and its own three examples, toolchain and package lock. Build a
  new Lake fixture; no caller-source overlay or primary compiled-output reuse.
- Checks: source-derived import closure, fresh primary build, strict clients, compiler-derived
  declaration inventory, the existing `verify.py` axiom producer/parser, and local kernel replay.
  Coverage and counts are computed from the selected revision. Pinned third-party compiled
  imports remain trusted; the runner is neither a new certificate nor a second kernel.
- Acceptance: meaningful Python regressions, independent small Git/Lean positive and negative
  fixtures, the exact public baseline and the final committed source. Full repository verification
  and remote-SHA confirmation are separate delivery checks. Failed attempts remain in the
  ignored `build/reusability/2026-10-18-downstream-runner/` evidence directory.

The user's API drafted the candidate, an isolated Claude session repaired and reviewed it,
and Codex performed independent acceptance and integration. The original Claude duplication
review retained its frozen inputs and completed before canonical integration; no duplication
replacement, dependency upgrade or proof change belongs to this delivery.

The previously accepted comment/API-navigation batches retain their separate receipts under
`build/reusability/2026-10-18-library-usability-followup/`. Local editor configuration is excluded.
See the [example guide](../../examples/README.md#reproduce-downstream-acceptance) for commands and
[verification guide](../verification.md#receipts-and-trust-scope) for the evidence boundary.

## Superseded handoff, preserved verbatim

The following handoff is historical. Its baseline and no-publication statements describe that
prior stage, not this delivery. Original UTF-8 SHA-256: `6d067bf34df5851d9a48f0a8666c47af23d8df43b7649797ca962b3ae90f1ce8`.

````markdown
# Current KLS handoff

Updated 2026-10-18 for independently accepted library-usability maintenance.

## Accepted result and open boundaries

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the selected BKL
cutoff-localization route. Its target is unchanged: one finite covariance-normalized
literature Poincaré bound for every dimension and every log-concave probability law with
finite second moment, including dimension zero and singular affine supports.

The accepted chain is compact Letwin Theorem 1.2 (constant 8) → finite-horizon cutoff BKL (95)
→ source-form BKL Theorem 4.1 → source-form BKL Theorem 1.1 → KLS.
The [paper register](research/progress/LITERATURE.md) owns exact scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean and its certificates.
BKL's main theorem is covered. Letwin's noncompact Theorems 1.1/1.2, the uncut Eldan
construction and literal identities (68)–(73), and the separate uncut intermediate statements
remain open. The four exploratory routes retain their own statuses.

## Current library and verification

The published baseline is `b9ebbc3c41462fa269f4240ab5a95c703192aea2`. Its full local receipt is
`build/verification/20261018T051822.281773Z/report.json`: 297 gates, 282 strict clients,
9,856 local declaration audits and 867 module replays, with 34 existing certificates.
The local record under `build/reviews/2026-10-18-reuse-comments-full-validation-and-push/`
binds the checked source tree to that commit and its confirmed remote SHA. Known
[vendor holes](formalization/vendor/README.md#upstream-holes) remain isolated.

The subsequent usability work has separate batch receipts under
`build/reusability/2026-10-18-library-usability-followup/STATE.json` and `COMPLETION.json`:

- Remaining process comments: 365 original passages archived verbatim, 184 files cleaned;
  non-comment code across all 628 primary source/solution/example files is unchanged.
- Published Git consumer: the exact baseline revision, three narrow clients, 32 fresh primary
  modules, 467 standard-only declaration audits and 35 kernel replays; no source overlay.
- Review and API navigation: the [short checklist](research/workflow.md#review-after-mechanical-checks),
  [generated compiler API directory](formalization/API.md) and [calling examples](examples/README.md).

The [usability decision](research/decisions/2026-10-18-library-usability.md) preserves the preceding
handoff and guide wording. Existing proofs, hypotheses, certificate states and dated history are
unchanged. Current comment/tooling checks do not renew the baseline's full Lean receipt;
[receipt scope](research/verification.md#receipts-and-trust-scope) remains explicit.

## Coordination and navigation

Proof API loops and the original Claude proof-integrator session are idle; the queued review
follow-up stays paused. Source owners are in the [module directory](formalization/MODULES.md),
with the [maintenance register](research/technical-debt/remaining-families.md) recording accepted
layout work and the deferred MetricBV cross-family relocation. No mathematical API migration is
part of this maintenance. Local editor configuration is excluded; no new commit or push is included.
````
