# Current KLS handoff

Updated 2026-10-18 after independent acceptance of the layout batches and the final documentation review.

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

## Current library and maintenance state

The article-standard review, BKL reorganization, documentation corrections and five subsequent
source-layout batches are complete and independently accepted. All 8,018 compared public
interfaces agree across the latter layout work. Proof statements, definitions, assumptions,
certificate states and existing historical records were preserved.

- [Lean design](LEAN_DESIGN.md) and [calling examples](examples/README.md): public interfaces and imports.
- [Module directory](formalization/MODULES.md) and [BKL guide](formalization/FunctionalInequalities/KLS/BKL/README.md): source owners.
- [Maintenance register](research/technical-debt/remaining-families.md): per-batch decisions, migration maps and acceptance requirements; MetricBV cross-family relocation remains deferred.
- [Final documentation decision](research/decisions/2026-10-18-final-documentation-review.md): corrected status prose and shortened navigation.

## Verification evidence

The last frozen-source full receipt is `build/verification/20261017T182503.125701Z/report.json`:
297 gates, 282 strict audit clients and 864 local-module kernel replays. It audits every
project-local declaration, including `KLS.kls`, with no target exclusion. Known
[vendored holes](formalization/vendor/README.md#upstream-holes) remain outside the proved local dependency closures.

The layout receipt chain and cumulative checks are indexed by
`build/file-management/2026-10-17-other-families-optimization/COMPLETION.json` and its `REPORT.md`.
The final documentation review and staged-input comparison (including six corrected module
docstrings, with all bytes outside those headers unchanged) are retained under
`build/file-management/2026-10-18-final-docs-and-push/`.
These ignored local artifacts apply to their recorded snapshots. Documentation checks do not
renew the full Lean receipt; see [receipt scope](research/verification.md#receipts-and-trust-scope).

## Coordination and delivery

All proof API loops are idle; the original Claude session remains the canonical proof integrator.
The queued review follow-up is paused. Sealed failures and earlier controller records remain
historical evidence and do not override this handoff.

The user authorized final documentation cleanup, one commit and an ordinary branch push on
2026-10-18. This delivery preserves the accepted mathematics and excludes local editor configuration.
The [previous handoff](research/decisions/2026-10-18-pre-final-documentation-handoff.md) preserves the superseded detail verbatim.
