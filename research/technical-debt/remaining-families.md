# Remaining-family maintenance

This is a live maintenance register. It tracks layout and documentation, without changing
proof, hypothesis, normalization, dimensional or certificate status. Dated decisions and the
older inventories retain their original claims and source paths.

| Item | Responsibility and state | Record / acceptance requirement |
| --- | --- | --- |
| D1–D3, C3 | Current-status, path and module-scope documentation corrected; scoped batch accepted | [Documentation correction](../decisions/2026-10-17-other-families-documentation.md); unchanged comment-free Lean code, links and private-index freshness |
| S2 | Generic cutoffs and weak-derivative layers implemented; full batch accepted | [Cutoff/weak-derivative layout](../decisions/2026-10-17-cutoff-weak-derivative-layout.md); exact source/interface, full verifier and index/history checks |
| S1 | Generic Hessian owners implemented; full batch accepted | [Hessian layout](../decisions/2026-10-18-hessian-owner-layout.md); exact matrix definition, C1/C2 scopes, no generic Stein-kernel dependency, full verification |
| S3, S5 | Trace algebra/spectral responsibilities and proximal object boundary implemented; full batch accepted | [Trace/proximal layout](../decisions/2026-10-18-trace-proximal-layout.md); exact owner/interface checks, real clients and full verification |
| S4, S6 | Stein identity and MetricBV responsibility boundaries implemented; full batch accepted | [Stein/MetricBV layout](../decisions/2026-10-18-stein-metricbv-layout.md); exact bounded-support scope, preserved identities and full verification |
| C1 | CEK producer layers implemented after actual private-dependency review; full batch accepted | [Moment producer layout](../decisions/2026-10-18-moment-regularity-layout.md); same actual witness, retained private trace/Stein chain and exact interfaces |
| C2 | Cross-top-level MetricBV relocation remains a candidate | Require actual independent reuse and dependency benefit; retain the existing family until justified |

The per-batch receipt index is
`build/file-management/2026-10-17-other-families-optimization/STATE.json`.
Each acceptance applies to its recorded snapshot. A proposed or implemented layout is not
marked accepted solely because a targeted build passes. Existing qualified public names remain
unchanged; module migrations and namespace/name changes are separate migration classes.

## Completed sequential delivery (2026-10-18)

Documentation was accepted before the five source-layout batches. Every source batch has a
separate fresh full-verification receipt plus exact source/interface comparisons and unchanged
mathematical/status/history/index checks. Current owner/import guides are generated or linked
from the [source map](../../formalization/README.md) and the decisions above.

The accepted receipt chain is indexed in
`build/file-management/2026-10-17-other-families-optimization/STATE.json`.
The cumulative checks and final report are in that same ignored output directory. Final
navigation-only updates have their own scoped acceptance and do not renew a full Lean receipt.

The MetricBV tests require bounded function support on arbitrary metric spaces; the old review's
compact-support shorthand is corrected in the new decision without editing the historical
review. C2 remains deferred for lack of an independent reuse consumer; the existing owner is
retained. The shared-private weak-derivative calculus and CEK trace/Stein chains remain together.
No further split is justified solely by file length. BKL's prior accepted reorganization and
all proof, certificate and paper-coverage states remain unchanged.
