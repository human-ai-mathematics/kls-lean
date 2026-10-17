# Handoff before final documentation review

Archived verbatim on 2026-10-18. The text below retains its original repository-root-relative links and historical authorization state. Current instructions live in the root handoff.

---

# Current KLS handoff

Updated 2026-10-18 during sequential layout maintenance. The accepted mathematical scope of the
2026-10-17 article-standard optimization is unchanged. The previous handoff is retained in the
[dated archive](research/decisions/2026-10-17-pre-article-optimization-handoff.md).

## Result and mathematical scope

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the selected BKL cutoff-localization route.
- **The target.** It is unchanged: one finite constant for every dimension and every log-concave probability law with
  finite second moment, in the covariance-normalized literature Poincaré form.
- **Coverage.** Dimension zero and singular affine supports are included.

| Stage | Accepted result | Detailed record |
| --- | --- | --- |
| 1 | Compact counterpart of Letwin Theorem 1.2, with exact constant 8 | [Letwin stage](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md) |
| 2 | BKL (95) in finite-horizon cutoff form | [Localization stage](research/handoffs/2026-10-17-bkl-step2-stochastic-localization.md) |
| 3 | BKL Theorem 4.1 in source form, one universal constant for all orders and dimensions | [Cumulant stage](research/handoffs/2026-10-17-bkl-step3-theorem41.md) |
| 4 | BKL Theorem 1.1 and the actual `KLS.kls` | [Final stage](research/handoffs/2026-10-17-bkl-step4-kls.md) |

The [paper register](research/progress/LITERATURE.md) owns exact source scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean. BKL's main theorem is covered. The following remain
separate open results:
- Letwin's noncompact Theorem 1.2;
- the uncut Eldan process and the literal identities (68)–(73);
- the uncut intermediate BKL statements.

The four exploratory routes of the progress diagrams are research records; they do not decide formalization targets.
Paper work is selected in the paper register by a named source, version and target theorem.

## Article-standard optimization (2026-10-17)

The [optimization record](research/decisions/2026-10-17-article-standard-optimization.md) has the findings, placements and
validation. No theorem statement, certificate, coverage or status changed.

- **Classical specification.** The [classical KLS gate](research/audits/KLS/Classical/README.md) is now part of the
  reviewed tree, with pinned Mathlib-only templates, a driver and a `research/verify.py` gate in both modes. It compiles
  three classical formulations and their client, checks the axioms, replays both modules and rejects false-statement
  mutations. The [review record](research/decisions/2026-10-17-classical-kls-specification.md) has the semantic review.
- **Reusable interfaces.**
  - `symmetric_trace_integral_extension_mul` and its a.e. form take an arbitrary real coefficient; the coefficient-2
    theorems are their specializations.
  - `BKL/CumulantBound.lean` holds the closed producers `cutoffEnergyClaim_153` and `cumulantBound_153`, which the BKL
    certificates and the final assembly consume.
  - `Theorem41.lean` keeps the conditional shared producers.
  - `exists_regular_moment_hessian_trace_bound` exposes the properties the Letwin regular-class proof uses at one actual
    moment witness.
- **License.** Project-owned code is licensed under the [Apache License 2.0](LICENSE). Vendored libraries keep their own
  licenses and notices.

## Verification evidence

**Every project-local declaration** is included in the axiom audit, with no target exclusion. The
[known vendored holes](formalization/vendor/README.md#upstream-holes) remain outside the KLS proof dependency closure.

**Receipts.**
- Each applies only to its recorded snapshot. Documentation-only maintenance has separate scoped checks and does not renew
  a full Lean receipt. See [receipt scope](research/verification.md#receipts-and-trust-scope).
- The full local verification receipt of the optimized snapshot, and its independent acceptance, are recorded in the
  optimization's control checkpoint (`build/reviews/2026-10-17-article-standard-optimization/STATE.json`).
- Earlier receipts, including the stage-4 checkpoint, cover their own snapshots.

## Navigation

- **Entry points:** the [Lean design](LEAN_DESIGN.md) and [calling examples](examples/README.md) give the current library
  entry points.
- **Source tree:** the [filename directory](formalization/MODULES.md) expands it.
- **BKL layout:** the [BKL module guide](formalization/FunctionalInequalities/KLS/BKL/README.md) and the
  [layout decision](research/decisions/2026-10-17-bkl-module-reorganization.md) describe it.
- **Documentation and naming:** the [documentation maintenance decision](research/decisions/2026-10-17-documentation-navigation.md)
  and the [filename decision](research/decisions/2026-10-17-functionalinequalities-filenames.md) record the organization.

## Remaining-family maintenance

The documentation correction and source-layout batches preserve proof statements, assumptions,
certificates and historical records. The current records are the
[documentation correction](research/decisions/2026-10-17-other-families-documentation.md) and
[cutoff/weak-derivative layout](research/decisions/2026-10-17-cutoff-weak-derivative-layout.md),
[generic Hessian owners](research/decisions/2026-10-18-hessian-owner-layout.md),
[trace/proximal responsibilities](research/decisions/2026-10-18-trace-proximal-layout.md),
[Stein/MetricBV boundaries](research/decisions/2026-10-18-stein-metricbv-layout.md),
[regular moment layers](research/decisions/2026-10-18-moment-regularity-layout.md), and the
[current maintenance register](research/technical-debt/remaining-families.md).
Per-batch scoped/full verification and acceptance receipts are tracked in
`build/file-management/2026-10-17-other-families-optimization/STATE.json`.
They apply to their own recorded snapshots; maintenance does not advance mathematical status.

All five source-layout batches are independently accepted. The final frozen-source full receipt is
`build/verification/20261017T182503.125701Z/report.json` (297 gates, 282 audit clients and
864 module replays). Each batch retains its exact source/interface comparison and
acceptance. Subsequent navigation-only closeout has scoped checks; it does not renew that full
source-and-documentation snapshot receipt. Current Lean-only inputs are compared separately.
The cumulative report is `build/file-management/2026-10-17-other-families-optimization/REPORT.md`.
The queued review follow-up remains paused.

## Coordination

The original Claude session remains the canonical proof integrator. All proof API loops are idle; no missing proof or new
API call is part of current work.

The sealed stage-1 S3 and S4 failures and all historical evidence stay intact. Historical controller queues do not
override this handoff.

No commit, push, tag, remote CI or publication is authorized.
