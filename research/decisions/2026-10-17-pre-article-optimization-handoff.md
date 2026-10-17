# Current KLS handoff

Updated 2026-10-17 after acceptance of the selected KLS proof route and the owner's request to organize documentation and navigation.
The previous handoff is retained in the [dated archive](research/decisions/2026-10-17-pre-documentation-navigation-handoff.md).

## Result and mathematical scope

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the selected BKL cutoff-localization route.
The unchanged target uses one finite constant for every dimension and every log-concave probability law with finite second moment,
in the covariance-normalized literature Poincaré form. Dimension zero and singular affine supports are included.

| Stage | Accepted result | Detailed record |
| --- | --- | --- |
| 1 | Compact Letwin Theorem 1.2 with exact constant 8 | [Letwin stage](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md) |
| 2 | BKL (95) in finite-horizon cutoff form | [Localization stage](research/handoffs/2026-10-17-bkl-step2-stochastic-localization.md) |
| 3 | BKL Theorem 4.1 in source form, one universal constant for all orders and dimensions | [Cumulant stage](research/handoffs/2026-10-17-bkl-step3-theorem41.md) |
| 4 | BKL Theorem 1.1 and the actual `KLS.kls` | [Final stage](research/handoffs/2026-10-17-bkl-step4-kls.md) |

The [paper register](research/progress/LITERATURE.md) owns exact source scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean. BKL's main theorem is covered.
Letwin's noncompact theorem, the uncut Eldan process and literal identities (68)–(73), the uncut intermediate BKL statements,
and the four exploratory routes remain separate open results.

## Verification evidence

The selected integrated proof snapshot passed full local verification and independent acceptance, recorded in the
[stage-4 checkpoint](build/reviews/2026-10-17-bkl-step4-kls-goal/STATE.json).
The [second independent review](build/reviews/2026-10-17-kls-second-independent-review/REVIEW.json) adds fresh full verification,
strictly compiled Mathlib-only specification clients and the actual KLS proof-dependency traversal.
Its classical convex-body and locally Lipschitz clients use only Lean's standard axioms.

Every project-local declaration is included in the axiom audit, with no target exclusion.
The [known vendored holes](formalization/vendor/README.md#upstream-holes) remain outside the KLS proof dependency closure.
Receipts apply only to their recorded snapshots; documentation-only maintenance has separate scoped checks and does not renew a full Lean receipt.
See [receipt scope](research/verification.md#receipts-and-trust-scope).

## Current work and coordination

The selected mathematical route is complete. Documentation and navigation have been organized as
recorded in the [maintenance decision](research/decisions/2026-10-17-documentation-navigation.md). No further proof goal is selected.
Use the [Lean design](LEAN_DESIGN.md) and [calling examples](examples/README.md) for current library entry points.
The [filename directory](formalization/MODULES.md) expands the complete source tree; the
[filename decision](research/decisions/2026-10-17-functionalinequalities-filenames.md) records the current path-only family organization and its acceptance boundary.

The subsequent [BKL layout decision](research/decisions/2026-10-17-bkl-module-reorganization.md)
separates process integration, cutoff-energy induction, posterior estimates and final theorem assembly.
Use the [BKL module guide](formalization/FunctionalInequalities/KLS/BKL/README.md) and
[complete declaration-location map](research/api-migration/2026-10-17-bkl-module-map.json).
Its [maintenance receipt](build/file-management/2026-10-17-bkl-reorganization/COMPLETION.json)
records validation of this layout; mathematical scope and certificate status do not change.

The original Claude session remains the canonical proof integrator. All proof API loops are idle; no missing proof or new API call is part of this task.
The sealed stage-1 S3 and S4 failures and all historical evidence stay intact. Historical controller queues do not override this handoff.
No commit, push, tag, remote CI or publication is authorized.
