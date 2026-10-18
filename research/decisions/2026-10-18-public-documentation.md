# Public documentation preparation

Date: 2026-10-18. Documentation-only maintenance before public release: root README wording,
a recorded-baseline section in `research/verification.md`, proof-path navigation to that
section, a pinned consumer revision in the example guide, targeted ignore rules for local
configuration and dotenv secrets, and a compact current handoff. No Lean source, hypothesis,
proof, certificate state, generated progress block, literature register or historical file
changed. The baseline evidence summarised in the verification guide applies to commit
`5d41bd7dd379d0c0858f1b8416f61c82e0fe26eb`, not to the tree containing these edits.

## Placement

- Owner: root and research guides (`README.md`, `HANDOFF.md`, `research/verification.md`,
  `research/progress/PROOF-PATH.md`, `examples/README.md`, `.gitignore`); extend existing owners,
  no new guide.
- Scope: English prose and ignore rules. The former `owner-selected`/`current controller`
  wording is replaced by the mathematical route description and current-work links; the cutoff
  versus uncut and compact versus noncompact distinctions are retained.
- Validation: scoped diff and link review, ignore-path probes (the three excluded files are
  ignored by name; sibling shared rules stay visible), preservation of unrelated files and of
  this archive's bytes; no Lean rebuild for prose.

## Superseded handoff, preserved verbatim

The following handoff is historical. Its coordination statements describe that prior stage.
Original UTF-8 SHA-256: `4f2ded76df6af523d18eb8115902da47b8414a50ec47d5acfce1748ff03f8b2f`.

````markdown
# Current KLS handoff

Updated 2026-10-18 for reusable downstream acceptance and library-usability maintenance.

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

## Library use and verification

Use the [calling examples](examples/README.md), [compiler API directory](formalization/API.md)
and [short review checklist](research/workflow.md#review-after-mechanical-checks).
The [downstream runner](research/downstream.py) accepts a full Git commit, builds three narrow
clients in a fresh Lake project, audits their complete primary declaration closure and replays
its local compiled modules. It does not accept a working-tree overlay or renew a certificate;
explicit third-party compiled caches remain trusted. Commands and failure receipts are described
in the [example guide](examples/README.md#reproduce-downstream-acceptance).

The [verification guide](research/verification.md) owns the full local command and receipt
boundaries. `build/verification/latest.json` records the latest full attempt; its source snapshot,
status and logs determine its scope. The downstream delivery evidence is kept separately under
`build/reusability/2026-10-18-downstream-runner/`. Known
[vendor holes](formalization/vendor/README.md#upstream-holes) remain isolated.

The [usability record](research/decisions/2026-10-18-library-usability.md) preserves the accepted
comment cleanup, Git consumer and API navigation batches. The
[runner record](research/decisions/2026-10-18-downstream-runner.md) preserves the preceding handoff
and this tool's placement and acceptance scope. Existing proofs, hypotheses, 34 certificate states
and historical records are unchanged; this work adds verification tooling and navigation.

## Coordination and next work

The original Claude read-only duplication review has delivered `READY_FOR_CODEX` under
`build/reusability/2026-10-18-duplication-review/`; independent acceptance of its classifications
and any implementation of its suggestions are separate work. No replacement was adopted here.
Proof workers are idle and the queued review follow-up stays paused. Source owners are in the
[module directory](formalization/MODULES.md); the
[maintenance register](research/technical-debt/remaining-families.md) retains deferred MetricBV
relocation. Local editor configuration is excluded from delivery.
````
