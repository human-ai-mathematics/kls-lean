# Current KLS handoff

Updated 2026-10-19 for public-revision preparation.

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

Use the [context MCP](research/context-mcp.md) for snapshot-bound registry and local-receipt
queries. The [verification guide](research/verification.md#receipts-and-trust-scope) defines
acceptance scopes. Receipts and execution logs stay local under ignored `build/`; remote Lean
evidence is the terminal GitHub Actions run for its exact `head_sha`. Neither a registry entry
nor an old receipt verifies a later source tree.

Use the [calling examples](examples/README.md), the [compiler API directory](formalization/API.md),
the [audit client guide](research/audits/README.md) and the
[short review checklist](research/workflow.md#review-after-mechanical-checks). The
[downstream runner](research/downstream.py) accepts one full Git commit, builds three narrow
clients in a fresh Lake project, audits their complete primary declaration closure and replays
the local compiled modules; it does not accept a working-tree overlay or renew a certificate,
and explicit third-party compiled caches remain trusted. Known
[vendor holes](formalization/vendor/README.md#upstream-holes) remain isolated.

## Current work and next step

The current task prepares a frozen source snapshot for full local verification and an
approved Git revision for downstream and remote certification. The
[release procedure](research/release.md), [contribution guide](CONTRIBUTING.md) and
[citation metadata](CITATION.cff) describe public use and the exact-revision requirements.
Repository visibility and previously pushed history remain unchanged by this preparation.

CI cache preparation recognizes both aggregate `Mathlib` and dotted imports, checks their
pinned compiled closure, and rejects an incomplete cache before the build. The verifier
prints live progress and retains incomplete-run state; disk exhaustion, cache misses,
compiler failures and manual cancellation have distinct evidence. The strict declaration,
audit and kernel-replay gates remain enabled. No old or cancelled run verifies a new revision.

The section-variable maintenance is recorded in the
[scope review](research/technical-debt/variable-scopes.md). Repeated property premises,
instance exclusions and clipped-test hypotheses have local scopes with unchanged interfaces
and proofs. Five theorem-local `unusedVariables` exceptions remain intentionally: `omit`
would change their interfaces, while unused explicit `include` premises still warn in
Lean 4.33.0. No further style cleanup is required before the release checks.

Mathematical statements, proof bodies, hypotheses, parameter names/order, normalization,
dimensional scope and all 34 certificate states are retained. New mathematical work selects
a pinned literature target under the [workflow](research/workflow.md). The
[module directory](formalization/MODULES.md) locates source owners; the
[maintenance register](research/technical-debt/remaining-families.md) lists unresolved debt.
Superseded operational handoff text is preserved verbatim with its hash under ignored
local history. Fresh-clone instructions and validation inputs remain tracked.
