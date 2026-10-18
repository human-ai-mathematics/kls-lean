# Current KLS handoff

Updated 2026-10-19 for the local context-maintenance phase.

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

The maintenance scope is the read-only context MCP, scoped section variables in
`KLS/LogConcave/HessianStein.lean` and `HminusOne.lean`, and local retention of superseded
operational history. Mathematical statements, proofs, hypotheses, normalization, dimensional
scope and all 34 certificate states are retained. Current source reviews and validation inputs
remain tracked, so a fresh clone does not need the local history archive.

Each batch requires independent acceptance. Delivery requires full local verification of the
frozen combined tree before one commit and push, followed by one remote Lean certification for
the final pushed SHA after all local work. Read the outcome from that run; this file anticipates
no result. No further proof construction is queued. A new mathematical task must select its
pinned literature target under the [workflow](research/workflow.md). The repository stays private
until the owner explicitly changes visibility. The [module directory](formalization/MODULES.md)
locates source owners; the [maintenance register](research/technical-debt/remaining-families.md)
lists unresolved debt.
