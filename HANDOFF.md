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

Use the [verification guide](research/verification.md#receipts-and-trust-scope) for receipt
rules and acceptance scopes. Receipts and execution logs stay local under ignored `build/`; remote Lean
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
compiler failures and manual cancellation have distinct evidence. No old or cancelled run
verifies a new revision.

Remote CI keeps the strict build and declaration/vendor/classical audits, with the final
local-module kernel replay assigned to the [full local receipt](research/verification.md#receipts-and-trust-scope).
A single `leanchecker` process accumulates memory (14.4 GB after 40 modules locally), freezing
the 16 GB hosted runner; remote certification therefore skips that replay gate.
Run 39228796618 certified `845e61b` under that scope (1h21m; 9,856 local declarations, standard
axioms only; vendor gate 4,789 declarations with the 5 listed upstream holes isolated).

Mathematical statements, proof bodies, hypotheses, parameter names/order, normalization,
dimensional scope and all 34 certificate states are retained. New mathematical work selects
a pinned literature target under the [workflow](research/workflow.md). The
[module directory](formalization/MODULES.md) locates source owners.
Relocating `KLS/Geometry/Perimeter/MetricBV` to a top-level family remains a candidate only if an
independent reuse consumer and a dependency benefit are demonstrated; otherwise its existing KLS
perimeter owner remains.
Fresh-clone instructions and validation inputs remain tracked.
