# Current KLS handoff

Updated 2026-10-20 for noncompact Letwin Theorem 1.2.

## Accepted result and open boundaries

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the finite-horizon cutoff
stochastic-localization route of BKL. Its target is unchanged: one finite covariance-normalized
literature Poincaré bound for every dimension and every log-concave probability law with
finite second moment, including dimension zero and singular affine supports.

The accepted chain is compact Letwin Theorem 1.2 (constant 8) → finite-horizon cutoff BKL (95)
→ source-form BKL Theorem 4.1 → source-form BKL Theorem 1.1 → KLS.
The [paper register](research/progress/LITERATURE.md) owns exact scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean and its certificates.
BKL's main theorem is covered. Letwin's noncompact Theorem 1.2 is now proved separately
by `KLS.LogConcave.letwinQuadraticBound`, with the source matrix form
`matrix_variance_le_eight`, for every n > 0 and exact constant 8. Theorem 1.1, the full
smooth regular approximation of Lemma A.1, the uncut Eldan
construction and literal identities (68)–(73), and the separate uncut intermediate statements
remain unformalized locally. The four exploratory routes retain their own statuses.

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

The 2026-10-20 local formalization batch removes compactness from Letwin Theorem 1.2 by
conditioning on growing balls, centering and covariance whitening, and passing mixed moments
through degree four to the limit. Generic convergence tools extend `Probability/Conditioning`;
the paper endpoint lives in `KLS/Letwin/QuadraticBound`. The existing compact certificate and
BKL main chain retain their scope. Lean/Mathlib remain v4.33.0; the proposed upgrade was cancelled.
The first four Product-Lp section/averaging helpers are independently accepted locally in
the separate Mathlib checkout; no Mathlib submission or second package is implied.
This batch adds no paper-target certificate and does not renew remote verification.

The [statement review](research/progress/statement-review.md) checks the contracts of all 34
registered certificates against the live text, with source checks for the main BKL/Letwin
statements and the ADMG target. It corrects stale completion claims, quantifier attribution,
test-class descriptions and the attribution of the local constant 153. Lean types, definitions,
proofs and certificate/progress states are unchanged by those textual corrections.

The module ownership and text corrections retain all mathematical statements and certificate
states. Further proof work selects a pinned literature target under the repository workflow.
Before an approved verification milestone, freeze the intended source snapshot, run full local
verification and select the exact committed revision for downstream and remote certification. The
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
General scalar coarea and slice helpers live in `Analysis/Coarea` and `Analysis/Hausdorff/Slice`;
metric BV foundations live in `Analysis/MetricBV`. The arbitrary-metric finite-measure client
[`examples/MetricBV.lean`](examples/MetricBV.lean) composes measure scaling with complement
symmetry and asserts that no KLS conjecture or smooth-test Poincaré interface is imported.
Perimeter/Minkowski identification and log-concave application modules retain their owners.
Product variance identities live in `Probability/ProductVariance.lean`, removing the
Probability-to-Poincare import; compact-set log-concavity lives in `Probability/LogConcave.lean`,
with Poincaré and affine-support imports now stated by their actual consumers. The public
namespaces of these moved modules are retained independently of file ownership.

BKL source Theorem 4.1 is assembled in `BKL/CumulantInduction.lean`, with
`exists_cumulantBoundCompact_of_letwinCompact` and `exists_cumulantBound_of_letwinCompact`;
source Proposition 7.1 lives in `BKL/TaylorBound.lean`; the closed source Theorem 1.1 entry is
`BKL.Localization.exists_isotropicBound`. These are explicit name/path migrations, with no
old aliases or forwarding modules. Conditional inputs and closed producers remain distinct.
The reviewed statement baselines permit only the log-concavity declaration's owning-module
substitution; their types and definition closures remain unchanged. Full local verification,
strict independent clients, axiom audits and local-module replay retain their distinct scopes.
Fresh-clone instructions and validation inputs remain tracked.
