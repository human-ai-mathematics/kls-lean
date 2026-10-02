# Current KLS handoff

Updated 2026-10-02. This file holds the current state only. Earlier execution windows,
instructions and evidence are preserved in the
[handoff history](research/decisions/2026-10-02-handoff-history.md); they are not current task
authorization.

## Verified baseline

[Remote Lean certification run 36846629874](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/36846629874)
passed for commit `6ca1824f18e81b7409fd6e5aafdc0df53b14678e`, after the cache inventory was
fixed to include audit-client imports (the cause of the failed run 36165615113). Commit
`6c3437f` has the same tracked tree. Later commits change only documentation, progress
metadata and the progress generator; no Lean source changed, and that remote receipt does not
certify them.

The ledger has 26 certificates. Auxiliary proofs do not create certificates automatically.
`FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is the one intentional hole and lies outside
every certificate closure. Dimension-free KLS is open.

## Current mathematical scope

- Both numerical Cheeger–Buser comparisons hold for every finite-dimensional log-concave law:
  `C_P^lit ≤ 4 Ψ²` and `Ψ² ≤ π C_P^lit`, including affine-support dimension zero and infinite
  optima. The π bound passes through actual Gaussian smoothing and Cheeger test stability.
- The one-dimensional certificate proves the `4 Var` upper bound; it does not certify sharpness.
- ADMG Theorem 3.6's relaxed lower and upper Minkowski identities hold at measurable finite-mass
  Borel targets for measures finite on bounded Borel sets, with global indicator `L¹`
  convergence. Definition 3.3's globally Lipschitz class gives the bounded-support perimeter
  for every Borel measure at such targets. Lemma 2.1's equality of the two relaxed contents
  needs only a Borel measure. These are equalities of infima, not pointwise identities.
- On proper metric spaces the Remark 3.5 locally Lipschitz classes (global or compact-local
  `L¹`) give the perimeter at finite-mass targets for every Borel measure. Nonproper spaces,
  nonconvex support transfer and general RCD comparisons remain open.

No paper is covered under the criterion in the
[literature register](research/progress/LITERATURE.md#when-a-paper-is-covered). For exact
declarations, certificates and scopes use that register and the
[node register](research/progress/STATUS.md), not historical prose.

## Work plan

Work follows the published literature
([issue #8](https://github.com/numina-functional-inequalities/kls-lean/issues/8)); see the
[literature priorities](research/progress/README.md#literature-priorities) and the
[decision record](research/decisions/2026-10-02-literature-register.md). The four-route diagram
on the progress page is kept as an exploratory record; its pending nodes are not the work queue.

Paper lemma maps (numbered statements of a pinned source version, each mapped to Lean
declarations with ✓/◐/○/⇑) now cover Kannan–Lovász–Simonovits 1995, Bobkov 1999, E. Milman 2009,
Ambrosio–Di Marino–Gigli 2017 and De Ponti–Mondino 2021; see the
[paper lemma map](research/progress/README.md#paper-lemma-map). Source PDFs are kept outside the
repository.

Next: prepare a certificate for ADMG Theorem 3.6 stated against Definition 3.3
(`lipschitzRelaxation`). The exact statement is already proved by composition in
`research/audits/MetricBVDefinitionClassAudit.lean`; it needs a library declaration, Blueprint
and ledger registration, and owner semantic review before a milestone tag. The priority-1
Bakry–Émery `C_P ≤ 1/ρ` target waits for the Bakry–Gentil–Ledoux text; the existing Γ₂ results
for convex potentials do not prove the positive-curvature endpoint.

Open owner decisions: how to obtain stochastic calculus for priorities 4–5 (build here or build
on external Lean efforts), Mathlib upstreaming after an API cleanup, and the remaining CI
proposals in issue #8 (build cache, self-hosted runner). A scheduled CI run is declined: it
would add remote runs outside milestones. The opt-in milestone-only pre-push gate is described in
[workflow.md](research/workflow.md#local-milestone-gate).

## Delivery

Run change-appropriate checks in [research/workflow.md](research/workflow.md). Stage intended
canonical metadata, then regenerate progress with `python3 research/progress/update.py`; use
`--check` to detect drift. Remote CI is Lean-only and runs only by manual dispatch or a
`milestone/**` tag; do not use `[skip ci]`. Move superseded handoff sections to dated files in
`research/decisions/`.
