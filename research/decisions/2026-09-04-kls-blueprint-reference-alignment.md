# KLS Blueprint reference alignment

**Decision date:** 2026-09-04 (Asia/Shanghai).

**Type:** documentation, provenance, and dependency-graph alignment.

**User authorization:** the repository user instructed that Blueprint repair phase one should
start and required the handoff filename to be the literal `HANDOFF.md`, not an agent-specific
name.

## Audited baseline

The read-only audit began from clean `main` at
`5b1b44219050be0290c24e5765166f0298ff1ca4`, then equal to `origin/main`. The canonical write
remote is `https://github.com/human-ai-mathematics/kls-lean.git`. The remotes named
`legacy-fork` and `legacy-upstream` are historical sources. `legacy-fork` is a historical remote,
not the repository named by this decision.

The Lake package is nested under `formalization/`. The external planning prompt reviewed before
this decision named the old `lyw-ops/numina-functional-inequalities-formalization` repository and
assumed files and commands that do not exist in the current checkout. Those mismatches are not
instructions to recreate the old layout.

## Decision

Phase one makes the following documentation and graph corrections without changing Lean theorem
statements or the production `a-series` ledger:

1. `HANDOFF.md` becomes the current root handoff. The prior agent-specific snapshot is absent from
   the current branch.
2. The Blueprint distinguishes the generic optimizer `constantOfL2Energy μ E` from the
   repository-selected intrinsic-affine canonical energy and constant.
3. A shared analytic bridge layer records selected-to-literature comparison, affine-isotropic
   reduction, Cheeger comparison, and the one-dimensional endpoint. Spectral sufficiency remains
   in the route chapter rather than being attributed to this shared layer.
4. The legacy/relaxed constant bridge is routed through relaxation and recovery, not through the
   stronger raw/core agreement statement.
5. Ambient/intrinsic equality is stated as a coordinate theorem with a concrete proof plan rather
   than an unspecified comparison.
6. Route composition gains explicit pinned provenance, recursive AND/OR structure, shared
   repository-facing adapters, evidence classes, and active/historical/refuted branch
   disposition. Upstream states and evidence paths are a manually audited snapshot bound to an
   immutable source revision. The checker validates their schema and composition, not their remote
   contents; the pinned source remains authoritative for upstream lifecycle and review evidence.
7. The literal weighted Eldan-B package is recorded as refuted historical provenance and excluded
   from active alternatives. No speculative replacement is created.
8. Bibliography and prose are aligned with the actual roles of the sources. In particular,
   Lee--Vempala 2024 is not described as a survey, and no reviewed upstream implication is called
   a Lean theorem.

The Blueprint continues to follow the repository's Formech-inspired writing convention: small
public interfaces, ordinary mathematical language, explicit dependency edges, and explicit
non-claims.

## Source and status rules

- Local Lean declarations plus the local build determine local certification.
- `research/a-series/ledger.yaml` owns the four production node lifecycles.
- Blueprint sources and route metadata are derived navigation, not a second certification ledger.
- Long-route statements and provenance are pinned to
  `numina-functional-inequalities/kls-exploration@8185e46ffb040e04fea076953e5bcaeb4157d71a`.
- `checked_by: agent` is review provenance and never authorizes `\leanok`.
- An exact mathematical statement without `\leanok` is not locally Lean-certified. Its separate
  mathematical or upstream state may be open, conditional, proved with agent review, or imported.
  `\notready` is reserved for an interface whose hypotheses or normalization are not frozen.
- TeX `\uses{...}` is logical AND. Recursive OR belongs in `route-composition.yaml`.
- `route-composition.yaml` records roadmap composition; it is not a proof certificate.
- For a git-backed source the local checker verifies the repository/revision pin and metadata
  shape, but it does not fetch that revision or read its ledger and review artifacts. Any pin
  change therefore requires a fresh manual provenance audit.

## Mathematical alignment

The already certified closed-quadratic spine is unchanged. This record does not promote the
Dirichlet property, `2 Ch_μ`, a raw/core theorem, frontend equality, affine whitening, a generator,
a spectral-gap identity, or KLS.

The key correction is that equality of the legacy smooth-test and ambient relaxed Poincare
constants does not require raw/core energy equality. The fixed-constant predicates should be
identified by the defining relaxation inequality in one direction and a recovery sequence plus
`L²` variance continuity in the other. Raw/core agreement remains optional and requires genuine
extra hypotheses because raw gradient energy is representative-dependent for singular measures.

The ambient/intrinsic-affine bridge is stated precisely at the Blueprint level as a proposed exact
equality: restriction projects ambient gradients to the affine-support direction, while an intrinsic
smooth test extends constantly along normal directions. It remains pending human statement review
and non-certified until a Lean proof exists.

The statements introduced in the shared-bridge chapter are phase-one review proposals, not
human-frozen public theorem contracts. They carry `\notready` until their hypotheses and
normalizations have been reviewed. Statements attributed to published sources are imported
mathematics, but this does not freeze the repository's chosen formal interface or certify it in
Lean.

## Tool and source pins

- Long-route source: `numina-functional-inequalities/kls-exploration` at
  `8185e46ffb040e04fea076953e5bcaeb4157d71a`.
- Blueprint builder: `leanblueprint==0.0.20`.
- Declaration checker:
  `PatrickMassot/checkdecls@3d425859e73fcfbef85b9638c2a91708ef4a22d4`.
- Writing-style reference only:
  `lyw-ops/formech@d0bb1913acc1f710ba6eadf1244b633abbc75fb9`.

## Operational consequences

Every later worker must first verify the checkout, branch, remotes, and dirty state, then read
`HANDOFF.md`. Historical files must not be interpreted as current status. Generated Blueprint
artifacts must be rebuilt, not edited. Local validation, publication, and remote CI must be
reported separately and by exact SHA.

This decision supplements rather than rewrites
`research/decisions/2026-09-04-kls-lean-blueprint.md`. It asserts no commit, push, or remote CI
result beyond facts independently checked and named after the implementation is complete.

## Implementation scope

Phase one changes exactly 18 repository paths, grouped as follows:

- entry points and handoff: `HANDOFF.md`, `README.md`, `formalization/README.md`, and
  `formalization/blueprint/README.md`;
- Blueprint source and composition: `formalization/blueprint/route-composition.yaml`,
  `formalization/blueprint/src/content.tex`, `formalization/blueprint/src/macros/common.tex`,
  `formalization/blueprint/src/references.bib`, and the seven chapter files
  `00-orientation-and-status.tex`, `10-canonical-basic.tex`,
  `20-smooth-gradient-and-affine.tex`, `30-open-canonical-bridges.tex`,
  `40-certified-models.tex`, `45-shared-analytic-bridges.tex`, and `50-kls-routes.tex`;
- governance and validation: this decision, `research/check_blueprint.py`, and
  `research/tests/test_check_blueprint.py`.

No Lean source file and no production ledger file is changed.

## Local validation evidence

Before publication, the completed working tree passed the following local gates:

- ledger checker: `1 ledger(s), 4 nodes. 0 error(s).`;
- Blueprint checker: schema v2, 7 chapter files, 60 labels, 4 active routes, 0 errors;
- Python test suite: 62 tests, all passing;
- Lean build: 3230 jobs completed successfully;
- Blueprint build: PDF, web tree, and declaration checking all completed successfully;
- PDF inspection: 22 A4 pages, no overfull box or unresolved-reference warning, and every page
  visually inspected without clipping or overlap;
- `git diff --check`: clean.

These are local working-tree facts. They do not assert a commit, push, or remote CI result.
