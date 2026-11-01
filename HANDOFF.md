# Current KLS handoff

Updated 2026-11-02. This publication candidate contains accepted mathematical sources and current
maintenance. The paper register and the current declarations own mathematical scope; a local
working-tree receipt does not certify a future commit or release.

## Accepted scope and retained boundaries

The dimension-free KLS theorem is proved through the accepted BKL main line, including zero
dimension and singular affine supports. Compact Letwin constant 8 remains the BKL input.
The noncompact Letwin constant-8 theorem and the BKL alternative to Letwin Theorem 1.1 have
separate registered certificates. No numerical final KLS constant is extracted.

Letwin Lemma 2.2, Theorem 2.5 and the same-potential calculus/Stein results hold for the
paper's bounded open convex source class, at every admissible moment potential. CEK Theorem 2
is proved; a CEK paper-target certificate is not registered. Earlier C0 variational and
Dirichlet constructions retain their own intermediate gaps. The original Letwin Theorem 1.1
route and the uncut Eldan construction remain outside the completed scope.

Use the [literature register](research/progress/LITERATURE.md),
[proof path](research/progress/PROOF-PATH.md),
[current source-scope review](research/progress/target-reviews.md) and
[source layout review](research/progress/source-layout-review.md) for exact statements,
hypotheses, constants, dimensions and current owners. The four exploratory routes remain
historical research records, not current formalization targets.

<!-- BEGIN CURRENT MAINTENANCE -->
## Current maintenance

`KLSOpenAI.kls` at public commit `33fff6ea218ae07e42115bd1eacfcf7d39c534cb` is registered as
[PALOMAR-2026-11-01-000014 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=1).
The public record, exact source/target/configuration, archived mechanical report, automated review
and preserved source tag have been checked. The automated review is not human peer review.
The monitoring automation was deleted at the user's request and remains stopped.

The separate Lean v4.33.1 [Formal Conjectures PR #7712](https://github.com/google-deepmind/formal-conjectures/pull/7712)
links that immutable version with `formal_proof using lean4`; its main theorem is a statement
placeholder. Strict module build, exact ordinary-statement correspondence and standard axiom checks
pass locally. The PR is ready for review and its Google CLA check passes; upstream workflows
still require maintainer approval. The user confirmed personal copyright ownership. No CLA was
signed by an agent.
See the [current source review](research/progress/2026-10-31-palomar-publication-review.json).
The original KLS and preparation worktrees, unrelated validation-tool edits and mathematical interfaces remain preserved.
Readability maintenance reorganizes local scopes without changing proof text. Complete full local verification of the selected maintenance tree before publishing it.
These maintenance commits are local only; no push or remote certification is authorized. The registered Palomar record continues to identify only its fixed public commit above.
<!-- END CURRENT MAINTENANCE -->

## Current publication candidate

The selected publication contains the accepted Lean/Mathlib v4.35.0 proof development and
`integrations/palomar` for the closed `KLSOpenAI.kls` endpoint. The original v4.33 checkout and
the accepted v4.35 preparation worktree remain separate and unchanged. All 33 paused Mathlib
proposal files are excluded. The [publication review](research/progress/2026-10-31-palomar-publication-review.json)
records that selection; the [migration review](research/progress/2026-10-31-palomar-module-migration-map.json)
records the explicit interface adaptations. No Lean proof or statement changes in this publication step.

Fourteen formerly private declarations are exposed with identical data; eight remain scoped.
The explicit `eLpNormEssSup` and same-function probability-map representations preserve their
reviewed mathematical meanings. Five vendor norm formulas gain existing a.e. strong
measurability premises; upstream Cadlag/indistinguishability owner and type adaptations are
itemized. These exceptions add no KLS endpoint hypotheses or paper/certificate coverage.

The [Formal Conjectures inputs](integrations/palomar/formal-conjectures/README.md) target the
separate Lean v4.33.1 pin. Their main theorem is a deliberate statement placeholder. The
`formal_proof` annotation records the verified Palomar v1 entry above; it does not supply a local
proof of the FC statement placeholder.

## Verification of future publication snapshots

Freeze the full source before verification. Run `python3 research/verify.py` for strict builds,
all 447 live independent audit clients, local/vendor/private/generated declaration axiom
audits, statement and metadata checks, and local-module kernel replay. The OpenAI bridge
and Palomar retain their separate strict checks. Run an independent Git consumer with
`python3 research/downstream.py --rev <full-commit>`.

The final public commit also needs the KLS, OpenAI and Palomar Linux sandbox Comparator
checks (Palomar requires NanoDa), remote Lean certification and the separate official Palomar
preflight. Native macOS development judging does not provide Linux sandbox evidence.
[BKL independent targets](research/audits/BKL/IndependentTargets/README.md) retain their
separate source-PDF, definition-closure, mutation and replay checks.

Raw pass/fail receipts remain under ignored `build/` and in their workflow artifacts. A
receipt certifies its recorded input hashes, revision and trust scope; earlier preparation,
v4.33 or Linux receipts do not certify this publication commit. No future pass or registration
is asserted by this tracked handoff. Imported compiled dependencies retain their documented
trust boundary. See the [verification guide](research/verification.md) and
[release procedure](research/release.md).

Preserve the two original worktrees, indexes, staging and paused contributions. Regenerate
progress views from the publication index, keeping proof statuses and literature scope fixed.
Human UP-1/API-1/LET-1 boundaries in the
[maintainer checklist](research/progress/public-interface-review.md#focused-maintainer-checklist)
remain unchanged; automated checking supplies no personal approval or independent peer review.
