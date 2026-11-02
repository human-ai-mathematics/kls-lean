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

This checkout adds `KLSOpenAI.kls_locallyLipschitz` alongside the registered `KLSOpenAI.kls` endpoint,
using Lean/Mathlib v4.35.0, with the extended Formal Conjectures statement published on Lean v4.33.1.
The proof source is frozen at `ed8da44bf8637d31bfd352d22a8a59a3a4445bf2`; certificate states remain unchanged.
See the [pre-extension base-selection review](research/progress/2026-10-31-palomar-publication-review.json).
The original KLS checkout and accepted preparation worktree remain preserved. The 33 paused Mathlib proposal files are excluded from this publication.
Next step: complete new-version intake after the Palomar host permits access, review the returned report, then add a proof link only after actual registration.
The official full preflight passed for both endpoints at the frozen proof commit; new-version intake is blocked by the submission host and no new Palomar version exists.
<!-- END CURRENT MAINTENANCE -->

## Current publication candidate

The publication contains the accepted Lean/Mathlib v4.35.0 proof development and
`integrations/palomar`. The original v4.33 checkout and the accepted v4.35 preparation worktree
remain separate and unchanged. All 33 paused Mathlib proposal files are excluded. The
[publication review](research/progress/2026-10-31-palomar-publication-review.json) records that
selection; the [migration review](research/progress/2026-10-31-palomar-module-migration-map.json)
records the explicit interface adaptations.

Fourteen formerly private declarations are exposed with identical data; eight remain scoped.
The explicit `eLpNormEssSup` and same-function probability-map representations preserve their
reviewed mathematical meanings. Five vendor norm formulas gain existing a.e. strong
measurability premises; upstream Cadlag/indistinguishability owner and type adaptations are
itemized. These exceptions add no KLS endpoint hypotheses or paper/certificate coverage.

The 2026-11-02 extension adds new project code in `integrations/openai/KLSOpenAI/LocallyLipschitz.lean`
and a second Palomar endpoint, `KLSOpenAI.kls_locallyLipschitz`: a density-coordinate formulation of
BKL Theorem 1.1 for locally Lipschitz `L²` tests with possibly infinite gradient energy, over the
unchanged OpenAI model. The library in `formalization/` and its certificates are unchanged.
Registered version 1 (`PALOMAR-2026-11-01-000014`) covers only `KLSOpenAI.kls`; the new endpoint
is not registered. Its new-version intake is blocked by the submission host's Cloudflare
client-signature denial; no new submission was created.

The [Formal Conjectures inputs](integrations/palomar/formal-conjectures/README.md) target the
separate Lean v4.33.1 pin and state the locally Lipschitz form. Their main theorem is a deliberate
statement placeholder. Add the `formal_proof` annotation only after a registered Palomar version
includes `KLSOpenAI.kls_locallyLipschitz`.

## Verification

The [official full preflight](https://github.com/human-ai-mathematics/kls-lean/actions/runs/41430632501)
passed on 2026-11-02 for both endpoints at `ed8da44bf8637d31bfd352d22a8a59a3a4445bf2`, with
Lean, NanoDa and con-ron acceptance and no reported errors or warnings. Local strict builds,
bridge boundary/all-declaration axiom audits, the actual development Comparator, and the
Formal Conjectures strict build and statement correspondence also passed. The generalized
statement is published in [PR #7712](https://github.com/google-deepmind/formal-conjectures/pull/7712)
at `98067de1693653eec73b644e64a17b35477ede78`; upstream human review remains required.
These receipts cover the frozen proof source. Later documentation changes are checked
separately and do not inherit an exact-commit preflight claim.

To reproduce extension checks, run the strict OpenAI package build with its
import-boundary and all-declaration axiom audits, the Palomar `lake build Challenge Solution`,
`python3 research/comparator.py --target palomar --mode development` (NanoDa, unsandboxed),
the Formal Conjectures `--wfail` build with the correspondence client, and the documentation and
comparator Python checks. The public commit then needs the official Palomar full preflight
before submission. Native macOS development judging does not provide Linux sandbox evidence.
A change to `formalization/` instead needs `python3 research/verify.py` for strict builds, all
live audit clients, declaration axiom audits, metadata checks and local-module kernel replay.
[BKL independent targets](research/audits/BKL/IndependentTargets/README.md) retain their
separate source-PDF, definition-closure, mutation and replay checks.

Raw pass/fail receipts remain under ignored `build/` and in their workflow artifacts. A
receipt certifies its recorded input hashes, revision and trust scope; earlier preparation,
v4.33 or Linux receipts do not certify this publication commit. No registration of the new
endpoint is asserted by this handoff. Imported compiled dependencies retain their documented
trust boundary. See the [verification guide](research/verification.md) and
[release procedure](research/release.md).

Preserve the two original worktrees, indexes, staging and paused contributions. Regenerate
progress views from the publication index, keeping proof statuses and literature scope fixed.
Human UP-1/API-1/LET-1 boundaries in the
[maintainer checklist](research/progress/public-interface-review.md#focused-maintainer-checklist)
remain unchanged; automated checking supplies no personal approval or independent peer review.
