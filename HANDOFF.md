# Current KLS handoff

Updated 2026-11-03. The paper register and the current Lean declarations define the mathematical
scope. Verification receipts apply to their recorded source snapshots.

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
The 2026-11-02 style revision edits the bridge source after the preflighted commit `ed8da44bf8637d31bfd352d22a8a59a3a4445bf2`; certificate states remain unchanged.
See the [pre-extension base-selection review](research/progress/2026-10-31-palomar-publication-review.json).
The original KLS checkout and accepted preparation worktree remain preserved. The 33 paused Mathlib proposal files are excluded from this publication.
Next step: run the official full preflight on the public commit containing the style revision, then complete new-version intake once the Palomar host permits access; add a proof link only after actual registration.
The historical official full preflight covers `ed8da44` only; the edited source awaits a fresh preflight, new-version intake remains blocked by the submission host and no new Palomar version exists.
<!-- END CURRENT MAINTENANCE -->

## Publication and verification

- [Palomar v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=1)
  registers `KLSOpenAI.kls`. The [Palomar submission guide](integrations/palomar/README.md)
  describes the locally Lipschitz endpoint and the historical [official preflight at `ed8da44`](https://github.com/human-ai-mathematics/kls-lean/actions/runs/41430632501).
- [Formal Conjectures PR #7712](https://github.com/google-deepmind/formal-conjectures/pull/7712)
  is open for upstream review. Its [submission inputs](integrations/palomar/formal-conjectures/README.md)
  pin Lean v4.33.1 and use a deliberate statement placeholder.
- The [verification guide](research/verification.md) covers strict builds, declaration audits,
  kernel replay and metadata checks. The [OpenAI](integrations/openai/README.md) and
  [Palomar](integrations/palomar/README.md#checking) guides give the separate bridge and Comparator
  commands. Use the [release procedure](research/release.md) for publication checks.
