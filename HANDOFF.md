# Current KLS handoff

Updated 2026-11-07. The paper register and the current Lean declarations define the mathematical
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

Palomar version 2 registers `KLSOpenAI.kls` and `KLSOpenAI.kls_locallyLipschitz` at
source commit `e60bc39b18ef691263c66e2dba8d64726f18060d`.
The proof packages use Lean/Mathlib v4.35.0; the Formal Conjectures statement uses Lean v4.33.1.
Publication updates do not change the mathematical declarations or internal certificate states.
See the [pre-extension base-selection review](research/progress/2026-10-31-palomar-publication-review.json).
The original KLS checkout and accepted preparation worktree remain preserved. The 33 paused Mathlib proposal files are excluded from this publication.
Next step: add the registered version-2 proof link to Formal Conjectures PR #7712 and address upstream review.
The [official full preflight](https://github.com/human-ai-mathematics/kls-lean/actions/runs/41625639426) and [Palomar mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/41631278646) passed for both endpoints at `e60bc39b18ef691263c66e2dba8d64726f18060d`. [Palomar version 2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=2) was registered on 2026-11-07 after the automated editorial review identified no blocking problems or warnings.
<!-- END CURRENT MAINTENANCE -->

## Publication and verification

- [Palomar v2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-01-000014&version=2)
  registers `KLSOpenAI.kls` and `KLSOpenAI.kls_locallyLipschitz` at
  `e60bc39b18ef691263c66e2dba8d64726f18060d`. The
  [Palomar submission guide](integrations/palomar/README.md) records their scope and evidence.
- [Formal Conjectures PR #7712](https://github.com/google-deepmind/formal-conjectures/pull/7712)
  is open for upstream review. Its [submission inputs](integrations/palomar/formal-conjectures/README.md)
  pin Lean v4.33.1 and use a deliberate statement placeholder.
- The [verification guide](research/verification.md) covers strict builds, declaration audits,
  kernel replay and metadata checks. The [OpenAI](integrations/openai/README.md) and
  [Palomar](integrations/palomar/README.md#checking) guides give the separate bridge and Comparator
  commands. Use the [release procedure](research/release.md) for publication checks.
