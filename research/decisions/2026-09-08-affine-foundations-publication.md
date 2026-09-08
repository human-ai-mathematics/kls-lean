# Affine foundations: semantic corrections and publication change list

Date: 2026-09-08. The owner requested a semantic and mathematical acceptance review of the
current work, then explicitly authorized fixing the findings and pushing to GitHub. This CL
covers the accumulated publication to `numina-functional-inequalities/kls-lean` on `main`.

## Accepted mathematical scope

The local ledger has seventeen proved nodes. This publication includes the Borell density and
moment representation, ambient/intrinsic covariance comparison, the covariance-gradient core
closure, the closed affine covariance form, affine translation invariance, and the equivalence
of the isotropic, covariance-normalized and affine KLS bounds for each fixed finite constant.
It includes their library dependencies, certificates, axiom guards, definition checks, Blueprint
anchors, task infrastructure records, and the topic-directory organization used by the proofs.

The existing linear-test, tensorization, Gaussian and frontend-comparison certificates remain
part of the validation scope. No universal KLS bound, Markov/Dirichlet witness, Cheeger-energy
identification, or CMH recovery theorem is added. The literal `KLS.Conjecture` currently receives
a one-way implication from `AffineBound`; the converse passage from the `Fin n` space family to
the all-spaces formulation is not a library theorem in this publication.

## Semantic review and corrections

The review checked the new statements against the actual definitions, the closed-operator and
approximation proofs, the intrinsic covariance and Borell hypotheses, and the pinned CMH source
`modules/kls/41-cmh-normalization.tex` at
`8185e46ffb040e04fea076953e5bcaeb4157d71a`. The source core is the restrictions of ambient
`R + C_c^infinity(V)`, completed in the covariance graph norm. The Lean core has this meaning
and does not impose a zero boundary trace on the support interior.

Two corrections are made after that review:

1. `Covariance.exists_whitening` and `exists_whitening_of_isSymmetric` return a self-adjoint
   continuous linear equivalence satisfying `W Sigma W = I`. They do not return positivity or
   uniqueness of `W`; `Sigma = I, W = -I` is a counterexample to inferring the positive inverse
   square root from these conditions. The theorem/module comments, reduction commentary,
   Blueprint, handoff and ledger provenance now say “self-adjoint whitening”. The proof's
   construction still uses positive eigenvalue square roots, and the reduction still consumes
   only the existing whitening identity. Both affected Lean files have identical non-comment
   source before and after the correction; no statement, proof or normalization changed.
2. Current handoff and verification/Blueprint guides no longer describe the Borell density and
   moment theorem as unproved. Current certificate summaries are synchronized, while dated
   decisions retain their original historical status. The definition-stage handoff now points
   to the subsequent closability, closed-form and translation certificates.

The two affected source hashes in the isotropic-reduction infrastructure record are refreshed
after the comment-only comparison. No infrastructure state or mathematical claim is promoted
by this refresh. The original statement golden remains unchanged and covers its original
26-declaration closure; it does not cover every newly introduced affine definition.

The prior review also compiled two temporary, standard-axiom-only checks: the negative-whitening
example above and the identity between raw covariance energy and variance for a linear test.
Those checks and the detailed review remain local artifacts under
`build/semantic-audit/2026-09-08/`; they are not additional production certificates.

## Remote history and publication contents

The fetched `origin/main` is `fc235a149bff0cba64f2547908e78a74e38d4ec2`, which reverts
`575c82c30c93f35ca5550ab866466490e046743c`; its tree equals `0451f2e`. The reviewed local
checkout is based on `575c82c` and contains the subsequently completed affine work.
Publishing this accepted complete version therefore restores the previously withdrawn
Borell/covariance foundations as dependencies of the new results.

Preserve the prior revert in history. Integrate that exact remote revert with an explicit
non-fast-forward `ours` merge retaining the reviewed foundation tree, then commit the current
source batch on `main`. This resolution is limited to the verified revert; a different remote
change requires inspection. Check that the integration preserves the working files, and use a
normal fast-forward push from the remote tip, without rewriting remote history.

The batch also includes the already-reviewed `checkdecls` repair: `Dev/Search.lean` remains a
scratchpad, but is not declared as a never-built Lake library that the Blueprint checker would
try to import. Its historical failure is recorded separately in
`research/explorations/2026-09-07-blueprint-ci-checkdecls-dev-library.md`.

## Validation and evidence boundary

The pre-correction semantic review passed
`build/verification/20260908T073853.560740Z/report.json`: 100 Python tests, seventeen certificates,
250 declaration axiom reports and 104 local-module kernel replays; its source digest was
`0c10753b50952aed4a090a625d8de60b2dbc072770e5aa292c4d99a20c5bbe72`.
This is prior evidence, not the receipt for the changed publication candidate.

After finishing source/decision edits and committing, run `python3 research/verify.py` on the
actual candidate and render the Blueprint PDF/web with declaration-link checks. Push only after
these checks pass. The generated verification receipt owns the final source digest and HEAD;
do not write its digest back into this source record. Verify GitHub `refs/heads/main` against the
pushed SHA and inspect the workflows for that exact commit.

Local replay trusts pinned third-party compiled imports. Generated artifacts and local caches
remain ignored. Local validation, publication and remote CI completion are separate events;
this pre-publication record does not assert a future event has already succeeded.
