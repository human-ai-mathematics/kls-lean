# General log-concave measures: intrinsic absolute continuity and literature-constant comparison

Date: 2026-09-06. The user requested “first generalize to arbitrary log-concave measures”,
continuing the earlier authorization to complete proofs directly. This batch completes the
general finite-dimensional version locally, without adding absolute continuity, density,
positive dimension, or moment assumptions to the original theorem.
HEAD is `70ca1c19c4d207a31716c2e589c0b096521a5490`; the working tree contains earlier uncommitted
work. No commit/push or remote CI; the original index remains byte-identical.

## Conclusions, sources, and reading order

1. [Affine support](../../formalization/FunctionalInequalities/Probability/AffineSupport.lean): add the theorem that the intrinsic measure of any probability law has full affine support.
2. [Log-concave geometry](../../formalization/FunctionalInequalities/KLS/LogConcave.lean): affine-isometric reconstruction preserves compact-set log-concavity; equal-radius closed-ball masses satisfy the log-concavity inequality; support and mass superlevel sets are convex. Intrinsic support has nonempty interior and Haar-null boundary.
3. [Ball averages](../../formalization/FunctionalInequalities/Probability/BallAverages.lean) and [measure domination](../../formalization/FunctionalInequalities/Probability/BallDomination.lean): neighborhood masses have a uniform positive lower bound on compact subsets of the support; Tonelli gives total ball-average integrals and local lower bounds; Besicovitch covering turns small-ball mass-ratio upper bounds into measure domination.
4. [Intrinsic absolute continuity](../../formalization/FunctionalInequalities/KLS/LogConcaveDensity.lean): derive intrinsic absolute continuity fully from those compact-set inequalities, then null probability mass of the intrinsic support boundary.
5. [General constant comparison](../../formalization/FunctionalInequalities/Poincare/Euclidean/LogConcaveComparison.lean): combine certified smooth/literature and legacy/relaxed comparisons to obtain the ambient legacy, intrinsic legacy, and literature constant chain for arbitrary log-concave probability laws, and selected/literature equality.

Absolute continuity is part of the finite-dimensional representation content of Borell (1974),
*Convex measures on locally convex spaces*, Theorem 1.1. The local proof follows the ball-average
route below, directly using this repository's compact-set definition. It does not claim to
translate the original proof line by line or assume an unproved Borel-set log-concavity bridge.
The constant comparison fully covers the original Blueprint specification
`thm:selected-literature-constant-equivalence`.

## Absolute-continuity proof and boundary review

Let ν be the intrinsic law, m the Haar reference, q_r(x)=ν(closedBall x r), and
b_r=m(closedBall 0 r).

- Minimality of affine support and isometric reconstruction give full affine span of intrinsic support; convexity then gives nonempty interior.
- Choose a larger compact ball in the interior. For fixed δ>0, compactness gives a uniform lower bound γ>0 for δ-ball masses at its centers. Tonelli gives an integral of q_r over the larger ball of at least γ b_r, hence a point with q_r≥c b_r in every neighborhood, where c>0 is independent of the small radius r.
- Superlevel sets of q_r are convex. Separation strengthens the existence of high-mass points in neighborhoods to q_r≥c b_r everywhere on a fixed ball B(a,R). A unit direction of a nonzero separating functional is used only when separation actually occurs; nontriviality of the space is not assumed.
- For arbitrary x, the midpoint inequality gives q_r≥sqrt(q_r(x)c b_r) on B((x+a)/2,R/2). Its total integral is b_r. Integrating, squaring, and cancelling positive finite b_r yields q_r(x)≤b_r/(c m(B(0,R/2))²). This constant depends on the measure; it is not a dimension-free KLS constant.
- Use the Besicovitch Vitali family for source measure ν. Its absolute-continuity premise is reflexivity ν≪ν, so the covering argument does not circularly assume ν≪m. Finally obtain ν≤C m and hence ν≪m.

All positivity and finiteness of Haar volumes are proved in Lean; division and cancellation
explicitly handle zero and infinity. The intrinsic space may be zero-dimensional and the
ambient measure singular. Optimal-constant equality holds in ENNReal, allowing zero and
infinity, without attainment or second moments, and without changing test domains or
normalization. The new certificate includes arbitrary `Fin n` Euclidean applications matching
`Conjecture` and a separate `Fin 0` check.

## Certification and atlas registration

The new exact node `lem:logconcave-intrinsic-absolute-continuity` is certified by
`Solutions.LemLogConcaveIntrinsicAbsoluteContinuity.certificate`; the existing
`thm:selected-literature-constant-equivalence` by
`Solutions.ThmSelectedLiteratureConstantEquivalence.certificate`. Both are
`proved / checked_by: lean`. Retain the ledger schema's `kind: lemma` convention, including
nodes labeled `thm:`; do not change checker kind rules.

The full statement and task classification of `thm:borell-logconcave-density` are retained.
Its upper semicontinuous log-concave density representative, interior local positive bounds,
and moments of all orders remain unproved. The constant comparison uses only absolute
continuity, so its Blueprint dependency now points to the new exact node. The route sidecar
marks only the actually proved shared selected/literature adapter as proved and binds local
ledger evidence. The KLS target, long routes, their conditions, and AND/OR composition are unchanged.

The original eight ledger node objects and all existing `mathematics` classifications are
unchanged. The new node is `published`, with local infrastructure available. Source hashes
for the constant comparison and comments in older comparison files are synchronized. New
proofs, axiom guards, and both certificates enter the default build. Current guides now list
74 mathematical nodes, 87 navigation labels, 10 certificates, and 4 active routes. Python
fixtures now allow a node to serve both as a certified result and as a route adapter, avoiding
duplicate labels while supplying the actual local evidence required by the checker.

All 57 protected files—KLS Definitions, Statement, golden files, and existing
decisions/explorations—match their entry hashes. `LiteratureComparison.lean` only updates
documentation to point to the generalization module; its eight proofs and signatures are
unchanged. No proof placeholder or additional axiom is introduced. KLS, Cheeger-energy
identification, and concrete Dirichlet properties are not proved in this batch.

## Local checks and final verification boundary

The entry source snapshot is
`af64ebc752ef58d682a1b747f2853b4c6f775ddbeac4bafff605ba56f10b6372`.
The precheck snapshot before writing this record is
`fb690033bfc84e7a4e8f4759f75982004fc8dc8c92d926ab6c52849d257ba87a`;
its ledger, Blueprint, and atlas structure checks passed, with no dependency cycles.
This stage completed default `lake build` (3268 jobs), both certificate builds (3107 jobs),
the final Euclidean-family and zero-dimensional typed-check build (3106 jobs), and 97 Python
tests. Tests initially failed on duplicate labels in an old fixture and all passed after
correcting it. All 23 new transitive axiom guards report exactly
`propext`, `Classical.choice`, and `Quot.sound`. Logs:

- `build/logconcave-extension/default-build.log`
- `build/logconcave-extension/certificates-build.log`
- `build/logconcave-extension/typed-checks-build.log`
- `build/logconcave-extension/python-tests.log`
- `build/logconcave-extension/change-audit.json`

After this record is written, run `python3 research/verify.py` to recheck tests, default build,
public-statement golden files, transitive axioms, and kernel replay of all local modules on
the final snapshot including this record. Actual outcomes, gate logs, final source SHA256,
and HEAD are recorded in `build/verification/<UTC timestamp>/report.json`, with atlas export
after success. This record neither claims a final pass in advance nor writes the final hash
back into itself, which would invalidate the receipt.

Third-party compiled imports remain trusted; there is no external independent check, isolated
source rebuild, or remote CI result. Local proofs, final-snapshot verification, and remote
publication are separate facts.
