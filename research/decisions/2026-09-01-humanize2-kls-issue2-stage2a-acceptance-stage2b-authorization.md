# Accept Stage 2A Run 1 and authorize Stage 2B

Date: 2026-09-01

## Human decision

After receiving the stopped Stage 2A candidate, its zero-diagnostic mechanical evidence, the human
checklist, and an optional Claude 5 Fable interactive-review prompt, the user said “授权 Stage 2B”.
Within the staged dependency protocol, this explicitly accepts Stage 2A Run 1 as the experimental
dependency required by Stage 2B and authorizes preparation and one isolated subscription-backed
Stage 2B Run 1.

No persisted Claude final matrix was found. The acceptance rests on the user's authorization plus
the independently reproduced Lean, surface, semantic-comparison, and trace evidence recorded
below. It does not promote production code or certify a mathematical dossier.

Accepted candidate SHA-256:

```text
83847c7ef06cd6045a1d5d5a8595f3fb645be28e8af4c71d3e577187fb0ad586
```

The accepted copy is byte-identical to `review/pending/CandidateStage2ARun1.lean` and is named
`accepted/AcceptedStage2A.lean`.

## Sixteen-item acceptance record

1. **PASS — complete trace:** one root session, one turn, zero descendants, no forbidden tool,
   path, output, network, collaboration, client-state access, or Seatbelt drift.
2. **PASS — visible fixture:** exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B source and
   compiled pairs, and `CandidateStage2A.lean` were visible.
3. **PASS — mutation boundary:** only the candidate changed; all four accepted artifacts retained
   their pins and read-only modes, and no file was created, renamed, or deleted.
4. **PASS — imports and compilation:** the candidate imports only `AcceptedStage1B`, compiles with
   pinned Lean/Mathlib 4.33.0 and upstream Mathlib only, and passes the exact five-declaration
   surface verifier.
5. **PASS — namespace and surface:** it extends exactly `Issue2Autoformalization.Stage1A` and adds
   no namespace or public declaration beyond the requested five.
6. **PASS — linear-test definition:** `linearTest v` is exactly `fun x ↦ inner ℝ v x`, in the
   frozen argument order.
7. **PASS — pointwise simplifier:** `linearTest_apply` has the frozen statement and `@[simp]`
   attribute without an added assumption.
8. **PASS — function equality:** `linearTest_eq_inner` exposes the exact requested function
   equality rather than an API-different representation.
9. **PASS — gradient witness:** `hasGradientAt_linearTest` uses the correct real-Hilbert Riesz
   derivative, with completeness and no measurable-space hypothesis.
10. **PASS — gradient formula:** `gradient_linearTest` has the frozen pointwise type and `@[simp]`
    attribute and follows from the valid gradient witness.
11. **PASS — assumption placement:** the first three declarations use only the normed additive
    group and real inner-product hypotheses; completeness begins only at the gradient layer.
12. **PASS — zero-dimensional boundary:** no measurability, measure, probability, moment,
    finite-dimensionality, or nontriviality assumption was introduced.
13. **PASS — stage boundary:** no energy, admissibility, variance, Rayleigh, covariance, spectral,
    final theorem, extra import, or stronger ambient assumption appears.
14. **PASS — soundness:** there is no `sorry`, `admit`, axiom, unsafe/opaque/external escape,
    unrequested syntax/notation/macro/attribute, or diagnostic suppression.
15. **PASS — diagnostic cleanliness:** both the isolated verifier and independent review project
    compile at exit zero with no warning or linter diagnostic.
16. **PASS — status boundary:** acceptance creates only a human-reviewed experimental dependency;
    it changes no production theorem, dossier, certificate, ledger, manuscript, or mathematical
    status.

## Stage 2B authorization boundary

Stage 2B may expose the accepted Stage 1A, Stage 1B, and Stage 2A source/compiled dependencies to a
fresh isolated actor. It contains exactly the linear-test analytic layer:

- the probability-normalized Dirichlet energy of a linear test;
- admissibility of the linear test from a finite second moment of the identity; and
- the fixed-constant variance bound obtained by applying the accepted Poincaré inequality.

The authorization covers freezing the exact three-declaration API, prompt, human checklist,
oracle surface, three-dependency fixture, verifier, deny-default candidate-only runner, complete
trace audit, model-free validation, direct authentication of a fresh Stage 2B actor home, and one
subscription-authenticated Run 1.

It excludes the extended Rayleigh quotient, covariance and spectral layers, final Issue 2
assembly, another KLS target, hidden production source or proof text in the actor lane, a model
reviewer, automatic acceptance, production promotion, dossier certification, and any ledger or
manuscript change.

## Frozen Stage 2B design and pre-run validation

The exact API is frozen to `dirichletEnergy_linearTest`, `isAdmissible_linearTest`, and
`variance_linearTest_le` under the complete real-inner-product and abstract measurable-space
context. The finite-moment hypothesis is exactly `MemLp (id : E → E) 2 μ`. No Borel,
finite-dimensional, nontrivial, Rayleigh, covariance, spectral, or final-assembly material is in
scope.

The stopped Stage 2A candidate and its accepted copy compare byte-for-byte. Rebuilding all three
accepted modules under Lean 4.33.0 with upstream Mathlib only produced the pinned Stage 2A
compiled-artifact SHA-256
`e2581fe4fcd46cd98353e47874bfb32d1ae5400c5cbae115c165b8f8ae0fce8f`.

Before any Stage 2B model call, the model-free suite passed all of the following:

- deterministic source-to-`.olean` rebuild of all three accepted layers;
- exact nine-entry actor reset and physically immutable accepted artifacts;
- compiler-failing untouched sentinel and exit-2 verifier rejection;
- silent compilation of the hidden known-good exact three-theorem surface;
- rejection of an added axiom and of diagnostic suppression;
- deny-default Seatbelt enforcement with candidate-only writes and hidden repository/oracle/client
  state;
- one-session, one-turn, zero-descendant complete-trace policy tests; and
- fail-closed live-run acknowledgement and fresh-login gates.

`pins/stage_2b.sha256` freezes the actor-facing semantics, prompt, human rubric, three accepted
dependency pairs, toolchain metadata, nine-entry fixture, hidden production surface hash,
candidate verifier, isolation policy, flow, runner, trace auditor, and tests. A live result will be
recorded separately after the actor stops; none of these pre-run checks constitutes acceptance.
