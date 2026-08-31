# Accept Stage 1B Run 3 and authorize Stage 2A prompt preparation

Date: 2026-08-31

## Human decision

After reviewing the zero-warning Run 3 result and its Mathlib naming compatibility, the user said
to leave the two optional naming refinements unchanged and begin Stage 2A by generating its
prompt. This instruction accepts Run 3 as the experimental dependency for Stage 2A. It does not
promote the file into production Lean or certify a mathematical dossier.

Accepted candidate SHA-256:

```text
027e69674f78eb735b380b18beaf43e55779e0634d7222f46681f1bae30b752d
```

The accepted copy must remain byte-identical to
`review/pending/CandidateStage1BRun3.lean` and is named `accepted/AcceptedStage1B.lean`.

## Fourteen-item acceptance record

1. **PASS — complete trace:** one root session, one turn, zero descendants, no forbidden tool,
   path, output, network, collaboration, or client-state access.
2. **PASS — visible fixture:** exactly `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`,
   `AcceptedStage1A.olean`, and `CandidateStage1B.lean` were visible.
3. **PASS — mutation boundary:** only `CandidateStage1B.lean` changed; the accepted Stage 1A
   source and compiled dependency retained their pins and read-only modes.
4. **PASS — imports and compilation:** the candidate imports only `AcceptedStage1A`, compiles
   under pinned Lean/Mathlib 4.33.0, and passes the independent exact-surface checker.
5. **PASS — namespace and declarations:** the namespace and nested `HasPoincare` namespace expose
   exactly the thirteen frozen declarations.
6. **PASS — energy nonnegativity:** the proof uses pointwise nonnegativity of squared gradient
   norms and adds no integrability hypothesis.
7. **PASS — derivative/gradient norm:** the real-Hilbert Riesz isometry proves the norm identity
   without a measurable-space assumption.
8. **PASS — energy bridge:** almost-everywhere integral congruence proves the Fréchet-derivative
   energy formula without admissibility.
9. **PASS — fixed-constant API:** the four accessors and monotonicity theorem preserve the
   accepted test class and use energy nonnegativity.
10. **PASS — optimal constant definition:** it is definitionally the `ENNReal` infimum over finite
    nonnegative valid constants, with the empty subtype yielding `⊤`.
11. **PASS — optimal-constant theorems:** all five frozen directions and the universal-negation
    boundary compile with their exact precommitted types.
12. **PASS — soundness boundary:** no `sorry`, `admit`, axiom, unsafe/opaque/external escape,
    stronger hypothesis, extra import, or later-stage declaration is present.
13. **PASS — diagnostic cleanliness:** the exact compiler command exits zero with empty standard
    output and standard error, with no linter suppression.
14. **PASS — status boundary:** acceptance creates only a human-reviewed experimental dependency;
    it changes no production theorem, dossier, certificate, ledger, manuscript, or mathematical
    status.

## Stage 2A authorization boundary

Authorize preparation of the Stage 2A natural-language specification, exact declaration surface,
actor prompt, human checklist, fixture, and deterministic pre-model validation. Stage 2A contains
only linear-test geometry: the real linear test, its evaluation and function-equality rules, its
pointwise gradient witness, and the resulting gradient formula.

This decision does not yet authorize a subscription-authenticated Stage 2A model call. It excludes
Dirichlet energy, admissibility, finite-second-moment arguments, variance bounds, Rayleigh
quotients, covariance, spectral results, the final Issue 2 assembly, and every other KLS target.

## Frozen Stage 2A design

Stage 2A continues namespace `Issue2Autoformalization.Stage1A` and exposes exactly five public
declarations:

1. `linearTest` with definition `fun x ↦ inner ℝ v x`;
2. `linearTest_apply` with `@[simp]`;
3. `linearTest_eq_inner`;
4. `hasGradientAt_linearTest`; and
5. `gradient_linearTest` with `@[simp]`.

The inner-product order is frozen as `v, x`. The first three declarations require only a normed
additive commutative group and real inner-product space. Only the two gradient declarations add
completeness. No measurable-space, measure, probability, moment, finite-dimensionality, or
nontriviality hypothesis is permitted, so the interface includes the zero-dimensional case.

The actor-facing mathematical source is
`experiments/humanize2_kls_issue2_staged/inputs/issue2_stage_2a_linear_test_geometry.md`; the actor
prompt is `prompts/issue2_stage_2a_actor.md`. The actor workspace is specified to contain exactly
seven entries: `AGENTS.md`, `TASK.md`, the accepted Stage 1A and Stage 1B source/compiled pairs, and
`CandidateStage2A.lean`. Accepted artifacts are read-only and only the candidate is owner-writable.
The human checklist, hidden exact-surface oracle, known-good fixture, and verification scripts are
not actor-visible.

## Model-free validation

The Stage 2A model-free suite passed on 2026-08-31. It established:

- deterministic recompilation of `AcceptedStage1A.olean` and `AcceptedStage1B.olean` with pinned
  Lean 4.33.0 and upstream Mathlib only;
- byte-identical resets of the exact seven-entry actor workspace;
- expected rejection of the compiler-failing unattempted sentinel;
- silent compilation of a hidden known-good candidate and the independent exact five-declaration
  surface checker;
- rejection of an added axiom; and
- rejection of diagnostic suppression.

The initial aggregate pin check exposed one mistyped 63-character `lean-toolchain` checksum in the
new pin file. The checksum was corrected to the actual 64-character SHA-256, after which the full
suite completed with no warning output. This was a harness preparation defect and caused no model
call or mathematical attempt.

`pins/stage_2a.sha256` freezes the specification, prompt, human checklist, accepted dependencies
and hash records, Lean/Lake metadata, hidden oracle pin, fixture, exact-surface checker, known-good
test input, and model-free scripts. The live Humanize2 runner, Seatbelt policy, authentication
state, trace auditor, and post-run mutation audit have intentionally not been created in this
decision because no live model call is authorized yet.
