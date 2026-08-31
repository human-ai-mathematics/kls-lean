# Accept Stage 2B Run 1 and authorize Stage 3 Run 1

Date: 2026-09-01

## Human decision

The user accepted Stage 2B Run 1 as the experimental dependency required by Stage 3 and
authorized one isolated subscription-authenticated Stage 3 Run 1. The decision followed a Claude
5 Fable interactive review using the persisted prompt at
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_2b_claude5_fable_interactive_review.md`.
That independent review reproduced the candidate hash, a silent 2,930-job
`lake build Stage2BRun1Review`, both Stage 2B verification scripts, the hidden oracle pin, and the
compact trace audit, then returned all sixteen checklist items `PASS` with a recommendation to
accept.

The review found no Stage 2B semantic or frozen-API difference. Relative to production, the
pre-accepted experimental namespace remains an API difference, missing docstrings are
documentation-only, and three implementation variants are proof-only:
`(InnerProductSpace.toDual ℝ E v).contDiff`, `hμ.const_inner v`, and the explicit
`rw [← dirichletEnergy_linearTest]` before applying the accepted inequality.

This acceptance does not promote production code, certify a mathematical dossier, or change a
ledger, manuscript, theorem status, or KLS claim.

Accepted candidate SHA-256:

```text
69c2eead467fbc0516c191e034cedd1c8593bdaac50c1681912a429337b5dffc
```

The accepted copy is byte-identical to `review/pending/CandidateStage2BRun1.lean` and is named
`accepted/AcceptedStage2B.lean`.

## Sixteen-item acceptance record

1. **PASS — complete trace:** one actor-root session, one turn, zero descendants, six local
   `exec` calls, no forbidden tool, path, output, network, collaboration, client-state access, or
   Seatbelt drift.
2. **PASS — visible fixture:** exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A source
   and compiled pairs, and `CandidateStage2B.lean` were visible, together with only the pinned
   toolchain and upstream Mathlib.
3. **PASS — mutation boundary:** only the candidate changed; all six accepted artifacts retained
   their pins and read-only modes, and no file was created, renamed, or deleted.
4. **PASS — imports and compilation:** the candidate imports only `AcceptedStage2A`, compiles
   silently with pinned Lean/Mathlib 4.33.0 and upstream Mathlib only, and passes the exact
   three-theorem surface verifier.
5. **PASS — namespace and surface:** it extends exactly `Issue2Autoformalization.Stage1A` and adds
   no namespace, section, attribute, or public declaration beyond the requested three theorems.
6. **PASS — energy identity:** `dirichletEnergy_linearTest` has the frozen statement; the accepted
   constant-gradient formula reduces the integrand to `‖v‖ ^ 2`, and probability normalization
   integrates that constant correctly, including at `v = 0` and in dimension zero.
7. **PASS — admissibility surface:** `isAdmissible_linearTest` has the frozen statement and uses
   exactly the explicit `IsProbabilityMeasure μ` witness and `MemLp (id : E → E) 2 μ`.
8. **PASS — smoothness field:** the Riesz functional
   `InnerProductSpace.toDual ℝ E v` proves smoothness of `x ↦ inner ℝ v x` without adding a
   differentiability, dimensional, or measurability assumption.
9. **PASS — square-integrability field:** `hμ.const_inner v` derives precisely the scalar
   projection `MemLp` fact from the coordinate-free second moment.
10. **PASS — energy-integrability field:** the supplied probability witness becomes a local
    instance, the squared gradient reduces to a constant, and integrability is proved rather than
    inferred from totalized integration.
11. **PASS — fixed-constant variance bound:** `variance_linearTest_le` obtains probability from
    `hP`, applies the accepted admissibility theorem and Poincaré inequality, and rewrites in the
    correct direction with the accepted energy identity.
12. **PASS — ambient and zero-dimensional boundary:** no `BorelSpace`, finite-dimensionality,
    nontriviality, separability, centered-moment, or stronger second-moment assumption appears.
13. **PASS — stage boundary:** no Rayleigh quotient, optimal-constant comparison, covariance,
    spectral result, Euclidean specialization, final theorem, extra import, or later-stage
    declaration appears.
14. **PASS — soundness:** there is no `sorry`, `admit`, axiom, unsafe/opaque/external escape,
    unrequested syntax/notation/macro/attribute/option, custom IO, or diagnostic suppression.
15. **PASS — diagnostic cleanliness:** the isolated verifier and independent review project both
    compile at exit zero with empty compiler output and no warning or linter diagnostic.
16. **PASS — status boundary:** acceptance creates only a human-reviewed experimental dependency;
    it changes no production theorem, dossier, certificate, ledger, manuscript, or mathematical
    status.

## Stage 3 authorization boundary

Stage 3 may expose the accepted Stage 1A, Stage 1B, Stage 2A, and Stage 2B source/compiled pairs to
a fresh isolated actor. It contains exactly this five-declaration surface inside namespace
`Issue2Autoformalization.Stage1A`, importing only `AcceptedStage2B`:

- `poincareRayleighQuotient`, defined as
  `ENNReal.ofReal (variance f μ) / ENNReal.ofReal (dirichletEnergy μ f)`;
- `poincareRayleighQuotient_le_optimal` for every admissible test, including zero energy and no
  finite valid Poincaré constant;
- `poincareRayleighQuotient_eq_of_pos` at strictly positive energy;
- `poincareRayleighQuotient_eq_top_of_energy_eq_zero` for positive variance and zero energy; and
- `admissibleRayleighQuotient_le_optimal`, the positive-energy real-quotient specialization.

Division is frozen to occur in `ENNReal` after separately applying `ENNReal.ofReal` to variance
and energy. Thus positive variance over zero energy is `⊤`, while `0 / 0 = 0`; no real
division-by-zero convention is imported. The definition has no probability hypothesis. No
`BorelSpace`, finite-dimensionality, nontriviality, separability, centered-moment assumption, or
stronger ambient condition is allowed, and dimension zero remains included.

The authorization excludes centered covariance forms or operators, covariance Rayleigh maxima,
spectral or eigenvalue results, Euclidean specialization, final Issue 2 assembly, every other KLS
target, hidden production source or proof text in the actor lane, a model reviewer, automatic
acceptance, production promotion, dossier certification, and any ledger or manuscript change.

## Frozen Stage 3 design and pre-run validation

The exact five-declaration API, mathematical specification, actor prompt, and human sixteen-item
checklist are frozen. The actor fixture contains exactly eleven entries: `AGENTS.md`, `TASK.md`,
the four accepted source/compiled pairs, and `CandidateStage3.lean`. All accepted artifacts are
physically read-only; only the candidate may mutate.

Rebuilding all four accepted modules under Lean 4.33.0 with upstream Mathlib only reproduced the
pinned Stage 2B compiled-artifact SHA-256
`1a28f1163e22e693bb5b269d671ad18b335838a1ce9018fe92c95e1b49c602cd`.
Before the Stage 3 model call, the model-free suite passed all of the following:

- deterministic source-to-`.olean` rebuild of all four accepted layers;
- exact eleven-entry actor reset and immutable accepted artifacts;
- compiler-failing untouched sentinel and exit-2 verifier rejection;
- silent compilation of the hidden known-good exact five-declaration surface;
- rejection of an added axiom and of diagnostic suppression;
- deny-default Seatbelt enforcement with candidate-only writes and hidden repository, oracle, and
  client state;
- one-session, one-turn, zero-descendant complete-trace policy tests; and
- fail-closed live-run acknowledgement and fresh-login gates.

The relevant five-declaration production surface is frozen separately by the hidden oracle hash
`4375bab0c97bcecb7e352eb3af2fb2d4a11e9784c8255c9f3fc77cc8b733d09b`.
`pins/stage_3.sha256` freezes the full actor-facing harness. One fresh
`gpt-5.6-sol` Run 1 at `high` effort is authorized under
`/private/tmp/humanize2-kls-issue2-stage3-run1`. A live result must stop at `mechanical-pass` for
post-run verification and a separate human acceptance decision.
