# Accept Stage 3 Run 1 and authorize Stage 4A Run 1

Date: 2026-09-01

## Human decision

The user accepted Stage 3 Run 1 as the experimental dependency required by Stage 4A and
authorized one isolated subscription-authenticated Stage 4A Run 1. The decision followed a
Claude 5 Fable interactive review using the persisted prompt at
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_3_claude5_fable_interactive_review.md`.
That independent review reproduced the candidate hash, a silent 2,931-job
`lake build Stage3Run1Review`, both Stage 3 verification scripts, the hidden production pin
`4375bab0c97bcecb7e352eb3af2fb2d4a11e9784c8255c9f3fc77cc8b733d09b`, and the compact trace
audit, then returned all sixteen checklist items `PASS` with a recommendation to accept.

The review found no Stage 3 semantic or frozen-API difference. Relative to production, the
pre-accepted experimental namespace remains an API difference and missing docstrings are
documentation-only. Three implementation variants are proof-only: the explicit zero/positive-
energy split in the global bound, symmetric use of `(ENNReal.ofReal_div_of_pos …).symm`, and the
named positive-numerator witness normalized by `simpa only [ENNReal.ofReal_zero]`. The three
compiler-feedback repair iterations recorded in the exploration were technical `ENNReal`
orientation and witness repairs within the protocol.

This acceptance does not promote production code, certify a mathematical dossier, or change a
ledger, manuscript, theorem status, or KLS claim.

Accepted candidate SHA-256:

```text
4b4a6950fa80b4bd13ea291ff25955b9dca075de52c92e1900783066ce8a0583
```

The accepted copy is byte-identical to `review/pending/CandidateStage3Run1.lean`, is named
`accepted/AcceptedStage3.lean`, and has deterministic compiled-artifact SHA-256
`e0c25643fc5c7147bb494032fbc20c2d437faef9a8f732f7d636b675d9ed59ef` under the pinned
Lean/Mathlib toolchain.

## Sixteen-item acceptance record

1. **PASS — complete trace:** one actor-root session, one turn, zero descendants, six local
   `exec` calls, and no forbidden tool, path, output, network, collaboration, client-state access,
   sandbox denial, or Seatbelt drift.
2. **PASS — visible fixture:** exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A/2B
   source and compiled pairs, and `CandidateStage3.lean` were visible, together with only the
   pinned toolchain and upstream Mathlib.
3. **PASS — mutation boundary:** only `CandidateStage3.lean` changed; all eight accepted artifacts
   retained their pins and read-only modes, and no file was created, renamed, or deleted.
4. **PASS — imports and compilation:** the candidate imports only `AcceptedStage2B`, compiles
   silently with pinned Lean/Mathlib 4.33.0 and upstream Mathlib only, and passes the exact
   five-declaration surface verifier.
5. **PASS — namespace and surface:** it extends exactly `Issue2Autoformalization.Stage1A` and adds
   no namespace, section, attribute, or public declaration beyond the requested five.
6. **PASS — extended quotient definition:** `poincareRayleighQuotient` separately maps variance
   and energy through `ENNReal.ofReal` before dividing in `ENNReal`, with no probability or
   admissibility hypothesis.
7. **PASS — global optimal bound:** `poincareRayleighQuotient_le_optimal` has the frozen statement
   and proves the bound for every admissible test, including zero energy and the absence of any
   finite valid Poincaré constant.
8. **PASS — positive-energy identity:** `poincareRayleighQuotient_eq_of_pos` has the frozen
   statement and correctly identifies extended division with `ENNReal.ofReal` of the real
   quotient at strictly positive energy.
9. **PASS — zero-energy boundary:**
   `poincareRayleighQuotient_eq_top_of_energy_eq_zero` has the frozen statement and correctly uses
   positive variance plus zero energy to obtain `⊤`.
10. **PASS — positive-energy specialization:** `admissibleRayleighQuotient_le_optimal` has the
    frozen statement and validly specializes the extended comparison without changing quotient
    order or coercion placement.
11. **PASS — ambient boundary:** the surface is exactly a complete real inner-product space with
    an abstract measurable structure; it adds no `BorelSpace`, finite-dimensionality,
    nontriviality, separability, probability, centered-moment, or stronger assumption.
12. **PASS — zero-dimensional and extended-value conventions:** every declaration remains
    meaningful in dimension zero; positive variance over zero energy is `⊤`, `0 / 0 = 0`, and no
    real division-by-zero convention is imported.
13. **PASS — stage boundary:** no centered covariance form or operator, spectral or eigenvalue
    result, Euclidean specialization, final Issue 2 theorem, extra import, or other later-stage
    material appears.
14. **PASS — soundness:** there is no `sorry`, `admit`, axiom, unsafe/opaque/external escape,
    unrequested syntax/notation/macro/attribute/option, custom IO, or diagnostic suppression.
15. **PASS — diagnostic cleanliness:** the isolated verifier and independent review project both
    compile at exit zero with empty compiler output and no warning or linter diagnostic.
16. **PASS — status boundary:** acceptance creates only a human-reviewed experimental dependency;
    it changes no production theorem, dossier, certificate, ledger, manuscript, or mathematical
    status.

## Stage 4 split decision

The production `CenteredCovariance` section contains sixteen declarations, too many for one
one-turn actor run at the established three-to-five-declaration cadence. As a harness decision,
Stage 4 is split into:

- **Stage 4A — centered covariance operator and real Rayleigh maximum**, authorized here; and
- **Stage 4B — spectral bridge and extended `lambdaMaxCovariance` bounds**, requiring a later
  authorization and not run by this decision.

Stage 4A contains, in production order:

1. `centeredCovarianceOperator`;
2. `centeredCovarianceOperator_inner`;
3. `centeredCovarianceOperator_isSymmetric`;
4. `centeredCovarianceOperator_self_nonneg`;
5. `centeredCovarianceOperator_self_eq_variance`;
6. `covarianceRayleighMax`;
7. `covarianceRayleighMax_eq_iSup_covariance_sphere`; and
8. `covarianceRayleighMax_nonneg`.

Stage 4B contains, in the immediately following production order:

1. `centeredCovarianceOperator_hasEigenvalue_iSup`;
2. `lambdaMaxCovariance`;
3. `lambdaMaxCovariance_toReal`;
4. `lambdaMaxCovariance_eq_zero_of_subsingleton`;
5. `lambdaMaxCovariance_le_operatorNorm`;
6. `lambdaMaxCovariance_ne_top`;
7. `lambdaMaxCovariance_le`; and
8. `lambdaMaxCovariance_le_optimal`.

The two halves concatenated are exactly the sixteen production declarations. The split point
follows production declaration order, and Lean file order is already a topological order of the
dependency graph: later declarations may use earlier ones, while an earlier declaration cannot
refer to a later declaration not yet present in the environment. Therefore Stage 4B can depend
only on Stage 4A and earlier layers, never the reverse.

Before freezing, the exact Stage 4A known-good surface was grepped for the alternation of all eight
Stage 4B names. `rg` returned no matches (exit 1), so the mechanical match count was zero. This
check accompanies the dependency-order argument; it does not assert an unproved mathematical
equivalence between the halves.

The split changes no mathematical status. Each half must run the full protocol with its own
hidden oracle pin, sixteen-item human checklist, complete trace audit, and explicit human
acceptance gate.

## Stage 4A import boundary adjustment

The initial pre-freeze compilation established that `covarianceBilin` is not transitively
reachable through the immutable `AcceptedStage3` import chain. The production reference
`formalization/FunctionalInequalities/Poincare.lean` imports the same pinned upstream Mathlib
module directly. Retrofitting that import into `AcceptedStage3.lean` is forbidden because Stage 3
was accepted byte-for-byte at the SHA-256 above.

The user therefore authorized exactly this ordered import surface:

```lean
import AcceptedStage3
import Mathlib.Probability.Moments.CovarianceBilin
```

No third import, omission, replacement, or reordering is permitted. This is a harness/API-surface
adjustment with no semantic content: the required declarations already refer to the same
Mathlib `covarianceBilin` used by production. The fail-closed verifier parses the candidate's
import lines and requires precisely this two-element ordered list. Model-free negative controls
reject a third import and reversed order.

## Stage 4A authorization boundary

Stage 4A may expose the accepted Stage 1A, Stage 1B, Stage 2A, Stage 2B, and Stage 3
source/compiled pairs to a fresh isolated actor. It freezes exactly eight declarations inside
namespace `Issue2Autoformalization.Stage1A` under:

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
```

The operator is exactly the Riesz representation of Mathlib's centered `covarianceBilin`, not its
uncentered covariance operator. The surface includes the represented inner-product identity and
its sole `@[simp]` attribute, symmetry, quadratic-form nonnegativity, the finite-measure/second-
moment variance identity, the real nonzero-vector Rayleigh supremum, its unit-sphere formula, and
nonnegativity including the subsingleton empty-supremum case.

No global `FiniteDimensional ℝ E`, `Nontrivial E`, separability, probability, or stronger moment
assumption is allowed. The exact Borel ambient block is source-checked, and a model-free missing-
`BorelSpace` negative control must fail.

The authorization excludes every Stage 4B name, any eigenvalue or extended
`lambdaMaxCovariance` result, Euclidean specialization, final Issue 2 assembly, every other KLS
target, hidden production source or proof text in the actor lane, a model reviewer, automatic
acceptance, production promotion, dossier certification, and any ledger or manuscript change.

## Frozen Stage 4A design and pre-run validation

The exact eight-declaration API, ordered two-import surface, mathematical specification, actor
prompt, and human sixteen-item checklist are frozen. The actor fixture contains exactly thirteen
entries: `AGENTS.md`, `TASK.md`, the five accepted source/compiled pairs, and
`CandidateStage4A.lean`. All accepted artifacts are physically read-only; only the candidate may
mutate.

Rebuilding all five accepted modules under Lean 4.33.0 with upstream Mathlib only reproduced the
pinned Stage 3 compiled-artifact SHA-256
`e0c25643fc5c7147bb494032fbc20c2d437faef9a8f732f7d636b675d9ed59ef`.
The relevant eight-declaration production surface is frozen separately by hidden oracle SHA-256
`d395edf875f5adf73ed6a4edf27f31ee997cf1e879ee10fc216ed6d0566d3e97`.

Before the model call, the full model-free suite passed:

- deterministic source-to-`.olean` rebuild of all five accepted layers;
- exact thirteen-entry reset and immutable accepted artifacts;
- compiler-failing untouched sentinel and exit-2 verifier rejection;
- silent compilation of the hidden known-good exact eight-declaration surface;
- fail-closed rejection of a third import, reversed imports, and missing `BorelSpace`;
- rejection of an added axiom and diagnostic suppression;
- deny-default Seatbelt enforcement with candidate-only writes and hidden repository, oracle, and
  client state;
- one-session, one-turn, zero-descendant complete-trace policy tests; and
- fail-closed live-run acknowledgement and fresh-login gates.

`pins/stage_4a.sha256` freezes the 44-file actor-facing harness. One fresh
`gpt-5.6-sol` Run 1 at `high` effort is authorized under
`/private/tmp/humanize2-kls-issue2-stage4a-run1`. A live result must stop at `mechanical-pass` for
post-run verification and a separate human acceptance decision. Stage 4B remains unstarted and
unauthorized.
