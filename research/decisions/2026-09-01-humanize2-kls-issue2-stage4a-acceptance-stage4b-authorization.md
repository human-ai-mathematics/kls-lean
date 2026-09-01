# Accept Issue 2 Stage 4A Run 1 and authorize Stage 4B Run 1

Date: 2026-09-01

## Human decision

The user accepts Stage 4A Run 1 as the experimental Stage 4B dependency. A Claude 5 Fable
interactive review independently reproduced the accepted candidate hash, silent
`lake build Stage4ARun1Review` across 2,946 jobs, both verification scripts, hidden production-
surface pin `d395edf875f5adf73ed6a4edf27f31ee997cf1e879ee10fc216ed6d0566d3e97`,
and the compact one-session/one-turn/zero-descendant trace audit with thirteen visible files,
candidate-only mutation, and nineteen local `exec` calls. It returned all sixteen checklist items
`PASS` and recommended acceptance.

The reviewer checked the expanded Bochner-integral variance proof and explicit range-
normalization sphere proof line by line against pinned Mathlib sources. In particular, the
`covarianceBilin_apply` side goal is discharged by the trailing `exact hμ`, and the two longer
proofs are valid proof-only alternatives to production. The eight declarations are the formal
split of the manuscript's Remark 3.8 / Family 4.1 statement
`Var_P(f) = v^T Σ v; the Rayleigh quotient equals λmax(Σ)`. The pre-accepted experimental
namespace remains an API difference, the second covariance import remains the pre-authorized
harness/API-surface adjustment, missing docstrings are documentation-only, and all other
differences are proof-only. The seven disclosed compiler-feedback repairs remain within protocol.

Accepted candidate SHA-256:

```text
233e0297d99e52467e4ef7533af76f2310b23400ed720228361d540ffa36a90d
```

`review/pending/CandidateStage4ARun1.lean` was copied byte-for-byte to
`accepted/AcceptedStage4A.lean`; `cmp` succeeded and both paths reproduced this hash. The accepted
compiled dependency rebuilt deterministically under Lean 4.33.0 with SHA-256
`e1246d222fa57af253958aef8d935e4352609f1f2fb5496429c603c974475774`.

## Stage 4A sixteen-item PASS matrix

1. **PASS — complete trace:** one actor-root session, one turn, zero descendants, nineteen local
   `exec` calls, no reviewer/collaboration/browser/web/MCP/network/client-state access, and no
   forbidden path or output.
2. **PASS — visible fixture:** exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A/2B/3
   source/compiled pairs, and `CandidateStage4A.lean`, plus only the pinned toolchain and upstream
   Mathlib.
3. **PASS — mutation boundary:** only `CandidateStage4A.lean` changed; all ten accepted artifacts
   stayed byte-identical and physically read-only, with no created, renamed, or deleted file.
4. **PASS — imports and compilation:** the imports are exactly `AcceptedStage3` followed by
   `Mathlib.Probability.Moments.CovarianceBilin`; the second import is the pre-authorized minimal
   harness/API-surface adjustment, and the fail-closed ordered-import and exact-surface verifier
   passed under pinned Lean 4.33.0.
5. **PASS — namespace and surface:** the candidate extends only
   `Issue2Autoformalization.Stage1A`, adds only the frozen `@[simp]` on
   `centeredCovarianceOperator_inner`, and exposes exactly the eight requested declarations.
6. **PASS — centered operator:** `centeredCovarianceOperator` is exactly the Riesz representation
   of Mathlib's centered `covarianceBilin`, not the uncentered covariance operator.
7. **PASS — representation and symmetry:** the frozen inner-product representation and symmetric-
   linear-map types are exact, and the proofs correctly expose and use centered covariance
   symmetry.
8. **PASS — quadratic positivity:** `centeredCovarianceOperator_self_nonneg` has the frozen type
   and correctly transfers nonnegativity of the centered covariance quadratic form.
9. **PASS — variance identity:** with exactly `[IsFiniteMeasure μ]` and
   `MemLp (id : E → E) 2 μ`, the expanded Bochner-integral proof correctly identifies the
   operator quadratic form with variance of the accepted linear test.
10. **PASS — real Rayleigh maximum:** `covarianceRayleighMax` is exactly the real `iSup` of the
    centered operator's Rayleigh quotient over the nonzero-vector subtype.
11. **PASS — sphere normalization:** the exact unit-sphere equality is valid; the explicit
    normalization proof establishes both range inclusions, including the empty zero-dimensional
    case.
12. **PASS — nonnegativity and zero dimension:** the theorem correctly handles a nonzero witness
    through a bounded `iSup` and the subsingleton empty-supremum branch as `0`.
13. **PASS — ambient and stage boundary:** assumptions are exactly the complete real Hilbert,
    measurable, and Borel block; no global finite-dimensionality, nontriviality, separability,
    probability, stronger moment, eigenvalue, extended covariance, Euclidean, or later-stage
    material appears.
14. **PASS — soundness:** no `sorry`, `admit`, axiom, unsafe/opaque/external escape, unrequested
    syntax/notation/macro/attribute/option, custom IO, or diagnostic suppression appears.
15. **PASS — diagnostic cleanliness:** the exact actor compiler command, independent candidate
    verifier, exact-surface checker, and 2,946-job review build all completed at exit zero without
    a warning, linter suggestion, or other diagnostic.
16. **PASS — status boundary:** acceptance creates only a human-reviewed experimental dependency;
    it promotes no production code, certifies no dossier, and changes no ledger, manuscript, or
    mathematical status.

## Stage 4B frozen scope

Stage 4B is authorized as the remaining eight production `CenteredCovariance` declarations in
production order, inside namespace `Issue2Autoformalization.Stage1A` and under the same ambient
complete real Hilbert/measurable/Borel block:

1. `centeredCovarianceOperator_hasEigenvalue_iSup`;
2. `lambdaMaxCovariance`;
3. `lambdaMaxCovariance_toReal` with the sole `@[simp]` attribute;
4. `lambdaMaxCovariance_eq_zero_of_subsingleton`;
5. `lambdaMaxCovariance_le_operatorNorm`;
6. `lambdaMaxCovariance_ne_top`;
7. `lambdaMaxCovariance_le`; and
8. `lambdaMaxCovariance_le_optimal`.

Every name, binder, type, instance argument, attribute, expression, and right-hand side is frozen
to the relevant production surface. `[FiniteDimensional ℝ E]` and `[Nontrivial E]` occur only as
local instance hypotheses of the eigenvalue theorem. `[Subsingleton E]` occurs only on the zero-
dimensional theorem. None enters the ambient variable block.

`lambdaMaxCovariance` has no measure hypothesis and is exactly
`ENNReal.ofReal (covarianceRayleighMax μ)`. Accepted nonnegativity keeps the zero-dimensional value
at `0`, `ofReal` never produces `⊤`, and the Poincaré bounds use exactly `HasPoincare μ C` and/or
`MemLp (id : E → E) 2 μ`. No probability hypothesis beyond the instance supplied by
`HasPoincare`, stronger moment, separability, or Borel-beyond-ambient hypothesis is authorized.

This layer completes the staged formalization of Remark 3.8's linear-test lower bound
$C_P \geq \lambda_{\max}(\operatorname{Cov}_P)$. Euclidean/Gaussian specialization and final
Issue 2 assembly remain Stage 5 or out of scope and must not be added.

## Frozen import and actor boundary

A pre-freeze known-good compilation of all eight declarations established that
`Module.End.HasEigenvalue` and
`IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` are transitively available through the
accepted Stage 4A module. The exact import surface is therefore the single line:

```lean
import AcceptedStage4A
```

No additional pinned Mathlib import is required or authorized. The fail-closed verifier rejects
an extra or replacement import. The hidden production eight-declaration surface is pinned at
`7500c5f90a481f81aecc994173b049a013e51f8b62a1641ee885d69ae9526551`.

The frozen actor specification, actor prompt, and human sixteen-item checklist contain no
production proof text, oracle material, or reviewer finding. The actor fixture has exactly fifteen
entries: `AGENTS.md`, `TASK.md`, the six accepted source/compiled pairs, and
`CandidateStage4B.lean`. The accepted files are physically read-only and only the candidate may
mutate. `pins/stage_4b.sha256` freezes the complete 47-file actor-facing harness.

## Model-free validation and live-run authorization

Before any model call, the complete model-free suite passed:

- deterministic source-to-`.olean` rebuild of all six accepted layers, including the accepted
  Stage 4A compiled hash;
- exact fifteen-entry reset and immutable accepted artifacts;
- compiler-failing sentinel and exit-2 verifier rejection;
- silent compilation of the hidden known-good exact eight-declaration surface;
- fail-closed rejection of an extra import, a replacement accepted-layer import, and missing
  `BorelSpace`;
- rejection of an added axiom and diagnostic suppression;
- deny-default Seatbelt enforcement with candidate-only writes and hidden repository, oracle,
  review, client state, and production source;
- one-session, one-turn, zero-descendant complete-trace policy tests; and
- fail-closed live acknowledgement and fresh subscription-login gates.

One fresh subscription-authenticated `gpt-5.6-sol` Run 1 at `high` effort is authorized under
`/private/tmp/humanize2-kls-issue2-stage4b-run1`. The exact command
`lean CandidateStage4B.lean` must exit zero with empty standard output and standard error. No
escape hatch is allowed beyond the sole frozen `@[simp]` declaration attribute.

After the actor stops, independent verification, the hidden oracle pin, complete trace audit, and
post-stop semantic comparison are required. The exact actor output must be persisted under
`review/pending/`, a new append-only exploration must record the attempt, and a Claude 5 Fable
interactive review prompt must follow the Stage 4A phased template with the eigenvalue theorem and
the two Poincaré bounds receiving high attention. Claude may read only the compact external trace
summary, not raw sessions or client state.

`mechanical-pass` is not acceptance. Stage 4B must stop for a separate explicit human decision.
This authorization changes no production code, proof certification, ledger, manuscript, or
mathematical status.
