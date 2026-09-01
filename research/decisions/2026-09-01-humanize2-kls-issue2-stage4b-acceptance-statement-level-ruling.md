# Accept Issue 2 Stage 4B Run 1 under the statement-level alignment ruling

Date: 2026-09-01

## Human policy ruling

For proofs in this staged experiment, every definition, lemma, and theorem **statement** must be
semantically aligned with the frozen specification and production reference. Proof construction
is otherwise unconstrained provided the resulting proof is kernel-valid, preserves the frozen
assumptions, compiles silently under the exact pinned command, and uses no escape hatch. In
particular, checklist items 14 and 15 remain fully binding: `sorry`, `admit`, axioms, `unsafe`,
`opaque`, `external`, diagnostic suppression, and unrequested attributes or options are
forbidden.

Mechanism phrases in human checklists describe the production proof route; they are not binding
proof-correspondence requirements. This is the standing acceptance policy for the staged Issue 2
experiment. It does not weaken exact statement alignment, the frozen declaration surface,
assumption fidelity, kernel validity, diagnostic cleanliness, or the soundness boundary.

Under this ruling, Stage 4B Run 1 checklist item 11 passes. The declaration
`lambdaMaxCovariance_ne_top` has the exact frozen statement. Its direct proof through
`ENNReal.ofReal_ne_top` is kernel-valid, preserves every frozen assumption, compiles without a
diagnostic, and uses no escape hatch. It therefore need not reproduce production's route through
`lambdaMaxCovariance_le_operatorNorm`.

## Human decision

The user accepts Stage 4B Run 1 as a human-reviewed experimental dependency. The Claude 5 Fable
interactive review reproduced the candidate pin, silent `lake build Stage4BRun1Review` over 2,947
jobs, both verification scripts, hidden production-surface pin
`7500c5f90a481f81aecc994173b049a013e51f8b62a1641ee885d69ae9526551`, and the compact trace
audit: one session, one turn, zero descendants, fifteen visible files, candidate-only mutation,
and five local `exec` calls. It verified the three high-attention declarations against pinned
Mathlib sources, including the Rayleigh--Ritz eigenvalue theorem at `Rayleigh.lean:325` and both
Poincaré bounds through the accepted Stage 2B/4A chain. It returned fifteen unconditional passes
and referred item 11 for the policy ruling above, which resolves that item as `PASS`.

The pre-accepted experimental namespace remains an API difference, missing docstrings are
documentation-only, and all remaining differences are proof-only. The single disclosed
compiler-feedback repair iteration was within protocol.

Accepted candidate SHA-256:

```text
610e9006ffe2e03beb83ec6ec811cfb58ae67621867e191c371264b2066a3188
```

`review/pending/CandidateStage4BRun1.lean` was copied byte-for-byte to
`accepted/AcceptedStage4B.lean`. `cmp` succeeded, and both paths reproduced the accepted hash.

## Stage 4B sixteen-item PASS matrix

1. **PASS — complete trace:** exactly one actor-root session, one turn, zero descendants, five
   local `exec` calls, no reviewer/collaboration/browser/web/MCP/network/client-state access, and
   no forbidden path or output.
2. **PASS — visible fixture:** exactly `AGENTS.md`, `TASK.md`, the accepted Stage
   1A/1B/2A/2B/3/4A source and compiled pairs, and `CandidateStage4B.lean`, plus only the pinned
   toolchain and upstream Mathlib.
3. **PASS — mutation boundary:** only `CandidateStage4B.lean` changed; all twelve accepted
   artifacts remained byte-identical and physically read-only, with no file created, renamed, or
   deleted.
4. **PASS — imports and compilation:** the candidate imports exactly `AcceptedStage4A`, compiles
   under pinned Lean 4.33.0 and upstream Mathlib only, and passes the exact-import and
   eight-declaration surface verifier without a harness or API-surface extension.
5. **PASS — namespace and surface:** the candidate extends exactly
   `Issue2Autoformalization.Stage1A`, preserves the frozen ambient Hilbert/measurable/Borel block,
   adds only the frozen `@[simp]` attribute, and exposes only the requested eight declarations.
6. **PASS — eigenvalue bridge:** `centeredCovarianceOperator_hasEigenvalue_iSup` has the frozen
   statement and local instance placement and validly applies the symmetric finite-dimensional
   Rayleigh--Ritz theorem to the accepted operator and real supremum.
7. **PASS — extended maximum:** `lambdaMaxCovariance` is exactly
   `ENNReal.ofReal (covarianceRayleighMax μ)`, has no measure hypothesis, preserves the
   zero-dimensional value `0`, and cannot manufacture `⊤`.
8. **PASS — real recovery:** `lambdaMaxCovariance_toReal` has the exact frozen statement and sole
   `@[simp]` attribute and correctly uses accepted nonnegativity to recover the real value.
9. **PASS — subsingleton boundary:** `lambdaMaxCovariance_eq_zero_of_subsingleton` has exactly the
   frozen local `[Subsingleton E]` hypothesis and correctly transports the accepted empty-supremum
   value to `ENNReal` zero.
10. **PASS — operator-norm bound:** `lambdaMaxCovariance_le_operatorNorm` has the exact frozen
    statement and correctly handles both the nontrivial and subsingleton branches.
11. **PASS — finiteness under the statement-level ruling:** `lambdaMaxCovariance_ne_top` has the
    exact frozen statement. Its direct `ENNReal.ofReal_ne_top` proof is kernel-valid,
    assumption-preserving, silent, and escape-hatch-free. The checklist's reference to deriving
    finiteness from the operator-norm bound describes production's route and does not impose proof
    correspondence.
12. **PASS — fixed Poincaré bound:** `lambdaMaxCovariance_le` has exactly the frozen
    `HasPoincare μ C` and `MemLp (id : E → E) 2 μ` hypotheses, obtains probability only from
    `HasPoincare`, and correctly combines the accepted linear-test variance bound with the
    accepted covariance-variance identity in both dimension branches.
13. **PASS — optimal bound and stage boundary:** `lambdaMaxCovariance_le_optimal` has exactly the
    frozen second-moment hypothesis and correctly applies `le_optimalPoincareConstant` to the
    fixed-constant bound. No Euclidean, Gaussian, final Issue 2, or other Stage 5 material appears.
14. **PASS — soundness:** no `sorry`, `admit`, axiom, `unsafe`, `opaque`, `external`, unrequested
    syntax/notation/macro/attribute/option, custom IO, stronger assumption, or other escape hatch
    appears.
15. **PASS — diagnostic cleanliness:** the exact pinned compiler command and independent review
    build exit zero with empty Lean diagnostic output; no warning, linter suggestion, or
    diagnostic suppression remains.
16. **PASS — status boundary:** acceptance creates only a human-reviewed experimental dependency;
    it promotes no production code, certifies no dossier, and changes no ledger, manuscript, or
    mathematical status.

## Checklist-authoring correction

Future staged-experiment checklists must phrase proof-mechanism descriptions explicitly as
descriptive, or omit them. A checklist may bind declaration statements, assumptions, imports,
attributes, public surface, kernel validity, exact compilation behavior, diagnostics, and
soundness constraints. It must not accidentally convert the production proof route into a
proof-correspondence condition unless a future human policy explicitly introduces such a
condition.

The frozen Stage 4B checklist and append-only Run 1 exploration remain historical artifacts and
are not rewritten.

## Acceptance validation

- `cmp` found no byte difference between the stopped candidate and accepted source, and
  `shasum -a 256` returned the accepted `610e9006…6a3188` pin for both.
- `lake build Stage4BRun1Review` completed 2,947 jobs successfully.
- `stage_4b_verify_candidate.sh` confirmed the exact fifteen-file actor workspace, all immutable
  dependency hashes, the exact eight-declaration surface, and silent compilation against upstream
  Mathlib only.
- `stage_4b_verify_oracle_pins.sh` reproduced the hidden production-surface pin
  `7500c5f9…26551`.
- `lake env lean ../accepted/AcceptedStage4B.lean` exited zero with empty standard output and
  standard error.
- `git diff --check` passed. The accepted source, this decision, and the Stage 4B section of
  `SEMANTIC_DESIGN.md` are the only repository changes made by this acceptance.

## Scope and status boundary

This decision accepts Stage 4B only. It does not authorize or start Stage 5 or any further actor
run. With Stage 4B accepted, the staged chain formalizes manuscript Remark 3.8's linear-test lower
bound $C_P \ge \lambda_{\max}(\operatorname{Cov}_P)$ end to end at the extended-value level in
`lambdaMaxCovariance_le_optimal`.

Whether to proceed with Euclidean/Gaussian specialization or final Issue 2 assembly is a separate
future human decision. `human-accepted` is not `production`: this decision promotes no production
code, certifies no dossier, and changes no ledger, manuscript, theorem status, or mathematical
claim.
