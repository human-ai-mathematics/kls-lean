# Accept Issue 2 Stage 5 Run 1

Date: 2026-09-01

## Human decision

The user accepts Stage 5 Run 1 as the final human-reviewed experimental layer of the staged Issue
2 reconstruction. The standing statement-level alignment ruling remains binding: declaration
statements and hypotheses must match the frozen specification and production reference exactly;
proof construction is otherwise unconstrained when kernel-valid, assumption-preserving, silent,
and free of every prohibited escape hatch, attribute, option, or diagnostic suppression.

Immediately before this decision, an overall read-only semantic-alignment audit compared the
frozen Stage 5 specification, stopped candidate, accepted dependency chain, and production
`Project/LinearTestLower.lean` reference. After normalizing whitespace and removing proof bodies,
all three theorem signatures had zero difference. The audit separately checked the deliberate
finite-dimensional/probability redundancy, strict-implicit certificate binder, canonical
Euclidean instances, and `D = 0` boundary. All sixteen checklist items pass.

Accepted candidate SHA-256:

```text
b0ca9554c137307d16161cd6ccd57e46eadb4e6691e09c64d8c314c80acbfd6b
```

`review/pending/CandidateStage5Run1.lean` was copied byte-for-byte to
`accepted/AcceptedStage5.lean`. `cmp` succeeded, and both paths reproduced the accepted hash.

## Stage 5 sixteen-item PASS matrix

1. **PASS — complete trace:** exactly one actor-root session, one turn, zero descendants, five
   local `exec` calls, no reviewer/collaboration/browser/web/MCP/network/client-state access, and
   no forbidden path or output.
2. **PASS — visible fixture:** exactly `AGENTS.md`, `TASK.md`, the accepted Stage
   1A/1B/2A/2B/3/4A/4B source and compiled pairs, and `CandidateStage5.lean`, plus only the pinned
   toolchain and upstream Mathlib.
3. **PASS — mutation boundary:** only `CandidateStage5.lean` changed; all fourteen accepted
   artifacts remained byte-identical and physically read-only, with no file created, renamed, or
   deleted.
4. **PASS — import and compilation:** the candidate imports exactly `AcceptedStage4B`, compiles
   under pinned Lean 4.33.0 and upstream Mathlib only, and passes the fail-closed exact-import and
   three-declaration surface verifier without a harness/API-surface extension.
5. **PASS — namespace and surface:** the candidate extends exactly
   `Issue2Autoformalization.Stage1A`, preserves the frozen ambient Hilbert/measurable/Borel block,
   and exposes exactly the three requested theorems with no attribute, definition, instance, or
   other public declaration.
6. **PASS — abstract lower bound:** `linearTestLower` has exactly the frozen
   finite-dimensional/probability instances, explicit second-moment hypothesis, and extended
   covariance lower-bound conclusion. Its proof invokes the accepted
   `lambdaMaxCovariance_le_optimal` without an added assumption.
7. **PASS — deliberate hypothesis redundancy:** `[FiniteDimensional ℝ E]` and
   `[IsProbabilityMeasure μ]` remain exactly on the abstract packaging theorem. They implement the
   frozen statement-fidelity exception and are not smuggled proof assumptions.
8. **PASS — certificate statement and binder:** `linearTestLowerCertificate` has the exact frozen
   hypotheses and conjunction, including strict-implicit `⦃f : E → ℝ⦄` rather than an ordinary
   implicit or explicit binder.
9. **PASS — certificate meaning:** the first conjunct is exactly the accepted universal
   admissible-test Rayleigh bound, and the second is exactly the accepted covariance lower bound.
   The proof uses the accepted Stage 3 theorem and the first Stage 5 theorem respectively.
10. **PASS — Euclidean statement:** `euclideanLinearTestLower` has exactly free `{D : ℕ}`, the
    canonical `EuclideanSpace ℝ (Fin D)` measure and identity types, the local probability
    instance, explicit second moment, and frozen conclusion.
11. **PASS — canonical instances and zero dimension:** the Euclidean proof adds no manual
    instance or nonzero-dimensional hypothesis. Mathlib supplies every structural instance, and
    `D = 0` remains included with the accepted subsingleton covariance value `0`.
12. **PASS — exact final surface:** exactly the three production statements appear in production
    order. No Gaussian formula, additional KLS target, fourth declaration, definition, or new
    mathematical content appears.
13. **PASS — repository boundary:** Stage 5 adds no ledger binding, `solutions/` artifact,
    certificate metadata field, production code, or manuscript change. The staged chain ends
    inside the experiment.
14. **PASS — soundness:** no `sorry`, `admit`, declared axiom, `unsafe`, `opaque`, `external`,
    unrequested syntax/notation/macro/attribute/option, custom IO, diagnostic suppression,
    stronger premise, or other escape hatch appears. Candidate and production `#print axioms`
    both report only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`, with no
    `sorryAx` or custom axiom.
15. **PASS — diagnostic cleanliness:** the exact final actor compiler call, independent candidate
    verifier, exact-surface checker, and 2,948-job review build all exit zero without a warning,
    linter suggestion, style diagnostic, or suppressed output.
16. **PASS — acceptance boundary:** acceptance marks only the final staged layer as a human-
    reviewed experimental artifact. It does not create the separate experiment wrap-up, promote
    production code, certify a dossier, or change a ledger, manuscript, or mathematical status.

## Difference classification

- **Semantic:** none.
- **API/harness:** the previously accepted experimental namespace and the frozen single
  `AcceptedStage4B` import replace production's namespace and aggregated project import. No new
  declaration-API difference appears.
- **Documentation-only:** the candidate omits production module and theorem docstrings.
- **Proof-only:** `linearTestLower` and `euclideanLinearTestLower` wrap the same production proof
  terms with `by exact`; the certificate constructor proof follows production.

The earlier accepted `HasPoincare` definition uses an explicit function binder where production
uses strict-implicit binder metadata. That inherited API-only difference does not change its
proposition and does not affect Stage 5: the new certificate's own strict-implicit binder matches
production exactly.

## Acceptance validation

- `cmp` found no byte difference between the stopped candidate and accepted source, and
  `shasum -a 256` returned the accepted `b0ca9554…acbfd6b` pin for both.
- `lake build Stage5Run1Review` completed 2,948 jobs successfully without a diagnostic.
- `stage_5_verify_candidate.sh` confirmed the exact seventeen-file actor workspace, all immutable
  dependency hashes, the exact three-declaration surface, and silent compilation against upstream
  Mathlib only.
- `stage_5_verify_oracle_pins.sh` reproduced the hidden production-surface pin
  `08583f55…bd17f9`.
- the compact trace audit returned `ok: true`, an empty error list, one session, one turn, zero
  descendants, five local `exec` calls, seventeen visible files, and candidate-only mutation;
- accepted-source compilation exits zero with empty standard output and standard error; and
- `git diff --check` passes, with no production, solution, ledger, or manuscript change.

## Completion and non-promotion boundary

This acceptance completes the staged reconstruction through the abstract lower bound, full
certificate surface, and Euclidean specialization at the extended-value level. The stopped
candidate and append-only Run 1 exploration remain unchanged for provenance.

The experiment wrap-up or synthesis record is a separate later human decision and is not started
here. `human-accepted` is not `production`: this decision promotes no production code, certifies
no dossier, and changes no ledger, manuscript, theorem status, or mathematical claim.
