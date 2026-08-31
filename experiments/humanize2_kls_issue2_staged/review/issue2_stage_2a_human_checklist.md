# Issue 2 Stage 2A human semantic/proof checklist

This checklist is human-only. Do not mount, quote, or return it to the Stage 2A actor session.

A stopped candidate may be accepted for use as the input to Stage 2B only if every item passes:

1. The complete actor session tree and tool trace show exactly one root session, one turn, zero
   descendants, no reviewer/collaboration/browser/web/MCP/network/client-state access, and no
   forbidden path or output.
2. The actor saw exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B source and compiled pairs,
   and `CandidateStage2A.lean`, plus only the pinned toolchain and upstream Mathlib artifacts.
3. Only `CandidateStage2A.lean` changed. All four accepted artifacts remain byte-identical to
   their pins and physically read-only; no file was created, renamed, or deleted.
4. The candidate imports only `AcceptedStage1B`, compiles under pinned Lean 4.33.0 and upstream
   Mathlib only, and passes the independent exact five-declaration surface verifier.
5. The candidate extends exactly namespace `Issue2Autoformalization.Stage1A` and adds no nested
   namespace or public declaration beyond the requested five.
6. `linearTest v` is exactly the real-valued function `x ↦ inner ℝ v x`; the inner-product
   argument order is `v, x`.
7. `linearTest_apply` has the frozen statement and `@[simp]` attribute, without adding an
   assumption.
8. `linearTest_eq_inner` is the exact function equality and does not replace the right-hand side
   by a merely extensionally equivalent but API-different expression.
9. `hasGradientAt_linearTest` proves the real-Hilbert Riesz/Fréchet derivative statement with
   gradient `v`, using `CompleteSpace E` but no measurable-space hypothesis.
10. `gradient_linearTest` has the frozen pointwise statement and `@[simp]` attribute and follows
    from the valid gradient witness.
11. The first three declarations require only a normed additive commutative group and real inner
    product; only the gradient declarations add completeness.
12. Every declaration remains valid in dimension zero and assumes no measurability, measure,
    probability, moment, finite-dimensionality, or nontriviality.
13. No Stage 2B energy/admissibility/variance result, Rayleigh quotient, covariance object,
    spectral result, final theorem, extra import, or stronger ambient assumption is present.
14. No declaration uses `sorry`, `admit`, an axiom, `unsafe`, `opaque`, `external`, unrequested
    syntax/notation/macro/attribute, or another custom escape hatch.
15. The exact compiler command exits zero with empty standard output and standard error. No Lean
    warning or linter suggestion remains, and no diagnostic suppression is used.
16. Acceptance would create only a human-reviewed experimental dependency. It would not promote
    production code, certify a dossier, or change a ledger, manuscript, or mathematical status.

The human reviewer may compare the stopped candidate with the hidden relevant `Poincare.lean`
surface only after the actor run, mechanical verification, and complete trace audit have stopped.
No finding or proof text may be returned to that actor session.
