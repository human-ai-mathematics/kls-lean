# Issue 2 Stage 2B human semantic/proof checklist

This checklist is human-only. Do not mount, quote, or return it to the Stage 2B actor session.

A stopped candidate may be accepted for use as the input to Stage 3 only if every item passes:

1. The complete actor session tree and tool trace show exactly one root session, one turn, zero
   descendants, no reviewer/collaboration/browser/web/MCP/network/client-state access, and no
   forbidden path or output.
2. The actor saw exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A source and compiled
   pairs, and `CandidateStage2B.lean`, plus only the pinned toolchain and upstream Mathlib.
3. Only `CandidateStage2B.lean` changed. All six accepted artifacts remain byte-identical to their
   pins and physically read-only; no file was created, renamed, or deleted.
4. The candidate imports only `AcceptedStage2A`, compiles under pinned Lean 4.33.0 and upstream
   Mathlib only, and passes the independent exact three-theorem surface verifier.
5. The candidate extends exactly namespace `Issue2Autoformalization.Stage1A` and adds no nested
   namespace, section, attribute, or public declaration beyond the requested three theorems.
6. `dirichletEnergy_linearTest` has exactly the frozen statement and uses probability
   normalization to integrate the constant squared norm of the accepted constant gradient.
7. `isAdmissible_linearTest` has exactly the frozen statement; its only measure hypotheses are an
   explicit `IsProbabilityMeasure μ` value and `MemLp (id : E → E) 2 μ`.
8. Its smoothness field proves smoothness of `x ↦ inner ℝ v x` without adding a differentiability,
   finite-dimensional, or measurability assumption.
9. Its `MemLp` field correctly derives square integrability of the scalar projection by composing
   `id` with the continuous linear functional `innerSL ℝ v`.
10. Its energy-integrability field correctly reduces the squared gradient to the constant
    `‖v‖ ^ 2` and uses the supplied probability normalization; it does not exploit totalized
    integration without proving integrability.
11. `variance_linearTest_le` has exactly the frozen statement, obtains the probability instance
    from `hP`, applies the accepted Poincaré inequality to the accepted admissibility theorem, and
    rewrites with the accepted energy identity.
12. The ambient surface is exactly a complete real inner-product space with an abstract measurable
    structure. No `BorelSpace`, finite-dimensionality, nontriviality, separability, centered-moment,
    or stronger second-moment assumption appears, so dimension zero remains included.
13. No Rayleigh quotient, optimal-constant comparison, covariance object, spectral result,
    Euclidean specialization, final theorem, extra import, or later-stage material is present.
14. No declaration uses `sorry`, `admit`, an axiom, `unsafe`, `opaque`, `external`, unrequested
    syntax/notation/macro/attribute/option, custom IO, or another escape hatch.
15. The exact compiler command exits zero with empty standard output and standard error. No Lean
    warning or linter suggestion remains, and no diagnostic suppression is used.
16. Acceptance would create only a human-reviewed experimental dependency. It would not promote
    production code, certify a dossier, or change a ledger, manuscript, or mathematical status.

The human reviewer may compare the stopped candidate with the hidden relevant `Poincare.lean`
surface only after the actor run, mechanical verification, and complete trace audit have stopped.
No finding or proof text may be returned to that actor session.
