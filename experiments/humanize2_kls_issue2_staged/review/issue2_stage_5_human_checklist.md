# Issue 2 Stage 5 human semantic/proof checklist

This checklist is human-only. Do not mount, quote, or return it to the Stage 5 actor session.

Under the standing statement-level alignment ruling, statement/type fidelity, hypothesis
fidelity, soundness, and diagnostic cleanliness are binding. Proof construction is unconstrained
when kernel-valid and assumption-preserving; production proof routes are descriptive only and are
not acceptance conditions.

A stopped candidate may be accepted only if every item passes:

1. The complete actor session tree and tool trace show exactly one root session, one turn, zero
   descendants, no reviewer/collaboration/browser/web/MCP/network/client-state access, and no
   forbidden path or output.
2. The actor saw exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A/2B/3/4A/4B source and
   compiled pairs, and `CandidateStage5.lean`, plus only the pinned toolchain and upstream
   Mathlib.
3. Only `CandidateStage5.lean` changed. All fourteen accepted artifacts remain byte-identical to
   their pins and physically read-only; no file was created, renamed, or deleted.
4. The candidate imports exactly `AcceptedStage4B` and no second module. It compiles under pinned
   Lean 4.33.0 and upstream Mathlib only and passes the fail-closed exact-import and
   three-declaration surface verifier. No harness/API-surface extension was required.
5. The candidate extends exactly namespace `Issue2Autoformalization.Stage1A`, preserves the exact
   ambient Hilbert/measurable/Borel block, and adds no namespace, section, attribute, definition,
   or public declaration beyond the requested three theorems.
6. `linearTestLower` has exactly the frozen statement, including local
   `[FiniteDimensional ℝ E]` and `[IsProbabilityMeasure μ]` instances and the explicit
   second-moment hypothesis, and establishes the accepted extended covariance lower bound.
7. The finite-dimensional and probability instances on `linearTestLower` are the deliberate
   statement-fidelity redundancy. They are present exactly as frozen and are neither removed nor
   strengthened.
8. `linearTestLowerCertificate` has exactly the frozen conjunction and hypotheses, including the
   strict-implicit binder `⦃f : E → ℝ⦄` rather than an implicit or explicit binder.
9. The first certificate conjunct exposes the accepted universal admissible-test Rayleigh bound,
   and the second exposes the accepted covariance lower bound, with no change to either theorem
   statement.
10. `euclideanLinearTestLower` has exactly free `{D : ℕ}`, the canonical
    `EuclideanSpace ℝ (Fin D)` measure and identity types, the local probability instance, and the
    explicit second-moment hypothesis.
11. The Euclidean theorem uses only canonical Mathlib Hilbert/measurable/Borel/
    finite-dimensional instances, adds no manual instance, and includes `D = 0` with the accepted
    zero-dimensional covariance value.
12. Exactly the three production statements appear in production order. No Gaussian formula,
    additional KLS target, fourth declaration, definition, or new mathematical content appears.
13. The layer adds no ledger binding, `solutions/` artifact, certificate metadata field, or
    production change; the experimental chain terminates inside the experiment.
14. No declaration uses `sorry`, `admit`, an axiom, `unsafe`, `opaque`, `external`, unrequested
    syntax/notation/macro/attribute/option, custom IO, diagnostic suppression, or another escape
    hatch. No assumption beyond the frozen statements appears.
15. The exact compiler command exits zero with empty standard output and standard error. No Lean
    warning or linter suggestion remains, and no diagnostic suppression is used.
16. Acceptance would mark only the final staged layer as a human-reviewed experimental
    dependency. It would not itself create the later wrap-up record, promote production code,
    certify a dossier, or change a ledger, manuscript, or mathematical status.

The human reviewer may compare the stopped candidate with the hidden relevant production surface
only after the actor run, mechanical verification, and complete trace audit have stopped. No
finding or proof text may be returned to that actor session.
