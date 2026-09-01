# Issue 2 Stage 4A human semantic/proof checklist

This checklist is human-only. Do not mount, quote, or return it to the Stage 4A actor session.

A stopped candidate may be accepted for use as the input to Stage 4B only if every item passes:

1. The complete actor session tree and tool trace show exactly one root session, one turn, zero
   descendants, no reviewer/collaboration/browser/web/MCP/network/client-state access, and no
   forbidden path or output.
2. The actor saw exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A/2B/3 source and
   compiled pairs, and `CandidateStage4A.lean`, plus only the pinned toolchain and upstream
   Mathlib.
3. Only `CandidateStage4A.lean` changed. All ten accepted artifacts remain byte-identical to their
   pins and physically read-only; no file was created, renamed, or deleted.
4. The candidate's import list is exactly `AcceptedStage3` followed by
   `Mathlib.Probability.Moments.CovarianceBilin`, with no third import; this is the required
   harness/API-surface adjustment because `covarianceBilin` is not transitively reachable through
   the immutable accepted layer and production imports the same pinned upstream module. It
   compiles under pinned Lean 4.33.0 and upstream Mathlib only and passes the fail-closed exact
   import and eight-declaration surface verifier.
5. The candidate extends exactly namespace `Issue2Autoformalization.Stage1A`, adds exactly the
   frozen `@[simp]` attribute, and adds no namespace, section, attribute, or public declaration
   beyond the requested eight.
6. `centeredCovarianceOperator` is exactly the Riesz-represented continuous linear map of
   Mathlib's centered `covarianceBilin`, not the uncentered covariance operator.
7. `centeredCovarianceOperator_inner` and `centeredCovarianceOperator_isSymmetric` have exactly the
   frozen statements and correctly expose the bilinear representation and symmetry.
8. `centeredCovarianceOperator_self_nonneg` has exactly the frozen statement and correctly derives
   nonnegativity from the centered covariance quadratic form.
9. `centeredCovarianceOperator_self_eq_variance` has exactly the frozen statement and uses only
   `[IsFiniteMeasure μ]` and `MemLp (id : E → E) 2 μ` to identify the quadratic form with the
   accepted linear-test variance.
10. `covarianceRayleighMax` has exactly the frozen real-valued definition as the supremum of the
    centered operator's Rayleigh quotient over `{x : E // x ≠ 0}`.
11. `covarianceRayleighMax_eq_iSup_covariance_sphere` has exactly the frozen unit-sphere statement
    and correctly transports the Rayleigh quotient to `covarianceBilin μ v v` at radius one.
12. `covarianceRayleighMax_nonneg` has exactly the frozen statement, proves nonnegativity in a
    nontrivial space, and explicitly handles the subsingleton empty-supremum case as `0`.
13. The ambient surface is exactly the complete real inner-product, measurable, and Borel setting.
    No finite-dimensionality, global nontriviality, separability, probability, stronger moment,
    spectral, eigenvalue, extended `lambdaMaxCovariance`, Euclidean, final Issue 2, extra import,
    or other later-stage material appears.
14. No declaration uses `sorry`, `admit`, an axiom, `unsafe`, `opaque`, `external`, unrequested
    syntax/notation/macro/attribute/option, custom IO, or another escape hatch.
15. The exact compiler command exits zero with empty standard output and standard error. No Lean
    warning or linter suggestion remains, and no diagnostic suppression is used.
16. Acceptance would create only a human-reviewed experimental dependency. It would not promote
    production code, certify a dossier, or change a ledger, manuscript, or mathematical status.

The human reviewer may compare the stopped candidate with the hidden relevant `Poincare.lean`
surface only after the actor run, mechanical verification, and complete trace audit have stopped.
No finding or proof text may be returned to that actor session.
