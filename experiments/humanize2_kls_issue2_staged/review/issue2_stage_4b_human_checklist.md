# Issue 2 Stage 4B human semantic/proof checklist

This checklist is human-only. Do not mount, quote, or return it to the Stage 4B actor session.

A stopped candidate may be accepted only if every item passes:

1. The complete actor session tree and tool trace show exactly one root session, one turn, zero
   descendants, no reviewer/collaboration/browser/web/MCP/network/client-state access, and no
   forbidden path or output.
2. The actor saw exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A/2B/3/4A source and
   compiled pairs, and `CandidateStage4B.lean`, plus only the pinned toolchain and upstream
   Mathlib.
3. Only `CandidateStage4B.lean` changed. All twelve accepted artifacts remain byte-identical to
   their pins and physically read-only; no file was created, renamed, or deleted.
4. The candidate imports exactly `AcceptedStage4A` and no second module. It compiles under pinned
   Lean 4.33.0 and upstream Mathlib only and passes the fail-closed exact-import and
   eight-declaration surface verifier. No harness/API-surface extension was required.
5. The candidate extends exactly namespace `Issue2Autoformalization.Stage1A`, preserves the exact
   ambient Hilbert/measurable/Borel block, adds exactly the frozen `@[simp]` attribute, and adds no
   namespace, section, attribute, or public declaration beyond the requested eight.
6. `centeredCovarianceOperator_hasEigenvalue_iSup` has exactly the frozen statement, with
   `[FiniteDimensional ℝ E]` and `[Nontrivial E]` only as its local instance hypotheses, and
   correctly applies the symmetric finite-dimensional Rayleigh--Ritz result to the accepted
   centered covariance operator and real supremum.
7. `lambdaMaxCovariance` is exactly `ENNReal.ofReal (covarianceRayleighMax μ)`, has no measure
   hypothesis, preserves the zero-dimensional value `0`, and cannot manufacture `⊤`.
8. `lambdaMaxCovariance_toReal` has exactly the frozen statement and sole `@[simp]` attribute and
   correctly recovers the real value from the accepted nonnegativity theorem.
9. `lambdaMaxCovariance_eq_zero_of_subsingleton` has exactly the frozen local `[Subsingleton E]`
   hypothesis and correctly transports the accepted empty-supremum value to `ENNReal` zero.
10. `lambdaMaxCovariance_le_operatorNorm` has exactly the frozen statement and correctly bounds
    both the nontrivial and subsingleton branches by the `ENNReal.ofReal` operator norm.
11. `lambdaMaxCovariance_ne_top` has exactly the frozen statement and correctly derives finiteness
    from the operator-norm bound without adding a measure or dimensional hypothesis.
12. `lambdaMaxCovariance_le` has exactly the frozen `HasPoincare μ C` and
    `MemLp (id : E → E) 2 μ` hypotheses, obtains probability only from `HasPoincare`, and
    correctly combines the accepted linear-test variance bound with the accepted covariance-
    variance identity in both dimension branches.
13. `lambdaMaxCovariance_le_optimal` has exactly the frozen second-moment hypothesis and correctly
    applies `le_optimalPoincareConstant` to the preceding fixed-constant bound. No Euclidean,
    Gaussian, final Issue 2, or other Stage 5 material appears.
14. No declaration uses `sorry`, `admit`, an axiom, `unsafe`, `opaque`, `external`, unrequested
    syntax/notation/macro/attribute/option, custom IO, or another escape hatch. No stronger
    moment, probability, separability, or Borel-beyond-ambient assumption appears.
15. The exact compiler command exits zero with empty standard output and standard error. No Lean
    warning or linter suggestion remains, and no diagnostic suppression is used.
16. Acceptance would create only a human-reviewed experimental dependency. It would not promote
    production code, certify a dossier, or change a ledger, manuscript, or mathematical status.

The human reviewer may compare the stopped candidate with the hidden relevant `Poincare.lean`
surface only after the actor run, mechanical verification, and complete trace audit have stopped.
No finding or proof text may be returned to that actor session.
