# Issue 2 Stage 1B human semantic/proof checklist

This checklist is human-only. Do not mount, quote, or return it to the Stage 1B actor session.

A stopped candidate may be accepted for use as the input to Stage 2A only if every item passes:

1. The complete actor session tree and tool trace pass the Stage 1B isolation auditor: exactly one
   root session, one turn, zero descendants, no reviewer/collaboration/browser/web/MCP/network or
   client-state access, and no forbidden path or output.
2. The actor saw exactly `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`,
   `AcceptedStage1A.olean`, and `CandidateStage1B.lean`, plus the pinned Lean toolchain and upstream
   Mathlib artifacts.
3. Only `CandidateStage1B.lean` changed. The accepted source and `.olean` remain byte-identical to
   their pins and physically read-only; no file was created, renamed, or deleted.
4. The candidate imports only `AcceptedStage1A`, compiles with pinned Lean 4.33.0 and upstream
   Mathlib only, and passes the independent exact-surface verifier.
5. The namespace is exactly `Issue2Autoformalization.Stage1A`, with only the requested nested
   `HasPoincare` namespace and exactly the thirteen requested public declarations.
6. `dirichletEnergy_nonneg` proves nonnegativity from the squared-gradient integrand, without an
   integrability hypothesis or a changed definition of energy.
7. `norm_fderiv_eq_norm_gradient` has no `MeasurableSpace E` assumption and correctly uses the
   real-Hilbert Riesz identification between `fderiv` and `gradient` norms.
8. `dirichletEnergy_eq_fderiv` proves equality of the two real integrals pointwise or almost
   everywhere and does not silently require admissibility.
9. The four `HasPoincare` declarations expose exactly probability normalization, constant
   nonnegativity, the accepted universal admissible-test inequality, and monotonicity. The
   monotonicity proof uses `dirichletEnergy_nonneg` and neither strengthens the test class nor adds
   assumptions.
10. `optimalPoincareConstant` is definitionally the `ENNReal` infimum over the subtype of
    `C : NNReal` satisfying the accepted explicit-binder `HasPoincare`; the empty subtype therefore
    yields `⊤`.
11. The five optimal-constant theorems have the requested directions, quantify over all finite
    nonnegative valid constants, and prove both directions of the finite-versus-`⊤` equivalence
    without assuming existence in the empty case.
12. No theorem uses `sorry`, `admit`, an axiom, `unsafe`, `opaque`, `external`, a custom unsound
    escape hatch, an extra import, a stronger ambient hypothesis, or later-stage material.
13. The exact compiler command exits zero with empty standard output and standard error. No Lean
    warning or linter suggestion remains, and no `set_option`, `attribute`, or other diagnostic
    suppression is used.
14. The candidate is only a human-reviewed experimental dependency. Lean compilation and this
    checklist do not promote production code, certify a dossier, or change a ledger/manuscript or
    mathematical status.

The human reviewer may compare the stopped candidate with the hidden relevant `Basic.lean`
surface only after the actor run, mechanical verification, and complete trace audit have stopped.
No finding or proof text may be returned to that actor session.
