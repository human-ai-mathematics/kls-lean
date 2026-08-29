# Issue 2 Stage 1A human-review checklist

This checklist is human-only. Do not mount or quote it in the actor workspace.

A candidate may be accepted for use as the input to Stage 1B only if every item passes:

1. The complete actor session tree and tool trace pass the isolation auditor.
2. The actor saw only the three fixture files, approved Mathlib artifacts, Lean toolchain, and its
   own isolated runtime state.
3. `CandidateStage1A.lean` is the only actor-workspace file that changed.
4. The candidate compiles with pinned Lean 4.33.0 and the pinned Mathlib dependency set.
5. The namespace is exactly `Issue2Autoformalization.Stage1A`.
6. The only requested top-level mathematical declarations are `IsAdmissible`, `dirichletEnergy`,
   and `HasPoincare`; all additional generated declarations are standard `IsAdmissible` structure
   machinery.
7. `IsAdmissible` has exactly the fields `smooth'`, `memLp_two`, and `energy_integrable`, expressing
   smoothness, `MemLp` at exponent two, and gradient-square integrability.
8. `dirichletEnergy` is exactly the real integral of the squared canonical-gradient norm.
9. `HasPoincare` includes probability normalization, nonnegativity of the real constant, and the
   universal variance-energy inequality over every admissible test.
10. No extra assumption, strengthened test class, altered variance convention, proof escape hatch,
    later-stage content, or hidden import of existing Issue 2 code appears.
11. The candidate is classified only as a human-accepted experimental layer. It is not promoted to
    production, certified, or used to change a ledger or manuscript.

The human reviewer may compare the stopped candidate with the existing repository implementation
only after the actor run and trace audit are complete. That comparison must not be returned to the
same actor session.
