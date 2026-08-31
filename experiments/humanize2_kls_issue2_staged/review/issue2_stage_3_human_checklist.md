# Issue 2 Stage 3 human semantic/proof checklist

This checklist is human-only. Do not mount, quote, or return it to the Stage 3 actor session.

A stopped candidate may be accepted for use as the input to Stage 4 only if every item passes:

1. The complete actor session tree and tool trace show exactly one root session, one turn, zero
   descendants, no reviewer/collaboration/browser/web/MCP/network/client-state access, and no
   forbidden path or output.
2. The actor saw exactly `AGENTS.md`, `TASK.md`, the accepted Stage 1A/1B/2A/2B source and compiled
   pairs, and `CandidateStage3.lean`, plus only the pinned toolchain and upstream Mathlib.
3. Only `CandidateStage3.lean` changed. All eight accepted artifacts remain byte-identical to
   their pins and physically read-only; no file was created, renamed, or deleted.
4. The candidate imports only `AcceptedStage2B`, compiles under pinned Lean 4.33.0 and upstream
   Mathlib only, and passes the independent exact five-declaration surface verifier.
5. The candidate extends exactly namespace `Issue2Autoformalization.Stage1A` and adds no nested
   namespace, section, attribute, or public declaration beyond the requested five.
6. `poincareRayleighQuotient` has exactly the frozen definition: both variance and energy are
   separately mapped by `ENNReal.ofReal` and division then occurs in `ENNReal`, with no probability
   or admissibility hypothesis.
7. `poincareRayleighQuotient_le_optimal` has exactly the frozen statement and proves the extended
   quotient bound for every admissible test, including zero energy and the absence of a finite
   valid Poincaré constant.
8. `poincareRayleighQuotient_eq_of_pos` has exactly the frozen statement and correctly identifies
   the extended quotient with `ENNReal.ofReal` of the real quotient at strictly positive energy.
9. `poincareRayleighQuotient_eq_top_of_energy_eq_zero` has exactly the frozen statement and uses
   positive variance plus zero energy to prove that the extended quotient is `⊤`.
10. `admissibleRayleighQuotient_le_optimal` has exactly the frozen statement and is a valid
    positive-energy specialization of the extended comparison, without changing quotient order or
    coercion placement.
11. The ambient surface is exactly a complete real inner-product space with an abstract measurable
    structure. No `BorelSpace`, finite-dimensionality, nontriviality, separability, probability,
    centered-moment, or stronger assumption appears.
12. The definition and all theorems remain meaningful in dimension zero; positive variance over
    zero energy is `⊤`, `0 / 0 = 0`, and no real division-by-zero convention is silently imported.
13. No centered covariance form/operator, spectral or eigenvalue result, Euclidean specialization,
    final Issue 2 theorem, extra import, or other later-stage material is present.
14. No declaration uses `sorry`, `admit`, an axiom, `unsafe`, `opaque`, `external`, unrequested
    syntax/notation/macro/attribute/option, custom IO, or another escape hatch.
15. The exact compiler command exits zero with empty standard output and standard error. No Lean
    warning or linter suggestion remains, and no diagnostic suppression is used.
16. Acceptance would create only a human-reviewed experimental dependency. It would not promote
    production code, certify a dossier, or change a ledger, manuscript, or mathematical status.

The human reviewer may compare the stopped candidate with the hidden relevant `Poincare.lean`
surface only after the actor run, mechanical verification, and complete trace audit have stopped.
No finding or proof text may be returned to that actor session.
