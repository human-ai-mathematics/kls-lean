Run the first KLS-facing statement-fidelity calibration. This task generates and reviews a Lean
proposition only; it does not prove a theorem or change any mathematical status.

RLAR assigns the current session exactly one role. Do not combine the actor and reviewer roles,
delegate any part of the task, spawn a subagent, or use a collaboration tool. In particular, the
actor must not conduct an oracle-backed review or ask another agent to conduct one. The actor stops
after completing the actor instructions; the separate RLAR reviewer performs the review.

Actor instructions:

1. Read `AGENTS.md` and
   `experiments/humanize2_kls_statement_fidelity/inputs/linear_test_lower.md`.
2. You may inspect only these Lean API files:
   - `formalization/FunctionalInequalities/Basic.lean`
   - `formalization/FunctionalInequalities/Poincare.lean`
   - `experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean`
3. To keep the calibration prompt-blind, do not read:
   - `experiments/humanize2_kls_statement_fidelity/oracle/`
   - `formalization/FunctionalInequalities/Project/LinearTestLower.lean`
   - `solutions/LemLinearTestLower.lean`
   - `solutions/glm-linear-baselines.tex`
   - `research/a-series/ledger.yaml`
   - `research/knowledge/lemmas.md`
   - any prior linear-test exploration or review
4. Edit only `experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean`.
5. Replace the `HUMANIZE2_UNATTEMPTED` sentinel with a definition whose value is the requested
   `Prop`. Keep the required definition name. Do not add a theorem, proof, `sorry`, `admit`, or
   `axiom`.
6. Run exactly:
   `cd formalization && lake env lean ../experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean`
7. Inspect the scoped Git diff and finish only when Lean exits successfully and no unrelated file
   changed.

Reviewer instructions:

1. Remain read-only. Read `AGENTS.md`, the frozen input, the candidate, and
   `experiments/humanize2_kls_statement_fidelity/oracle/semantic_rubric.md`.
2. Run `experiments/humanize2_kls_statement_fidelity/scripts/verify_oracle_pins.sh`.
3. Read the four pinned oracle sources named by the rubric and compare every binder and both
   conjuncts. Compilation alone is not semantic acceptance.
4. Run the exact Lean command above, scan for the sentinel and proof placeholders, and inspect
   staged, unstaged, and untracked Git state. Reject any unrelated modification.
5. Set `done: false` and provide concrete mismatch notes if any rubric item fails. Do not paste the
   complete oracle declaration. Those notes become the actor's next prompt verbatim.
6. Set `done: true` only if all ten rubric items, Lean compilation, and Git scope pass. List the
   commands and oracle sources used in the final notes.
