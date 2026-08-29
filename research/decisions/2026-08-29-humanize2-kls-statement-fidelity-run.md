# Accept the second Humanize2 KLS statement-fidelity run

- **Date:** 2026-08-29
- **Type:** authenticated agent-harness result
- **Scope:** `experiments/humanize2_kls_statement_fidelity/`
- **Mathematical effect:** none

## Authorization and configuration

The user explicitly authorized sending the frozen linear-test specification, permitted
`Basic.lean` and `Poincare.lean` API material, candidate contents and diff, Git metadata, Lean
compiler output, and semantic reviewer results to OpenAI for this experiment.

The accepted retry began from clean commit
`c94863c5642edd95ef7622d723f4391a489a2cab` with a reset sentinel and fresh external Humanize state.
It used Humanize2 commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` (`hmz 0.1.0`), flowverse
commit `22de7178543140edaaaef2bea351b51ac29e6f04`, Codex `gpt-5.6-sol` at high
effort, and the repository's Lean 4.33.0 toolchain. Humanize state and raw session logs remained
outside the repository.

## Actor trace audit

The actor made four direct tool calls and spawned no child agent:

1. read `AGENTS.md`, the frozen input, `Basic.lean`, `Poincare.lean`, and the candidate, then checked
   short Git status;
2. replaced the sentinel in the candidate;
3. ran the exact required Lean command; and
4. inspected the scoped candidate diff and short Git status.

The actor made no collaboration call and neither it nor any descendant read the oracle, project
certificate, solution certificate, ledger, knowledge summary, or prior review. This satisfies the
prompt-enforced blindness criterion. The actor trace audit covered the complete actor session tree,
not only its final prose report.

## Candidate and reviewer result

The candidate SHA-256 is
`fe594274d55934a6152a8be813c549682a930adac6952720583ae9ed6137990d`. It preserves:

- arbitrary `D : ℕ`, including `D = 0`;
- `EuclideanSpace ℝ (Fin D)`;
- a probability measure and explicit `MemLp id 2 μ` hypothesis;
- the universal admissible-test extended Rayleigh-quotient bound; and
- the centered-covariance maximum bound as the second conjunct.

The separate read-only RLAR reviewer verified all four pinned oracle sources, compared all ten
semantic-rubric items, reran Lean, scanned for the sentinel and proof placeholders, audited staged,
unstaged, and untracked state, and returned structured `done: true`. It reported only harmless macOS
temporary-cache warnings caused by its read-only sandbox; all commands exited successfully.

## Independent validation

After RLAR exited 0:

- `experiments/humanize2_kls_statement_fidelity/scripts/verify_candidate.sh` passed;
- `cd formalization && lake env lean ../experiments/humanize2_kls_statement_fidelity/candidate/CandidateStatement.lean`
  exited 0 without diagnostics;
- all four oracle SHA-256 pins matched;
- placeholder and proof-declaration scans found no forbidden content;
- semantic comparison independently confirmed every binder and both conjuncts; and
- Git scope contained only the candidate modification before this result documentation was added.

## Decision

Classify Run 2 as **PASS** for statement fidelity. Preserve the generated candidate as benchmark
output and the first run's blind-validity failure as harness evidence. This result shows that the
configured pipeline can generate and independently review this already-known KLS-facing Lean
proposition under the stated protocol. It does not establish general autoformalization capability.

The candidate is a `Prop` definition, not a theorem or proof. No ledger, manuscript statement,
proof dossier, review certification, claim status, or mathematical dependency changes.
