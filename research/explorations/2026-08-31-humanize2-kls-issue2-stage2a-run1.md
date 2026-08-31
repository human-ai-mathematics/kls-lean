# Humanize2 Issue 2 Stage 2A Run 1

Date: 2026-08-31

## Run boundary

The valid Run 1 started from pushed preparation commit
`4a20147` on branch `autoformalization-experiments`. It used the fresh external root
`/private/tmp/humanize2-kls-issue2-stage2a-run1`, whose dedicated `CODEX_HOME` was authenticated
directly through the user's ChatGPT subscription. No global, Stage 1A, Stage 1B, or wrong-workspace
credential or transcript was copied.

The runner reset the candidate to the pinned failing sentinel, rebuilt both accepted `.olean`
dependencies from pinned source with Lean 4.33.0 and upstream Mathlib only, and passed the complete
pin, oracle, exact-workspace, immutable-dependency, compiler-failure, physical-isolation,
forbidden-read, client-state, Codex app-server, and Humanize2 adapter preflights before the model
call.

## Actor result

The `gpt-5.6-sol` actor at `high` effort used one session and one turn with zero descendants. It
read only `AGENTS.md`, `TASK.md`, `AcceptedStage1A.lean`, `AcceptedStage1B.lean`, and the candidate;
it did not inspect either compiled dependency. It edited only `CandidateStage2A.lean`, ran the
required Lean command once, observed exit zero with empty standard output and standard error, then
performed the permitted final candidate inspection. It reported zero compiler-feedback repair
iterations and no identified uncertainty.

Candidate SHA-256:

```text
83847c7ef06cd6045a1d5d5a8595f3fb645be28e8af4c71d3e577187fb0ad586
```

The candidate exposes exactly `linearTest`, `linearTest_apply`, `linearTest_eq_inner`,
`hasGradientAt_linearTest`, and `gradient_linearTest`. It uses `inner ℝ v x`, adds completeness
only for the gradient declarations, and adds no measure-theoretic or later-stage material.

## Independent mechanical verification

The candidate verifier recompiled the candidate silently with immutable accepted dependencies and
upstream Mathlib only. The independent surface checker accepted all five exact types and both
`@[simp]` attributes. The hidden five-declaration `Poincare.lean` surface pin matched.

The complete-session trace audit returned `ok: true` with:

- one actor-root session and one actor turn;
- zero descendants or collaboration/reviewer activity;
- four local `exec` tool calls and no other tool class;
- exactly seven actor-visible files;
- only `CandidateStage2A.lean` mutated;
- both accepted source/compiled pairs still matching their pins; and
- no forbidden path, output, network command, client-state access, sandbox denial, or Seatbelt
  drift.

Compact trace-audit SHA-256:

```text
0be977e90fea1cf5019028c71e3faf90563b2ac990b55cf038396603a61828e1
```

Raw sessions, authentication, tokens, runtime state, generated `.olean` files, and the rendered
machine-specific Seatbelt profile remain external and uncommitted.

## Status

Run 1 is a zero-diagnostic mechanical pass, not a human acceptance. The exact actor output is
preserved at
`experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage2ARun1.lean`. It changes no
production Lean, dossier, certificate, review certification, ledger, manuscript, or mathematical
status. The next action is the sixteen-item human semantic/proof checklist; Stage 2B remains
blocked until an explicit accept decision.
