# Humanize2 Issue 2 Stage 2B Run 1

Date: 2026-09-01

## Run boundary

The valid Run 1 started from pushed preparation commit `46601c2` on branch
`autoformalization-experiments`. It used the fresh external root
`/private/tmp/humanize2-kls-issue2-stage2b-run1`, whose dedicated `CODEX_HOME` was authenticated
directly through the user's ChatGPT subscription. No global or earlier-stage credential or
transcript was copied.

The runner reset the candidate to the pinned failing sentinel, rebuilt all three accepted
`.olean` dependencies from pinned source with Lean 4.33.0 and upstream Mathlib only, and passed
the complete pin, oracle, exact-workspace, immutable-dependency, compiler-failure,
physical-isolation, forbidden-read, client-state, Codex app-server, and Humanize2 adapter
preflights before the model call.

## Actor result

The `gpt-5.6-sol` actor at `high` effort used one session and one turn with zero descendants. It
read only the six permitted text files and did not inspect any compiled dependency. It edited only
`CandidateStage2B.lean` and invoked the exact Lean command twice.

The first compile exposed one definitional mismatch plus style diagnostics. The actor repaired the
source by changing the scalar-projection goal explicitly, using the linter-preferred anonymous
probability instance, and simplifying constant-gradient integrability. The second compile exited
zero with empty standard output and standard error. The actor reported one compiler-feedback
repair iteration and no identified semantic or proof uncertainty.

Candidate SHA-256:

```text
69c2eead467fbc0516c191e034cedd1c8593bdaac50c1681912a429337b5dffc
```

The candidate exposes exactly `dirichletEnergy_linearTest`, `isAdmissible_linearTest`, and
`variance_linearTest_le`. It uses the exact `MemLp (id : E → E) 2 μ` hypothesis and adds no
Borel, finite-dimensional, nontrivial, Rayleigh, covariance, spectral, or final-stage material.

## Independent mechanical verification

The candidate verifier recompiled the candidate silently with all three immutable accepted
dependency pairs and upstream Mathlib only. The independent surface checker accepted all three
exact theorem types. The hidden three-declaration `Poincare.lean` surface pin matched.

The complete-session trace audit returned `ok: true` with:

- one actor-root session and one actor turn;
- zero descendants or collaboration/reviewer activity;
- six local `exec` tool calls and no other tool class;
- exactly nine actor-visible files;
- only `CandidateStage2B.lean` mutated;
- all three accepted source/compiled pairs still matching their pins; and
- no forbidden path, output, network command, client-state access, sandbox denial, or Seatbelt
  drift.

Compact trace-audit SHA-256:

```text
69baf3ad061c0139692e6d3bbdaf66e6bfa3d376246d5d6becbf37f070cad74f
```

Raw sessions, authentication, tokens, runtime state, generated `.olean` files, and the rendered
machine-specific Seatbelt profile remain external and uncommitted.

## Post-stop semantic comparison

The candidate has no semantic or API difference from the frozen surface or the corresponding
production declarations. Its alternate use of `InnerProductSpace.toDual.contDiff`,
`MemLp.const_inner`, and an explicit energy rewrite changes only proof construction. These facts
are review aids and do not amount to human acceptance.

## Status

Run 1 is a zero-diagnostic mechanical pass, not a human acceptance. The exact actor output is
preserved at
`experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage2BRun1.lean`. It changes no
production Lean, dossier, certificate, review certification, ledger, manuscript, or mathematical
status. The next action is the sixteen-item human semantic/proof checklist; Stage 3 remains
blocked until an explicit accept decision.
