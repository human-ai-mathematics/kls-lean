# Humanize2 Issue 2 Stage 5 Run 1

Date: 2026-09-01

## Run boundary

Run 1 started from authorization commit `f3d8909` on branch
`autoformalization-experiments`. It used the fresh external root
`/private/tmp/humanize2-kls-issue2-stage5-run1`, whose dedicated `CODEX_HOME` was authenticated
directly through the user's ChatGPT subscription. No global or earlier-stage credential,
candidate, transcript, or feedback was copied.

The runner reset the candidate to the pinned failing sentinel, rebuilt all seven accepted `.olean`
dependencies from pinned source with Lean 4.33.0 and upstream Mathlib only, and passed the complete
fifty-file pin, hidden oracle, exact-workspace, immutable-dependency, compiler-failure, single-
import, exact-surface, strict-implicit, deliberate-hypothesis, no-attribute, physical-isolation,
forbidden-read, client-state, Codex app-server, and Humanize2 adapter preflights before the model
call.

## Actor result

The subscription-authenticated `gpt-5.6-sol` actor at `high` effort used one session and one turn
with zero descendants. It read only the ten permitted text files, did not inspect a compiled
dependency, and edited only `CandidateStage5.lean`. The complete trace contains five local
`exec` calls: one permitted text read, two candidate edits, and two exact Lean calls.

The initial complete implementation used a compact proof lambda whose argument order treated the
strict-implicit function binder as the first proof argument. The first exact compiler call exposed
that elaboration error. One compiler-feedback repair made the binder explicit inside the proof
without changing the theorem signature. The second exact `lean CandidateStage5.lean` call exited
zero with empty standard output and standard error.

Candidate SHA-256:

```text
b0ca9554c137307d16161cd6ccd57e46eadb4e6691e09c64d8c314c80acbfd6b
```

The candidate has exactly the single import `AcceptedStage4B`, the accepted ambient block, no
attribute, and the three frozen theorem statements in production order. It preserves the strict-
implicit `⦃f : E → ℝ⦄` certificate binder and the deliberate finite-dimensional/probability
hypotheses. It adds no manual Euclidean instance, excludes no dimension, and adds no definition,
fourth declaration, Gaussian formula, KLS target, ledger binding, solution artifact, certificate
metadata, production change, or other mathematics.

## Independent mechanical verification

The candidate verifier recompiled the candidate silently with all seven immutable accepted
dependency pairs and upstream Mathlib only. Its fail-closed source checks accepted exactly the
single import, exact ambient block, strict-implicit binder, local redundant instances, no-
attribute boundary, free Euclidean dimension, and three declaration names. The independent Lean
surface checker accepted all three exact declaration types, and the hidden production surface pin
matched `08583f55632c3a199dcb71b33828539602d922b4cdcfc8cf1913eebd99bd17f9`.

The independent review project built `AcceptedStage4B` and `CandidateStage5Run1` successfully in
a 2,948-job build with no warning, linter suggestion, or style diagnostic.

The complete-session trace audit returned `ok: true` with:

- one actor-root session and one actor turn;
- zero descendants or collaboration/reviewer activity;
- five local `exec` calls and no other tool class;
- exactly seventeen actor-visible files;
- only `CandidateStage5.lean` mutated;
- all seven accepted source/compiled pairs still matching their pins; and
- no forbidden path, output, network command, client-state access, sandbox denial, or Seatbelt
  drift.

Compact trace-audit SHA-256:

```text
318a2bbdf10bb1ef67d403f728ca169cc47e1bf2b8da6d0cbce1601cb24be5f0
```

Raw sessions, authentication, tokens, runtime state, generated `.olean` files, and the rendered
machine-specific Seatbelt profile remain external and uncommitted.

## Post-stop semantic comparison

The candidate has no semantic or declaration-API difference from the frozen surface or the three
corresponding production declarations. The experimental namespace remains the previously accepted
API difference. The single accepted-module import replaces production's aggregated project import
inside the isolated experimental chain and is the frozen harness surface, not a statement change.
Missing production module and theorem docstrings are documentation-only.

All remaining differences are proof-only:

- `linearTestLower` uses `by exact lambdaMaxCovariance_le_optimal hμ` instead of the same term as
  the theorem body;
- `linearTestLowerCertificate` uses the same constructor proof and accepted dependencies as
  production; and
- `euclideanLinearTestLower` uses `by exact linearTestLower μ hμ` instead of the same term as the
  theorem body.

The deliberate `[FiniteDimensional ℝ E]` and `[IsProbabilityMeasure μ]` instances on the first
two statements exactly match production and the frozen statement-fidelity exception; they are not
proof additions or smuggled assumptions. The strict-implicit certificate binder is byte-for-byte
present in the public statement despite the first failed proof attempt. The Euclidean theorem
relies only on canonical Mathlib instances and keeps free `D : ℕ`, so `D = 0` remains included.

## Status

Run 1 is a zero-diagnostic `mechanical-pass`, not a human acceptance. The exact actor output is
preserved at
`experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage5Run1.lean`. It changes no
production Lean, proof dossier, certificate, ledger, manuscript, or mathematical status and does
not create the separate experiment wrap-up. The next action is the sixteen-item human semantic/
proof checklist; no actor feedback, fresh run, or acceptance is authorized by this record.
