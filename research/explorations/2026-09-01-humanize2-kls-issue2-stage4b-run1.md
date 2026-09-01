# Humanize2 Issue 2 Stage 4B Run 1

Date: 2026-09-01

## Run boundary

Run 1 started from preparation commit `84c0c8c` on branch
`autoformalization-experiments`. It used the fresh external root
`/private/tmp/humanize2-kls-issue2-stage4b-run1`, whose dedicated `CODEX_HOME` was authenticated
directly through the user's ChatGPT subscription. No global or earlier-stage credential,
candidate, transcript, or feedback was copied.

The runner reset the candidate to the pinned failing sentinel, rebuilt all six accepted `.olean`
dependencies from pinned source with Lean 4.33.0 and upstream Mathlib only, and passed the complete
47-file pin, hidden oracle, exact-workspace, immutable-dependency, compiler-failure, single-import,
Borel-surface, physical-isolation, forbidden-read, client-state, Codex app-server, and Humanize2
adapter preflights before the model call.

## Actor result

The subscription-authenticated `gpt-5.6-sol` actor at `high` effort used one session and one turn
with zero descendants. It read only the nine permitted text files, did not inspect a compiled
dependency, and edited only `CandidateStage4B.lean`. The complete trace contains five local
`exec` calls: one permitted text read, two candidate edits, and two exact Lean calls.

The initial complete implementation produced two proof errors—an ambiguous coerced zero in the
subsingleton proof and a definitional wrapper around the operator quadratic form—and style
diagnostics for proposition-valued local instances. One compiler-feedback repair iteration made
the local types explicit and aligned the quadratic-form target. The second exact
`lean CandidateStage4B.lean` call exited zero with empty standard output and standard error.

Candidate SHA-256:

```text
610e9006ffe2e03beb83ec6ec811cfb58ae67621867e191c371264b2066a3188
```

The candidate has exactly the single import `AcceptedStage4A`, the exact ambient block, the sole
`@[simp]` attribute on `lambdaMaxCovariance_toReal`, and the eight frozen declarations in
production order. It adds no ambient finite-dimensional, nontrivial, or subsingleton instance; no
probability, stronger moment, separability, or Borel-beyond-ambient assumption; and no Euclidean,
Gaussian, final Issue 2, or other later-layer material.

## Independent mechanical verification

The candidate verifier recompiled the candidate silently with all six immutable accepted
dependency pairs and upstream Mathlib only. Its fail-closed source checks accepted exactly the
single import, exact ambient block, three local-instance placements, sole attribute, and eight
declaration names. The independent Lean surface checker accepted all eight exact declaration
types, and the hidden production surface pin matched
`7500c5f90a481f81aecc994173b049a013e51f8b62a1641ee885d69ae9526551`.

The independent review project built `AcceptedStage4A` and `CandidateStage4BRun1` successfully in
a 2,947-job build with no warning, linter suggestion, or style diagnostic.

The complete-session trace audit returned `ok: true` with:

- one actor-root session and one actor turn;
- zero descendants or collaboration/reviewer activity;
- five local `exec` calls and no other tool class;
- exactly fifteen actor-visible files;
- only `CandidateStage4B.lean` mutated;
- all six accepted source/compiled pairs still matching their pins; and
- no forbidden path, output, network command, client-state access, sandbox denial, or Seatbelt
  drift.

Compact trace-audit SHA-256:

```text
403c3cfb5eb43fd42329f1292c179509efb46244e44c67492aae118c807b04bd
```

Raw sessions, authentication, tokens, runtime state, generated `.olean` files, and the rendered
machine-specific Seatbelt profile remain external and uncommitted.

## Post-stop semantic comparison

The candidate has no semantic or declaration-API difference from the frozen surface or the eight
corresponding production declarations. The experimental namespace remains the previously accepted
API difference. Unlike Stage 4A, Stage 4B needs no direct Mathlib import and therefore adds no new
harness/API-surface adjustment. Missing production docstrings are documentation-only.

All remaining differences are proof-only:

- the eigenvalue theorem line-breaks the same symmetric Rayleigh--Ritz application;
- `lambdaMaxCovariance_toReal` lets simplification infer the explicit measure argument;
- the subsingleton proof uses an explicit `(x : E)`/`(0 : E)` equality and a final `simp` rather
  than a separate `ENNReal.ofReal_zero` step;
- the operator-norm and fixed-Poincaré bounds split on nonemptiness of the nonzero-vector subtype
  rather than on `Nontrivial E`, which is logically the same dimensional dichotomy;
- the fixed-Poincaré proof rewrites the accepted covariance-variance identity and applies
  `variance_linearTest_le` directly at the matching multiplication orientation;
- `lambdaMaxCovariance_le_optimal` uses an unrestricted final `simpa` instead of naming only
  `ENNReal.ofReal_coe_nnreal`; and
- `lambdaMaxCovariance_ne_top` proves the frozen theorem directly from the definition and
  finiteness of `ENNReal.ofReal`, rather than routing through the preceding operator-norm bound.

The last proof is kernel-valid and assumption-preserving, but the frozen human checklist asks the
reviewer to assess the intended “finiteness from the operator-norm bound” correspondence. It is
therefore a specific human-review attention point, not an automatic failure or repair request.

## Status

Run 1 is a zero-diagnostic `mechanical-pass`, not a human acceptance. The exact actor output is
preserved at
`experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage4BRun1.lean`. It changes no
production Lean, proof dossier, certificate, ledger, manuscript, or mathematical status. The next
action is the sixteen-item human semantic/proof checklist; no actor feedback or fresh run is
authorized by this record.
