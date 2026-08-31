# Humanize2 Issue 2 Stage 3 Run 1

Date: 2026-09-01

## Run boundary

The valid Run 1 started from pushed preparation commit `ab32dba` on branch
`autoformalization-experiments`. It used the fresh external root
`/private/tmp/humanize2-kls-issue2-stage3-run1`, whose dedicated `CODEX_HOME` was authenticated
directly through the user's ChatGPT subscription. No global or earlier-stage credential or
transcript was copied.

The runner reset the candidate to the pinned failing sentinel, rebuilt all four accepted `.olean`
dependencies from pinned source with Lean 4.33.0 and upstream Mathlib only, and passed the complete
pin, oracle, exact-workspace, immutable-dependency, compiler-failure, physical-isolation,
forbidden-read, client-state, Codex app-server, and Humanize2 adapter preflights before the model
call.

## Actor result

The `gpt-5.6-sol` actor at `high` effort used one session and one turn with zero descendants. It
read only the seven permitted text files and did not inspect any compiled dependency. It edited
only `CandidateStage3.lean` and invoked the exact Lean command four times.

The first implementation used an explicit zero-versus-positive-energy split for the global
quotient bound. Three compiler-feedback repair iterations corrected the orientation of
`ENNReal.ofReal_div_of_pos`, supplied the positive numerator witness required by
`ENNReal.div_zero`, and normalized `ENNReal.ofReal_zero`. The fourth compile exited zero with empty
standard output and standard error. The actor reported no remaining semantic or proof uncertainty.

Candidate SHA-256:

```text
4b4a6950fa80b4bd13ea291ff25955b9dca075de52c92e1900783066ce8a0583
```

The candidate exposes exactly the five frozen declarations, imports only `AcceptedStage2B`, and
adds no probability, Borel, finite-dimensional, nontriviality, separability, centered-moment,
covariance, spectral, Euclidean, final-assembly, or other KLS material.

## Independent mechanical verification

The candidate verifier recompiled the candidate silently with all four immutable accepted
dependency pairs and upstream Mathlib only. The independent surface checker accepted all five
exact declaration types. The hidden five-declaration `Poincare.lean` surface pin matched.

The complete-session trace audit returned `ok: true` with:

- one actor-root session and one actor turn;
- zero descendants or collaboration/reviewer activity;
- six local `exec` tool calls and no other tool class;
- exactly eleven actor-visible files;
- only `CandidateStage3.lean` mutated;
- all four accepted source/compiled pairs still matching their pins; and
- no forbidden path, output, network command, client-state access, sandbox denial, or Seatbelt
  drift.

Compact trace-audit SHA-256:

```text
cfbb822a10d60d1175fb2a5178f0a64aa56bbc6ba62521ff706dd9695995f8cd
```

Raw sessions, authentication, tokens, runtime state, generated `.olean` files, and the rendered
machine-specific Seatbelt profile remain external and uncommitted.

## Post-stop semantic comparison

The candidate has no semantic or new API difference from the frozen surface or the corresponding
production declarations. Its explicit energy split in the global bound, symmetric use of
`ENNReal.ofReal_div_of_pos`, and named positive-numerator proof for `ENNReal.div_zero` change only
proof construction. The pre-accepted experimental namespace remains an API difference from
production, while omitted docstrings are documentation-only. These facts are review aids and do
not amount to human acceptance.

## Status

Run 1 is a zero-diagnostic mechanical pass, not a human acceptance. The exact actor output is
preserved at
`experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage3Run1.lean`. It changes no
production Lean, dossier, certificate, review certification, ledger, manuscript, or mathematical
status. The next action is the sixteen-item human semantic/proof checklist; Stage 4 remains blocked
until an explicit accept decision.
