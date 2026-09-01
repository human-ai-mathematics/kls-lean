# Stage 5 Run 1 human review

## Decision boundary

Run 1 is a stopped, zero-diagnostic mechanical pass stored under `review/pending/`. A human must
complete every item in `issue2_stage_5_human_checklist.md` before the final layer may be accepted.
Do not send review findings or hidden production proof text back to the stopped actor.

## Frozen files and hashes

```text
b0ca9554c137307d16161cd6ccd57e46eadb4e6691e09c64d8c314c80acbfd6b  pending/CandidateStage5Run1.lean
318a2bbdf10bb1ef67d403f728ca169cc47e1bf2b8da6d0cbce1601cb24be5f0  external stage5-trace-audit.json
```

The candidate is byte-identical to the stopped actor output at
`/private/tmp/humanize2-kls-issue2-stage5-run1/actor-workspace/CandidateStage5.lean`. Raw
transcripts, authentication, tokens, runtime state, and generated `.olean` files remain outside
Git.

## Independent review build

Open `Stage5Run1Review.code-workspace` from this directory. The project pins Lean and Mathlib to
`v4.33.0`. If an editor offers a newer `stable`, choose **Use Old Version**.

Run:

```bash
cd experiments/humanize2_kls_issue2_staged/review
lake build Stage5Run1Review
```

The recorded build completed successfully in 2,948 jobs. Success requires no warning, linter
suggestion, or style diagnostic.

## Independent harness reproduction

From the repository root:

```bash
export H2_ISSUE2_STAGE5_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage5-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_5_verify_candidate.sh \
  "$H2_ISSUE2_STAGE5_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_5_verify_oracle_pins.sh
jq '{ok, errors, actor_root_sessions, actor_turns, actor_descendants, actor_visible_files, \
     workspace_mutations, tool_calls}' \
  "$H2_ISSUE2_STAGE5_STATE_ROOT/audit/stage5-trace-audit.json"
```

Expected trace facts are `true`, `[]`, one root session, one turn, zero descendants, seventeen
declared actor-visible files, only `CandidateStage5.lean` mutated, and five local `exec` calls.
The second exact Lean call was silent after one feedback-driven repair iteration.

## Semantic comparison already prepared

The exact import, ambient block, strict-implicit binder, deliberately redundant hypotheses, no-
attribute boundary, production order, hidden production pin, and all three declarations passed.
Post-stop comparison found no semantic or new declaration-API difference. The namespace remains
the accepted API difference, missing production docstrings are documentation-only, and the
remaining source differences are proof-only.

Give dedicated attention to:

- the finite-dimensional and probability hypotheses on the first two theorems, which are
  deliberate statement-fidelity redundancy and must not be rejected as smuggled assumptions;
- the exact strict-implicit binder `⦃f : E → ℝ⦄` in the certificate surface;
- both conjuncts of `linearTestLowerCertificate` and their accepted dependencies; and
- the Euclidean specialization's use of canonical instances and inclusion of `D = 0`.

## Optional Claude-assisted interactive walkthrough

The user may use `../prompts/issue2_stage_5_claude5_fable_interactive_review.md` with Claude 5
Fable for a read-only phased walkthrough. Use it as an ordinary interactive conversation, not
`/goal`. Claude must check the deliberate redundancy and strict-implicit binder explicitly and
may read only the compact external trace summary. It may recommend an outcome, but only the user
may accept or reject the candidate.

## Human outcome

There are three valid next actions:

- **Accept:** record all sixteen checklist results in a new append-only decision and copy the
  candidate byte-for-byte into a newly authorized accepted layer.
- **Reject:** record the failed checklist item or items and preserve the candidate unchanged.
- **Request repair:** freeze only non-oracular feedback and authorize another fresh isolated run.

No outcome automatically creates the later experiment wrap-up, promotes production Lean, or
changes a theorem, dossier, ledger, manuscript, or mathematical status.
