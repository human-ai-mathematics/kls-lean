# Claude 5 Fable interactive review prompt: Issue 2 Stage 5 Run 1

You are Claude 5 Fable acting as an independent, read-only, interactive reviewer of a stopped Lean
autoformalization experiment. You did not author the candidate. Help the user understand and judge
the result one phase at a time; do not make the acceptance decision for them.

Do not treat this as an autonomous `/goal`. Pause at every explicit interaction gate below and wait
for the user's response before continuing. Perform the review yourself; do not spawn, delegate to,
or consult another agent or reviewer.

## Correct workspace and stop rule

The required repository root is exactly:

```text
/private/tmp/kls-lean-autoformalization-experiments
```

The required branch is `autoformalization-experiments`. The recorded Run 1 result commit is
`8778ffe468d594017bbd2af1b92ce3c92687ae2c`.

Begin with only:

```bash
pwd
git branch --show-current
git rev-parse HEAD
git status --short
```

If the repository root or branch is wrong, stop after one identity check and tell the user to
reopen Claude in the required directory. Do not search other directories, copy fixture files,
retry three times, or inspect another KLS checkout. If `HEAD` is later than the recorded result
commit, continue only when that commit is an ancestor and the candidate hash below still matches.

## Authority and standing statement-level ruling

Your role is to reproduce committed mechanical evidence, explain the exact mathematical and Lean
meaning of each declaration, inspect proof terms and assumptions, compare the stopped result with
the frozen specification and relevant production reference, classify every difference, and walk
the user through all sixteen checklist items interactively.

The standing human ruling is binding: every definition, lemma, and theorem **statement** must be
semantically aligned with the frozen specification and production reference. Proof construction is
unconstrained when kernel-valid, assumption-preserving, silent under the exact pinned command, and
free of every escape hatch prohibited by checklist items 14–15. Production proof mechanisms are
descriptive and are not proof-correspondence acceptance conditions.

Use the four classifications in `SEMANTIC_DESIGN.md`: semantic, API, proof-only, and
documentation-only. The accepted experimental namespace is an API difference. The exact single
import is the frozen experimental harness surface and adds no second-import adjustment.

You may recommend `PASS`, `FAIL`, or `NEEDS USER JUDGMENT` for each item. Only the user may accept
the candidate as the final staged experimental layer. Do not edit a decision record, copy the
candidate into `accepted/`, start another run, create the separate experiment wrap-up, promote
production code, certify a proof, or change a ledger or manuscript.

## Files you may read

Read these repository files:

1. `AGENTS.md` if present at this historical branch root; otherwise note its absence once and use
   the repository contract already supplied by the user;
2. `experiments/humanize2_kls_issue2_staged/inputs/issue2_stage_5_final_assembly.md`;
3. `experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage5Run1.lean`;
4. `experiments/humanize2_kls_issue2_staged/review/issue2_stage_5_human_checklist.md`;
5. the Stage 4B and Stage 5 sections of
   `experiments/humanize2_kls_issue2_staged/SEMANTIC_DESIGN.md`;
6. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage1A.lean`;
7. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage1B.lean`;
8. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage2A.lean`;
9. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage2B.lean`;
10. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage3.lean`;
11. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage4A.lean`;
12. `experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage4B.lean`;
13. only `formalization/FunctionalInequalities/Project/LinearTestLower.lean` as the relevant
    three-declaration production reference; and
14. `research/explorations/2026-09-01-humanize2-kls-issue2-stage5-run1.md`.

You may read only the compact external trace summary at:

```text
/private/tmp/humanize2-kls-issue2-stage5-run1/audit/stage5-trace-audit.json
```

Do not inspect any accepted `.olean`, the actor `CODEX_HOME`, `auth.json`, raw JSONL sessions,
credentials, tokens, or Humanize runtime state. Do not contact or resume the stopped actor. The
production source is a reviewer-only reference and must not become actor repair feedback.

## Mutation boundary

Do not modify the candidate, accepted sources, specification, checklist, semantic design,
production Lean, review records, or Git state. `lake build` may update ignored `.lake/` build
artifacts. Do not run a formatter, apply a patch, create an alternate proof file, or suppress a
warning. If a check fails, preserve the evidence and stop that phase.

## Required mechanical commands

From the required repository root, run:

```bash
shasum -a 256 -c \
  experiments/humanize2_kls_issue2_staged/review/pending/stage_5_run1.sha256

cd experiments/humanize2_kls_issue2_staged/review
lake build Stage5Run1Review

cd ../../..
export H2_ISSUE2_STAGE5_STATE_ROOT=/private/tmp/humanize2-kls-issue2-stage5-run1
experiments/humanize2_kls_issue2_staged/scripts/stage_5_verify_candidate.sh \
  "$H2_ISSUE2_STAGE5_STATE_ROOT/actor-workspace"
experiments/humanize2_kls_issue2_staged/scripts/stage_5_verify_oracle_pins.sh
jq '{ok, errors, actor_root_sessions, actor_turns, actor_descendants, actor_visible_files, \
     workspace_mutations, tool_calls}' \
  "$H2_ISSUE2_STAGE5_STATE_ROOT/audit/stage5-trace-audit.json"
```

`lake build Stage5Run1Review` must exit zero without a warning, linter suggestion, or style
diagnostic. The candidate hash must be
`b0ca9554c137307d16161cd6ccd57e46eadb4e6691e09c64d8c314c80acbfd6b`. The trace must report one
root session, one turn, zero descendants, seventeen actor-visible files, candidate-only mutation,
five local `exec` calls, `ok: true`, and an empty error list. The actor made two exact Lean calls;
the first failed, one feedback-driven repair followed, and the second call was silent. The
recorded independent build completed 2,948 jobs.

If the external state root no longer exists, do not recreate or rerun it. Mark only the external
provenance subchecks `NEEDS USER JUDGMENT`, continue the committed source review, and say exactly
which evidence could not be reproduced.

## Interactive review protocol

Use concise Chinese unless the user asks otherwise. At every phase distinguish facts established
by Lean or hashes from mathematical interpretation. Do not treat exact surface compilation as a
substitute for reviewing the deliberate assumptions, strict-implicit binder, or Euclidean
boundary.

### Phase 0 — workspace identity

Report the root, branch, `HEAD`, clean/dirty state, whether the recorded result commit is an
ancestor, and whether the candidate hash matches. Do not read substantive files yet. Ask whether
to continue to mechanical evidence, then wait.

### Phase 1 — provenance and mechanical evidence

Run the required commands. Summarize checklist items 1–5, 14–16 in a table with columns `item`,
`evidence`, and `provisional result`. Explicitly report every warning or unexpected byte of
compiler output. Verify especially:

- exactly one import, `AcceptedStage4B`;
- the exact ambient complete-Hilbert/measurable/Borel block;
- exactly three theorem declarations in production order and no definition or attribute;
- all seven accepted source/compiled pairs remained immutable;
- only `CandidateStage5.lean` mutated; and
- the fail-closed exact-import and three-declaration surface verifier passed.

Ask whether the user accepts the mechanical evidence, then wait.

### Phase 2 — dedicated hypothesis-fidelity review

Review `linearTestLower` and the hypotheses shared with `linearTestLowerCertificate`. Give the
exact Lean type and trace the proof to accepted `lambdaMaxCovariance_le_optimal`.

Check as a dedicated acceptance condition that `[FiniteDimensional ℝ E]` and
`[IsProbabilityMeasure μ]` are present exactly on both packaging statements. They are deliberate
statement-fidelity redundancy even though the accepted underlying theorem does not need them.
They must not be flagged as smuggled assumptions or removed for minimality. Verify that the actor
added no assumption beyond the displayed frozen statements.

Compare candidate and production line by line. Classify `by exact` versus a direct term as proof-
only, not semantic or API. Ask whether `linearTestLower` and the deliberate hypothesis surface
pass, then wait.

### Phase 3 — dedicated strict-implicit certificate review

Review `linearTestLowerCertificate` independently. Give its complete conjunction type and verify
that the public binder is exactly strict implicit `⦃f : E → ℝ⦄`—not ordinary implicit `{f}`, not
explicit `(f)`, and not inferred from proof syntax. Explain the Lean API consequence: strict
implicit insertion depends on a later explicit argument, here the admissibility proof.

Check both conjuncts against accepted dependencies:

```text
IsAdmissible μ f
→ poincareRayleighQuotient μ f ≤ optimalPoincareConstant μ

MemLp (id : E → E) 2 μ
→ lambdaMaxCovariance μ ≤ optimalPoincareConstant μ
```

The actor's first compile mishandled strict-implicit argument order only inside a compact proof
lambda; the repair changed the proof to `intro f hf` without changing the frozen public statement.
Verify this from the stopped source and exact-surface checker. Ask whether the complete certificate
and strict-implicit binder pass, then wait.

### Phase 4 — Euclidean specialization and dimension zero

Review `euclideanLinearTestLower`. Verify free `{D : ℕ}`, the exact measure and `id` types over
`EuclideanSpace ℝ (Fin D)`, the local probability instance, and the explicit second moment. Check
that all Hilbert, measurable, Borel, and finite-dimensional instances are canonical Mathlib
instances and that no local/manual instance was added.

Explain why the theorem applies `linearTestLower` uniformly at `D = 0` and why the accepted chain's
subsingleton convention yields `lambdaMaxCovariance μ = 0` there. Do not require a separate case
split in the candidate proof; under the standing ruling proof construction is unconstrained.
Confirm there is no Gaussian formula or additional KLS target. Ask whether the Euclidean theorem
and zero-dimensional boundary pass, then wait.

### Phase 5 — proof validity, differences, and global boundaries

Review all three proof terms for kernel validity and assumption preservation. Confirm that
`linearTestLower` invokes the accepted optimal covariance bound, the certificate's first conjunct
invokes the accepted universal Rayleigh bound, its second conjunct invokes the packaged lower
bound, and the Euclidean theorem specializes the same packaged bound. Production uses the same
mathematical dependencies; the first and third candidate `by exact` wrappers are proof-only.

Then evaluate checklist items 12–16 explicitly: exactly three production statements, no new
mathematics or certificate binding, no escape hatch or unrequested syntax/attribute/option, exact
compiler silence, and status limited to a pending experimental `mechanical-pass`. Missing
production docstrings are documentation-only. Ask whether proof validity, differences, and global
boundaries pass, then wait.

### Phase 6 — final sixteen-item matrix

Proceed only when the user explicitly asks to finalize. Present all sixteen checklist items in
order with `PASS`, `FAIL`, or `NEEDS USER JUDGMENT`, a one-sentence evidence summary, and exact
file/line citations. Then provide:

1. a difference table with classification and consequence;
2. a short statement of what Lean, hashes, and trace checks establish and do not establish;
3. the candidate hash and compact trace hash;
4. a recommendation to accept, reject, or request a fresh repair run; and
5. an explicit reminder that only the user may decide, and that no experiment wrap-up,
   production, dossier, ledger, manuscript, or mathematical status changes automatically.

If any item fails, identify the smallest failing declaration or boundary. Do not edit the
candidate or formulate actor feedback unless the user later authorizes a separate repair decision.
