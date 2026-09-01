# Add a Claude-assisted interactive review for Stage 5 Run 1

Date: 2026-09-01

## Decision

After valid Stage 5 Run 1 reached the human-review stop, add a reviewer-only Claude 5 Fable
prompt at
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_5_claude5_fable_interactive_review.md`.

This is a post-stop review aid, not an actor, automatic acceptance mechanism, experiment wrap-up,
or model reviewer inside the reconstruction harness. Claude may reproduce committed mechanical
evidence, inspect the stopped candidate and accepted sources, and compare the three relevant
production declarations because the actor session has ended. It must not contact or provide
feedback to the stopped actor.

## Interaction and authority boundary

The prompt uses seven phases and requires Claude to pause after workspace, mechanical, hypothesis-
fidelity, strict-implicit certificate, Euclidean zero-dimensional, and proof/global-boundary
checks. It produces the final sixteen-item matrix only when the user explicitly asks to finalize.
Claude may label evidence and recommend an outcome, but only the user may accept the candidate.

The reviewer is read-only apart from ignored Lean build artifacts and performs the review itself
without delegation. It may read the compact external trace audit but not raw sessions, client
state, credentials, or accepted `.olean` files. It may not edit the candidate, create an accepted
copy or acceptance decision, start another run, create the separate experiment wrap-up, promote
production code, certify a dossier, or change a ledger or manuscript.

## Dedicated Stage 5 checks

The prompt applies the standing statement-level alignment ruling explicitly. It treats proof
construction as unconstrained when kernel-valid, assumption-preserving, diagnostic-free, and
escape-hatch-free; production mechanisms are descriptive rather than proof-correspondence gates.

Two dedicated phases cover the user-identified high-attention surfaces:

- `[FiniteDimensional ℝ E]` and `[IsProbabilityMeasure μ]` on the first two statements are
  deliberate statement-fidelity redundancy and must not be rejected as smuggled assumptions; and
- `linearTestLowerCertificate` must expose exactly strict-implicit `⦃f : E → ℝ⦄`, independently
  of the proof's internal binder syntax and the repaired first elaboration attempt.

The Euclidean phase separately checks canonical Mathlib instances, free `D : ℕ`, inclusion of
`D = 0`, and absence of a Gaussian formula or further KLS target.

## Workspace failure prevention

The prompt fixes the required root as `/private/tmp/kls-lean-autoformalization-experiments`, branch
`autoformalization-experiments`, recorded result commit
`8778ffe468d594017bbd2af1b92ce3c92687ae2c`, candidate hash `b0ca9554…bfd6b`, and compact trace
hash `318a2bbd…e5f0`. If Claude starts elsewhere, it must stop after one identity check rather than
search, copy fixtures, or repeat an invalid audit. The prompt is an ordinary interactive
conversation, not an autonomous `/goal`, so its pause points remain meaningful.

## Validation

The prompt's mechanical commands were reproduced from the stated directory before this record.
The candidate pin passed, `Stage5Run1Review` built 2,948 jobs without warnings or linter
diagnostics, the exact single-import/three-declaration verifier passed silently, the hidden
production pin matched, and the compact trace satisfied one session, one turn, zero descendants,
five local `exec` calls, seventeen visible files, and candidate-only mutation.

Prompt SHA-256:

```text
fd3028a2bde10174d7f2e50a6aefddf0cc099cc7c51b75716db1910018722c34
```
