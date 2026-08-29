# Accept Issue 2 Stage 1A and freeze the Stage 1B actor prompt

- **Date:** 2026-08-29
- **Type:** human experiment gate and next-stage prompt design
- **Scope:** `experiments/humanize2_kls_issue2_staged/`
- **Mathematical effect:** none

## Human Stage 1A decision

After the authenticated actor stopped and every mechanical gate passed, the user explicitly
accepted the remaining semantic/API difference: `HasPoincare` quantifies its function argument
explicitly (`∀ f`) rather than using the hidden implementation's implicit binder (`∀ ⦃f⦄`). The
logical proposition is unchanged, and the explicit binder is now the intentional experimental
interface inherited by Stage 1B.

The accepted candidate SHA-256 is:

```text
9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6
```

The prior run established checklist items 1–4 mechanically: complete trace isolation, the exact
three-file actor view, candidate-only mutation, and pinned Lean compilation. Post-run comparison
established items 5–10, with the binder style as the sole question subsequently accepted by the
user. Item 11 remains a classification boundary: this file is only a human-accepted experimental
layer. It is not production code, a proof dossier, a certificate, a ledger event, or a manuscript
change.

Store a byte-identical copy at
`experiments/humanize2_kls_issue2_staged/accepted/AcceptedStage1A.lean` and pin its hash. Stage 1B
may consume this accepted artifact; no other hidden Issue 2 artifact becomes actor-visible.

## Stage 1B prompt decision

Freeze a new actor-facing mathematical specification and prompt for foundational energy,
derivative, fixed-constant, monotonicity, extended-infimum, and finite-versus-`⊤` declarations.
The actor must extend the accepted experimental namespace, use the accepted explicit binder, edit
only `CandidateStage1B.lean`, and stop for human review after actual Lean compilation.

The future Stage 1B workspace must contain exactly:

```text
AGENTS.md
AcceptedStage1A.lean
AcceptedStage1A.olean
CandidateStage1B.lean
TASK.md
```

The `.olean` must be compiled deterministically from the pinned accepted source using the pinned
Lean toolchain before the actor starts. A disposable upstream-Mathlib-only compilation confirmed
that the Stage 1B declaration surface is implementable with the accepted explicit binder. The
disposable proof file is not retained or committed.

The first disposable import check deliberately supplied only the accepted source directory on
`LEAN_PATH`; Lean exited `1` with `unknown module prefix 'AcceptedStage1A'`. After compiling the
pinned source to `AcceptedStage1A.olean` with the pinned toolchain, the same Stage 1B declaration
surface compiled with exit `0`. This establishes a harness requirement, not a model proof result.

This decision does not yet supply a Stage 1B reset fixture, verifier, trace pinset, oracle pin,
human rubric, runner, or model result. The actor prompt must not be pasted into an existing desktop
task. A separate harness step must first build and validate the external five-entry workspace and
its physical isolation. The bounded repository-work prompt for that step is
`experiments/humanize2_kls_issue2_staged/prompts/issue2_stage_1b_harness_setup.md`.
