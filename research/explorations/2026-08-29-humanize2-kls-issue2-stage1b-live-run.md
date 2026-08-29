# Humanize2 Issue 2 Stage 1B authenticated Run 1

- **Date:** 2026-08-29
- **Target:** Stage 1B foundational lemmas and extended optimal Poincaré constant
- **Run type:** subscription-authenticated Humanize2 → Codex → Lean actor-only reconstruction
- **Repository commit at launch:** `23e0cd3`
- **Outcome:** mechanical FAIL at the exact-surface verifier; no human acceptance review
- **Mathematical effect:** none

## Frozen scope and isolation

The user explicitly started the authorized Issue 2 Stage 1B run. The runner reset a dedicated
external state root, preserved only its subscription authentication, and passed the prompt,
toolchain, fixture, accepted-dependency, oracle, sentinel, Seatbelt, client-state, network, and
forbidden-read preflights before the model call.

The actor-visible entries were exactly:

```text
AGENTS.md
TASK.md
AcceptedStage1A.lean
AcceptedStage1A.olean
CandidateStage1B.lean
```

The accepted source and compiled dependency retained their pinned hashes and read-only modes.

## Actor attempt

One actor session ran one turn with no descendants or reviewer. It read the four permitted text
files, edited only `CandidateStage1B.lean`, ran `lean CandidateStage1B.lean` once, and performed one
final candidate inspection. The first implementation compiled, so the actor made zero
compiler-feedback repair edits and reported no uncertainty.

Candidate SHA-256:

```text
cfde84ba4de0fe4230331979b586fee5da43b4f20aae2bc27dbfdfd5ac9e2df9
```

## Mechanical failure

The independent candidate verifier recompiled the candidate successfully but its hidden surface
module rejected five optimal-constant theorem APIs. The actor made `μ`, and where applicable `C`
or `L`, explicit positional arguments; the frozen surface requires the corresponding parameters to
be implicit. The final equivalence was stated as
`¬ ∃ C : NNReal, HasPoincare μ (C : ℝ)` rather than the frozen
`∀ C : NNReal, ¬ HasPoincare μ (C : ℝ)`. These propositions are logically equivalent, but the Lean
types and invocation ergonomics are not the frozen exact surface.

The actor-facing specification gave the intended mathematical directions but did not spell out
the full Lean signatures of the five theorems. A fair retry therefore requires an explicitly
hardened Stage 1B specification and prompt in a fresh isolated session; changing the checker to
accept this candidate would invalidate the precommitted surface gate.

## Trace result

The runner stopped at the surface verifier before its final trace command. A manual audit of the
stopped session initially failed because the path scanner interpreted the Lean subtype delimiter
`//` as an absolute path. The append-only decision
`2026-08-29-humanize2-kls-issue2-stage1b-trace-subtype-delimiter.md` records that parser repair.
Re-auditing the same session, without rerunning the model, returned `ok: true`: one session, one
turn, zero descendants, four local `exec` calls, and only candidate mutation.

The compact external audit artifacts have SHA-256 values:

```text
f6ca9741ebef5d4f6e690cad1c0ed6a8dd72defa8529275a38e6868025e749b3  stage1b-trace-audit.json
55519daeff9cb6521a409ffd5498b8fc336abfe03e360ceecb349c0010ea2a53  stage1b-candidate-verifier.txt
```

## Status boundary

Human checklist item 4 requires the exact-surface verifier to pass, so semantic/proof acceptance
did not begin. The candidate is not an accepted Stage 1B dependency, production theorem, proof
dossier, certificate, ledger event, or manuscript change. Stage 2A did not start. Raw transcripts,
authentication state, generated `.olean` files, and Humanize/Codex runtime state remain external
and are not committed.
