# Humanize2 Issue 2 Stage 1A authenticated reconstruction run

- **Date:** 2026-08-29
- **Target:** Issue 2 Stage 1A foundational Poincaré vocabulary
- **Run type:** subscription-authenticated Humanize2 → Codex → Lean actor-only reconstruction
- **Repository commit at launch:** `83c37f2`
- **Outcome:** mechanical PASS after trace-parser repair; human semantic review pending
- **Mathematical effect:** none

## Frozen scope

The actor was authorized to receive only the frozen Stage 1A specification and three-file external
fixture. It was asked to define `IsAdmissible`, `dirichletEnergy`, and `HasPoincare` in namespace
`Issue2Autoformalization.Stage1A`. It was not asked to prove a theorem, formalize Stage 1B or later,
read existing Issue 2 code, use a model reviewer, or modify production files.

The actor workspace contained exactly:

```text
AGENTS.md
CandidateStage1A.lean
TASK.md
```

## Attempt

All reset, pin, oracle, expected-sentinel, Seatbelt, forbidden-read, upstream Lean, Codex app-server,
and auditor-unit preflights passed before the prompt was sent. The subscription-authenticated actor
then ran one session and one turn. It read the three local files, edited only the candidate, and
used Lean diagnostics for repair.

The first candidate used the wrong notation for the infinite differentiability order and Lean
rejected it. The actor inspected only the local candidate line, made a bounded correction, received
another diagnostic clarifying the `WithTop` representation, changed the order to `⊤`, and compiled
successfully. It performed a final local file inspection and stopped. The visible run contained
three `lean CandidateStage1A.lean` invocations; the complete trace contained six local `exec` calls.
No subagent, collaboration call, reviewer, MCP/browser/web/computer tool, network shell command, or
additional workspace root appeared.

## Candidate and mechanical result

The stopped candidate SHA-256 is:

```text
9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6
```

The candidate verifier confirmed the exact three-file workspace, imports, namespace, top-level
declaration names, structure field names, absence of the sentinel and escape hatches, and Lean exit
zero against upstream Mathlib only. The hidden `Basic.lean` oracle pin remained unchanged.

The original runner stopped at the trace gate because the auditor included JSON escape backslashes
in otherwise legal actor-root paths. The append-only decision
`2026-08-29-humanize2-kls-issue2-stage1a-trace-json-escaping.md` records the diagnosis and repair.
The model was not rerun. Re-auditing the same session returned `ok: true`, one session, one turn,
zero descendants, six `exec` calls, and no errors. Trace-input SHA-256 was
`9139ac615f7829cb2b9b1fe361445449a6c9bbdc2faa6a460a62a9efa69a6517`.

## Human-review boundary

Mechanical comparison shows that `IsAdmissible` and `dirichletEnergy` use the same formulas as the
hidden reference. `HasPoincare` has the same probability, nonnegativity, and universal
variance-energy proposition, but the candidate writes the quantified function binder explicitly
(`∀ f`) whereas the hidden implementation uses an implicit binder (`∀ ⦃f⦄`). This does not change
the logical proposition, but it is an API ergonomics difference for the human reviewer to accept or
reject under the frozen checklist.

No human acceptance has yet been recorded. The candidate is not an accepted Stage 1A dependency,
production formalization, theorem, proof, dossier, certificate, ledger event, or manuscript change.
Raw model transcripts, authentication state, and Humanize/Codex runtime state remain external and
are not committed.
