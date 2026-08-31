# Humanize2 Issue 2 Stage 1B authenticated zero-warning Run 3

- **Date:** 2026-08-31
- **Target:** Stage 1B foundational lemmas and extended optimal Poincaré constant
- **Run type:** subscription-authenticated Humanize2 → Codex → Lean actor-only reconstruction
- **Repository commit at launch:** `e1a4aa2`
- **Outcome:** zero-diagnostic mechanical PASS; human semantic/proof review pending
- **Mathematical effect:** none

## Authorized repair boundary

The user rejected Run 2 as the Stage 2A dependency because its exact Lean command emitted one
`unnecessarySimpa` linter suggestion, then authorized one fresh Run 3. Run 3 retained the same
thirteen declarations, exact theorem types, mathematical specification, accepted Stage 1A
dependency, model, effort, compiler loop, hidden surface, and review boundary. The sole new
actor-facing requirement was that `lean CandidateStage1B.lean` exit zero with empty standard
output and standard error, with no diagnostic suppression.

Run 3 used `/private/tmp/humanize2-kls-issue2-stage1b-run3` and a newly authenticated dedicated
`CODEX_HOME`. It received no Run 2 candidate, warning location, replacement proof, production
implementation, hidden oracle, checklist, or reviewer reasoning.

## Physical isolation and visible fixture

The deny-default Seatbelt preflight passed before the model call. The actor-visible workspace had
exactly five entries:

```text
AGENTS.md
TASK.md
AcceptedStage1A.lean
AcceptedStage1A.olean
CandidateStage1B.lean
```

Only the literal candidate path was writable. The accepted source and compiled dependency stayed
read-only at SHA-256 values
`9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6` and
`212cd1f5a0c20d2f3974c5948ea4c26550409a5b3b7b47a4b65e1e9cdf65a3a0`.
The migration-compatible isolation test denied repository formalization, main-checkout,
certificate, design, review, knowledge, handoff, oracle, checklist, and actor-client-state probes.

## Actor attempt and compiler feedback

Pinned Humanize2 commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` launched one
`gpt-5.6-sol` actor at high effort. The first Lean run exposed an unavailable library lemma name
and one style diagnostic. The same actor repaired the underlying proof terms without disabling a
linter, completed three compiler-feedback repair iterations, and finally obtained exit zero with
empty output. It then performed the required final source inspection.

Stopped candidate SHA-256:

```text
027e69674f78eb735b380b18beaf43e55779e0634d7222f46681f1bae30b752d
```

## Mechanical gates and trace result

The runner and an independent post-run invocation of `stage_1b_verify_candidate.sh` both accepted
the candidate. The exact Lean command was independently captured with empty output. The candidate
imports only the accepted Stage 1A dependency, exposes the exact thirteen-declaration surface,
uses no diagnostic suppression or escape hatch, and compiles against upstream Mathlib with pinned
Lean 4.33.0. The separately pinned `Basic.lean` surface remained
`c929454a4ee73ddf152c4c739c6fc5eb3be76cd133746c600856b110bb835e0e`.

The complete-session auditor reported `ok: true`, no errors, one actor-root session, one turn,
zero descendants, ten local `exec` calls, exactly the five allowed visible files, and a mutation
set containing only `CandidateStage1B.lean`. The compact audit SHA-256 is:

```text
be9972dacfcf56a0af3e5bb61ea3ad12a7757a0d3c2ff0863f4ade8fce98aa44
```

## Post-stop semantic comparison and boundary

The generated statement and definition surface agrees exactly with the precommitted checker. A
comparison with the corresponding production `Basic.lean` layer found no new semantic difference
beyond the accepted Stage 1A binder choice and experimental namespace. Remaining differences from
production and Run 2 are proof-only: alternate Riesz-isometry, almost-everywhere
integral-congruence, infimum, and finite-versus-`⊤` proof terms. This comparison is evidence for
the human review, not acceptance.

The candidate is published byte-for-byte at
`experiments/humanize2_kls_issue2_staged/review/pending/CandidateStage1BRun3.lean`. The run stops at
the fourteen-item human checklist. It creates no accepted dependency, production theorem, proof
dossier, certificate, ledger event, manuscript change, or mathematical-status transition. Stage
2A has not started.
