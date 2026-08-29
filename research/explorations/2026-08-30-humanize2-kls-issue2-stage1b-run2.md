# Humanize2 Issue 2 Stage 1B authenticated Run 2

- **Date:** 2026-08-30
- **Target:** Stage 1B foundational lemmas and extended optimal Poincaré constant
- **Run type:** subscription-authenticated Humanize2 → Codex → Lean actor-only reconstruction
- **Repository commit at launch:** `b62f18f`
- **Outcome:** mechanical PASS; human semantic/proof review pending
- **Mathematical effect:** none

## Authorized repair boundary

The user explicitly approved a fresh Stage 1B Run 2 with only the five exact Lean theorem
signatures hardened. The actor-facing `TASK.md` printed the frozen headers for
`optimalPoincareConstant_le`, `le_optimalPoincareConstant`,
`optimalPoincareConstant_eq_top_of_no_finite`,
`optimalPoincareConstant_ne_top_of_hasPoincare`, and
`optimalPoincareConstant_eq_top_iff`. It supplied no proof term, proof strategy, Run 1 candidate,
verifier diagnostic, hidden reference, review, ledger answer, or production implementation.

Run 2 used the new external root
`/private/tmp/humanize2-kls-issue2-stage1b-run2` and a directly authenticated, dedicated actor
`CODEX_HOME`. It neither reset nor reused the stopped Run 1 state. The other eight declarations,
accepted Stage 1A dependency, verifier, oracle pin, checklist, model, effort, compiler loop,
Seatbelt policy, and trace policy were unchanged.

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

The actor directory and four input/dependency files were read-only. Only the literal candidate
path was writable. The accepted source and `.olean` retained SHA-256 values
`9bb81dd659453cfb7bcc514cc5d20693209ca985e049edd46f0da8f9de1395e6` and
`212cd1f5a0c20d2f3974c5948ea4c26550409a5b3b7b47a4b65e1e9cdf65a3a0`.
Repository source, existing KLS proofs and certificates, solutions, reviews, ledgers, manuscript,
oracle, later stages, client state, and other session trees were denied.

## Actor attempt and compiler feedback

Pinned Humanize2 commit `e8bcede84d4b3365378e04f9c80d0fd397903c30` launched one
`gpt-5.6-sol` actor at high effort. The actor read the four permitted text files, wrote an initial
thirteen-declaration candidate, and ran exactly `lean CandidateStage1B.lean`. The first compiler
pass reported one namespace qualification issue for the Hilbert-space Riesz isometry. The same
actor changed only that identifier, reran the exact Lean command, obtained exit zero, and performed
a final read-only inspection. This was one compiler-feedback repair iteration.

Stopped candidate SHA-256:

```text
3778490dcbd79f4632795f9b541a281b9032596c4cfe415e81b627a4c48e6c4e
```

## Mechanical gates and trace result

The runner and an independent post-run invocation of `stage_1b_verify_candidate.sh` both compiled
the candidate against the immutable accepted dependency plus upstream Mathlib only and passed the
hidden exact thirteen-declaration surface. The only diagnostic was a non-failing
`unnecessarySimpa` linter warning. `stage_1b_verify_oracle_pins.sh` matched the separately pinned
thirteen-block `Basic.lean` surface with SHA-256
`c929454a4ee73ddf152c4c739c6fc5eb3be76cd133746c600856b110bb835e0e`; the complete harness
pinset also passed.

The complete-session auditor reported `ok: true` with one actor-root session, one turn, zero
descendants, six local `exec` calls, no forbidden tools, paths, outputs, network, collaboration,
reviewer, client-state access, or Seatbelt denial, and a mutation set containing only
`CandidateStage1B.lean`. The compact external audit summary has SHA-256:

```text
f3519b985381ba083e85b422273a782943f572bc08daa6683fa0ad2f5829731f
```

Raw transcripts, authentication, tokens, Codex/Humanize state, machine-private configuration, and
generated `.olean` files remain outside Git.

## Stop boundary

The guarded runner exited zero and stopped at the pinned thirteen-item human semantic/proof
checklist. Mechanical success does not accept this candidate for Stage 2A. A human must still
review the proof against the hidden reference and explicitly accept, reject, or authorize another
fresh isolated repair run. No candidate was promoted into production Lean, no proof dossier or
review certification was created, and no theorem, certificate, ledger, manuscript, or mathematical
status changed.
