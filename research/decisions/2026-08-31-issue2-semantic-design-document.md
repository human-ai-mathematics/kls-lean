# Add a semantic design document for staged Issue 2

Date: 2026-08-31

## Decision

Add `experiments/humanize2_kls_issue2_staged/SEMANTIC_DESIGN.md` as the living navigation layer for
the staged experiment's mathematical meaning, Lean encodings, intentional differences, downstream
contracts, unresolved questions, and current acceptance states.

The document is not a new mathematical ledger and does not replace frozen actor inputs, human
checklists, append-only decisions/explorations, or the production `LEAN_DESIGN.md`. Append-only
records remain authoritative history; the semantic document summarizes the current design and
links to them.

## Rationale

The experiment previously distributed semantic information across actor specifications, human
rubrics, handoffs, production design notes, and decisions. That made it easy to conflate four
different kinds of change:

- a change in mathematical meaning;
- a binder, namespace, or other Lean API difference;
- a proof-term-only difference; and
- an experimental acceptance or production-status change.

A single staged design map makes those distinctions explicit before later layers inherit them. It
also keeps open boundaries such as the smooth finite-energy core, abstract measurable structure,
extended-value conventions, and zero-dimensional behavior visible.

## Initial content and status

The initial document records:

- Stage 1A as a human-accepted experimental dependency, including its explicit-binder API
  difference and unchanged mathematical proposition;
- Stage 1B as a mechanical pass with human review pending, including a declaration-group
  comparison with production and the remaining semantic decisions; and
- Stages 2A through 5 as plans with questions, not authorized or proved statements.

This documentation contribution changes no Lean source, candidate hash, accepted artifact,
actor-visible fixture, frozen pinset, mathematical claim, dossier, ledger, manuscript, or
certification status.

## Validation

Before push, verify all relative links, confirm the Stage 1A and Stage 1B hashes against their
pins, rebuild the reviewer Lake project, run `git diff --check`, and confirm the repository root
`README.md` remains identical to `origin/main`.

## Observed validation

All relative links resolved. The accepted Stage 1A and pending Stage 1B SHA-256 checks passed. The
reviewer project completed 2,928 Lake jobs with only the already recorded non-failing
`unnecessarySimpa` suggestion. `git diff --check` passed, and the root `README.md` remained
identical to `origin/main`.
