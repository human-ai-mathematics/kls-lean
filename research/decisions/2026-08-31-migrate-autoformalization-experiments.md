# Migrate autoformalization experiments to `kls-lean`

Date: 2026-08-31

## Decision

Publish the complete Humanize2 experiment chain on
`numina-functional-inequalities/kls-lean:autoformalization-experiments`, based on the focused Lean
project already present on `kls-lean/main`. Keep the root `README.md` byte-identical to `main`.

The migrated scope is limited to:

- the Humanize2 infrastructure baseline;
- the KLS statement-fidelity experiment;
- the isolated proof-repair scaffold;
- the staged Issue 2 experiment, including its append-only decisions and failed/successful run
  records; and
- the exact Stage 1B Run 2 candidate, pinned under `review/pending/` for human review.

The old research monorepo, ledgers, manuscript, unrelated proof dossiers, raw transcripts,
credentials, Codex/Humanize state, and generated `.olean` files are not migrated. Two exact
reviewer-oracle dependencies are retained: `research/knowledge/lemmas.md` and
`research/reviews/2026-08-29-lean-linear-test-semantic-followup.md`. The existing focused
`formalization/` and `solutions/LemLinearTestLower.lean` files provide the remaining oracle
material.

The focused repository's `solutions/LemLinearTestLower.lean` differs from the original experiment
only in its module comment; its declaration and proof are unchanged. The statement-fidelity oracle
pin is updated from the historical source hash
`7cccca09bb4630b38903536f60ba2df2127ef5ab3ab31e01b24975d85e2c90d7` to the focused repository
hash `96c8a8bb8e4639308f8bfdd9dc6ca22766ba515982ad57c2c11a51a545d23342`, and the candidate is
reverified against this migrated oracle before push.

## Rationale

Keeping experiments on a dedicated branch leaves `main` as Nicolas's minimal Lean repository while
making the reproducible harness, provenance, and pending human gate available remotely. Committing
the stopped candidate under `review/pending/` closes the previous reproducibility gap without
misclassifying it as accepted or exposing it to the already terminated isolated actor.

## Validation contract

Before push:

1. confirm the root `README.md` is unchanged from `origin/main`;
2. verify all recorded SHA-256 pinsets;
3. run the Python and trace-auditor tests;
4. run shell syntax checks for every migrated runner;
5. rebuild the focused Lean project;
6. reproduce the Stage 1B candidate's exact-surface check in a fresh review root;
7. scan for proof placeholders and credential patterns; and
8. leave `git diff --check` clean.

These checks validate migration and harness mechanics only. Stage 1B remains human-review pending,
and no mathematical or certification status changes.

## Observed validation

The migration checks passed on 2026-08-31:

- `README.md` had no diff from `origin/main`;
- all statement-fidelity, proof-repair, Stage 1A, Stage 1B, and pending-candidate SHA-256 checks
  passed;
- the baseline Python suite passed 2 tests, and the three trace-auditor suites passed 4, 5, and 7
  tests;
- every migrated shell script passed `bash -n`;
- `lake build` completed 2,946 jobs;
- a fresh `/private/tmp/humanize2-kls-issue2-stage1b-review` workspace reproduced the immutable
  Stage 1A hashes and the Stage 1B exact-surface/upstream-Mathlib-only compilation check;
- the migrated Lean files contained no `sorry`, `admit`, `axiom`, or `unsafe`, and the scoped
  credential-pattern scan was clean; and
- `git diff --check` passed.

Lean emitted one non-failing `unnecessarySimpa` linter suggestion in the pending Stage 1B candidate.
It does not change the theorem or the mechanical PASS and is left untouched pending human review.
