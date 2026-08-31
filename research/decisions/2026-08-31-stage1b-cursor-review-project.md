# Add a Cursor project for Stage 1B human review

Date: 2026-08-31

## Problem

The persisted Run 2 candidate imports `AcceptedStage1A`, but `review/pending/` was only an archive
location. Opening the file directly in Cursor therefore selected the global Lean executable and
failed with `unknown module prefix 'AcceptedStage1A'`, even though the isolated verifier compiled
the same bytes with its explicit `LEAN_PATH`.

## Decision

Make `experiments/humanize2_kls_issue2_staged/review/` a reviewer-only Lake project pinned to Lean
and Mathlib 4.33.0. Define one library root at the already accepted Stage 1A source and one at the
pending Stage 1B Run 2 candidate. Enable Cursor's automatic dependency build only for this nested
workspace and ignore its generated `.lake/` directory.

This is editor infrastructure. It does not alter either Lean source, add files to an actor
workspace, accept Stage 1B, or change any mathematical or certification status.

## Validation

Validate from the `review/` directory with `lake build`, direct `lake env lean` elaboration of the
pending candidate, the candidate SHA-256 pin, and a clean Git diff check. Confirm separately that
the repository root `README.md` remains identical to `origin/main`.
