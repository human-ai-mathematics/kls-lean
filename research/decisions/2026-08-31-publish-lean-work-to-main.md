# Publish the focused Lean work directly to `kls-lean/main`

## Decision

Publish the completed Issue #2 Lean project directly to the organization repository's `main`
branch. The destination repository is dedicated to the Lean formalization stream, so a separate
migration pull request is unnecessary for this initial import.

The uploaded closure consists of:

- the pinned project and reusable modules under `formalization/`;
- the separately compiled certificate `solutions/LemLinearTestLower.lean`;
- the root and project READMEs;
- `LEAN_DESIGN.md`; and
- repository ignore rules and this decision record.

The broader manuscript, A-series and KLS ledgers, numerical experiments, unrelated proof dossiers,
historical agent records, generated PDFs, and local duplicate files are intentionally excluded.
The mathematical statement and Lean proof are copied without modification; only repository-facing
documentation is adapted so that it has no broken dependencies on the former monorepo.

## Rationale

This keeps `kls-lean` small, reproducible, and aligned with its stated purpose. It also avoids
publishing unrelated research material merely because the first Lean certificate was developed in
a larger working repository.

## Validation

Before the direct push:

- run `lake build` from `formalization/`;
- scan the uploaded Lean sources for `sorry`, `admit`, and custom `axiom` declarations;
- run `git diff --check`; and
- verify that the commit is a fast-forward of the remote `main` branch.
