# Migrate existing work to `kls-lean`

## Decision

Move the committed state of the functional-inequalities working repository into the
`numina-functional-inequalities/kls-lean` repository on a migration branch based on that
repository's `main` branch.

The migration copies the current committed tree rather than force-pushing the old repository
history. This keeps the destination's initial commit, produces a branch that GitHub can compare
and merge normally, and preserves the former personal fork and source repository as legacy Git
remotes.

Local untracked duplicate files, generated PDF output, and editor metadata are excluded from the
migration. They remain untouched in the original working directory.

## Rationale

The `kls-lean` repository is the organization-owned home for the KLS Lean formalization effort,
and Issue #2 has been transferred there. Keeping the active remote and review workflow in that
repository avoids further divergence from the organization project while retaining recoverable
links to the earlier repositories.

## Validation

Before pushing the migration branch:

- run `python3 research/check_ledger.py`;
- run `python3 -m unittest discover -s research/tests -p 'test_*.py'`;
- run `lake build` from `formalization/`;
- verify that the migration branch is based on `origin/main` and that the original working tree's
  untracked files are unchanged.
