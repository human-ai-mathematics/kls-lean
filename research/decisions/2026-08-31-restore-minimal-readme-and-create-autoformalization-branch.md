# Restore the minimal README and create an autoformalization branch

## Decision

Keep the organization repository's `main` README in its original minimal form:

```text
# kls-lean
kls-lean formalization
```

Create `autoformalization-experiments` from the updated `main` branch as the dedicated workspace
for automatic-formalization experiments. The branch name intentionally does not use an agent
prefix because it is a persistent project branch rather than a temporary implementation branch.

## Rationale

The main branch should preserve the repository description chosen at initialization, while
experimental harness work should remain isolated from the checked Lean baseline until it has its
own review and validation.

## Validation

- verify the README contents byte-for-byte before pushing;
- push the README update as a fast-forward of `origin/main`; and
- verify that `autoformalization-experiments` points to the updated `main` commit when created.
