# Publish Issue #2 directly on main

**Date:** 2026-09-03 (Asia/Shanghai)

## Decision

The user directs all subsequent work to take place on `main`, without feature branches or pull
requests. Publish the completed Issue #2 CI closeout directly to `origin/main`; keep the
tensorization/lifecycle follow-up as local uncommitted work until it is ready for publication.
This supersedes the branch/PR submission arrangement in the preceding exploration entry.

The published Issue #2 scope contains the existing native proof and certification harness, the
CI workflow, and closeout documentation. Its ledger has one proved node, with 13 checker tests
and the original default Lean targets. No tensorization skeleton or lifecycle change belongs
to this publication.

## Preservation and cleanup

Before changing the checkout, preserve the complete follow-up diff from `e7805f8` to `997caa2`
in a local patch. Restore that diff as uncommitted work on `main`. Retire PRs #4 and #5 and remove
the two branches created for this work, `codex/ci-poincare-tensorization` and
`codex/issue2-ci-closeout`, including the temporary closeout worktree. Other pre-existing
branches are outside this cleanup.

The tensorization node remains drafted, all 24 proposition placeholders stay intact, and
human freezing remains required before the separate proof phase. This change of Git workflow
does not freeze statements or certify tensorization.

## Existing acceptance evidence

The Issue #2-only commit `e7805f86cb89b1fe085179d9255722ccc8a8cbf5` passed both
[push CI](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/33667425988)
and [PR CI](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/33667472558).
The direct-main publication additionally runs the three required local commands and its own
push workflow. The historical CI and design records remain append-only.
