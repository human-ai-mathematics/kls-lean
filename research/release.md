# Preparing a public revision

A release identifies one Git commit and the evidence for that exact source. This procedure
does not change mathematical coverage or authorize changing repository visibility.
The [paper register](progress/LITERATURE.md) owns source correspondence and certificate scope;
the [verification guide](verification.md) owns receipt and trust boundaries.

## Finish the source snapshot

Review the intended diff, preserve unrelated local changes and staging, and finish public
documentation before verification. Keep theorem hypotheses, constants, normalizations and
dimension ranges faithful to their pinned sources. Review license and vendor notices,
contribution and citation links, and reachable Git history for material unsuitable for
publication. Automated credential-pattern checks are a limited screening step, not a complete
privacy or security audit. Do not rewrite previously pushed history as a cleanup shortcut.

Archive superseded operational notes verbatim with hashes under ignored `build/history/`.
Current instructions and acceptance inputs must remain in their tracked owning directories,
so that a fresh clone needs no local archive. Keep the root README short and follow the
[trust-scope rules](verification.md#receipts-and-trust-scope).

## Validate locally

From the root, populate and check the pinned third-party cache, then freeze the files:

```bash
python3 research/cache_mathlib.py
python3 research/verify.py
```

Read the terminal status and `report.json`, not just the presence of compiled files.
Inspect the recorded snapshot and all errors. The full verifier includes all current Lean
modules, strict audit clients, declaration axiom checks, statement/metadata checks and local
kernel replay. It trusts pinned third-party compiled imports. A later source or documentation
edit requires a new matching full receipt before release.

After the intended changes have an approved commit, verify a separate Git consumer:

```bash
python3 research/downstream.py --rev FULL_40_HEX_COMMIT
```

A local repository can be selected with `--repository /absolute/path/to/repository`.
The runner checks committed source in a fresh project and compiles its primary modules;
it never accepts the caller's working tree as a source overlay. Use its exact-revision receipt
to choose the documented consumer pin. A disposable committed fixture validates its own tree
and revision; it is not evidence for a different eventual release SHA.

## Certify the approved remote revision

Follow the [CI workflow](workflow.md#remote-ci-at-verification-milestones): after local
acceptance, push the approved revision and use one manual dispatch or one `milestone/**`
tag. Confirm the run's actual `head_sha`, successful conclusion and evidence artifact.
Remote certification checks the Lean scope; it does not replace the full local gate.
Only then update publication claims for that revision and change visibility when authorized.
Do not describe an older, cancelled, timed-out or incomplete run as current acceptance.

## Diagnose a long or failed run

Read the stage and log before retrying. The verifier prints a heartbeat every 30 seconds
for active commands, including elapsed time, log size, free disk and the last output line.
`build/verification/<time>/progress.json` retains completed gates and active commands even
when no final report exists. Its `running` state is incomplete evidence, not acceptance.
GitHub uploads these JSON/log files after a normal failure or cancellation when the runner
is still able to execute the artifact step.

The CI cache preflight recognizes both `Mathlib` and `Mathlib.*`, follows the pinned Mathlib
import closure, and refuses missing compiled modules. An aggregate import needs the aggregate
cache: fetching only dotted imports can otherwise turn a build into hours of source compilation.
For a read-only local diagnosis, run `python3 research/cache_mathlib.py --check`.
Cache completeness checks file presence; they are not a replay of third-party proofs.

The hosted runner reserves disk before setup and bounds the job to 180 minutes. A disk error,
missing cache, compiler error and manual cancellation are different outcomes. Preserve their
logs and annotations, fix the identified cause, and retry at a meaningful milestone. Keep the
strict audits and replay enabled; raising a timeout alone does not repair a cache or disk problem.
