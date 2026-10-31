# Preparing a public revision

A release identifies one Git commit and the evidence for that exact source. This procedure
does not change mathematical coverage or authorize changing repository visibility.
The [paper register](progress/LITERATURE.md) owns source correspondence and certificate scope;
the [verification guide](verification.md) owns receipt and trust boundaries.

## Public access and the v1.0 release

For [Issue #10](https://github.com/human-ai-mathematics/kls-lean/issues/10), the maintainer
chose on **2026-10-26** to make the repository public after approving the README,
before final freeze verification. Finish and review the intended public documentation
and source diff first. Record README approval before changing visibility; making the
source public does not establish a verified v1.0 release.

When visibility changes, update the private-access notes in the
[root README](../README.md#build-and-verify) and the
[separate-project examples guide](../examples/README.md#connect-a-separate-lake-project).
Check that the documented public clone and dependency URLs work without repository credentials.

Then select the release commit, complete the local checks below, and push
`milestone/v1.0` to trigger Lean certification. Both that CI run and the Linux sandboxed
Comparator runs for `kls` and `openai` must pass for the **same final commit** before
publishing the GitHub release with its receipts. Follow with the Zenodo archive/DOI
and Palomar registration. The 2026-10-27 Linux Comparator passes for both targets
and CI run 40477880376 cover `0233f0b837131da5bb20420c4152d13260b8260a`.
They do not cover the subsequent uncommitted maintenance or a later release commit.

Prepare the Formal Conjectures proposal before the Mathlib contribution, as agreed
in the issue. The external proof annotation needs an accessible, immutable proof
link and a checked statement correspondence; neither proposal preparation nor public
source access implies that a contribution has been submitted or accepted.

## Finish the source snapshot

Review the intended diff, preserve unrelated local changes and staging, and finish public
documentation before verification. Keep theorem hypotheses, constants, normalizations and
dimension ranges faithful to their pinned sources. Review license and vendor notices,
contribution and citation links, and reachable Git history for material unsuitable for
publication. Automated credential-pattern checks are a limited screening step, not a complete
privacy or security audit. Do not rewrite previously pushed history as a cleanup shortcut.

If the working tree contains concurrent uncommitted development, prepare and verify the
release in a separate clean checkout of the chosen commit. Keep the original files and Git
index intact. A passing check of a larger working tree does not certify a smaller committed
release; bind every receipt to the source it actually checked. Local, uncommitted modules
are not part of the release simply because they are available in the development checkout.

Archive superseded operational notes verbatim with hashes under ignored `build/history/`.
Current instructions and acceptance inputs must remain in their tracked owning directories,
so that a fresh clone needs no local archive. Keep the root README short and follow the
[trust-scope rules](verification.md#receipts-and-trust-scope).

## Validate locally

From the root, populate and check the pinned third-party cache, then freeze the files:

```bash
python3 research/cache_mathlib.py --project all
python3 research/verify.py
```

Read the terminal status and `report.json`, not just the presence of compiled files.
Inspect the recorded snapshot and all errors. The full verifier includes all current Lean
modules, strict audit clients, declaration axiom checks, statement/metadata checks and local
kernel replay. It trusts pinned third-party compiled imports. A later source or documentation
edit requires a new matching full receipt before release.

The OpenAI bridge is a separate Lake package. Follow its
[build and audit instructions](../integrations/openai/README.md) as well as the
[Comparator guide](audits/KLS/Comparator/README.md). The cache command above prepares
both packages; the root verifier does not replace the bridge's separate checks.

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
Remote certification checks the Lean build, strict audit clients, every local declaration
against only `propext`, `Classical.choice` and `Quot.sound`, and the vendor and classical KLS
gates. See [receipt scope](verification.md#receipts-and-trust-scope) for full local kernel replay
evidence and the remaining local gates.
Only then claim remote certification for that revision. Public access may already have
been enabled under the README-first decision above; the verified release still waits
for both final-commit sandboxed Comparator passes and the remaining local checks.
Do not describe an older, cancelled, timed-out or incomplete run as current acceptance.

## Review and Linux handoff

Use the [focused maintainer checklist](progress/public-interface-review.md#focused-maintainer-checklist)
to record the actual personal review scope. The agent follow-up supplies contract inspection
and executable clients for UP-1, API-1 and LET-1; it cannot supply a maintainer's or Nicolas's
personal approval. Record a correction or an explicit review boundary when an item remains
open. The README positioning pass and the source diff must refer to the proposed public
revision. The maintainer has already accepted the Mathlib contact and review-discussion role;
that agreement does not need to be requested again.

For the Linux reviewer, identify the full final commit first and follow the
[Comparator preparation](audits/KLS/Comparator/README.md#judge-and-preparation),
including every package's Mathlib cache, bubblewrap, and a checkout outside the directories
the toolchain-bundled `lake comparator` sandbox covers. Run the targets against that checkout:

```bash
python3 research/comparator.py --target kls --mode sandbox
python3 research/comparator.py --target openai --mode sandbox
python3 research/comparator.py --target palomar --mode sandbox
```

Return the complete `receipt.json` files and their logs, with the full source commit and
source hashes. Confirm `COMPARATOR_PASSED_LINUX_SANDBOX`, `source_preserved` and
`staging_preserved` for each. Palomar's official full preflight is separate from these
receipts. A comment reporting success, a macOS development receipt or a
run for an earlier commit remains evidence only for its stated scope. Keep received raw
artifacts in the local verification archive and attach the reviewed receipts to the release;
do not replace them with truncated hashes in the issue discussion.

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

The hosted runner reserves disk before setup and bounds the job to the timeout in the
[Lean certification workflow](../.github/workflows/lean.yml). A disk error,
missing cache, compiler error and manual cancellation are different outcomes. Preserve their
logs and annotations, fix the identified cause, and retry at a meaningful milestone. Keep the
strict build and axiom audits enabled; raising a timeout alone does not repair a cache or disk problem.
