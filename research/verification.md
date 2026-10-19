# Local verification and task atlas

Use the [current handoff](../HANDOFF.md) for active work, the
[receipt rules](#receipts-and-trust-scope) for snapshot-bound evidence, and the
[paper register](progress/LITERATURE.md) for theorem scope, source versions and coverage.
The [BKL main proof chain](progress/README.md#bkl-main-proof-chain) provides a short reading order.
This guide describes current commands and trust boundaries.

## Authorities and task navigation

Lean sources define the propositions and proofs. Blueprint records statements and declared
mathematical dependencies; the ledger maps certificates; `tasks.json` records classification,
assumptions, priorities and evidence. None is a second informal proof-status database.
The atlas derives navigation from these sources and does not infer truth from prose.

```bash
python3 research/atlas.py check
python3 research/atlas.py export
python3 research/atlas.py ready
python3 research/atlas.py show thm:bkl-taylor-criterion
```

The graph has declared dependencies, not proof-term dependency extraction. Atlas actions such
as `complete` require a passing receipt matching the current snapshot. Missing, stale or failed
receipts request verification; they do not establish proof or certificate status.

## Verification commands

From the repository root:

```bash
python3 research/cache_mathlib.py
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/verify.py
```

The full verifier runs structural/task checks and Python regressions, builds all current
library, solution, example and vendored modules (including modules outside default import
closures), and strictly compiles every live `research/audits/**/*.lean` client. It checks the
statement baseline and registered declarations, audits transitive axioms, and replays the
current local modules with Lean's kernel.

The generated axiom audit checks every project-local declaration, including private and
generated declarations and the target theorem `FunctionalInequalities.KLS.kls`; no local
declaration is excluded. A local declaration or wrapper depending on `sorryAx` or another
nonstandard axiom fails. The vendor gate uses an exact, separately reviewed list of five upstream
`sorry` declarations; it does not permit project-local results to depend on those holes.
See the [vendor policy](../formalization/vendor/README.md#upstream-holes).

The `classical-kls` gate (both modes, after the research-audit sweep) runs
[research/audits/KLS/Classical/check.py](audits/KLS/Classical/README.md) with the same filtered view.
- **Inputs.** Pinned Mathlib-only templates of three classical KLS formulations and their client.
- **Checks.** Strict compilation of both, exactly four standard-axiom reports, kernel replay of both runtime modules, and
  three false-statement mutations of the specification, each rejected by the expected client elaboration error.
- **Pins.** The pins change only with a reviewed source change; the gate does not refresh them.
- **Lean-only receipt.** It binds every file in that directory.
The full verifier also checks the vendored files offline against
`formalization/vendor/vendor-lock.json` (inventory, vendored hashes, `port.patch` hash, and strict
reverse application of the patch to the locked upstream hashes); `python3 research/vendor_lock.py
--fetch` additionally compares the lock with the upstream repositories at the pinned commits. See
the [provenance lock](../formalization/vendor/README.md#provenance-lock).

Audit clients use warnings-as-errors. Proposition type checks remain candidate statements;
compiling them neither proves the proposition nor registers a certificate. Audit elaboration
and local-module kernel replay are separately reported scopes.

Before a cold build, `cache_mathlib.py` recognizes both `Mathlib` and `Mathlib.*`, requests
their pinned precompiled closure, and checks all required Mathlib `.olean` files. The CI
preflight fails on an incomplete cache instead of silently rebuilding Mathlib from source.
Use `python3 research/cache_mathlib.py --check` to inspect existing caches without fetching.
This checks file presence, not third-party proof validity. Cache inputs remain pinned;
the trusted-third-party boundary is unchanged.

The runner builds a filtered compiled-module view for the current source inventory, replacing
the local entry in the Lean search path. Hidden production sources, missing artifacts, orphan
module adoption and replay coverage mismatches fail. See the implementation in [verify.py](verify.py).

For a separate Git consumer, use the [downstream runner](downstream.py) and its
[command guide](../examples/README.md#reproduce-downstream-acceptance). It builds three narrow
clients from one exact commit, audits their primary declaration closure and replays their
local modules. Its receipt is a separate downstream check; it neither runs the full KLS
verifier nor changes certificate status. Third-party compiled dependencies remain trusted.

## Receipts and trust scope

Each run retains its report, generated clients and logs under `build/verification/<UTC time>/`.
`latest.json` identifies the latest full attempt; `latest-lean.json` identifies the latest
Lean-only attempt. A failed latest attempt is not a success receipt.

Active commands print progress every 30 seconds: elapsed time, log size, free disk and the
last log line. `progress.json` is updated as gates complete and while commands run, including
parallel audit clients. It remains available after an interrupted run without a final report;
`running` is incomplete evidence. The final report and terminal status determine acceptance.
See the [release guide](release.md#diagnose-a-long-or-failed-run) for cache, disk and cancellation
diagnosis. Lean-only snapshots also bind the cache-preparation script and its import parser.

Receipts record HEAD separately from source hashes and scope. A full receipt includes tracked
and nonignored untracked source content and documentation; the Lean-only snapshot includes
Lean sources, pinned build inputs and verification tooling. Sources must remain unchanged
during a run. A receipt applies to its recorded snapshot, not automatically to a later tree
or HEAD alone. Finish documentation before a full acceptance run; do not write its final hash
back into source files and still call it current.

Pinned third-party compiled imports, including Mathlib and its dependencies, remain trusted.
Local-module replay is not an independent second kernel, a fresh dependency replay or an
isolated source reconstruction. Kernel replay alone accepts `sorryAx`; the separate axiom
gates reject it in their stated proof scopes. No-sorry claims require the actual declaration
and import-boundary audits, not just a successful build.

## Statement baseline

[statement_snapshot.py](statement_snapshot.py) checks elaborated types and local definition
closures rooted in the target/domain/energy interfaces against the reviewed
[golden file](a-series/statement-snapshot/golden.json). The actual roots are maintained in the
script; dependency expansion includes local definitions and types, not theorem proof bodies.
Pinned external declarations are trust-boundary leaves. This detects drift within its explicit
coverage; it is not a proof of source fidelity or semantic equivalence.

```bash
python3 research/statement_snapshot.py check
```

The verifier never refreshes the golden automatically. An intentional baseline change requires a
newly named, tracked [statement-snapshot review](a-series/statement-snapshot/REVIEW.md) stating the
old/new mathematical scope or the toolchain/printing-only nature of the change, re-pinned explicitly:

```bash
python3 research/statement_snapshot.py update --decision research/a-series/statement-snapshot/NEW-REVIEW.md
```

## BKL independent target pilot

Theorem 3.1 and Proposition 7.1 have a separately compiled specification, explicit definition
bridges and a reviewed target/definition-closure baseline. Run the pilot separately:

```bash
python3 research/audits/BKL/IndependentTargets/run.py check --paper /absolute/path/2610.05474v1.pdf --mutations
```

The PDF hash is checked. [The pilot guide](audits/BKL/IndependentTargets/README.md) states its
foundation parameters, source-review boundary, replay scope and receipt locations. It does
not run implicitly as part of the full verifier, refresh the general golden, discharge the
universal cumulant hypothesis or add certificates. It is not an external comparator or a
second-kernel check.

## Progress generation

All canonical generator inputs are read from the selected Git index: Blueprint, ledger,
tasks, route/provenance records, the three progress catalogs, the README template and the
Lean declaration sources used by the paper maps. Old generated block bodies are excluded
from the template input. The canonical digest covers the complete input set.

```bash
python3 research/progress/update.py
python3 research/progress/update.py --check
python3 -m unittest discover -s research/progress -p 'test_*.py'
```

Stage intended canonical records before generation. In a dirty tree, use a task-local
`GIT_INDEX_FILE` containing exactly the intended inputs; preserve the real index. Run generation
and checks with that same index. Unstaged catalog, template or declaration changes are excluded.
Generated views are navigation, not a new Lean run. Do not edit generated blocks directly.

## Change-appropriate checks and remote CI

Follow [workflow.md](workflow.md#6-deliver-with-evidence-proportional-to-the-change).
Documentation-only edits need link/rule review, scoped diff checks and generated-view checks,
not a Lean rebuild. Generator changes also need regressions for index isolation and status
propagation. Proof/API/module changes retain their existing Lean acceptance requirements.

Remote certification runs `python3 research/verify.py --lean-only` only on manual dispatch or
an explicitly pushed `milestone/**` tag, with owner authorization. Metadata checks remain local;
Blueprint rendering remains local. Record remote success only for the exact successful SHA.
See the [CI procedure](workflow.md#remote-ci-at-verification-milestones).
