# Comparator checks for KLS

The trusted [challenge](Challenge.lean.in) states the existing
`FunctionalInequalities.KLS.kls : FunctionalInequalities.KLS.Conjecture`.
It imports only the statement module, not the KLS proof. The [solution](Solution.lean.in)
imports the original closed declaration; no new proof or wrapper changes its type.
Review the challenge, `KLS/Statement.lean` and its definition closure together.
Comparator compares the statement closure, checks permitted axioms and replays the
exported proof in Lean's kernel. Its result does not establish mathematical source
faithfulness or constitute human review.

The `.lean.in` suffix deliberately keeps the challenge's single placeholder outside
the strict proof-client inventory. The runner copies these tracked inputs into a
new ignored `build/comparator/` fixture. No placeholder enters the library or its
proof-development counts. The [config](config.json) permits only `propext`,
`Classical.choice` and `Quot.sound`; there are no definition holes.

## Judge and preparation

The judge is the `lake comparator` bundled with the pinned Lean toolchain
([bundled-judge.json](bundled-judge.json): `leanprover/lean4:v4.35.0`). It builds and exports
the challenge and solution, compares the configured theorem statements and their definition
closure, rejects axioms outside `permitted_axioms`, and replays the solution export in Lean's
kernel (`leanchecker`). Its exporter `leanexport` is the toolchain's own. NanoDa runs only when
a configuration registers it (`enable_nanoda: true`); the `kls` and `openai` configs do not,
the Palomar config does. `--paranoid` and the other bundled checkers are not used.

[tools.json](tools.json) is the historical pin of the external Comparator v4.33.0
(`3927ad38`) and lean4export (`15f6055e`) that judged the receipts made before the Lean v4.35
migration. It is kept unchanged for those receipts and for the metadata-schema pin below; the
current runner records its hash but never uses it, and rejects the old `--tools` option.

From the repository root, prepare and build the trusted projects normally:

```sh
python3 research/cache_mathlib.py --project all
lake -d formalization build
lake -d integrations/openai build
lake -d integrations/palomar build Solution
```

The runner uses the existing local dependency checkouts and their build caches, not a
pristine Git downstream reconstruction. It writes a new fixture with an explicit
`lake-manifest.json` (which `lake comparator` requires) whose entries are absolute paths to
the same pinned checkouts, and records the toolchain prefix, `lean --githash` and the SHA-256
of the bundled `lake`, `lean`, `leanexport`, `leanchecker` (and `nanoda_bin` when registered).

The library and OpenAI bridge are separate Lake packages, and the Palomar project is a third.
On a fresh checkout each can have its own `.lake/packages/mathlib`; preparing only the
library's cache leaves the others without compiled Mathlib modules. The `--project all`
command above fetches the required Mathlib closure in each package and checks each
package's own `.olean` files before a build. It includes both aggregate `Mathlib`
imports and dotted imports, including the bridge's library dependency.
This addresses the source rebuild reported in [Issue #10](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6290311466).

Use `--project openai` or `--project palomar` to prepare one contained project, or add
`--check` to check the selected caches without fetching. The default remains
`--project formalization` for the main-library build and CI. Precompiled third-party imports
remain trusted. Project and bridge sources still build normally.

## Run

Strictly compile the original-declaration client and print its transitive axioms:

```sh
python3 research/comparator.py --target kls --mode compile
```

On macOS, explicitly request the **unsandboxed development mode**:

```sh
python3 research/comparator.py --target kls --mode development
```

This runs the bundled `lake comparator --inadvisably-no-sandbox`, including statement
comparison, axiom checks and Lean kernel replay; the receipt says
`COMPARATOR_PASSED_WITHOUT_SANDBOX`, and the runner requires the tool's own
sandbox-disabled warning in that mode. Use it only with the trusted local project. It is not
a sandboxed or independent-kernel result.

On Linux, install [bubblewrap](https://github.com/containers/bubblewrap) (`bwrap` on `PATH`,
with unprivileged user namespaces or a setuid installation) and run:

```sh
python3 research/comparator.py --target kls --mode sandbox
```

`lake comparator` binds `/` read-only and covers `/home`, `/root`, `/run/user` and `/tmp`
with empty file systems; only the fixture, the toolchain prefix and Lake's home are bound
back, only the fixture's `.lake` is writable, and the build, export and kernels have no
network. The trusted dependency checkouts must therefore live outside those covered
directories and be fully prebuilt; the runner refuses sandbox mode otherwise. It performs
no unsandboxed Solution preflight in this mode. The OS, sandbox, toolchain binaries and
trusted prebuilt dependencies retain the trust assumptions of `lake help comparator`.

The separate [OpenAI bridge package](../../../../integrations/openai/README.md) is
included at `integrations/openai`. Its challenge imports the upstream OpenAI model, and its
solution imports `KLSOpenAI.Target`. The runner reverses the recorded module-header
adaptation of the model and checks the original upstream SHA-256 and the local SHA-256 in
that project's `UPSTREAM.json`:

```sh
python3 research/comparator.py --target openai --mode development
```

The [Palomar project](../../../../integrations/palomar) is checked with `--target palomar`.
Its committed `Challenge.lean`, `Solution.lean` and `comparator.json` are staged unchanged;
the runner requires module headers, a Challenge importing only Mathlib, a configuration with
exactly `KLSOpenAI.kls`, the standard axioms, no definition holes and `enable_nanoda: true`,
and the same dependency pins as the OpenAI bridge. In compile mode its axiom report comes
from a generated non-module client, because the Palomar Solution prints none. This local
check does not replace Palomar's official full preflight (protected configuration, con-ron).

```sh
python3 research/comparator.py --target palomar --mode development
```

Use `--bridge-root` or `--palomar-root` with an absolute path to select another location.
These independent Lake projects use the substantive KLS library from the same repository
revision through relative path dependencies. Build them as described above first.

Each invocation preserves a new fixture, logs and `receipt.json`, with source/input
hashes and staging checks. Read the terminal status and full receipt. Failed runs
are retained; a config, compilation-only result or earlier receipt is not acceptance
of a later source tree. The runner does not commit, publish or launch remote CI.

## Metadata

The root [formalization.yaml](../../../../formalization.yaml) reports provenance,
AI involvement, external libraries, source fidelity and the maintainer's review of
key statements. It does not claim independent human peer review or source-author
endorsement. Its version-0.4 schema is pinned in `tools.json`; with PyYAML and
jsonschema installed, the published schema can be used to validate it.
