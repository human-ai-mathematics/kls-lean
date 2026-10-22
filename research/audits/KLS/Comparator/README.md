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

## Pinned tools and preparation

[tools.json](tools.json) fixes Comparator v4.33.0 and its exact lean4export dependency,
matching this project's unchanged toolchain. Comparator was incorporated into Lake
in Lean 4.35; upgrading is a separate decision. For this 4.33 project use these pins.

From the repository root, build the project normally and prepare the tools in an
unused local directory (the following path is an example):

```sh
python3 research/cache_mathlib.py --project all
lake -d formalization build
lake -d integrations/openai build
git clone https://github.com/leanprover/comparator.git build/comparator-tools
git -C build/comparator-tools checkout 3927ad383f208ae977c340a91c48ac9b497d2097
lake -d build/comparator-tools build lean4export comparator
```

Keep its committed `lake-manifest.json`: it pins lean4export to
`15f6055e299ad5b89345e533cc2192f4cc00f659`. The runner refuses another revision or
modified source in either tool checkout. It uses the existing local dependency
checkouts and their build caches, not a pristine Git downstream reconstruction.

The library and OpenAI bridge are separate Lake packages. On a fresh checkout,
the bridge can have its own `.lake/packages/mathlib`; preparing only the library's
cache leaves that copy without compiled Mathlib modules. The `--project all`
command above fetches the required Mathlib closure in each package and checks each
package's own `.olean` files before a build. It includes both aggregate `Mathlib`
imports and dotted imports, including the bridge's library dependency.
This addresses the source rebuild reported in [Issue #10](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6290311466).

Use `--project openai` to prepare only the bridge, or add `--check` to check the
selected caches without fetching. The default remains `--project formalization`
for the main-library build and CI. Dependency pins are unchanged; precompiled
third-party imports remain trusted. Project and bridge sources still build normally.

## Run

Strictly compile the original-declaration client and print its transitive axioms:

```sh
python3 research/comparator.py --target kls --mode compile
```

On macOS, explicitly request the upstream **unsandboxed development mode**:

```sh
python3 research/comparator.py --target kls --mode development --tools build/comparator-tools
```

This executes the actual pinned Comparator and lean4export, including statement
comparison, axiom checks and Lean kernel replay. It uses upstream `fake-landrun.sh`,
so the receipt says `COMPARATOR_PASSED_WITHOUT_SANDBOX`. Use it only with the trusted
local project. It is not a Linux sandbox or independent-kernel result.

On Linux, install real [Landrun](https://github.com/Zouuup/landrun) and ensure a
working unprivileged systemd user session. Before running the sandbox mode, address
the two setup issues reported in [Issue #10](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6289895395):

**Landrun version.** Use a source build from upstream `main`. The reported Linux
setup used [`ec104f6`](https://github.com/Zouuup/landrun/commit/ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a)
(v0.1.18); the tagged v0.1.15 failed with `permission denied` in that setup.
For reproducibility, check out that exact commit before building rather than
following a moving `main`, and ensure the built `landrun` is on `PATH`.

**Lean toolchain on PATH.** With a standard elan installation, `lake` may resolve
to the proxy at `~/.elan/bin/lake`. Comparator grants execution access (`--rox`)
to the Lean toolchain prefix, which does not include that proxy. This can make the
sandboxed run fail immediately with `permission denied`. Put the pinned toolchain's
`bin` first on `PATH` in the shell that launches the runner:

```sh
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.33.0/bin:$PATH"
command -v lake
```

The printed path should end in
`leanprover--lean4---v4.33.0/bin/lake`, not `.elan/bin/lake`. Adjust the prefix if
elan is installed elsewhere. Then run:

```sh
python3 research/comparator.py --target kls --mode sandbox --tools build/comparator-tools
```

The runner invokes the upstream systemd restriction on Unix-domain sockets. This
mode requires Linux and real Landrun; it never falls back to the development shim.
It performs no unsandboxed Solution preflight: Comparator itself builds and exports
the challenge and solution inside Landrun. Prebuild only the trusted project dependencies
as above; the separate strict client command is for trusted local development.
The OS, sandbox, pinned tool binaries and trusted prebuilt dependencies retain the
trust assumptions in the [upstream documentation](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097).
No extra proof kernel is enabled by these configs.

The separate [OpenAI bridge package](../../../../integrations/openai/README.md) is
included at `integrations/openai`. Its challenge imports the unmodified upstream OpenAI
model, and its solution imports `KLSOpenAI.Target`. The runner checks the model's
hash against that project's `UPSTREAM.json`:

```sh
python3 research/comparator.py --target openai --mode development --tools build/comparator-tools
```

Use `--bridge-root /absolute/path/to/bridge` to select another location, and
`--mode sandbox` on the Linux setup above. This independent Lake project uses the
substantive KLS library from the same repository revision through a relative path
dependency. Build it as described in its README before running Comparator.

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
