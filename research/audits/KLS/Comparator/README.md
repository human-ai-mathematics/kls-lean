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
lake -d formalization build
git clone https://github.com/leanprover/comparator.git build/comparator-tools
git -C build/comparator-tools checkout 3927ad383f208ae977c340a91c48ac9b497d2097
lake -d build/comparator-tools build lean4export comparator
```

Keep its committed `lake-manifest.json`: it pins lean4export to
`15f6055e299ad5b89345e533cc2192f4cc00f659`. The runner refuses another revision or
modified source in either tool checkout. It uses the existing local dependency
checkouts and their build caches, not a pristine Git downstream reconstruction.

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
working unprivileged systemd user session, then run:

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

For the separate OpenAI bridge, its directory must be present (default:
adjacent `../KLS-OpenAI`). Its challenge imports the unmodified upstream OpenAI
model, and its solution imports `KLSOpenAI.Target`. The runner checks the model's
hash against that project's `UPSTREAM.json`:

```sh
python3 research/comparator.py --target openai --mode development --tools build/comparator-tools
```

Use `--bridge-root /absolute/path/to/KLS-OpenAI` to select another location, and
`--mode sandbox` on the Linux setup above. This separate project remains a local
path dependency until it has its own published source revision.

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
