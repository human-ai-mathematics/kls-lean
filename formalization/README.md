# Lean formalization

Reusable mathematics lives under `FunctionalInequalities/`. Each registered certificate
has an entry in repository-root `solutions/` that imports its mathematical owners directly.
For current proof scope, use the [paper register](../research/progress/LITERATURE.md),
[BKL main proof chain](../research/progress/README.md#bkl-main-proof-chain) and
[current handoff](../HANDOFF.md). This guide describes layout and operations, not a second
proof-status register. The target theorem `KLS.kls` is proved; acceptance evidence belongs to the handoff.

The [Lean design](../LEAN_DESIGN.md) explains current interface boundaries; the
[calling examples](../examples/README.md) identify narrow imports and checked clients.

## Source map

The [complete filename directory](MODULES.md) expands every source directory and links all
Lean modules. Regenerate it with `python3 research/module_inventory.py` after module moves.
The [generated API directory](API.md) provides compiler signatures and an offline search page.

| Family | Responsibility / guide |
| --- | --- |
| `Analysis/` | Reusable analytic and algebraic tools, including operators, convexity, matrices and Bakry–Émery calculus |
| `Probability/` | Laws, affine support, covariance, transport and moment measures |
| `L2/` | Mean, variance and Hilbert-space probability interfaces |
| `Energy/` | Extended energies, relaxation and Euclidean realizations; [guide](FunctionalInequalities/Energy/README.md) |
| `Poincare/` | Test classes, constants, products, Gaussian models and identification bridges; [guide](FunctionalInequalities/Poincare/README.md) |
| `KLS/` | Target definitions, log-concave models and literature-specific applications; [guide](FunctionalInequalities/KLS/README.md) |
| `vendor/` | Pinned stochastic-calculus sources, port changes and isolated upstream holes; [guide](vendor/README.md) |
| `blueprint/` | Mathematical statements, declared dependencies and rendering tools; [guide](blueprint/README.md) |
| `../solutions/` · `../examples/` | Certificate clients and reusable calling examples |
| `../research/audits/` | Independent proof clients and explicitly classified candidate statements |

Focused family guides explain the maintained import boundaries:
[weak derivatives](FunctionalInequalities/Analysis/WeakDerivative/README.md),
[matrix trace](FunctionalInequalities/Analysis/Matrix/Trace/README.md),
[Stein identities](FunctionalInequalities/Probability/Stein/README.md),
[metric BV](FunctionalInequalities/KLS/Geometry/Perimeter/MetricBV/README.md), and
[regular moment producers](FunctionalInequalities/KLS/CEK/MomentRegularity/README.md).
The [module directory](MODULES.md) lists current placements; layout maintenance records and
migration maps are archived locally under ignored `build/history/`.

The aggregate `FunctionalInequalities.lean` is a library import root, not a completion marker.
The target is [KLS/Statement.lean](FunctionalInequalities/KLS/Statement.lean), with its definitions
in [KLS/Definitions.lean](FunctionalInequalities/KLS/Definitions.lean) and the target theorem in
[KLS/Target.lean](FunctionalInequalities/KLS/Target.lean).

## Placement rules

Follow [research/workflow.md](../research/workflow.md) and
[research/naming.md](../research/naming.md) before a module split or public API change.
Classify by mathematical object, actual scope, role and dependency level. Reuse an existing
owner; put identification bridges at the integration boundary. Keep reusable tools below
concrete applications, and audit-only candidate statements outside the proof library.
File moves and public-name migrations have separate maps and semantic checks.

## Lean Blueprint

The Blueprint supplies statements, reading order and declared dependencies; the four route
alternatives are exploratory records. See the [Blueprint marker rules](blueprint/README.md#markers-in-the-tex-sources)
and the [paper-coverage criteria](../research/progress/LITERATURE.md#when-a-paper-is-covered).

With Python, `xelatex`, `latexmk` and Graphviz available, run from the repository root:

```bash
python3 -m venv /tmp/kls-blueprint-venv
source /tmp/kls-blueprint-venv/bin/activate
python -m pip install --requirement formalization/blueprint/requirements.txt
python3 research/check_blueprint.py
python3 formalization/blueprint/build.py checkdecls
python3 formalization/blueprint/build.py pdf
python3 formalization/blueprint/build.py web
```

Build the Lean sources before `checkdecls`. The generated declaration list, PDF and web artifacts
under `blueprint/` are ignored outputs. Blueprint rendering runs locally when needed.

## Build and validation

Install Elan. `lean-toolchain` selects Lean v4.33.0; `lake-manifest.json` fixes Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d` and the other package revisions. From this directory:

```bash
lake exe cache get
lake build
```

The Mathlib cache download is optional. Keep the manifest for reproduction; `lake update`
changes dependency resolution. Default targets include the library, certificates, examples
and vendored libraries. Use the [verification guide](../research/verification.md) for the full
local gate and the separate Lean-only remote scope. Documentation-only changes do not need
a Lean rebuild. Builds, axiom audits, kernel replay and certificate registration have distinct scopes.
