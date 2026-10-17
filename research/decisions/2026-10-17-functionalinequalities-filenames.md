# FunctionalInequalities filenames (2026-10-17)

## Scope and placement plan

The owner requested a complete expansion of the library filenames and filename management.
The [generated directory](../../formalization/MODULES.md) lists all 551 modules, grouped by
their six existing top-level owners. [The generator](../module_inventory.py) checks direct
local imports, cycles, case-insensitive collisions and sibling `X.lean` / `X/` collisions;
it does not infer proof status or judge every declaration's mathematical scope.

The mechanical scan covers the entire filename/import tree. Focused source review covers
the three families below and the retained naming signals. This is not an exhaustive
mathematical review of all 551 modules or a declaration-name migration.

| Owner and exact scope | Destination | Decision and imports |
| --- | --- | --- |
| Haar mollification, L2 convergence and Lipschitz-gradient Hessian approximation | `Analysis/Mollification/{Basic,Hessian}.lean` | Genuine foundational/extension pair. Hessian imports Basic; every other dependency and import order is preserved. |
| Regular log-concave potentials/laws and their affine, isometric, isotropic and Poincaré transport | `KLS/LogConcave/Regular/{Basic,Affine,Isometry,Isotropic,Poincare}.lean` | Existing five-module object family. Basic retains the original definitions and results; the extensions retain their original dependency graph. |
| Smooth and weak inverse-Hessian integration by parts and height cutoffs | `Analysis/BakryEmery/IntegrationByParts/InverseHessian/{Basic,Cutoff,Weak,WeakCutoff}.lean` | Existing four-module object family. Weak qualifiers and compact-test/cutoff distinctions remain; no strong/weak proofs are merged. |

The [complete path, module and declaration-location map](../api-migration/2026-10-17-functionalinequalities-filename-map.json)
records all eleven whole-file relocations. Public names and namespaces stay unchanged.
Existing consumers import the new paths directly; no old-path wrappers or aliases are added.
No new proof, definition, assumption, normalization, dimensional restriction or certificate is introduced.

## Reviewed names retained

- `BKL/Theorem41.lean` and `BKL/Proposition71.lean` retain their established per-paper
  source-locator roles, as reviewed in the [previous filename decision](2026-10-12-analysis-bkl-filename-layout.md).
  Their module documentation identifies both mathematical content and pinned paper version.
- `HminusOne`, `C1Pieces`, `CompactBound`, `LocalThirdCumulant` and `Weak*` retain meaningful
  space, regularity, support and exponential-radius distinctions. Length alone is not a rename criterion.
- `WeakHessianEvolution` and `WeakLaplacian` remain separate responsibilities in IntegrationByParts;
  importing inverse-Hessian identities does not itself change ownership.
- Matrix weak trace identities, Bakry–Émery Hessian calculus and log-concave Hessian trace
  applications remain in their distinct existing families.
- `Definitions`, `Statement` and `Target` remain separate KLS definition, specification and proof
  entries. Existing `Basic` files are not renamed merely for sharing that basename.

## Preservation and acceptance boundary

The actual dirty source baseline, the real index bytes and ordered staging entries/flags are
saved in [the maintenance evidence directory](../../build/file-management/2026-10-17-functionalinequalities-filenames/).
Moved production Lean payloads must equal the saved source after only the explicit import-module
substitution. Audit clients apply that same import map; `LetwinUniformIntervalAudit` additionally
updates its literal module-name target for the existing all-constants standard-axiom check.
Its check conditions and declaration names stay unchanged. Source docstrings retain their recorded wording; old
embedded paths can be resolved through this migration map. No historical decisions, archived
handoffs, explorations, previous maps or prior verification receipts are rewritten.

The complete elaborated declaration-owner inventory includes private and compiler-generated
constants. Before refreshing evidence, compare every affected declaration type and non-theorem
definition closure structurally. Only the explicit module-owner map may normalize compiler-private
or hygienic names. Preserve public names, universe parameters, binder names/info, assumptions,
visibility and the existing instance environment. This comparison does not assert equality of
elaborated theorem proof values; proof source is preserved and checked by the full verifier.

The BKL independent-target golden keeps the original source-review identity and all statement,
definition and external-boundary fields. Only the four reviewed RegularPotential declaration-owner
module fields move to `Regular.Basic`; the new map supplies path-migration provenance.
Live infrastructure evidence hashes may be refreshed only after matching the saved baseline
and accepted import-only transform. Proof and paper statuses remain unchanged.

Acceptance requires the source/semantic comparisons, live consumer/link checks, full `lake build`,
full `research/verify.py`, private-index progress regeneration and index/history preservation.
The [completion receipt](../../build/file-management/2026-10-17-functionalinequalities-filenames/COMPLETION.json)
records actual outcomes and exact verification scope; this decision is not itself a proof receipt.
No commit, push, tag, remote CI, provider call or publication is part of this task.
