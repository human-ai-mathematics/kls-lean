# Topic-based Lean module layout

Date: 2026-09-03. This is an append-only follow-up to the finite tensorization candidate and
semantic review. It records source organization, not a statement freeze or a proof completion.
Work remains local and uncommitted on `main`, whose HEAD is
`4801ca958778ae02cc0d81fc7ec805a4e96a894c`.

## Reason and boundary

The user identified the flat `FunctionalInequalities/` source directory as difficult to navigate.
The library is now grouped by mathematical subject, with binary products and dependent finite
products in separate subdirectories. `Project/` still packages exact node statements and
Euclidean specializations; `solutions/` still provides the ledger-bound thin entry points.

The source count is unchanged: 17 Lean files across the root aggregate, the reusable/project
library, and the three solution entry points. Ten files moved; no proof was split, combined, or
rewritten. No new typeclass shorthand or mathematical hypothesis cleanup is included in this
move. The independent discussion of `variable? [HilbertSpace ...]` remains a separate choice.

Forwarding files at every old path would preserve the flat directory clutter, so old module
import paths are intentionally replaced. Declaration namespaces and full theorem names are
preserved. Any downstream source using the old imports must apply the mapping below.

## Path mapping

Both columns are relative to `formalization/FunctionalInequalities/`. Replace `/` by `.` and
remove `.lean` to obtain the corresponding import module after `FunctionalInequalities.`.

| Previous path | Current path |
| --- | --- |
| `Basic.lean` | `Poincare/Basic.lean` |
| `Poincare.lean` | `Poincare/LinearTest.lean` |
| `PoincareTransport.lean` | `Poincare/Transport.lean` |
| `ProductGeometry.lean` | `Poincare/Product/Geometry.lean` |
| `ProductVariance.lean` | `Poincare/Product/Variance.lean` |
| `ProductAdmissible.lean` | `Poincare/Product/Admissible.lean` |
| `Tensorization.lean` | `Poincare/Product/Tensorization.lean` |
| `ProductReverse.lean` | `Poincare/Product/Reverse.lean` |
| `FiniteProductGeometry.lean` | `Poincare/FiniteProduct/Geometry.lean` |
| `FiniteTensorization.lean` | `Poincare/FiniteProduct/Tensorization.lean` |

The three `Project/` paths and the three `solutions/` paths are unchanged. In particular, the
ledger's `lean_solution` paths require no migration. The former `Poincare.lean` is named
`LinearTest.lean` because its contents concern linear tests, Rayleigh quotients, and covariance
lower bounds. The general variance lemmas retain `FunctionalInequalities.ProductVariance` as
their namespace and retain their original generality in `Poincare/Product/Variance.lean`.

## Dependency and contract preservation

An independent read-only audit compared all 17 current Lean files with a pre-move snapshot:
each file is byte-for-byte the old text after only the specified import-line substitutions.
All ten old files are absent and no current Lean source retains an old import. The entire import
graph, including Mathlib edges, is identical after applying the module-name mapping.

The root aggregate remains restricted to the proved branch. The root, Issue #2 certificate, and
Issue #6 certificate have local import closures of 9, 4, and 7 modules respectively; none reaches
the five modules containing draft placeholders. Draft compilation is still required by the
existing default `solutions.LemPoincareFiniteTensorization` root. The Lake configuration was not
changed during this reorganization.

All 22 pre-existing protected files were compared by SHA-256 and remain unchanged. These cover
the decisions, explorations, signature snapshot, ledger, Lake configuration, toolchain, and
dependency manifest. Current navigation was updated in the root and formalization READMEs,
`LEAN_DESIGN.md`, `NEXT_STEPS_CONTEXT_FOR_CODEX.md`, and `solutions/README.md`.

No semantic definition, candidate/frozen signature, ledger statement, node status, or checker
rule changed. Both existing nodes remain `proved` / `checked_by: lean`; the finite node remains
`drafted` / `checked_by: null`. The earlier source correspondence and semantic audit still apply.

## Validation

The required checks were rerun after migration:

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

- Ledger: 1 ledger, 3 nodes, 0 errors, including the proved certificates' local dependency checks.
- Python: all 24 tests passed.
- Lean: build completed successfully, 2959 jobs. Exactly 52 warnings report the existing draft
  `sorry` obligations; no other warnings occurred.
- The 14 previously audited certificate/public declarations still depend only on `propext`,
  `Classical.choice`, and `Quot.sound`; no draft axiom is introduced.
- The finite declaration entry point still prints exactly the previous 53 full candidate
  signatures, including universe, implicit, and typeclass parameters. The Euclidean application
  and empty/singleton/zero-dimensional checks remain in the compiled project module.
- The binary `Holds.prod` and `constant_prod_le` full signatures still match their frozen output.

The unchanged signature hashes are:

| Output | SHA-256, including final newline |
| --- | --- |
| 53 finite candidate declarations | `26f387cbaaf2ce631c02dd79bfebf36f5514e922dd60bf8287fc7a690ac6aed4` |
| Two frozen binary declarations | `75e576722a02a1c49588534389331ed1f493fec233ee21756e348c23f8424d0a` |

From `formalization/`, the candidate output is reproducible with:

```bash
lake env lean ../solutions/LemPoincareFiniteTensorization.lean
```

For the binary output, use the following source with `lake env lean`:

```lean
import FunctionalInequalities.Poincare.Product.Tensorization
#check @FunctionalInequalities.Poincare.Holds.prod
#check @FunctionalInequalities.Poincare.constant_prod_le
```

## Historical exploration scripts

Historical records retain the imports and paths of their recorded stage. The earlier
`2026-09-03-finite-tensorization-mathlib-api.lean` probe was rerun successfully from a temporary
copy replacing only
`import FunctionalInequalities.Tensorization` with
`import FunctionalInequalities.Poincare.Product.Tensorization`. Its archived source was not
rewritten. The same mapping applies when reproducing older scripts against the current layout.

The full candidate and ledger review package remains
`../decisions/2026-09-03-finite-tensorization-candidate.md`, and the detailed semantic review
remains `2026-09-03-finite-tensorization-semantic-review.md`. Human statement freeze and the
independent proof stage are still outstanding. No commit or push was made.
