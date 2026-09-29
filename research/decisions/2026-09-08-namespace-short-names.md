# Declaration short names do not repeat the namespace

After the previous public API migration, the user explicitly requested that declaration short
names omit context already expressed by the namespace. Continue editing the verified local
tree, with baseline `271f002b9a9a9d762d39dc268b643e7627818e65d99ca6a41dedf5d6b76810b6`,
corresponding to `build/verification/20260908T115953.150706Z/report.json`.
Branch remains `main`, HEAD `19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`.
No source was restored from Git HEAD and no prior uncommitted work overwritten.

## Naming rule and complete scope

Migrate 32 public declarations. The [complete map](../api-migration/2026-09-08-short-name-map.json)
records entry names to new names. The previous map and audit remain historical records;
apply both maps in sequence. Namespaces and module paths are unchanged, without old-name
compatibility aliases or wrappers.

| Namespace | Previous short name | New short name |
| --- | --- | --- |
| `Covariance` | `covarianceBilin_intrinsic` | `bilin_intrinsic` |
| `Energy.WeightedGradient.IsTest` | `memLp_weightedGradient` | `memLp_apply` |
| Same as above | `weightedGradient_add_ae`, `weightedGradient_smul_ae` | `apply_add_ae`, `apply_smul_ae` |
| `Energy.LocalSlope` | `slope` and four `slope_*` lemmas | `apply` and `apply_*` |
| `Energy.Euclidean.LipschitzApproximation` | Four `exists_*_approximation` declarations | Corresponding `exists_*` |
| `KLS.ConditionalFiber` | `OrthogonalFiniteNonzeroVarianceFiber` | `Nondegenerate` |
| Same as above | `fiberEnergy` and three related lemmas | `energyAt` and corresponding lemmas |
| Same as above | `ae_fiber_congr` | `ae_restrict_congr` |
| `Poincare.SmoothTest` | `linearTest` and seven related lemmas | `linear` and corresponding lemmas |
| `ProductVariance` | `integrable_variance_left/right` | `integrable_left/right` |
| Same as above | `variance_decomposition`, `variance_integral_le`, `variance_le` | `decomposition`, `integral_le`, `le` |

`Nondegenerate` still requires an orthogonal base point, finite second moment, and nonzero
variance. Documentation states all conditions instead of enumerating fields in the name.
`energyAt κ b f` computes at one base point; `energy μ ρ f` still integrates over the base law.
They are not merged. `LocalSlope.apply` remains the original pointwise local slope.

`f.energy`, `f.toL2`, `hf.memLp`, and `hμ.theorem_name` remain usable. New typed applications
check `hf.memLp_apply` and `LocalSlope.apply_const`. Ordinary, weighted, and covariance
gradients, ambient/intrinsic carriers, and the object on the other side of a constant comparison
remain distinct. Helpers about ordinary `gradient` under `WeightedGradient` retain `gradient`.
The two equivalences in `ContinuousLinearEquiv.pullbackEquiv` act on the underlying space and
L² space respectively; they are not duplicate prefixes for one object. L1/L2, weighted, ae,
compact-support, and boundary conditions are not mechanically removed.

## Baseline, semantics, and evidence

At entry, compare every current source file against the previous passing receipt, then save
`build/api-shortnames/baseline/`, source hashes, and original `.ilean` declaration/reference
positions. Raw elaborated types and definition closures reuse the verified source's
`build/api-refactor/final-expressions.json` and losslessly compressed records in that directory.
Edits use resolved references and UTF-16 source positions, not global replacement of overloaded
names or ordinary English words.

No section, parameter order, explicitness, instance premise, universe, or interface generality
is changed. Source comparison confirms equality of 881 public signatures, 189 definition/structure
bodies, and 885 named declaration bodies including proofs after name mapping and format
normalization, without omissions or unexplained differences. Raw Lean Expr types and definition
closures of 1085 local declarations agree after exact name mapping and binder alpha normalization.
Modules, universes, dependencies, parameter order, and explicitness are unchanged. Anonymous
instance parameters at the 32 renamed entries have different compiler hygiene hashes;
itemwise checks confirm only those hashes differ, with identical modules/local hygiene indices
and unchanged explicit parameter names. Raw comparisons and metadata differences are retained
in the [audit](../api-migration/2026-09-08-short-name-review.json). Type/definition-closure
comparison does not replace kernel verification of theorem proofs.

The existing statement golden still covers 26 local declarations and 221 external dependency
leaves, agreeing completely after this name map. No module ownership or generated-proof
number changes and no mathematical formula updates. Toolchain, dependency locks, and external
trust boundary are unchanged. This record authorizes writing the successfully compared
candidate as the new golden; rewriting old records cannot bypass review.

Check old infrastructure hashes first, then refresh 29 affected entries across 15 source files
using source comparison. Paths, infrastructure assessments, ledger lifecycle, certificate
identity, and mathematical certification status are unchanged. See the
[source-hash review](../api-migration/2026-09-08-short-name-evidence.json).
All 86 previous decisions, explorations, and prior migration-evidence files remain byte-identical.

## Acceptance boundary

Pre-acceptance default build passes (3359 jobs). All 32 old names pass `#check_failure`, and
all 32 new names resolve. Existing guards, certificates, general finite-dimensional,
zero-dimensional, degenerate-carrier, and transport applications still build. No new `sorry`,
`axiom`, compatibility wrapper, or disabled linter.

Blueprint PDF, Web, and checkdecls pass. Structure checks retain 87 labels, 4 active routes,
and 0 errors. All 37 PDF pages were inspected as thumbnails, with enlarged review of local-slope
and conditional-fiber pages. Current guides, downstream references, axiom messages, Blueprint
anchors, and statement roots use the new names.

After finalizing this record and audit, run root `python3 research/verify.py`, retaining all
tests, statement snapshots, declaration/transitive-axiom audits, and kernel replay of all
local modules. Final results are in `build/verification/<UTC timestamp>/report.json`;
`build/verification/latest.json` stores the latest attempt. The final receipt must correspond
to actual source including this record. `git diff --check` checks formatting only.
Delivery is the local working tree, without commit, push, or publication.
