# Public naming cleanup and library-wide review

Date: 2026-09-07. The user approved replacing verbose construction names with names expressing
mathematical roles and requested a review of the rest of the library. Existing declarations
and calls are migrated directly, without compatibility aliases or moving directories, modules,
certificate files, or Blueprint nodes. Local edits only; no commit/push or remote CI.

## Scope and choices

Scanned 498 named public definitions, structures, and theorem declarations in the Lean library
(plus 36 private declarations), and reviewed solutions, examples, Blueprint, and current guides.
Repeated construction phrases concentrate in selected energy/constants and ambient/selected,
legacy/relaxed, and general log-concave comparisons. The generic L² optimizer has the same
prefix repetition and is included under `Poincare.L2Energy`.

29 public declarations are migrated. `Energy.Canonical.energy` retains the original intrinsic
affine smooth-gradient relaxation; `Poincare.Canonical.constant` is the selected optimum,
`Poincare.Ambient.constant` the ambient-relaxation optimum, and
`Poincare.L2Energy.constant μ energy` the parameterized optimizer. Names add no Cheeger,
Dirichlet, spectral-gap, or KLS conclusion.

See [naming conventions](../naming.md) for the other findings and lasting rules. Finiteness
conditions for recovery, Gaussian half-lines and density weights, compact-support/weighted/L¹/L²
approximation distinctions, and support/interior/closed-ball measure-theoretic conditions
are meaningful and retain descriptive names; names are not uniformly shortened by character count.

## Exact map

The shared prefix `FunctionalInequalities` is omitted. Original module paths are unchanged.

| Old declaration | New declaration |
| --- | --- |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationConstant` | `Poincare.Canonical.constant` |
| `Poincare.Euclidean.IntrinsicAffineSmoothGradientRelaxationHolds` | `Poincare.Canonical.Holds` |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationHolds_iff_constant_le` | `Poincare.Canonical.holds_iff_constant_le` |
| `Poincare.Euclidean.smoothGradientRelaxationConstant` | `Poincare.Ambient.constant` |
| `Poincare.Euclidean.SmoothGradientRelaxationHolds` | `Poincare.Ambient.Holds` |
| `Poincare.Euclidean.smoothGradientRelaxationHolds_iff_constant_le` | `Poincare.Ambient.holds_iff_constant_le` |
| `Poincare.Euclidean.smoothGradientRelaxationHolds_iff_intrinsicAffine` | `Poincare.Ambient.holds_iff_canonical` |
| `Poincare.Euclidean.smoothGradientRelaxationConstant_eq_intrinsicAffine` | `Poincare.Ambient.constant_eq_canonical` |
| `Poincare.Euclidean.holds_iff_smoothGradientPreEnergy` | `Poincare.Euclidean.holds_iff_preEnergy` |
| `Poincare.Euclidean.holds_iff_smoothGradientRelaxation` | `Poincare.Euclidean.holds_iff_ambient` |
| `Poincare.Euclidean.constant_eq_smoothGradientRelaxation` | `Poincare.Euclidean.constant_eq_ambient` |
| `Poincare.Euclidean.holds_iff_intrinsicAffineSmoothGradientRelaxation` | `Poincare.Euclidean.holds_iff_canonical` |
| `Poincare.Euclidean.constant_eq_intrinsicAffineSmoothGradientRelaxation` | `Poincare.Euclidean.constant_eq_canonical` |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationConstant_eq_literatureConstant` | `Poincare.Canonical.eq_literature_of_ac` |
| `Poincare.Euclidean.constant_eq_intrinsic_and_literature_of_logConcave` | `KLS.LogConcave.legacy_eq_intrinsic_and_literature` |
| `Poincare.Euclidean.constant_eq_literatureConstant_of_logConcave` | `KLS.LogConcave.legacy_eq_literature` |
| `Poincare.Euclidean.intrinsicAffineSmoothGradientRelaxationConstant_eq_literatureConstant_of_logConcave` | `KLS.LogConcave.canonical_eq_literature` |
| `Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation` | `Energy.Canonical.energy` |
| `Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation_apply` | `Energy.Canonical.energy_apply` |
| `Energy.Euclidean.intrinsicAffineSmoothGradientRelaxation_closedQuadratic` | `Energy.Canonical.closedQuadratic` |
| `Energy.Euclidean.smoothGradientRelaxation_eq_intrinsicAffineSmoothGradientRelaxation` | `Energy.Euclidean.smoothGradientRelaxation_eq_canonical` |
| `Poincare.constantOfL2Energy` | `Poincare.L2Energy.constant` |
| `Poincare.HoldsL2Energy` | `Poincare.L2Energy.Holds` |
| `Poincare.holdsL2Energy_iff` | `Poincare.L2Energy.holds_iff` |
| `Poincare.holdsL2Energy_iff_constant_le` | `Poincare.L2Energy.holds_iff_constant_le` |
| `Poincare.l2EnergyRayleighMap` | `Poincare.L2Energy.rayleighMap` |
| `Poincare.constantOfL2Energy_anti_mono` | `Poincare.L2Energy.constant_antitone` |
| `Poincare.HoldsL2Energy.of_energy_le_mul` | `Poincare.L2Energy.Holds.of_energy_le_mul` |
| `Poincare.constantOfL2Energy_le_mul_of_energy_le_mul` | `Poincare.L2Energy.constant_le_mul_of_energy_le_mul` |

## Mathematical content and calling conventions

Three `KLS.LogConcave` comparison theorems make the law `μ` implicit rather than explicit,
inferring it from `hμ : KLS.LogConcave μ`; quantifiers, assumptions, and conclusions are
unchanged. Default-build certificates now call `hμ.canonical_eq_literature` and retain typed
applications for general `Fin n` and `Fin 0`.

Before and after renaming, the existing `StatementSnapshot` tool expands the local dependency
closures of all 29 entries. `build/naming/compare.py` checks types and definition bodies for
123 declarations, replacing only exact names (including generated subordinate names),
normalizing printed whitespace and dependency order, and separately permitting the three μ
inference-marker changes above. Everything else—universes, module locations, external
dependencies—agrees. Theorem proof bodies are outside this text snapshot; default compilation
and final kernel replay verify them.

`build/naming/RemovedNames.lean` runs `#check_failure` for all 29 old names and exits successfully.
`Unknown identifier` in its log is expected and confirms that old names do not survive as aliases
after importing the current library. Current Lean calls and axiom guards are migrated.

## Synchronization and protected files

Blueprint anchors, axiom guards, examples, and current guides use the new names. Three ledger
statements only replace referenced Lean symbols; node count, lifecycle, checked_by,
mathematical classification, and certificate entry points are unchanged. Eight infrastructure
source hashes are updated to the reviewed migration files. The route sidecar is wholly unchanged.

All 59 protected entry files—KLS Definitions, Statement, golden files, route sidecar, and
existing decisions/explorations—retain their hashes. The original staged patch is byte-identical.
See `build/naming/change-audit.json`; name maps and expanded inputs are in the same directory.

## Verification facts

HEAD: `70ca1c19c4d207a31716c2e589c0b096521a5490`.
Entry source snapshot:
`91762f2379b2b510176237d0b9c3d0192e55320fe0582cd0add724cea613927a`.
Precheck snapshot before writing this record:
`2b4cc8a837e7bc23cdd967daf83b8f5e82aab666dbccaac87597b73670b801d0`.

Passed at this stage: ledger, Blueprint, and atlas structure checks; 97 Python tests; default
`lake build` (3268 jobs); 123 expanded declaration comparisons; 29 removed-name checks;
`git diff --check`. The atlas retains 74 mathematical nodes, 87 navigation labels,
10 certificates, and 4 active routes, without cycles. Logs and results:
`build/naming/build.log`, `tests.log`, `semantic-audit.json`, and `removed-names.log`.

The first migration build found old fully qualified names in axiom messages and an unqualified
cross-namespace reference. Both were fixed without deleting guards or adding compatibility
aliases; the subsequent default build passed.

After this record, run `python3 research/verify.py` on the final snapshot including it, checking
the default build, all tests, KLS golden files, axiom audits, and kernel replay of all local
modules. Generated `build/verification/<UTC timestamp>/report.json` records actual final
outcomes and source SHA256, followed by atlas export. This record does not claim a final pass
in advance or write the final hash back into source, invalidating the receipt.

Local replay trusts pinned third-party compiled imports; no external independent check,
isolated source rebuild, or verification of remote CI was performed.
