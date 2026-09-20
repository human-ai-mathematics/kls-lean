# Semigroup and Bakry–Emery module organization

2026-09-20. Authorized file-responsibility cleanup followed by a separate short-name migration
of the nine S0a public declarations. This round proves no new mathematical result and makes no
commit or push. Earlier uncommitted work is the baseline, not discarded or replaced by HEAD.

## Layout

Paths below are relative to `formalization/FunctionalInequalities/`.

| Before | After | Responsibility |
| --- | --- | --- |
| `Analysis/BakryEmery/Basic.lean` and generic tools in `IntegrationByParts.lean` / `Gamma.lean` | `Analysis/BakryEmery/Calculus.lean` | Hessian symmetry, directional derivatives, gradients and standard-basis trace/product identities |
| Weighted Laplacian definition, regularity and Lp facts in `IntegrationByParts.lean` | `Analysis/BakryEmery/Laplacian.lean` | The classical diffusion expression and its continuity, support and integrability |
| Remaining `IntegrationByParts.lean` | Same path | Haar integration by parts and the tilted-weight identity |
| Remaining `Gamma.lean` | Same path | Gamma, Gamma_2 and the product identity |
| Counterexample in `Analysis/Semigroup/Yosida/Family.lean` | `Analysis/Semigroup/Exponential/Counterexample.lean` | Nonnegativity and commutation alone do not imply convergence |
| Actual Yosida facts in `Yosida/Family.lean` | `Analysis/Semigroup/Yosida/Laws.lean` | Nonnegativity, symmetry, commutation and convergence on the generator domain |
| `KLS/LogConcave/CanonicalEnergy.lean` | `KLS/LogConcave/HeatSemigroup/Energy.lean` | Identification of the closed unit-weight form with canonical energy |

`Gamma` now imports `Laplacian`, which imports `Calculus`; it does not import integration by parts.
`Bochner` imports `Gamma`. `IntegrationByParts` separately imports `Laplacian`.
The Yosida construction imports its laws, not the counterexample. The aggregate library and the
counterexample audit import that independent module explicitly. No old-path compatibility modules
are retained. `IntegrationByParts` remains an unabbreviated mathematical term; `AdjointComp` and
`AdjointClosure` are unchanged because their parent directory does not encode the adjoint object.

The complete one-to-many module map and 60 declaration/module moves are in
[`2026-09-20-semigroup-layout-map.json`](../api-migration/2026-09-20-semigroup-layout-map.json).
Historical decisions, explorations and previous migration records retain their original paths.

## Public names

The file-only moves preserve namespaces and names. Separately, the nine S0a declarations move to
object-specific namespaces with the following short names (omit `FunctionalInequalities`).

| Namespace | New names |
| --- | --- |
| `Analysis.Semigroup.Generated` | `mem_domain_of_generator_limit`, `generator_limit_apply`, `preserves_domain`, `generator_comm`, `right_derivative` |
| `KLS.LogConcave.HeatSemigroup` | `preserves_domain`, `generator_comm`, `mem_closedWeightedOperator_domain`, `right_derivative` |

The declaration map records every full old and new name. No legacy aliases are introduced.
The original semigroup construction API and the older heat-semigroup APIs keep their names.
Clients of these nine declarations now use the dedicated namespaces. In particular the heat-domain
client uses `HeatSemigroup.preserves_domain m B hν hi f ht`; replacing the former `hν.` dot call
changes neither the declaration's parameter order nor its implicit arguments.

`preserves_domain` means the generator domain `D(T†T)` throughout this interface. `right_derivative`
still states the exact epsilon–delta right-limit proposition, not full real-line differentiability.
The positive commutator sign, arbitrary weight B, nonnegative time including zero, and distinction
between the closed weighted gradient and a classical representative all remain unchanged.

## Semantic review

Before edits, 700 current source/document files were copied to `build/layout-s0a/before/`, with
hashes and the staged diff saved alongside. From 106 public declarations in the affected families,
raw elaborated types and definition closures were exported before and after the migration.
All 206 closure declarations compare equally after the explicit nine-name map, whitespace
normalization and alpha normalization of binder labels. De Bruijn indices, binder information,
parameter types, universe levels, constant identities and definition bodies are retained in that
comparison. All 398 external dependency leaves are identical. Theorem proof bodies are not
compared by that expression audit; the strict compiler and final kernel replay validate them.
The comparison and original expression dumps are saved in `build/layout-s0a/`.

No parameter, assumption, dimensional scope, definition or mathematical statement is changed.
The complete Cheeger–Buser comparison and dimension-free KLS remain unproved; BE remains partial.
The planned next form-domain work belongs in `Generated/Form.lean` and `HeatSemigroup/Form.lean`;
arbitrary-input positive-time smoothing would belong in `Smoothing.lean` under those same families.
These are reserved responsibilities only: no empty modules or placeholder declarations are created.

## Validation

Default `lake build` passes (3554 jobs). All changed proof modules and affected audit clients are
checked with warnings as errors, with explicit old-name failures and new-name resolution checks.
The full validation includes `git diff --check`, ledger/Blueprint/Atlas checks, Python tests and
`research/verify.py`, including statement golden checks and replay of every current local module.
The existing intentional target warning in `KLS/Target.lean` is not a new warning or proof claim.
Blueprint theorem anchors are unchanged by these nine unregistered infrastructure renames; no
manuscript source is edited. Current evidence hashes and generated progress views are refreshed
using a temporary Git index and object directory, without staging the user's work.
Final results and the coherent snapshot receipt are recorded in `build/layout-s0a/final-snapshot.json`.
