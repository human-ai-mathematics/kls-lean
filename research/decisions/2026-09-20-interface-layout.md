# Concrete specializations and the closed-gradient interface

Date: 2026-09-20. Scope: LD-006, LD-007 and LD-009 in the
[technical-debt register](../technical-debt/README.md).

## Placement plan

- Keep the generic gradient-form validity and optimal-constant comparison in
  `Poincare/LocalSlope/Gradient`. Extend the existing `KLS/LogConcave/Poincare` frontend with
  its log-concave specialization. Its historical public Poincare namespace remains unchanged.
- Keep Cheeger definitions and absolutely-continuous comparisons in `Energy/Cheeger/Basic`.
  Put the concrete log-concave wrapper in `KLS/LogConcave/Cheeger`, importing the generic result
  and the intrinsic absolute-continuity theorem. Update the actual certificate client.
- Make `KLS/LogConcave/WeightedGradient` a three-module family: Basic owns the closable operator
  and core theorems, Closure owns the closed operator and its closedness/dense-domain interface,
  and Energy identifies its unit-weight norm-square form with the canonical/Cheeger energy.
  HeatSemigroup/Basic consumes Closure. Energy does not import heat-semigroup generation.

These are distinct responsibilities with actual consumers. There is no new empty future module,
no one-file directory, and no `WeightedGradient.lean` alongside `WeightedGradient/`.
The [complete map](../api-migration/2026-09-20-interface-layout-map.json) describes all splits,
moves and public source-declaration locations. Namespaces and public names are preserved; no
forwarding files or compatibility aliases remain. LD-008 is a separate public API migration.

## Mathematical boundaries

All existing assumptions, parameters, admissible classes, normalizations and statements are
preserved. In particular, closure supports arbitrary bounded linear `B`; the energy identity
keeps unit weight; the concrete Poincare statement constructs its Haar reference internally;
ambient singular and zero-dimensional laws keep their original scope. No proof completion,
certificate registration, domain identification or finite KLS bound is added by rearranging files.

## Validation

The dirty baseline, raw before/after expressions, source copies, original staging and logs are
saved in `build/interface-layout/`. Compare types and definition closures after ignoring only
bound-variable labels and compiler-generated anonymous-instance names. Moving closure into a
separate module also changes Lean’s proof-auxiliary sharing: identify generated theorem auxiliaries
only when their full normalized types and universe levels agree, recursively, using proof
irrelevance. Do not identify or rename any non-proof constant. Check explicit parameter
names, order and binder visibility independently. Compile affected modules and real certificate/
audit clients strictly, run a complete build and the standard verifier, and check the dependency
graph and live documentation. Refresh evidence hashes only after checking their old values against
the saved baseline. Regenerate progress with an isolated index/object store and retain historical
records. The [batch checks](../technical-debt/2026-09-20-interface-checks.json) record the results;
the standard verifier emits its own snapshot-bound receipt. No commit, push or remote CI is claimed.
