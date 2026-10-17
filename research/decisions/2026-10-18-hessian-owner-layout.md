# Generic Hessian ownership (2026-10-18)

This layout batch supports the existing weak regular-class Letwin arXiv:2607.24164v1 chain.
It moves declarations without changing their names, source proof payloads, assumptions,
constants, normalization, dimensions or certificate status.

## Placement and dependency direction

- Move the existing `Probability.Stein.KernelMatrix` abbreviation unchanged to the existing
  `Analysis/Operator/Coordinates.lean` owner. It remains the same real coordinate-matrix type;
  no duplicate alias or new abstraction is added. The Stein kernel interface consumes it.
- Extend `Analysis/BakryEmery/HessianOperator.lean` with the existing coordinate Hessian and
  C2 coordinate identities, including the original `hessianMatrix` definition and signature.
- Put the C1 pointwise identification, weak third-derivative symmetry and Hessian-entry bounds
  in `Analysis/BakryEmery/WeakHessian.lean`. Keep their shared private derivative helpers together.
- Retain actual Hessian–Stein kernels, pushforward/inverse-map facts and Stein-action adapters
  in `Probability/Stein/HessianKernel.lean`.

Convex, Piola and generic weak-Hessian clients depend on the generic owners, with no Stein
kernel or weighted Stein-extension dependency. The Stein model depends on those generic facts.
The existing qualified public names remain unchanged; namespace migration is a separate class
of API change and is not part of this batch. No old-path wrapper or public alias is introduced.

The coordinate Hessian is not replaced by another derivative definition: the C2 bridge and the
C1 bridge at an actual differentiability point of the gradient retain their distinct hypotheses,
including the zero-dimensional case. Matrix index order is unchanged.

## Provenance and independent acceptance

The source proof provenance remains the accepted Hessian–Stein and weak N11e/N10/N11b supporting
work, including the original inverse-map and measurable-Hessian arguments. The full original
sources and diagnostics remain in the per-batch baseline; historical records are not rewritten.

The [complete owner map](../api-migration/2026-10-18-hessian-owner-map.json) records source spans,
all declaration owners and compiler identifiers. Acceptance requires exact source-span checks,
elaborated statement/definition-closure comparison, updated real clients, actual dependency
closures, current metadata/navigation, a full local build and verifier, and real-index/history
preservation. Receipts are retained in
`build/file-management/2026-10-17-other-families-optimization/batch-02-hessian/`.
No mathematical status is advanced by the layout.
