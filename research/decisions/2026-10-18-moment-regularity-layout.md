# Regular moment producer layers (2026-10-18)

This resolves review candidate C1 by examining the actual source producers, direct consumers
and private-reference boundaries. The target is the existing regular-class weak counterpart
of Letwin arXiv:2607.24164v1 Lemma 2.2 supporting Theorems 2.5 and 1.2. Its scope is unchanged:
positive dimension, compact convex source body with nonempty interior, smooth uniformly convex
potential and the specified isotropic probability law. This layout adds no analytic premise,
C² regularity, diffeomorphism, new conclusion-bearing structure/class or paper coverage.

## Placement and dependency direction

The source-specific family remains `KLS/CEK/MomentRegularity/`; existing
`FunctionalInequalities.Analysis` declaration names are retained independently of module paths.
Potential owns the actual C¹ moment potential and R0 fields. WeakDerivative owns the actual weak
third tensor and first Monge--Ampere derivative producers. WeakHessian retains the weak inverse,
mean Hessian, evolution and bounded-testing stages together. Cutoff owns the height cutoffs and
their bounded weak testing. TraceStein keeps the complete trace-to-weak-Stein chain and its
shared private supports together, ending at the existing flat projection
`exists_regular_moment_hessian_trace_bound`.

The final projection already existed before this batch. It extracts its fields at the **same**
`u` and `L` from `exists_regular_moment_weak_stein_coupling`; this batch does not repair or replace
that theorem, choose another witness, or assume a requested conclusion. The exact `16/κ`
gradient/Hessian bound, trace constant 2 and all earlier payload fields remain as stated.
The constant-8 assembly remains in `KLS/Letwin/RegularClass.lean`. Noncompact Letwin and full
smooth Lemma 2.2 remain separate targets. Generic analytic tools keep their Analysis owners.

The old monolithic module is retired without a wrapper. Imports select actual producer layers;
there is no public namespace/name migration or duplication/exposure of private lemmas.
No split is made inside the shared-private TraceStein proof chain solely to reduce file length.

## Acceptance

The [complete migration map](../api-migration/2026-10-18-moment-regularity-map.json) records exact
source segments, declarations, clients and compiler identifiers. Acceptance checks the private
boundaries, exact authored source payloads, elaborated types and definition closures, actual
dependencies, evidence-owner updates, generated views and live navigation, then runs the full
local verifier on the frozen source snapshot. It preserves history, actual Git index/staging,
ledger and all mathematical/certificate statuses. Receipts remain under
`build/file-management/2026-10-17-other-families-optimization/batch-05-moment-regularity/`.
