# Stein identities and metric BV layout (2026-10-18)

This is an owner/import migration supporting the existing Letwin arXiv:2607.24164v1
Definition 2.6 / Appendix A.7 and the metric-perimeter KLS interfaces. All authored
declarations, proof payloads, hypotheses, constants, dimensions, namespaces and public names
are retained. No paper, certificate or proof status is changed.

## Stein boundaries

`Probability/Stein/Kernel.lean` keeps the kernel object, action, Hilbert--Schmidt norm and
compact smooth-test identities. `IdentityExtension.lean` owns the locally Lipschitz L²
extension and bound, retaining absolute continuity, finite second moment, a.e. symmetry and
the kernel's L² norm. It imports the weighted approximation machinery separately.
`SourceDualBound.lean` owns the compact-test estimate from a latent source identity and an
L² field. The source identity is an input; this estimate does not construct a Stein kernel.
The existing energy `DualBound.lean` remains a distinct consumer of the extended identity.

## Metric BV boundaries and exact support scope

The actual `Test.boundedSupport` field requires **bounded function support**. On an arbitrary
metric space this is not a compact-support assertion and requires no properness assumption.
The earlier read-only review's compact-support shorthand is corrected here; that historical
report is preserved unchanged. The actual Lean definition and hypotheses are unchanged.

The existing `KLS/Geometry/Perimeter/MetricBV/` family now separates Basic (test/relaxation,
recovery, lower semicontinuity and cost bounds), Finite (finite carriers, arbitrary measures),
Complement (finite-measure symmetry), Approximation (global-L¹ Lipschitz reductions),
Transport (subset restriction and closed-support laws), Scaling (measure scaling and
normalization), and Counterexample (real Lebesgue infinite-volume obstruction). The generic
infinite-mass obstruction remains in Basic; the concrete counterexample is a separate leaf.
Finite carriers and finite measures are different hypotheses. Empty/subsingleton cases,
target finite mass, zero/nonzero scaling and global rather than local L¹ convergence remain
as originally stated. Shared private helpers remain with their consumers.

Cross-top-level relocation (review candidate C2) is deferred: current direct library consumers
are KLS perimeter modules and no independent reuse justifies moving the entire family.
The old MetricBV module is retired without a wrapper. No namespace/name migration occurs.

## Validation and consumers

The [complete migration map](../api-migration/2026-10-18-stein-metricbv-map.json) records
source ranges, owners, direct consumers and compiler identifiers. Independent acceptance
requires exact authored source comparisons, elaborated types and definition closures,
actual dependency checks, updated clients/navigation/evidence, private-index generated views,
full local verification and unchanged history, ledger, statuses and real Git index.
The receipts live under
`build/file-management/2026-10-17-other-families-optimization/batch-04-stein-metricbv/`.
