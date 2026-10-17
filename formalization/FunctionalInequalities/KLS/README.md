# KLS module guide

Read [Definitions.lean](Definitions.lean) and [Statement.lean](Statement.lean) first.
[Target.lean](Target.lean) proves the KLS theorem `kls` through the BKL assembly in
[BKL/Poincare.lean](BKL/Poincare.lean); it is the final leaf, and no library module imports it. Exact proof scope and coverage belong to the
[paper register](../../../research/progress/LITERATURE.md) and
[BKL main proof chain](../../../research/progress/README.md#bkl-main-proof-chain).

## Entry points

| Owner | Reading purpose |
| --- | --- |
| [Definitions.lean](Definitions.lean) · [Statement.lean](Statement.lean) | Log-concavity and the intrinsic local-slope, covariance-scaled KLS target |
| [Isotropic.lean](Isotropic.lean) | Mean, second moments, isotropy and covariance interfaces |
| [LogConcave/](LogConcave/README.md) | Law representation, affine reductions and functional inequalities |
| [LogConcave/HeatSemigroup/](LogConcave/HeatSemigroup/) | Concrete weighted-gradient heat model and generator interfaces |
| [BKL/Reduction.lean](BKL/Reduction.lean) | Regular-law reduction and assembly conditional on the universal cumulant bounds |
| [BKL/](BKL/README.md) | Responsibility-based guide to the paper construction and its reusable prerequisites |
| [BKL/Theorem41.lean](BKL/Theorem41.lean) | Theorem 4.1 interfaces from the cutoff-energy induction |
| [BKL/Poincare.lean](BKL/Poincare.lean) | The closed producers `theorem11` (BKL Theorem 1.1) and `conjecture` |
| [BKL/Proposition71.lean](BKL/Proposition71.lean) · [BKL/Suspension/](BKL/Suspension/) | Source Proposition 7.1 and its suspension construction |
| [BKL/LocalThirdCumulant.lean](BKL/LocalThirdCumulant.lean) | BKL Lemma 4.2 counterpart retaining the Letwin quadratic bound |
| [CEK/](CEK/) | Moment-measure applications and source-law construction supports |
| [CEK/MomentRegularity/](CEK/MomentRegularity/README.md) | Actual-source weak regularity stages, cutoffs and the same-witness trace/Stein producer |
| [ConditionalFiber/](ConditionalFiber/) | Conditional laws, forms and energy comparisons |
| [Geometry/](Geometry/) · [Isoperimetry.lean](Isoperimetry.lean) | Coarea, boundary/perimeter and Cheeger interfaces |
| [Geometry/Perimeter/MetricBV/](Geometry/Perimeter/MetricBV/README.md) | Metric BV relaxation, bounded-support tests and separate finite-measure, approximation, transport and scaling interfaces |

Follow the generated BKL navigation for source theorem numbers, declarations, retained inputs
and certificates. It distinguishes conditional interfaces from the closed producers and from the separate
uncut stochastic-localization statements. `KLS.kls` is proved through `BKL.Localization.conjecture`.

## File placement

Log-concave properties belong in `LogConcave/`; BKL consumers belong in `BKL/`; target
contracts and shared KLS objects stay at this level. Generic matrix, convex, tensor and
Bakry–Émery tools retain their mathematical owners outside the application family.
Namespaces may span implementation modules. Completion alone does not trigger a move.
Use the [workflow](../../../research/workflow.md) and [naming guide](../../../research/naming.md).

## Verification and history

[Certificates](../../../solutions/README.md) are clients of the mathematics, not a replacement
for it. [Verification](../../../research/verification.md) checks actual transitive dependencies;
[HANDOFF.md](../../../HANDOFF.md) records current work and snapshot-specific acceptance.
The earlier construction rounds, WIP counts, assignments and module map are preserved in the
[2026-10-12 module-guide archive](../../../research/decisions/2026-10-12-kls-module-guide-history.md).
