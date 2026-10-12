# KLS module guide

Read [Definitions.lean](Definitions.lean) and [Statement.lean](Statement.lean) first.
[Target.lean](Target.lean) contains the intentional open KLS theorem; successful compilation
of an import root does not prove it. Exact proof scope and coverage belong to the
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
| [BKL/Proposition71.lean](BKL/Proposition71.lean) · [BKL/Suspension/](BKL/Suspension/) | Source Proposition 7.1 and its suspension construction |
| [BKL/LocalThirdCumulant.lean](BKL/LocalThirdCumulant.lean) | BKL Lemma 4.2 counterpart retaining the Letwin quadratic bound |
| [CEK/](CEK/) | Moment-measure applications and source-law construction supports |
| [ConditionalFiber/](ConditionalFiber/) | Conditional laws, forms and energy comparisons |
| [Geometry/](Geometry/) · [Isoperimetry.lean](Isoperimetry.lean) | Coarea, boundary/perimeter and Cheeger interfaces |

Follow the generated BKL navigation for source theorem numbers, declarations, retained inputs
and certificates. It distinguishes formalized conditional statements from undischarged
source-law and stochastic-localization obligations. `KLS.kls` remains open.

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
