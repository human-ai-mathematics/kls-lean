# KLS module guide

Read [compact-set log-concavity](../Probability/LogConcave.lean) and [Statement.lean](Statement.lean) first.
[Target.lean](Target.lean) proves the KLS theorem `kls` through the BKL assembly in
[BKL/Poincare.lean](BKL/Poincare.lean); it is the final leaf, and no library module imports it. Exact proof scope and coverage belong to the
[paper register](../../../research/progress/LITERATURE.md) and
[BKL main proof chain](../../../research/progress/README.md#bkl-main-proof-chain).

## Entry points

| Owner | Reading purpose |
| --- | --- |
| [compact-set log-concavity](../Probability/LogConcave.lean) · [Statement.lean](Statement.lean) | Log-concavity and the intrinsic local-slope, covariance-scaled KLS target |
| [Isotropic.lean](Isotropic.lean) | Mean, second moments, isotropy and covariance interfaces |
| [LogConcave/](LogConcave/README.md) | Law representation, affine reductions and functional inequalities |
| [LogConcave/HeatSemigroup/](LogConcave/HeatSemigroup/) | Concrete weighted-gradient heat model and generator interfaces |
| [BKL/Reduction.lean](BKL/Reduction.lean) | Regular-law reduction and assembly conditional on the universal cumulant bounds |
| [BKL/](BKL/README.md) | Responsibility-based guide to the paper construction and its reusable prerequisites |
| [BKL/Cumulant/Induction.lean](BKL/Cumulant/Induction.lean) | Theorem 4.1 interfaces from the cutoff-energy induction |
| [BKL/Poincare.lean](BKL/Poincare.lean) | The closed producers `exists_isotropicBound` (BKL Theorem 1.1) and `conjecture` |
| [BKL/TaylorBound.lean](BKL/TaylorBound.lean) · [BKL/Suspension/](BKL/Suspension/) | Source Proposition 7.1 and its suspension construction |
| [BKL/LocalThirdCumulant.lean](BKL/LocalThirdCumulant.lean) | BKL Lemma 4.2 counterpart retaining the Letwin quadratic bound |
| [CEK/](CEK/) | Moment-measure applications and source-law construction supports |
| [CEK/MomentRegularity/](CEK/MomentRegularity/README.md) | Actual-source weak regularity stages, cutoffs and the same-witness trace/Stein producer |
| [ConditionalFiber/](ConditionalFiber/) | Conditional laws, forms and energy comparisons |
| [Geometry/](Geometry/) · [Isoperimetry.lean](Isoperimetry.lean) | Boundary/perimeter and Cheeger applications |
| [Analysis/Coarea/](../Analysis/Coarea/README.md) · [Analysis/MetricBV/](../Analysis/MetricBV/README.md) · [Analysis/SmoothDomain/](../Analysis/SmoothDomain/) | General coarea, metric BV and smooth-domain (Gauss–Green) foundations used by the geometric applications |

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
