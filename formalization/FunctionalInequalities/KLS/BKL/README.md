# BKL module guide

This family formalizes the selected cutoff-localization proof of Bizeul–Klartag–Lehec,
arXiv:2610.05474v1. Exact theorem scope and certificates belong to the
[paper register](../../../../research/progress/LITERATURE.md); the
[proof path](../../../../research/progress/PROOF-PATH.md) explains its relationship to KLS.

## Main entries

| Entry | Responsibility |
| --- | --- |
| [Theorem41.lean](Theorem41.lean) | Source Theorem 4.1 interfaces and the shared cutoff/cumulant producers, retaining the explicit compact Letwin hypothesis |
| [CumulantBound.lean](CumulantBound.lean) | Closed (95) cutoff and Theorem 4.1 producers from the proved compact Letwin input, consumed by the certificates and `Poincare` |
| [Poincare.lean](Poincare.lean) | Closed Theorem 1.1 and KLS producers, from `CumulantBound` and the reduction |
| [Reduction.lean](Reduction.lean) | Regular-law reduction from universal cumulant bounds to Poincaré |
| [Proposition71.lean](Proposition71.lean) · [Suspension/](Suspension/) | Source Proposition 7.1 and suspension construction |
| [PoissonIterate/](PoissonIterate/) | Iterates, domains, symmetry, Taylor recursion and the cumulant criterion |

## Construction and dependency boundaries

| Family | Responsibility and reading order |
| --- | --- |
| [CumulantEnergy/](CumulantEnergy/) | `Basic` defines the energies; `Conjugation` identifies coordinate forms; `Bound` gives isotropic estimates |
| [Posterior/](Posterior/) | `Covariance` supplies algebra and radius bounds; `Regularity`, `Standardization`, `Noise`, `Moments` and `Response` contain their separate clients |
| [Localization/Process/](Localization/Process/) | `Basic` constructs the cutoff process; `Integral` supplies bounded-functional and time/product integration |
| [Localization/Energy/](Localization/Energy/) | Compact-posterior `Bound` and `Regularity`, pointwise `Generator` estimates and process `Integral` estimate |
| [Localization/CutoffEnergy/](Localization/CutoffEnergy/) | `Basic` defines the weighted claim; `Base`, `Boundary`, `ToCumulant`, `Step` and `Induction` own the separate proof responsibilities |
| [Localization/Lyapunov/](Localization/Lyapunov/) | `Basic` keeps the construction and exact calculus with shared private operator helpers; `Bound` proves the quantitative estimate; `Moment` applies it to the process |

The general [cumulant moment estimate](../../Analysis/BakryEmery/Cumulant/MomentBound.lean)
and [diffusion-generator product rule](../../Probability/Diffusion/Generator.lean) have no BKL imports.
Process integration is below cutoff-energy induction. Theorem 4.1 does not import the final
Poincaré reduction. These boundaries support narrower imports without changing any statement.

Namespaces span modules: existing declarations retain their public names and argument interfaces.
The uncut process and literal source identities remain separate from the accepted cutoff route.
The [layout decision](../../../../research/decisions/2026-10-17-bkl-module-reorganization.md)
and [complete migration map](../../../../research/api-migration/2026-10-17-bkl-module-map.json)
record ownership, import changes and preservation checks. The generated
[filename directory](../../../MODULES.md) lists every current module.
