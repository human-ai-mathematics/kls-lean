# Stein kernel interfaces

| Owner | Scope |
| --- | --- |
| [Kernel.lean](Kernel.lean) | Kernel definition, matrix action and norm, compact smooth-test identities and action algebra |
| [IdentityExtension.lean](IdentityExtension.lean) | Extension to locally Lipschitz L² tests, retaining absolute continuity, finite second moment, symmetry and kernel L² assumptions |
| [SourceDualBound.lean](SourceDualBound.lean) | Compact-test estimate conditional on a latent source identity and an L² field; no kernel producer |
| [DualBound.lean](DualBound.lean) | Energy dual estimates using an actual Stein kernel and the extended identity |
| [HessianKernel.lean](HessianKernel.lean) | Hessian/Stein identification, pushforward and kernel-specific properties |
| [QuadraticAction.lean](QuadraticAction.lean) | Quadratic matrix-action bounds |

Letwin Definition 2.6 and Appendix A.7 are the source targets. The actual regular-class
moment-map and weak Stein producer belongs to the [CEK moment family](../../KLS/CEK/MomentRegularity/README.md); these generic
interfaces assert no unrestricted-source construction. Matrix coordinate and Hessian tools
belong to Analysis. See the [layout decision](../../../../research/decisions/2026-10-18-stein-metricbv-layout.md)
and [paper register](../../../../research/progress/LITERATURE.md) for scope and evidence.
