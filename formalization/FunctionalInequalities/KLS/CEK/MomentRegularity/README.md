# Regular-class moment producers

These are the actual-source weak regularity producers for the existing compact regular-class
law. They retain positive dimension, the compact convex source body and its interior, smooth
uniform convexity, density identification and isotropy hypotheses exactly. Qualified
`FunctionalInequalities.Analysis` names remain unchanged.

| Owner | Producer stage |
| --- | --- |
| [Potential.lean](Potential.lean) | Convex Lipschitz C¹ moment potential, normalization, gradient pushforward and a.e. Hessian/log-det data |
| [WeakDerivative.lean](WeakDerivative.lean) | Weak third tensor and first weak Monge--Ampere derivatives at the same source witness |
| [WeakHessian.lean](WeakHessian.lean) | Weak inverse, mean Hessian, weak evolution and bounded Hessian testing |
| [Cutoff.lean](Cutoff.lean) | C¹ height cutoffs, inverse-Hessian generator control and bounded weak cutoff testing |
| [TraceStein.lean](TraceStein.lean) | Shared-private trace/Stein chain and the final same-witness Hessian trace projection |
| [HessianHolder.lean](HessianHolder.lean) | Given-data weak Harnack, frame oscillation decay, Hölder Hessian, C² and the everywhere log-determinant equation at the same witness |
| [Inverse.lean](Inverse.lean) | The same witness with a gradient homeomorphism onto int K and a C¹ inverse |
| [DifferenceQuotient.lean](DifferenceQuotient.lean) | The same witness with uniform-in-step log-determinant equations for the Hessians of its scalar-step finite differences (averaged-inverse coefficients; no regularity gain) |

The exact `16/κ` bound and weak trace constant 2 are retained. The final flat interface
`exists_regular_moment_hessian_trace_bound` projects fields at the same `u` and `L` produced by
the weak Stein coupling; it chooses no replacement witness. A cutoff producer alone does not
establish the later trace/Stein conclusions. `HessianHolder.lean` proves C² with a locally Hölder
Hessian and the everywhere positive definite log-determinant equation at the same `u`; `Inverse.lean` adds a homeomorphism
`∇u : ℝⁿ ≃ₜ int K` with a C¹ inverse; no `C^∞` smoothness, smooth gradient diffeomorphism or unrestricted-source Stein
construction is asserted. The constant-8 assembly belongs to
[Letwin/RegularClass.lean](../../Letwin/RegularClass.lean).

See the [proof path](../../../../../research/progress/PROOF-PATH.md) and
[paper register](../../../../../research/progress/LITERATURE.md) for precise scope and evidence.
