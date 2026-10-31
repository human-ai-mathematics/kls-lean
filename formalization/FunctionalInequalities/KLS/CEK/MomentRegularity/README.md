# Regular-class moment producers

These are the actual-source weak regularity producers for the existing compact regular-class
law. They retain positive dimension, the compact convex source body and its interior, smooth
uniform convexity, density identification and isotropy hypotheses exactly. Qualified
`FunctionalInequalities.Analysis` names remain unchanged.

| Owner | Producer stage |
| --- | --- |
| [Potential.lean](Potential.lean) | Continuous-target C¹ moment potential, strict convexity, gradient homeomorphism, Alexandrov/viscosity equation; strong-class Lipschitz-gradient and a.e. Hessian/log-det data |
| [GradientHolder.lean](GradientHolder.lean) | Literal continuous convex-body source: same-witness C¹,α gradient and compact-uniform section power radii |
| [WeakDerivative.lean](WeakDerivative.lean) | Weak third tensor and first weak Monge--Ampere derivatives at the same source witness |
| [WeakHessian.lean](WeakHessian.lean) | Weak inverse, mean Hessian, weak evolution and bounded Hessian testing |
| [Cutoff.lean](Cutoff.lean) | C¹ height cutoffs, inverse-Hessian generator control and bounded weak cutoff testing |
| [TraceStein.lean](TraceStein.lean) | Fixed-witness trace/Stein estimates and the final same-witness Hessian trace frontend |
| [HessianHolder.lean](HessianHolder.lean) | Given-data weak Harnack, frame oscillation decay, Hölder Hessian, C² and the everywhere log-determinant equation at the same witness |
| [Inverse.lean](Inverse.lean) | The same witness with a gradient homeomorphism onto int K and a C¹ inverse |
| [DifferenceQuotient.lean](DifferenceQuotient.lean) | The same witness with uniform-in-step log-determinant equations for the Hessians of its scalar-step finite differences (averaged-inverse coefficients; no regularity gain) |
| [Ellipticity.lean](Ellipticity.lean) | Uniformly elliptic same-witness quotient equations |
| [BootstrapThree.lean](BootstrapThree.lean) | C³ and locally Hölder third derivative, n ≥ 2 |
| [Smooth.lean](Smooth.lean) | Given-potential and source C∞, with a smooth gradient inverse, every n > 0 |
| [GivenGradient.lean](GivenGradient.lean) | C∞ of a given moment potential from any Lipschitz gradient bound, `W` convex on int K only; strong class with `W − (κ/2)‖·‖²` convex on int K only |
| [SmoothTrace.lean](SmoothTrace.lean) | C∞ at the actual sharp-trace witness, every symmetric B and exact constant 2 |

The exact `16/κ` bound and weak trace constant 2 are retained. The final flat interface
`exists_regular_moment_hessian_trace_bound` uses the same cutoff-source witness underlying
the weak Stein coupling, applying fixed-witness trace estimates without choosing a replacement potential. A cutoff producer alone does not
establish the later trace/Stein conclusions. `HessianHolder.lean` proves C² with a locally Hölder
Hessian and the everywhere positive definite log-determinant equation at the same `u`; `Inverse.lean` adds a homeomorphism
`∇u : ℝⁿ ≃ₜ int K` with a C¹ inverse. `Smooth.lean` retains every field of that producer and
adds C∞, locally Hölder derivatives of every finite order and a smooth inverse on int K,
for every n > 0. `SmoothTrace.lean` starts from the sharp weak trace witness, applies the
given-potential Hölder and all-order bridges to that very u, and retains the estimate
∫ tr(B Hess u B Hess u) dν ≤ 2 tr(B²), for all symmetric B. The corresponding smooth Stein
producer in `Letwin/SteinKernel.lean` has ∫|τ|²_HS dμ ≤ 2n, mean Id and exact coupling.

For the literal bounded open convex K, `exists_moment_potential_of_bounded_open_convex`
needs only continuity of W on closure K: it produces a normalized Lipschitz C¹ strictly convex u,
a gradient homeomorphism onto K, positive continuous Monge–Ampère right side and both viscosity
test inequalities. Its a.e. second-order expansion matrix is not asserted to equal the total
Hessian without differentiability of the gradient. `GradientHolder.lean` now retains these
fields at that same u and adds C^{1,α} on every compact set, together with uniform section
power radii c h^{1/(1+α)} for all h in (0,1]. The exponent and coefficients precede all
centres and scales. W^{2,p}, interior second-order regularity and smoothness of this same
variational witness are not proved: no uniqueness statement identifies it with another moment
potential. A smooth moment potential for the literal source class is produced separately, as a
limit of strong-class potentials, by [GivenGradient.lean](GivenGradient.lean) and
[Letwin/MomentMap.lean](../../Letwin/MomentMap.lean). The constant-8 assembly belongs to
[Letwin/RegularClass.lean](../../Letwin/RegularClass.lean).

See the [proof path](../../../../../research/progress/PROOF-PATH.md) and
[paper register](../../../../../research/progress/LITERATURE.md) for precise scope and evidence.
