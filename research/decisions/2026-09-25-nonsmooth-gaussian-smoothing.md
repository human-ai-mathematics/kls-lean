# Gaussian convolution ingredient for the nonsmooth pi passage

Date: 2026-09-25. Local continuation; no commit or push.

## Placement and proved scope

`Probability/BrunnMinkowski.lean` owns the generic measurable ENNReal
convolution consequence of finite-dimensional Prékopa–Leindler. The new
`Analysis.lintegral_mul_translate_logConcave` takes pointwise log-concavity
of both factors and proves pointwise log-concavity of their convolution,
allowing extended values. It changes no existing signature.

`KLS/LogConcave/Density/GaussianSmoothing.lean` specializes this to the
explicit unnormalized factor `exp(-s‖x‖²)`, with `s ≥ 0`, and a Borell density
representative of a probability law. It proves that the raw convolution is
measurable, equals integration of that factor against the original law, is
at most one and strictly positive at every point, and is pointwise
log-concave. Its real-valued `density` is measurable, strictly positive and
pointwise log-concave. Positivity and finiteness use the actual probability
mass, not an assumed conclusion. The `s = 0` endpoint is allowed.

The independent clients `ConvolutionLogConcavityAudit.lean` and
`GaussianSmoothingAudit.lean` reproduce full signatures. Their transitive
axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.

## Exact remaining gap

The convolution is deliberately unnormalized. The code does not yet prove
the Gaussian integral or construct a normalized probability law, show
smoothness or a convex smooth potential, show convergence of the measures,
bound the approximants' literature Poincaré constants by the original
constant plus Gaussian variance, or pass the smooth-domain mass and relative
perimeter estimates to the limit with the needed direction and extended-real
endpoints. Those are real proof obligations before
`inverseScale² ≤ π · literatureConstant` can be asserted for arbitrary
positive-dimensional log-concave laws. The unrestricted pi Buser theorem and
dimension-free KLS statement remain pending. No compatibility alias or
conclusion-bearing hypothesis was introduced.

## Evidence

- Generic source SHA-256: `657711f40cc38869c655e910ee11854d1b27b2e3dcfd70b789832936f79cc638`.
- Concrete source SHA-256: `1d7479fa7dfe4d82bbeba5cc960eff0d084850211935e1cf2d172add7341bb97`.
- Generic client SHA-256: `c1c4aeb6721e9ef23a568d412b12792a5c95119fcaf729ff97001d7037e026b9`.
- Concrete client SHA-256: `5124d2260faf250b569b4d6b0d0df63ce55b2c71f9384eaf40d2f38f97237a0a`.
- Full verifier and frozen snapshot: `build/audit/nonsmooth-gaussian-smoothing/final-snapshot.json`.
