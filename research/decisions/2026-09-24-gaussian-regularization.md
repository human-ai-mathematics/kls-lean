# Smooth Gaussian profile regularization

## Placement and scope

Extend `Probability/Line/GaussianProfile.lean` in its existing namespace. The new
results concern the same one-dimensional probability object and its scalar calculus;
no application assumptions or heat imports are added to this module. The compact
cutoff uses Mathlib's smooth bump functions. Existing public signatures are unchanged.

## Proved inputs

- The Gaussian CDF is smooth globally, and its quantile and profile are smooth on `(0,1)`.
- Reflection holds: `Phi(-x) = 1 - Phi(x)` and `I(1-p) = I(p)` on `[0,1]`.
  Consequently `Phi(0) = 1/2` and `I(1/2) = 1/sqrt(2*pi)`.
- The actual shifted profile is `shifted eps x = I(x+eps) - I(eps)`.
  For `0 < eps < 1/2` it is smooth near `[0,1-2*eps]`, vanishes at zero,
  and is nonnegative on that interval. Its derivatives are proved by composition:
  `shifted' = -quantile(x+eps)` and `shifted'' = -1/I(x+eps)`.
- The exact identity `shifted * (-shifted'') = 1 - I(eps)/I(x+eps)` holds where
  `0 < x+eps < 1`. First and second derivatives admit finite bounds on the
  admissible interval; a Lipschitz constant on that interval is constructed.
- `abs (shifted eps x) <= 1/sqrt(2*pi)` for every real `eps,x`, and
  `shifted eps x -> I(x)` as `eps -> 0+` for `0 <= x < 1`.
- Smooth functions whose shifted values stay in `(0,1)` remain smooth under
  composition; compact support is preserved because `shifted eps 0 = 0`.
- An actual globally smooth extension exists for `0 < eps < 1/2`. It vanishes at
  zero, agrees with `shifted eps` on a neighborhood of each point of `[0,1-2*eps]`,
  and has globally bounded value and first two derivatives. Construction: multiply
  `I` by a bump supported strictly inside `(0,1)` and equal to one near
  `[eps,1-eps]`, then translate and subtract `I(eps)`.

The extension is not claimed to be globally concave or nonnegative. Its purpose is
to allow scalar composition with approximants that leave the prescribed interval.
The convergence theorem is pointwise in `x`; it does not itself state convergence
of heat-flow fields or of their derivatives.

## Operator boundary and next proof

The independent `smooth_chain` client instantiates the existing pointwise weighted
Laplacian chain rule for smooth `f`. This does not prove a chain rule for an arbitrary
`L2` equivalence class in `D(A)`.

The next concrete step is the tested generator identity for a globally smooth scalar
extension `Phi`, with bounded derivatives and `Phi(0)=0`:

`integral (A psi) Phi(F) = integral psi Phi'(F) (A F)
                         - integral psi Phi''(F) Gamma(T F,T F)`.

Here `F in D(A)` and the test `psi in D(A)` retains the boundedness/integrability
conditions needed for the pairings. Prove the transfer from the smooth operator core;
do not assume that the core approximants stay in the range of `F`. The extension above
addresses that scalar-range obstruction. Composition domain membership, any stronger
operator-valued identity, the BGL heat interpolation and its endpoint limits remain
separate obligations. The current heat constants remain `M/sqrt(2t)` and `sqrt(2t)`.
Neither the sharp coefficient, general-law passage, pi Buser nor KLS is completed.

## Validation

Strict source compilation and `research/audits/GaussianRegularizationAudit.lean` verify
smoothness, symmetry, peak normalization, nonnegativity, the reciprocal identity,
local derivative bounds, the uniform value bound, Lipschitz control, the epsilon limit,
the global extension, compact composition and a genuine smooth-input chain-rule client.
Twelve transitive axiom reports must contain only `propext`, `Classical.choice`, and
`Quot.sound`. The full verifier result, source snapshot and index-preservation check
are recorded in `build/audit/gaussian-regularization/final-snapshot.json` after validation.
No commit, push or remote CI is part of this continuation.
