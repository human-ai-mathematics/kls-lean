# BKL independent target checks: source correspondence and trust boundary

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, PDF SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`. Targets: Theorem 3.1
(p. 10, (26)–(29)) and Proposition 7.1 (p. 28, (107)), with regularity (12), the Poincaré
convention (5), the tensor norms and the cumulant energy (65). This record is the tracked review
pinned by `golden.json` and named in `config.json`; it summarizes the existing local source correspondence. This archival cleanup does not
supply a new reading of the paper or external peer review.

## Statement correspondence

- **Theorem 3.1.** One positive universal constant is quantified before dimension, law,
  potential, regularity parameters, `R`, `f` and derivative order. The coefficient premise covers
  every real `L²` function and every `d ≥ 1`; `R ≥ 1`, centering and covariance `≤ Id` are
  retained. The production API uses normalized potential laws and additionally admits dimension
  zero; the independent target expresses the law separately from its potential.
- **Regularity (12).** Smoothness with polynomial growth of every derivative and pointwise
  Hessian bounds `a Id ≤ ∇²V ≤ b Id`. Mathlib's temperate-growth predicate expands to exactly the
  smoothness and iterated-derivative clauses used. In each finite dimension, bounds on all
  coordinate partial derivatives and on the multilinear derivative norm are equivalent up to
  finite-dimensional constants; no dimension-free constant is required in this definition. The
  audit retains both `a > 0` and `b > 0`; the production structure omits `b > 0`, implied by the
  Hessian bounds in positive dimension and a deliberate extra API scope in dimension zero.
  `regular_iff` checks the source contract with `b > 0`.
- **Normalization.** A law from `V` has density `exp(-V)/Z`; `normalized_density` identifies it
  with `exp(-W)` for `W = V + log Z`, and `regular_add_constant` preserves regularity. `Z > 0`
  follows from the retained regularity, not from a replacement assumption.
- **Averages and Taylor arrays.** `average_eq` identifies the normalized integral `F_f` with the
  production integral over the exponential tilt, including the totalized cases. Taylor arrays are
  `(d!)⁻¹` times the `d`-th derivative at zero over all ordered coordinate indices; `taylor_eq`
  and `taylor_norm_sq` check the factorial and the Hilbert–Schmidt norm. No multilinear operator
  norm is substituted. `L²` is Mathlib `MemLp` at exponent 2 and the finite norm is
  `eLpNorm.toReal`; the `MemLp` premise is retained.
- **Proposition 7.1.** `d ≥ 2`, `b > 0` and the universal, every-dimensional isotropic
  log-concave cumulant hypothesis are retained. `isotropic_iff` checks finite second moment, zero
  mean and identity raw second moments against the production covariance operator;
  `universalCumulant_iff` expands (65) with order `d + 1` and no factorial in the cumulant. The
  conclusion keeps exactly `2b/(d!)²` and all `L²` functions. The normalization and orthogonality
  conditions (108) belong to an intermediate proof step and are not added to the target.

## Explicit parameter boundary

The Poincaré constant and log-concavity are explicit parameters of the Mathlib-only
specification. The link specializes them to the current library definitions and their definition
closures are snapshotted as an explicit trust boundary, not claimed as a new Mathlib-only
formalization:

- the Poincaré boundary is the intrinsic local-slope constant `Poincare.LocalSlope.Intrinsic.constant`,
  with its finite-bound infimum, admissibility, local-slope definition, variance and
  affine-support construction; for regular full-support laws this is the Euclidean literature
  convention (5) through the existing intrinsic/ambient and slope/gradient bridges;
- the log-concavity boundary is compact-set log-concavity `KLS.LogConcave`, including singular
  laws; isotropy excludes a proper affine support in positive dimension, and regular laws have a
  positive log-concave density. The density/compact-set identification remains part of the
  reviewed foundation boundary, not a theorem of this pilot.

## Acceptance boundary

The two targets are checked by Lean proofs applying the existing certificates
`Solutions.ThmBklTaylorCriterion.certificate` and `Solutions.PropBklSuspension.certificate`
through the explicit bridges above. The closure baseline records the actual certificate and
specification types, the key local definitions and the external leaves; `check` compares it and
never regenerates it. Mutation probes remove the Taylor factorial, change the `2b` coefficient and
restrict the universal cumulant hypothesis to one dimension; each must compile as a specification
and fail when linked.

This pilot does not discharge Proposition 7.1's hypothesis, prove BKL Theorem 4.1 or 1.1, cover
the BKL paper, or prove dimension-free KLS; those are registered separately
(`thm:bkl-cumulant-bound`, `thm:bkl-poincare`). It is not an external comparator or a second-kernel
verification. Certificate inputs are source-built; pinned Mathlib and other third-party compiled
imports remain trusted, and the replay scope is reported in each receipt.
