# BKL independent target-check pilot

Date: 2026-10-12. Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1,
PDF SHA-256 `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
Targets: Theorem 3.1 (p. 10, (26)–(29)) and Proposition 7.1 (p. 28, (107)),
with regularity (12), the Poincaré convention (5), tensor norms and cumulant energy (65).

## Placement plan and scope

Owner: audit tooling under `research/audits/BKL/IndependentTargets/`. Create a standalone
Mathlib-only specification template and a separate linking/check template, with a local
runner, reviewed closure baseline and source mapping. These are audit artifacts, not new
production mathematics, certificates or changed public APIs. The runner compiles the
specification independently before loading either existing certificate. It checks explicit
bridges for regularity, normalized laws, tilt averages, factorial-scaled Hilbert–Schmidt
Taylor arrays, isotropy and the every-dimensional cumulant hypothesis.

The Poincaré-constant and log-concavity interfaces are explicit parameters of the standalone
specification; the link specializes them to the current library definitions. Their definition
closures are reviewed and snapshotted as an explicit trust boundary, not claimed as a new
Mathlib-only formalization of every foundational definition. Source review and Lean acceptance
are reported separately. Normalized potential laws and the zero-dimensional API extension
are compared with the paper's normalized density and positive-dimensional scope.

Preserve the dirty baseline, real staging, current hypotheses, proofs and unrelated work.
Do not submit, commit, push, tag, use remote CI or upload sources. Compile scoped existing
certificate inputs, independently compile the specification, compile/audit the link, snapshot
actual target types and key local definitions, replay the new audit modules, and record
source identities. The existing general statement golden is not automatically refreshed.

## Source review and definition correspondence

The pinned PDF was hash checked and the full relevant pages visually read: p. 2 for (5),
p. 5 for (12), pp. 9–10 for tensor/tilt conventions and (26)–(29), p. 18 for (65), and
p. 28 for (107). This is a local source-fidelity review, not external peer review.

- Theorem 3.1 quantifies one positive universal constant before dimension, law, potential,
  regularity parameters, R, f and derivative order. Its coefficient premise covers every
  real L2 function and every d >= 1, and R >= 1 is retained. Centering and covariance <= Id
  are retained. The production API uses normalized potential laws and additionally admits
  dimension zero. The independent target expresses the law separately from its potential.
- Regularity is smoothness with polynomial growth of every derivative and pointwise Hessian
  bounds. Mathlib's temperate-growth predicate expands to exactly the smoothness/iterated-
  derivative clauses used by the audit. In each finite dimension, bounds on all coordinate
  partial derivatives and bounds on the multilinear derivative norm are equivalent up to
  finite-dimensional constants; no dimension-free constant is required in this regularity
  definition. The audit retains both a > 0 and b > 0. The production structure omits b > 0:
  in positive dimension it is implied by the Hessian bounds, while in dimension zero it is
  a deliberate extra API scope. `regular_iff` checks the source contract with b > 0.
- A law from V has density exp(-V)/Z. `normalized_density` identifies it with exp(-W) for
  W = V + log Z, and `regular_add_constant` preserves the regularity contract. Z > 0 follows
  from the retained source regularity, not a conclusion-bearing replacement assumption.
- The normalized integral definition of F_f agrees with the production integral over the
  exponential tilt. `average_eq` checks that identity, including the totalized cases; regular
  probability laws have the finite, positive normalizers required by the paper.
- Taylor arrays use (d!)^(-1) times the d-th derivative at zero, with all ordered coordinate
  indices. `taylor_eq` and `taylor_norm_sq` check both the factorial and Hilbert–Schmidt norm.
  No multilinear operator norm is substituted. L2 is Mathlib MemLp at exponent 2, and the
  finite L2 norm is eLpNorm.toReal; the MemLp premise is retained.
- Proposition 7.1 retains d >= 2, b > 0 and the universal, every-dimensional isotropic
  log-concave cumulant hypothesis. `isotropic_iff` checks finite second moment, zero mean
  and identity raw second moments against the production covariance operator definition.
  `universalCumulant_iff` expands (65), with order d+1 and no factorial in the cumulant.
  The conclusion keeps exactly 2b/(d!)^2 and all L2 functions. The normalization/orthogonality
  conditions (108) belong only to an intermediate proof step and are not added to the target.
- The Poincaré boundary is the existing intrinsic local-slope constant: its finite-bound
  infimum, admissibility, local-slope definition, variance and affine-support construction are
  included in the new pilot closure. For regular full-support laws this is the Euclidean
  literature convention (5), via the existing intrinsic/ambient and slope/gradient bridges.
  The log-concavity boundary uses compact-set log-concavity, including singular laws; isotropy
  excludes a proper affine support in positive dimension, while regular laws have a positive
  log-concave density. The density/compact-set identification remains part of the reviewed
  foundation boundary, not a new theorem of this pilot.

## Acceptance boundary

The two independent targets are checked by Lean proofs applying the existing certificates
through explicit definition bridges. A separate closure baseline records actual certificate
and specification types, key local definitions and explicit external leaves. Neither the
old general statement baseline nor existing proof bodies are refreshed or rewritten.
The default snapshot command retains its original owner scope; an explicitly owned diagnostic
command adds certificate and independent-specification modules for this pilot only.
The baseline is created only after the scoped checks and new-module replay succeed. Later
`check` runs compare it and never silently regenerate it. Negative probes remove the Taylor
factorial, change the 2b coefficient and restrict the universal cumulant dimension; they must
compile as specifications but fail when linked to the reviewed proofs.

This pilot does not discharge Proposition 7.1's hypothesis, prove BKL Theorem 4.1 or 1.1,
cover the BKL paper, or prove dimension-free KLS. It is not an external comparator run or a
second-kernel verification. Existing certificate inputs are source-built; pinned Mathlib and
other third-party compiled imports remain trusted. The replay scope is reported explicitly.
