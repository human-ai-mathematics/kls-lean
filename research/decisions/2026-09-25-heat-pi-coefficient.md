# Gaussian gradient and small-time heat coefficients

Date: 2026-09-25. Local continuation; no commit or push.

## Proved statements

In the current full-dimensional log-concave tilted-law model with smooth convex
potential and unit gradient weight, the Gaussian BGL inequality now yields:

- For 0 <= f <= 1 and t > 0, `|T P_t f| <= 1/(2 sqrt(pi*t))` a.e.
- For |f| <= M and t > 0, `|T P_t f| <= M/sqrt(pi*t)` a.e.
- For every f in the whole closed-gradient form domain and t >= 0,
  `int |f-P_t f| <= 2 sqrt(t/pi) int |T f|`.
- The same coefficient transfers to arbitrary L2 data with the stated L1
  form-domain recovery criterion; the approximation error remains `2 int |f-u|`.
- For smooth domains D and a Borell density representative rho of the same law,
  `int |1_D-P_t 1_D| <= 2 sqrt(t/pi) P_rho(D)` when perimeter is finite.
  The extended-nonnegative version includes infinite perimeter and t=0.

These are statements for the constructed heat semigroup and closed gradient, not
pointwise classical smoothness assertions or a general nonsmooth log-concave-law
passage. The perimeter is the existing relative perimeter in the interior support.

## Placement, proof and API preservation

Extend `HeatSemigroup/GaussianProfile.lean` with
`ae_norm_gradient_le_of_unitInterval` and `ae_norm_gradient_le_of_bounded_pi`.
The scalar Gaussian maximum gives the first bound after explicit square-root
normalization. For M>0, normalize the input as f/(2M)+1/2. Heat invariance of
constants and the vanishing closed gradient of constants identify the normalized
terminal gradient. The M=0 case uses the existing zero bound; nonnegativity of M
follows from the a.e. bound under the probability law.

Extend `HeatSemigroup/Approximation.lean` with `inner_sub_operator_le_pi`,
`integral_abs_sub_operator_le_pi`,
`integral_abs_sub_operator_le_of_form_approximation_pi`, and
`integral_abs_sub_operator_le_of_recovery_pi`. The dual time argument integrates
1/sqrt(pi*s), with antiderivative 2 sqrt(s)/sqrt(pi). Its continuity at zero and
the semigroup's strong continuity supply t=0. The scalar square-root identity
identifies the coefficient as 2 sqrt(t/pi). Reuse the existing bounded L2 duality
and actual form-domain recovery argument; no L1 extension of the operator is assumed.

Approximation now imports GaussianProfile. ReversePoincare does not import the
Gaussian boundary, so the dependency direction remains acyclic.

In `HeatSemigroup/Perimeter.lean`, the substantive recovery proof now proves
`integral_abs_indicator_sub_operator_le_pi`. Its ENNReal extension is
`lintegral_enorm_indicator_sub_operator_le_pi`. Infinite perimeter at positive time
uses strict positivity of the coefficient; t=0 is handled first, by the actual
indicator representative and P_0=id, avoiding any use of 0*infinity as infinity.

All eight pre-existing public signatures in Approximation and Perimeter are
unchanged. The previous dual/form-approximation and perimeter statements are weaker
numerical consequences of the new bounds, using 2 sqrt(t/pi) <= sqrt(2t).
No compatibility aliases or module moves are added. Reused recovery proofs and
existing client contracts are preserved; no unrelated work is discarded.
The baseline/signature comparison is recorded in
`build/audit/heat-pi-coefficient/preserved-signatures.json`.

## Validation and remaining work

Eight independent full-signature clients in `research/audits/HeatPiCoefficientAudit.lean`
check both gradient bounds, duality, whole-form-domain L1 approximation, form
approximation, recovery, finite perimeter and extended-nonnegative perimeter.
Strict compilation, standard transitive axioms and full project verification are
required. Receipt: `build/audit/heat-pi-coefficient/final-snapshot.json`.

Progress generation uses an isolated Git index and object store. The real index and
unrelated dirty work are preserved. This is local verification, not remote CI.

The 2 sqrt(t/pi) heat/perimeter coefficient is now formalized in this smooth convex
model. General-law passage, remaining perimeter interfaces, spectral decay and the
pi Cheeger-Buser comparison still require their own proofs and assembly. The full
Cheeger-Buser and dimension-free KLS nodes remain open.
