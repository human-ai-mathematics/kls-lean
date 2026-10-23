# Current KLS handoff

Updated 2026-10-23 for the canonical integration of the Gilbarg–Trudinger linear theory (Newtonian potential chain, harmonic kernel, quantitative ellipticity, coefficient freezing, quotient limit, absorption) and the interior Theorem 4.6 in Hessian form; 2026-10-22 for three integrated Schauder support packets (affine derivative scaling with local cutoffs, local Hessian interpolation, same-witness difference-quotient equations); earlier the same day for the gradient homeomorphism onto int K with a C¹ inverse at the regular moment potential (strong class) and the averaged-inverse log-determinant coefficients; earlier the same day for the regular moment potential with C² Hölder Hessian and the everywhere log-determinant equation (strong class: frame oscillation decay, Hölder representatives, continuous-a.e.-derivative bridge); 2026-10-21 for Letwin smooth-route support tools, the directional weak subsolution, nonlinear weak test tools,
H¹ energy/Sobolev tools, the Moser inputs, the Morrey/critical-potential inputs, the local bounded Moser inputs, the bounded weak John–Nirenberg / fixed-compact joint inputs, the bounded actual weak Harnack inequality, the given-data weak Harnack with its joint regular-potential application, the GT 17.13 fixed frame, the GT 8.23 scalar iteration and the essential deficit identity; 2026-10-20 for noncompact Letwin, Letwin Lemma A.1, Comparator
metadata and synchronized BrownianMotion.

## Accepted result and open boundaries

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the finite-horizon cutoff
stochastic-localization route of BKL. Its target is unchanged: one finite covariance-normalized
literature Poincaré bound for every dimension and every log-concave probability law with
finite second moment, including dimension zero and singular affine supports.

The accepted chain is compact Letwin Theorem 1.2 (constant 8) → finite-horizon cutoff BKL (95)
→ source-form BKL Theorem 4.1 → source-form BKL Theorem 1.1 → KLS.
The [paper register](research/progress/LITERATURE.md) owns exact scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean and its certificates.
BKL's main theorem is covered. Letwin's noncompact Theorem 1.2 is now proved separately
by `KLS.LogConcave.letwinQuadraticBound`, with the source matrix form
`matrix_variance_le_eight`, for every n > 0 and exact constant 8. Letwin's Lemma A.1 (regular
approximation in all mixed moments of degree at most four) is proved by
`KLS.LogConcave.exists_regular_approximation`. Theorem 1.1, the smooth moment map of Lemma 2.2
(including its literal merely convex source class), the uncut Eldan
construction and literal identities (68)–(73), and the separate uncut intermediate statements
remain unformalized locally. The four exploratory routes retain their own statuses.

## Evidence and library use

The [formalization metadata](formalization.yaml) records sources, AI involvement, external
stochastic-calculus credit and the maintainer's self-review of key statements. The
[Comparator inputs and runner](research/audits/KLS/Comparator/README.md) cover the unchanged
KLS endpoint and the separate [OpenAI bridge package](integrations/openai/README.md).
The bridge is an independent Lake project in this repository, using the same-revision
KLS library; its conditional bridge and closed endpoint retain their original proofs.
Keep the distinction between compiled
clients, unsandboxed macOS development runs and Linux sandbox runs in their generated receipts.
This verification setup changes no mathematical statement, proof or certificate status.

Use the [verification guide](research/verification.md#receipts-and-trust-scope) for receipt
rules and acceptance scopes. Receipts and execution logs stay local under ignored `build/`; remote Lean
evidence is the terminal GitHub Actions run for its exact `head_sha`. Neither a registry entry
nor an old receipt verifies a later source tree.

Use the [calling examples](examples/README.md), the [compiler API directory](formalization/API.md),
the [audit client guide](research/audits/README.md) and the
[short review checklist](research/workflow.md#review-after-mechanical-checks). The
[downstream runner](research/downstream.py) accepts one full Git commit, builds three narrow
clients in a fresh Lake project, audits their complete primary declaration closure and replays
the local compiled modules; it does not accept a working-tree overlay or renew a certificate,
and explicit third-party compiled caches remain trusted. Known
[vendor closure](formalization/vendor/README.md#upstream-holes) has no accepted upstream holes.

## Current work and next step

The current proof priority is the authorized Letwin smooth toolchain (the linear Schauder bootstrap
R10 of the [smooth-route gap map](research/progress/letwin-smooth-route.json)), then the uncut Eldan
construction. Lemma A.1 is formalized in `KLS/Letwin/Approximation.lean`; the compact reduction and
the noncompact endpoint consume its producers with unchanged public types. For Lemma 2.2 the strong
class has, at the regular moment potential, C² with locally Hölder Hessian, the everywhere positive
definite log-determinant equation and a gradient homeomorphism onto int K with a C¹ inverse; the
literal merely convex class (Caffarelli C^{1,α}, W^{2,p}) and the smooth source form of Lemma 2.7
remain open.

Updated 2026-10-23: the Gilbarg–Trudinger linear theory that R10 needs is now in the canonical tree
(previously only independently accepted scratch under `build/history/`), in new generic families with
GT locators in every header and audit clients under `research/audits/Newtonian/`, `CEK/` and the root:

- `Analysis/Newtonian/` (52 modules; n ≥ 2 including n = 2, 0 < α < 1): the source-normalized kernel,
  Lemma 4.2 `newtonianPotential_contDiffOn_two`, Lemma 4.4 `newtonianPotential_schauder` and
  `newtonianPotential_localHolder`, the representation (4.15) `compact_C2_newtonian_representation`,
  Theorem 4.5 `compactPoisson_estimates`/`compactPoisson_GT4_5`, the interior **Theorem 4.6 in
  Hessian form** `poisson_interior_hessian_holder` (`Newtonian/InteriorSchauder.lean`: for Δu = f on
  B_{2R}(c), ‖D²u‖ ≤ C(U R⁻² + M + R^α H) and the Hessian Hölder bound with C(U R^{−2−α} + M R^{−α} + H)
  on B_R(c), C(n, α) before all data), and the constant-coefficient **Lemma 6.1** interior form
  `constant_coefficient_interior_hessian_holder` (`IteratedDerivative/ConstantCoefficientSchauder.lean`: symmetric A
  with λ|ξ|² ≤ ξᵀAξ ≤ Λ|ξ|², the same two bounds with C(n, α, λ, Λ), via T = A^{1/2} and the Hessian pullback).
- `Analysis/Harmonic/`, `Analysis/Laplacian/`, `Analysis/Convolution/`, `Analysis/Holder/`: the harmonic
  half of Theorem 4.6 (fixed annular reproducing kernel Δ(truncated Γ), ε = 1/8; local C^∞ with
  derivative caps through order 3; `ball_harmonic_hessian_holder`), Green symmetry, the compact
  convolution derivative caps and generic Hölder tools.
- Lemma 17.16 completed to uniformly elliptic linear equations: λ, Λ for the averaged-inverse
  coefficients before direction and step (`Analysis/Matrix/{CompactEllipticity,AveragedInverseEllipticity}`,
  `Analysis/BakryEmery/HessianEllipticity`), the W(∇u) forcing as Σ b_i ∂_i of the quotient with bounded
  Hölder b_i (`Analysis/GradientSegment`, `Analysis/BakryEmery/{GradientForcing,UniformGradientForcing,
  EllipticGradientForcing}`), and the same-witness application
  `exists_regular_moment_potential_elliptic_quotient_equations` (`KLS/CEK/MomentRegularity/Ellipticity`).
- Supports for Theorem 6.2: coefficient freezing (6.17)–(6.19) with small-radius absorption constants
  (`Analysis/IteratedDerivative/{CoefficientFreezing,CoefficientCoordinates}`, `Newtonian/PoissonFreezing`),
  Hessian pullback and Hölder transport under a linear equivalence
  (`IteratedDerivative/{LinearPullback,HolderTransport}`), the quotient-limit theorem
  `contDiffOn_two_of_hessian_limit` (`IteratedDerivative/QuotientLimit`: equi-bounded, equi-Hölder Hessians
  of C² approximants pass to a C² limit with the same bounds) and the radius absorption lemma
  `exists_absorption_constant` (`Analysis/AbsorptionIteration`).

What R10 still needs, in order (plan in the local record `build/history/2026-10-23-letwin-schauder-integration/PLAN-R10.md`):
the a priori interior estimate of Theorem 6.2 for variable Hölder coefficients (freezing + Lemma 6.1 on small balls +
interpolation + the absorption lemma), and the C^{k,α} ⇒ C^{k+1,α} bootstrap at the regular moment potential
(quotient equations + Theorem 6.2 + quotient limit), giving u ∈ C^∞ and a smooth gradient diffeomorphism. These are
supporting results; Lemma 2.2 stays partial and no certificate changes.

The first-wave Schauder supports (affine derivative scaling with local cutoffs `Analysis/IteratedDerivative/Affine`,
`Analysis/Cutoff/LocalRegularity`; Hessian interpolation `Analysis/IteratedDerivative/Interpolation`; averaged-inverse
difference quotients `Analysis/Matrix/AveragedInverse`, `Analysis/BakryEmery/DifferenceQuotient` with
`exists_regular_moment_potential_difference_quotient_equations`) keep their audit clients
`research/audits/{AffineDerivativeScaleAudit,HessianInterpolationAudit,CEK/DifferenceQuotientAudit}.lean`.

The 2026-10-21 support batch works at the same strong regular-class witness (unchanged old types):
`exists_regular_moment_potential_with_inverse` (injective gradient, measurable left inverse),
`exists_regular_moment_potential_locally_elliptic` (Hess u ≥ δ_S Id a.e. on each compact S, from the
determinant floor `posSemidef_sub_scalar_of_det_lower`) and `exists_regular_moment_target_stein_kernel`
in `KLS/CEK/MomentRegularity/TraceStein` (τ = Hess u ∘ Ψ a Stein kernel of μ, μ-a.e. positive definite,
∫|τ|²_HS dμ ≤ 2n). These are weak supports, not smoothness or the literal Lemma 2.2/2.7; the audit client is
`research/audits/Letwin/WeakHessianKernel.lean`.

The R9b step is proved at the same weak witness: `exists_regular_moment_directional_hessian_subsolution`
(`KLS/CEK/MomentRegularity/WeakHessian`) keeps every field of `exists_regular_moment_weak_hessian_evolution` and adds
the directional weak subsolution `∫ e^{-u} (∇²u)⁻¹∇h_v·∇ψ ≤ ∫ e^{-u} h_v ψ` for `h_v = vᵀ∇²u v`, `ψ ≥ 0` compact C¹,
and compact-local bounds `c₀ Id ≤ e^{-u}(∇²u)⁻¹ ≤ c₁ Id` a.e. on each compact S (audit
`research/audits/Letwin/DirectionalSubsolution.lean`). Oscillation decay and the strong-class C² Hölder conclusion are proved below. Schauder/C^∞ remains open; the bounded actual weak
Harnack inequality is proved below.

Nonlinear weak test tools are proved as supports:
- the compact bounded H¹ chain rule `hasWeakDerivAlong_comp_of_compact_bounded`;
- the normalized shifted log and real powers (every real q) of bounded weak tests `η ≥ 0` a.e.;
- the cutoff directional data `directional_cutoff_data`;
- bounded weak directional testing and the rough square test `rough_square_test_of_weak_data`;
- PSD Young `posSemidef_quadratic_young`.

The actual same-witness square/log/power examples are in `research/audits/Letwin/RoughTesting.lean`.

H¹ energy and Sobolev tools are proved as supports (GT (8.48)–(8.49); every dimension unless stated):
- the outer-cutoff energy variables `χ (δ + max w 0)^r` (every real r) and the square test `χ² s^q`, in
  `WeakDerivative/Calculus`;
- the Caccioppoli inequality `bounded_weak_supersolution_caccioppoli` for bounded weak supersolutions, with constants
  4β/(p²α) and 2F/(pα), in `WeakDerivative/Caccioppoli`;
- weak Sobolev bounds in `WeakDerivative/Sobolev`: critical GNS for n > 2; for n = 2 every finite q ≥ 2 with the
  factor `C_GNS(2q/(q+2)) · volume(cthickening ε K)^(1/q)` (L⁶ is the q = 6 case); for n = 1 an essential L^∞ bound only.

The audit `research/audits/Letwin/Caccioppoli.lean` selects one witness u, T, then for each compact S one α, β and a
density bound B, then works for every direction v and every cutoff χ with tsupport χ ⊆ S, with F_v = (16/κ)|v|²·B.
The ball corollaries bound only the thickening measure; they do not give full normalized radius scaling.

The Moser inputs are proved as supports:
- the bounded noncompact weak chain and the actual shifted log `log (δ + max w 0)` in `WeakDerivative/Calculus`;
- the logarithmic energy (p = 1) and the power energy of `χ s^r`, r < 1/2, in `WeakDerivative/Caccioppoli`;
- uniform concentric cutoffs (one D for all centers and radii) in `Cutoff/SmoothBall`;
- the L^p → essential L^∞ limit on probability spaces in `Analysis/LpExponent`;
- the coordinate L² energy `(Σ‖a_i‖₂)² ≤ n ∫ Σ a_i²` in `L2/Components`.

In the audit, `moser_inputs_unified_same_witness` (every n > 0) and `moser_inputs_unified_two_same_witness` (n = 2)
combine all of them at ONE witness. One u, T is chosen first, then one D before all radii, then for each compact S one α,
β, B for every cutoff in S, including every dyadic family χ_m with gap R·2^{-(m+1)} and ‖Dχ_m‖ ≤ D·2^{m+1}/R. The same
theorem gives the normalized closed-ball L^p → L^∞ limit, and in n = 2 the finite-q Sobolev bounds of the same g, dg.

The Morrey and critical-potential inputs are proved as supports:
- ball-growth geometry in `Analysis/MeasureGrowth`;
- all-ball Morrey bounds from cutoff energy (GT (8.49) → (7.51)) in `Analysis/MorreyGrowth`;
- radial and critical potentials (GT 7.20 at p = n ≥ 2, explicit constants) in `Analysis/RieszPotential/{Growth,Critical}`;
- moment growth → exponential integrability in `Probability/ExponentialMoments`.

At ONE witness the audit proves `actual_log_gradient_morrey_same_witness` (the all-ball Morrey bound of the actual
logarithmic gradient) and, for n ≥ 2, `actual_log_gradient_potential_exp_same_witness` (exponential integrability of its
critical potential). This is not the exponential integrability of log − mean: that needs GT 7.16. It is not
John–Nirenberg.

The local bounded Moser inputs are proved as supports, with nonnegativity only a.e. on the cutoff support:
- `local_rpow_cutoff_weak_data`, `local_rpow_cutoff_weak_test` and `exists_bounded_weak_log_extension` (one bounded weak
  extension of `log (δ + max w 0)`, identified where w ≥ 0; no global weak log derivative) in `WeakDerivative/Calculus`;
- the local Caccioppoli, power and log energies in `WeakDerivative/Caccioppoli` (the global versions are consumers);
- n > 2 one-step critical gains from a given power energy in `WeakDerivative/Sobolev`;
- small-ball + mass growth in `Analysis/MeasureGrowth` and the buffered all-ball Morrey bound on B_3R from energy on B_4R
  (K = ω_n 16^n (1 + E0 n D² + E1 R²)) in `Analysis/MorreyGrowth`.

The audit adds `actual_dyadic_power_gain_same_witness` (one global-class gain step, n > 2) and, for the LOCAL deficit
M − h_v with the cap only on B_4R at ONE public-producer witness, `actual_local_deficit_log_morrey_same_witness` (local log
energy, one weak extension, B_3R Morrey) and `actual_local_deficit_potential_exp_same_witness` (n ≥ 2, critical-potential
exponential at the same witness and extension). Coefficients are chosen once per R, not once per fixed compact set before
all radii, and the Morrey domain is centered at 0.

The bounded weak convex representation and critical John–Nirenberg are proved as supports:
- `measure_mul_abs_sub_average_le_riesz_of_contDiffOn` and `map_restrict_convex_ray_le` in `Analysis/RieszPotential/Representation`
  (GT 7.16 smooth step: C¹ on an open convex Ω, any measurable S, mass form D^n/n);
- `lintegral_riesz_potential_le_diameter_mul_lintegral` in `RieszPotential/Growth`, `L2.memLp_sqrt_sum_sq` and
  `L2.gradient_density_l1_of_coordinate_l2` in `L2/Components`;
- `measure_mul_abs_sub_average_le_riesz_of_bounded_weak_data` and `integrable_exp_abs_sub_average_of_bounded_weak_morrey`
  (critical JN, σ = [2(n−1)e]⁻¹ n|Ω|/D^n, n ≥ 2, global bounded weak H¹_loc data) in `Analysis/WeakDerivative/Representation`;
- `Probability.integral_rpow_mul_integral_rpow_neg_le_of_log_exp` and the centered buffered Morrey bound
  `exists_centered_buffered_morrey_bound_of_cutoff_energy`.

The audit adds two scopes at ONE witness: per R (unconditional, exponent σ/K16) `actual_local_deficit_john_nirenberg_same_witness`
and `actual_local_deficit_log_moment_product_same_witness`; and fixed compact S (coefficients once per S before every domain
center and radius) `actual_local_inputs_fixed_compact_same_witness` (all linear power data, energies, one weak extension,
centered Morrey) and `actual_joint_jn_moments_fixed_compact_same_witness` (under F R² ≤ αδ, JN and power moments at the
uniform p0 inside the same extension). This closes the fixed-S / all-domain-center joint bounded input gap.

The bounded actual weak Harnack inequality (GT 8.18 for bounded data, by the Moser iteration) is proved as supports:
- `geometric_exponential_recurrence_bound` and the root recurrences in `Analysis/DyadicSummation`; the general physical-exponent iteration `eLpNorm_top_le_of_shrinking_norm_steps` and
  `finite_normalized_eLpNorm_sequence_bound` (N/κ + a = N) in the new `Analysis/MoserIteration`;
- the L^p / essential-supremum exponent tools, the moment-to-product bridge `mul_eLpNorm_inv_top_le_of_moment_product` and
  the shift removal `unshifted_bound_of_shifted_inverse_norm_products` (essential infimum, explicit finite C) in
  `Analysis/LpExponent`;
- n = 2 and n = 1 cutoff Sobolev gains in `WeakDerivative/Sobolev`; the n = 1 kernel-1 representation and density-mass
  exponential bound in `WeakDerivative/Representation`;
- six weak-energy endpoints in the new `Analysis/WeakDerivative/Moser`: n > 2 inverse essential bound and positive boost
  for 0 < p < n/(n−2); n = 2 with the physical exponent a = 2 − 2/g; n = 1 direct inverse/positive essential bounds (no
  critical τ).

The standalone audit `research/audits/Letwin/Caccioppoli.lean`, in a final section after its producers, proves, at ONE
fixed-compact witness with every constant chosen per compact S before all centers, radii, directions, caps and shifts, the
full-exponent same-witness products for n > 2, n = 2 and n = 1, and `actual_essential_harnack_fixed_compact_same_witness`: for every
n > 0, R^{−n/p} ‖w‖_{p,B(x0,2R)} ≤ C(p) (essinf_{B(x0,R)} w + M B R²/α), for 0 < p < n/(n−2) when n > 2 and every finite
p > 0 when n ≤ 2. This is an essential infimum (a.e.), not a pointwise infimum or a regular representative. It closes the
R9a bounded actual Harnack sub-tool; R9 stays MISSING_DEEP.

The given-data weak Harnack inequality is proved as `bounded_weak_harnack_of_given_data` in
`Analysis/WeakDerivative/Harnack` (GT 8.18, bounded symmetric pure-divergence case, for GIVEN global bounded weak H¹_loc
data: C(p) before every ball, coefficient matrix, function, derivative, bound and forcing), with the single given-data
producers `cutoff_power_data_of_weak_supersolution_on_set` and `exists_weak_log_extension_with_energy_on_set` in
`WeakDerivative/Caccioppoli`. The audit adds `LetwinHarnackAudit.harnack_joint_regular_potential`: ONE regular moment
potential with all its regular-class data and, per compact S, α, β, B and C(p) before every center, radius, direction and
cap, with the weak Harnack inequality for every directional deficit (forcing M B).

Tools for the oscillation step are proved as supports: `exists_uniform_positive_rank_one_frame` (GT 17.13 in literal form:
a fixed finite unit frame with every e_i and (e_i+e_j)/√2 and coefficients in [lowerCoeff, hi]) and `coefficient_le_cap` in
`Analysis/Matrix/RankOneFrame`, the SPD congruence `exists_invertible_congruence_of_posDef` in `Matrix/Positivity`, the
GT 8.23 scalar iteration in `Analysis/Modulus` and `essInf_ofReal_deficit_eq_sub_essSup` in `Analysis/EssentialExtrema`.

At the same regular moment potential, `exists_regular_moment_potential_holder_hessian` in
`KLS/CEK/MomentRegularity/HessianHolder` proves: u is C² with continuous Hessian, every Hessian entry is locally Hölder (one
exponent and constant per ball, before all entries and points), and Hess u is positive definite with
log det Hess u = −u + W(∇u) and Hess u ≤ (16/κ) Id at EVERY point; all regular-class fields are retained. The route is the
rough-divergence form of GT 17.14 with the GT 17.13 frame (`Analysis/Matrix/LogDetOscillation`), the GT 8.23 power decay
(`Analysis/EssentialOscillation`), Hölder representatives (`Analysis/HolderRepresentative`, `Analysis/Matrix/Holder`), the
continuous-a.e.-derivative bridge (`Analysis/ContinuousDerivative`) and C² identification with the everywhere equation
(`Analysis/HessianRegularity`); the given-data Harnack application is reconstructed privately in the CEK owner. The audit
`research/audits/Letwin/HessianHolder.lean` checks transport, C², local Hölder and the everywhere equation from the original
inputs. This closes R9 and R11 of the gap map for the strong class; it is not the classical Evans–Krylov theorem or the
classical C⁴ GT 17.14.

For the same u, L, LF and T, `exists_regular_moment_potential_holder_hessian_inverse` in `KLS/CEK/MomentRegularity/Inverse`
keeps every field of `exists_regular_moment_potential_holder_hessian` and adds a homeomorphism ∇u : ℝⁿ ≃ₜ int K and a C¹ left
inverse of ∇u on int K (R12b/R12c). Generic supports: tilt minima, the convex open range, the open map and the homeomorphism of a
strictly convex gradient (`Analysis/Convex/GradientImage`, linear growth in `Analysis/Convex/Coercivity`); C^k inverses from
C^{k+1} with a positive definite Hessian (`Analysis/Convex/GradientInverse`, `Analysis/LocalInverse`); measure supports
(`Probability/Support`); the given-potential bridge `Probability/MomentMeasure/Gradient`. The averaged-inverse coefficients of
GT (17.56) with Hölder averaged inverses (`Analysis/Matrix/LogDetSegment`, `Analysis/Matrix/InverseHolder`,
`Analysis/MeasureAverage`, `Analysis/Matrix/DeterminantDerivative`) are prerequisites for linear Schauder only. The audit
`research/audits/Letwin/GradientInverse.lean` checks transport, C², the homeomorphism and the C¹ inverse from the original inputs.

The next step is the rest of the linear Schauder bootstrap R10 (C^{2,α} ⇒ C^∞) for the strong class (Lemma 6.1,
Theorem 6.2, bootstrap; see the 2026-10-23 update above): first the Letwin smooth route, then uncut Eldan. Full GT 8.18 for unbounded data (q > n, rough general coefficients), the domain-only W^{1,1} GT 7.16, the Schauder bootstrap
and the merely convex class stay open. Gilbarg–Trudinger is not covered as a paper (its Chapter 4 results are supports); Letwin Lemmas 2.2 and
2.7 stay partial and Theorem 1.1 unformalized; the 34 certificates are unchanged.

BrownianMotion is synchronized to `a7ad7af` on the unchanged Lean/Mathlib v4.33.0 toolchain.
Its corrected regularization contracts replace the old placeholders; the LevyStochCalc consumer
retains its public theorem types and right-continuity-in-measure hypotheses. The selected proved
closure excludes the unrelated UniformIntegrable module, and both declaration audits permit
only the three standard axioms. The provenance lock records upstream manifest pins separately
from the tested dependency overrides; see the [vendor policy](formalization/vendor/README.md).

The 2026-10-20 local formalization batch removes compactness from Letwin Theorem 1.2 by
conditioning on growing balls, centering and covariance whitening, and passing mixed moments
through degree four to the limit. Generic convergence tools extend `Probability/Conditioning`;
the paper endpoint lives in `KLS/Letwin/QuadraticBound`. The existing compact certificate and
BKL main chain retain their scope. Lean/Mathlib remain v4.33.0; the proposed upgrade was cancelled.
The first four Product-Lp section/averaging helpers are independently accepted locally in
the separate Mathlib checkout; no Mathlib submission or second package is implied.
This batch adds no paper-target certificate and does not renew remote verification.

The [statement review](research/progress/statement-review.md) checks the contracts of all 34
registered certificates against the live text, with source checks for the main BKL/Letwin
statements and the ADMG target. It corrects stale completion claims, quantifier attribution,
test-class descriptions and the attribution of the local constant 153. Lean types, definitions,
proofs and certificate/progress states are unchanged by those textual corrections.

The [public-interface review](research/progress/public-interface-review.md) records the current
human-review scope: the maintainer has reviewed the original important definitions and APIs;
the OpenAI statement/bridge and external upstream interfaces still await personal review.
Its follow-up corrects the Letwin/Cheeger source comments and target import description, and
distinguishes cumulant order, regular-potential positivity and the BKL certificate's dimensional
scope in the reading aids. Statements, proofs, imports and certificate/progress states are retained.
Nicolas reports checking the bridge/model hash, metadata and Letwin result in Issue 10, and
[reports both Linux sandboxed Comparator targets passed at `2639e79`](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6289895395).
The full receipts and logs await incorporation and have not yet been inspected in this checkout.
The local README now presents reusable library interfaces and calling examples first, retains
the pinned comparison table and explicitly lists the missing numerical KLS constant, Letwin
Theorem 1.1/Lemma 2.2 and uncut Eldan construction. This positioning pass changes no proof or
certificate status. The bridge cache fix and Linux setup notes are also present locally;
the final Linux sandbox run still needs the eventual frozen commit. Freeze requires a CI
receipt for that same HEAD, and repository visibility remains a maintainer decision. The maintainer
[accepted the Mathlib PR contact and review discussion role](https://github.com/human-ai-mathematics/kls-lean/issues/10#issuecomment-6288813867);
no numerical KLS-constant task is selected.

The usability improvements refresh the compiler API directory, improve keyword search,
add a [direct KLS application client](examples/KlsApplications.lean), and document
[first use from a separate Lake project](examples/FIRST-USE.md). The client passes the KLS
bound through existing smooth-test, Gaussian and convolution interfaces; its literature use
is the Poincaré input of In-and-Out (NeurIPS 2024, Lemma 11), with no sampler or paper-coverage
claim. The first-use client and documentation are maintained with the library interfaces.

The module-ownership and text-correction migration is already committed at `88547fc`.
The noncompact Letwin proof, Comparator/metadata and usability improvements are recorded
as separate changes. The next contribution package is the four Product-Lp helpers in Mathlib.
Before an approved verification milestone, freeze the intended source snapshot, run full local
verification and select the exact committed revision for downstream and remote certification. The
[release procedure](research/release.md), [contribution guide](CONTRIBUTING.md) and
[citation metadata](CITATION.cff) describe public use and the exact-revision requirements.
Repository visibility and previously pushed history remain unchanged by this preparation.

CI cache preparation recognizes both aggregate `Mathlib` and dotted imports, checks their
pinned compiled closure, and rejects an incomplete cache before the build. The helper now
supports `--project openai` and `--project all` for the separate bridge's dependency cache;
the default remains the main `formalization` package. Each selected package's own Mathlib
compiled closure is checked, and the Comparator guide prepares both before building.
The verifier
prints live progress and retains incomplete-run state; disk exhaustion, cache misses,
compiler failures and manual cancellation have distinct evidence. No old or cancelled run
verifies a new revision.

Remote CI keeps the strict build and declaration/vendor/classical audits, with the final
local-module kernel replay assigned to the [full local receipt](research/verification.md#receipts-and-trust-scope).
A single `leanchecker` process accumulates memory (14.4 GB after 40 modules locally), freezing
the 16 GB hosted runner; remote certification therefore skips that replay gate.
Run 39228796618 certified `845e61b` under that scope (1h21m; 9,856 local declarations, standard
axioms only; vendor gate 4,789 declarations with the 5 listed upstream holes isolated).

Mathematical statements, proof bodies, hypotheses, parameter names/order, normalization,
dimensional scope and all 34 certificate states are retained. New mathematical work selects
a pinned literature target under the [workflow](research/workflow.md). The
[module directory](formalization/MODULES.md) locates source owners.
General scalar coarea and slice helpers live in `Analysis/Coarea` and `Analysis/Hausdorff/Slice`;
metric BV foundations live in `Analysis/MetricBV`. The arbitrary-metric finite-measure client
[`examples/MetricBV.lean`](examples/MetricBV.lean) composes measure scaling with complement
symmetry and asserts that no KLS conjecture or smooth-test Poincaré interface is imported.
Perimeter/Minkowski identification and log-concave application modules retain their owners.
Product variance identities live in `Probability/ProductVariance.lean`, removing the
Probability-to-Poincare import; compact-set log-concavity lives in `Probability/LogConcave.lean`,
with Poincaré and affine-support imports now stated by their actual consumers. The public
namespaces of these moved modules are retained independently of file ownership.

BKL source Theorem 4.1 is assembled in `BKL/CumulantInduction.lean`, with
`exists_cumulantBoundCompact_of_letwinCompact` and `exists_cumulantBound_of_letwinCompact`;
source Proposition 7.1 lives in `BKL/TaylorBound.lean`; the closed source Theorem 1.1 entry is
`BKL.Localization.exists_isotropicBound`. These are explicit name/path migrations, with no
old aliases or forwarding modules. Conditional inputs and closed producers remain distinct.
The reviewed statement baselines permit only the log-concavity declaration's owning-module
substitution; their types and definition closures remain unchanged. Full local verification,
strict independent clients, axiom audits and local-module replay retain their distinct scopes.
Fresh-clone instructions and validation inputs remain tracked.

## Publication plan (2026-10-23)

The accepted `KLS.kls` chain is to be published on Prove2Me as one mission containing exactly the
import closure of `FunctionalInequalities.KLS.Target` (its project modules and the vendored
stochastic-calculus modules that closure requires, with upstream attribution retained), rebuilt
against the platform's pinned Lean/Mathlib environment and uploaded with the platform's
full-project extraction pipeline. The mission starts private; it is released only after the
owner audits the core statements. Platform statements and proofs are immutable, so the later
Letwin smooth route (Lemma 2.2, uncut Eldan construction) is added as new nodes and relinked by
the mission captain; the existing proof is not deprecated. The earlier private-upload artifacts
under ignored `build/prove2me-private*` are inputs for that step, not evidence. This snapshot
also integrates the section-variable refactor of the closed-proof modules; the 95 stale
infrastructure evidence hashes in `research/tasks.json` were refreshed against the current
sources (no pinned file was removed).
