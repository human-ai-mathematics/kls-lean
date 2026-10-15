# Proof path to KLS through BKL

Read this page as **source step → Lean declaration → owning module → remaining input**.
The [literature register](LITERATURE.md) owns paper scope and coverage, the
[node register](STATUS.md) records local status, and [HANDOFF](../../HANDOFF.md) owns the current
queue and evidence. This page adds no certificate or dependency edge. **KLS remains open.**

| Stage | Pinned target | Current boundary |
| --- | --- | --- |
| 1. Letwin constant 8 | arXiv:2607.24164v1, Theorem 1.2 via Theorem 2.5; BKL arXiv:2610.05474v1, Lemma 4.2 consumer | Selected target; supporting weak analysis is formalized, compact constant 8 remains open |
| 2. Stochastic localization | BKL arXiv:2610.05474v1, Section 5 | Existing cutoff-localization development; queued for source/evidence review |
| 3. BKL Theorem 4.1 | BKL arXiv:2610.05474v1, Theorem 4.1 | Proved conditionally on `LetwinCompactBound`; unconditional theorem open |
| 4. KLS | `KLS.Conjecture` | Conditional assembly exists; `KLS.kls` remains open |

## Stage 1: Letwin's constant 8

The exact input is `KLS.LogConcave.Suspension.LetwinCompactBound` in
[KLS/BKL/CompactReduction.lean](../../formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean).
For every n > 0 and every compactly supported isotropic log-concave probability law on
`EuclideanSpace ℝ (Fin n)`, it bounds the centered variance of every self-adjoint quadratic form
by 8 times its squared Hilbert–Schmidt norm. Singular and indefinite forms are included.
The proposed endpoint `letwinCompactBound : LetwinCompactBound` is not a proved declaration.

`letwinCompactBound_of_regularClass` in
[KLS/BKL/LetwinApproximation.lean](../../formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean)
reduces it to the regular class `1_K exp(−W) dx`, with compact convex K and smooth uniformly convex W.
The bound for that class remains an explicit premise. The entries below are **Formalized in Lean**
within their displayed hypotheses; they do not prove the stage or cover Letwin's paper.

| Source step / support | Lean entry and owner | Exact boundary |
| --- | --- | --- |
| Regular moment potential (R0) | `exists_regular_moment_potential` — [KLS/CEK/MomentRegularity.lean](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean) | C¹ u, Lipschitz gradient, normalization, actual gradient pushforward and a.e. Hessian/log-det data; no global C² conclusion |
| Hessian identification and symmetry (N11e) | [Probability/Stein/HessianKernel.lean](../../formalization/FunctionalInequalities/Probability/Stein/HessianKernel.lean) | Identifies pointwise Hessian; third-derivative symmetry assumes the supplied weak tensor |
| Generator identities (2.2), N10b | [Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean) | Weak C¹/Lipschitz-gradient potential; preserved original test regularity and integrability |
| Increment estimate (N11b) | [Analysis/Convex/HessianIncrement.lean](../../formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean) | Original integrated Hessian-increment energy statement |
| Weak third derivatives (N11d) | `exists_weak_third_derivative` — [Analysis/Convex/HessianRegularity.lean](../../formalization/FunctionalInequalities/Analysis/Convex/HessianRegularity.lean); translated-cutoff support in [Cutoff/Translation.lean](../../formalization/FunctionalInequalities/Analysis/Cutoff/Translation.lean) | Given global centered-difference bound and Lipschitz exponent; produces T with compact-local L² entries |
| Close those inputs for the actual source | `secondDifference_le_of_map_gradient` — [Convex/GradientLipschitz.lean](../../formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean); `exists_lipschitzWith_neg_add_comp_gradient` — [Lipschitz/Gradient.lean](../../formalization/FunctionalInequalities/Analysis/Lipschitz/Gradient.lean); `exists_regular_moment_weak_tensor` — [CEK/MomentRegularity.lean](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean) | Exact 4/κ difference bound and 16/κ gradient bound; actual T from the original R0 source hypotheses, with every R0 field retained; no given tensor/H¹ conclusion |
| Scalar products and finite polynomials | `HasWeakDerivAlong.mul_of_memLp_two`, `.mul_of_locally_memLp_two`, `hasWeakDerivAlong_finsetSum_mul`, `hasWeakDerivAlong_finsetProd_of_locally_memLp_two` — [Analysis/WeakDerivative.lean](../../formalization/FunctionalInequalities/Analysis/WeakDerivative.lean) | One fixed direction, including zero; global-L² product rule or globally L∞ factors with compact-local L² derivatives; finite linearity needs no bounded factors |
| Weak determinant and trace quadratic | `hasWeakDerivAlong_det_of_locally_memLp_two`, `hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two` — [Analysis/Matrix/WeakDerivative.lean](../../formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean) | Bounded entries; compact-local L² directional derivatives; arbitrary real B for tr(B A B A), no symmetry/invertibility requirement; empty dimensions included |
| Determinant density = Jacobi differential | `fderiv_det_eq_sum_permutation` — [Analysis/Matrix/DeterminantDerivative.lean](../../formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean) | Every finite index type and arbitrary singular/non-Hermitian matrices; actual Hessian density det(H) tr(H⁻¹ T_k) identified a.e. by the audit client |
| Exponential and a.e. representative tools | `lipschitzOnWith_exp_Iic` — [Lipschitz/Exponential.lean](../../formalization/FunctionalInequalities/Analysis/Lipschitz/Exponential.lean); `HasWeakDerivAlong.congr_ae` — [WeakDerivative.lean](../../formalization/FunctionalInequalities/Analysis/WeakDerivative.lean); `ae_fderiv_mongeAmpere_exponent` — [WeakInverseHessian.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean) | exp is e^C-Lipschitz on (−∞, C], all real C; a.e. transport preserves weak derivatives; existing exponent formula reused |
| Actual-source first weak (2.4) | `exists_regular_moment_weak_first_derivative` — [KLS/CEK/MomentRegularity.lean](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean) | Same u, L, LF, T and every R0 field; weak determinant/log-det derivatives and a.e. tr(H⁻¹ T_k) = −∂_k u + Σ_a H_ka ∂_aW(∇u); no second evolution identity |

Here H is the actual Hessian and T_k its coordinate weak derivative. The corresponding
[source-law](../decisions/2026-10-14-r0-source-weak-tensor-integration.md),
[product](../decisions/2026-10-15-weak-product-integration.md),
[polynomial](../decisions/2026-10-15-weak-polynomial-integration.md),
[Jacobi](../decisions/2026-10-15-weak-jacobi-density-integration.md) and
[first Monge–Ampère](../decisions/2026-10-15-weak-first-monge-ampere-integration.md) records
state the complete hypotheses, placement and audit clients. Generic tools retain their own
finite-dimensional scope; actual-source producers retain n > 0 and all regular-law hypotheses.

The remaining mathematical obligations, in dependency order, are:

1. Weak inverse (2.5), weighted coefficient calculus and bounded H¹ testing. The global-L∞
   product interface above does not supply a product rule for merely locally bounded inverse entries.
2. Actual C¹/Lipschitz-gradient source-height cutoffs A.4/A.5, with locally L¹ right-hand sides
   and locally L² flux. The smooth A.4 and old N13c locally-L² right-hand-side interface do not apply;
   local L² of T gives only local L¹ of T², not a global weighted estimate.
3. The second evolution identity (2.6) and integrated energy comparison (2.14),
   E tr(BHBH) ≥ 2 E G₁. First polynomial derivatives do not supply these generator identities.
4. Actual weak Brascamp–Lieb (A.6) and mean-Hessian (Lemma 2.3) consumers, then Theorem 2.5's
   upper bound E tr(BHBH) ≤ 2 tr(B²). Existing smooth given-potential supports do not close the
   actual weak-source hypotheses.
5. Stein/H⁻¹ transport and spectral/regular-class/compact constant-8 assembly.

## Stages 2–4: existing consumers

| Stage | Lean entry and module | Retained input |
| --- | --- | --- |
| Stochastic localization | [KLS/BKL/Localization/](../../formalization/FunctionalInequalities/KLS/BKL/Localization/): `Process`, `EnergyGenerator`, `EnergyIntegral`, `CutoffInduction`, `CutoffInductionStep` | Cutoff dynamics, Dynkin/generator identities and moment induction; source-specific stochastic inputs still require the queued review |
| BKL Theorem 4.1 | `theorem41`, `theorem41Compact` — [KLS/BKL/Theorem41.lean](../../formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean) | Explicit `LetwinCompactBound` hypothesis |
| KLS assembly | `conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture` — same module; [KLS/Statement.lean](../../formalization/FunctionalInequalities/KLS/Statement.lean) and [KLS/Target.lean](../../formalization/FunctionalInequalities/KLS/Target.lean) | Exact compact bound remains open; `KLS.kls` is not proved |

Completion requires the exact source statement, a proof with standard axioms, and matching
verification evidence. Kernel replay, axiom checks, source comparison, certificate registration
and remote CI have separate scopes; see [verification](../verification.md). For the current
receipt and unintegrated scratch status, read [HANDOFF](../../HANDOFF.md).
