# Current KLS handoff

Updated 2026-10-15 at the weak product integration. The previous handoff is preserved byte for byte in [the pre-weak-product archive](2026-10-15-pre-weak-product-handoff.md); earlier ones are listed in the [decision index](README.md). Exact statements and coverage belong to the [paper register](../progress/LITERATURE.md); the main line is summarized in the [proof path](../progress/PROOF-PATH.md).

## Active Goal

The owner's four-step roadmap is (1) Letwin constant 8, (2) stochastic localization, (3) BKL Theorem 4.1, (4) the KLS main theorem. Only step 1 is the active Goal ([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md); control directory `build/reviews/2026-10-14-letwin-constant-eight-goal/`).

The endpoint is a proof of the frozen `letwinCompactBound : LetwinCompactBound` through the actual regular-class producer. For every n > 0 and every compactly supported isotropic log-concave probability measure on `EuclideanSpace ℝ (Fin n)`, every self-adjoint quadratic form, singular and indefinite ones included, must have centered variance at most 8 times its squared Hilbert-Schmidt norm (Letwin arXiv:2607.24164v1, Theorem 1.2). Supports, conditional assemblies and documentation do not complete it.

Steps 2-4 are queued. The existing conditional Theorem 4.1 and KLS assembly will be re-reviewed against exact sources and evidence, not re-proved.

Roles:
- Codex owns sources, frozen contracts, dependency order, placement review and independent acceptance.
- The existing Claude session runs the existing API loop (gpt-6-astra/high, existing script and provider configuration, max_rounds 4, max_queries 6, one candidate at a time). It is the sole canonical writer after Codex acceptance.
- There is no other worker or sub-controller. The old claude-kls heartbeat stays paused, and the old eight large loops are not restarted.
- No commit, push, tag, remote CI or release is authorized for this integration. The earlier documentation checkpoint commit and push is history.

## Current mathematical state

Dimension-free KLS remains open. `KLS.kls` in `KLS/Target.lean` is the intentional hole outside certificate closures. `KLS.BKL.Localization.conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture` and `theorem41` (KLS/BKL/Theorem41.lean) hold conditionally on `LetwinCompactBound`. `letwinCompactBound_of_regularClass` reduces that bound to the smooth uniformly convex regular class, and the regular-class bound is still a premise.

Proved supports on the weak C^{1,1} route, each with its own scope:
- the bounded CEK moment-map producer and the R0 regular-class moment potential (`KLS/CEK/MomentRegularity.lean`);
- the pointwise Hessian identification and N11e weak third-derivative symmetry, which assumes a given weak tensor (`Probability/Stein/HessianKernel.lean`);
- the N10b weak generator identities of Letwin (2.2) (`Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`, `Analysis/Matrix/Piola.lean`);
- the original N11b integrated Hessian-increment energy estimate (`Analysis/Convex/HessianIncrement.lean`);
- the original N11d tensor `Analysis.exists_weak_third_derivative` (`Analysis/Convex/HessianRegularity.lean`), with its original global centered-difference and Lipschitz-exponent inputs ([N11d record](2026-10-14-n11d-weak-hessian-integration.md));
- **new:** the source-law closure of those two inputs ([R0 source-law record](2026-10-14-r0-source-weak-tensor-integration.md)):
  - the exact 4/κ centered-difference bound `Analysis.secondDifference_le_of_map_gradient` for the normalized moment map, exported from the existing proof; the unchanged 16/κ gradient theorem now consumes it (`Analysis/Convex/GradientLipschitz.lean`);
  - the generic producer `Analysis.exists_lipschitzWith_neg_add_comp_gradient` of a Lipschitz constant for −u + V(∇u), from a Lipschitz u, a Lipschitz total gradient and a C¹ V (`Analysis/Lipschitz/Gradient.lean`);
  - **the actual source-law tensor** `Analysis.exists_regular_moment_weak_tensor` (`KLS/CEK/MomentRegularity.lean`). Its hypotheses are the exact original R0 regular-source hypotheses: n > 0, compact convex K with nonempty interior, smooth W with W − (κ/2)‖·‖² convex, κ > 0, μ = 1_K e^{−W} dx probability and isotropic. It produces u, L, LF and T with all R0 fields, the global 4/κ centered-difference bound, the global Lipschitz exponent, and weak derivatives T of every Hessian entry along every coordinate direction, L² on every compact set. No given difference, exponent, tensor, H¹, trace or main-bound premise is assumed.

  For this actual regular source class, the two N11d inputs are therefore closed. The generic N11d theorem still carries its original inputs.
- **new:** weak scalar product calculus in `Analysis/WeakDerivative.lean` ([weak product record](2026-10-15-weak-product-integration.md)). Each theorem concerns weak derivatives along one fixed direction v. Both hold in every finite dimension and for every direction, with no C¹/C² regularity of the rough factors and no finite whole-space volume.
  - `HasWeakDerivAlong.mul_of_memLp_two`: if f, its weak derivative df, g and dg are all in global L², then f·g is globally integrable and has the directional weak derivative df·g + f·dg along v. Full-gradient W^{1,1} membership is not asserted.
  - `HasWeakDerivAlong.mul_of_locally_memLp_two`: if f and g are in L^∞ and df, dg are L² on every compact set, then the uncut product has weak derivative df·g + f·dg, which is L² on every compact set.
  - The audit `research/audits/BKL/WeakHessianProductAudit.lean` applies these to the actual regular source law. It produces cutoff and uncut Hessian products H_ij·H_ab and squares with compact-local L² derivatives T_kij·H_ab + H_ij·T_kab. Here T_kij is the weak derivative of H_ij along e_k, the potential's third-derivative tensor. No raw global L² of H or T is assumed.

Still open:
- **Next:** the determinant/cofactor/inverse and any other genuinely missing chain interfaces for the weak Hessian;
- then weak Hessian evolution and the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H⁻¹ transport and the spectral constant-8 assembly;
- full smooth Letwin Lemma 2.2, Letwin Theorems 1.1/1.2/2.5, unconditional BKL Theorems 4.1/1.1 and KLS.

The produced tensor is weak, locally L² Hessian regularity (Hessian entries in H¹_loc), and the new product results are weak product calculus for those entries. It does not establish global C² or smooth regularity, a gradient diffeomorphism, the trace estimate, Theorem 2.5, Theorem 1.2 or compact constant 8. The 30 certificates and the covered ADM-G/BGL targets retain their scopes, and no paper coverage changed.

## Evidence

- The parent snapshot `7db01f58…` (N11d package and R0 source-law closure) has a passing full receipt `build/verification/20261014T143611.827158Z/report.json` and Codex canonical acceptance (`R0-input-closure-integration/codex-final/ACCEPTANCE.json`). That evidence does not cover the weak product source or metadata.
- W3p1 and W3p2 have independent Codex acceptance (`independent/W3p1`, `independent/W3p2`). The combined placement passed Codex's isolated prototype (`W3-products-prototype/RESULT.json`) and placement acceptance (`W3-products-integration/PLACEMENT-ACCEPTANCE.json`). Local canonical checks passed: strict owner, aggregate and audit, eight preserved and six new complete types, six standard axiom reports, and two kernel replays.
- The weak product package's final full verification and Codex canonical acceptance are recorded in the ignored `W3-products-integration/` directory and the Goal `STATE.json`. Only a receipt for the post-integration snapshot counts for this package.

## Next action

After Codex's canonical acceptance, the next proof work is the determinant/cofactor/inverse and other genuinely missing chain interfaces for the weak Hessian. Weak Hessian evolution and the integrated trace estimate follow. Each is a separately frozen contract, and none is dispatched by this integration. The Goal endpoint remains `LetwinCompactBound`.
