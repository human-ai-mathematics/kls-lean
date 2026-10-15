# Current KLS handoff

Updated 2026-10-14 at the R0 source-law tensor integration. The previous handoff is preserved byte for byte in [the pre-R0-input-closure archive](2026-10-14-pre-r0-input-closure-handoff.md); earlier ones are listed in the [decision index](README.md). Exact statements and coverage belong to the [paper register](../progress/LITERATURE.md); the main line is summarized in the [proof path](../progress/PROOF-PATH.md).

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

Still open:
- **Next:** weak local calculus and chain rules for the produced tensor;
- then weak Hessian evolution and the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H⁻¹ transport and the spectral constant-8 assembly;
- full smooth Letwin Lemma 2.2, Letwin Theorems 1.1/1.2/2.5, unconditional BKL Theorems 4.1/1.1 and KLS.

The produced tensor is weak, locally L² Hessian regularity (Hessian entries in H¹_loc). It does not establish global C² or smooth regularity, a gradient diffeomorphism, the trace estimate, Theorem 2.5, Theorem 1.2 or compact constant 8. The 30 certificates and the covered ADM-G/BGL targets retain their scopes, and no paper coverage changed.

## Evidence

- The N11d package has Codex canonical acceptance for snapshot `0e9ee967…` with the full receipt `build/verification/20261014T124002.198897Z/report.json` (`N11d-integration/codex-final/ACCEPTANCE.json`). That receipt covers only that snapshot, not this integration.
- N11d.5 and N11d.6 have independent Codex acceptance (`independent/N11d5`, `independent/N11d6`). The package passed Codex's isolated prototype (`R0-input-closure-prototype/RESULT.json`) and placement acceptance (`R0-input-closure-integration/PLACEMENT-ACCEPTANCE.json`).
- Local canonical checks passed before the documentation review. They cover the three strict owners, the aggregate and the audit `research/audits/BKL/RegularMomentWeakTensorAudit.lean`, together with five complete types, ten standard axiom reports and three kernel replays.
- For this snapshot, the Codex metadata review, a fresh full verification and Codex's canonical acceptance are pending. Their results are recorded in the ignored `R0-input-closure-integration/` reports and the Goal `STATE.json`, not in this file.

## Next action

After Codex's canonical acceptance, the next proof work is weak local calculus and chain rules for the produced tensor. Weak Hessian evolution and the integrated trace estimate follow. Each is a separately frozen contract, and none is dispatched by this integration. The Goal endpoint remains `LetwinCompactBound`.
