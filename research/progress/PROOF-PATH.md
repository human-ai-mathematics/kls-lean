# Proof path to KLS through BKL

This is a reading guide to the owner-selected main line. It names the exact Lean interfaces and the
explicit inputs at each stage. It is navigation only: proof status, coverage and certificates are
recorded in the [literature register](LITERATURE.md), the [BKL main proof chain](README.md#bkl-main-proof-chain),
the [node register](STATUS.md) and the [current handoff](../../HANDOFF.md); evidence and its scope are
described in the [verification guide](../verification.md). Nothing here adds a status, a certificate
or a logical edge. **Dimension-free KLS remains open.**

The four stages are, in order: (1) Letwin's constant 8, (2) stochastic localization, (3) BKL
Theorem 4.1, (4) the KLS main theorem. Only stage 1 is the active Goal; stages 2-4 are queued for
re-review of their sources and verification receipts, and their existing conditional assembly is
reused rather than re-proved.

## Stage 1: Letwin's constant 8 for compactly supported laws (active)

- Source: Letwin, arXiv:2607.24164v1, Theorem 1.2 (through Theorem 2.5), consumed by BKL
  arXiv:2610.05474v1, Lemma 4.2.
- Exact current input: `FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound`
  in [KLS/BKL/CompactReduction.lean](../../formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean).
  It is a proposition, not a theorem: for every `n > 0` and every compactly supported isotropic
  log-concave probability measure on `EuclideanSpace ℝ (Fin n)`, every self-adjoint quadratic form,
  singular and indefinite ones included, has centered variance at most `8` times its squared
  Hilbert-Schmidt norm.
- Goal endpoint: the frozen statement `letwinCompactBound : LetwinCompactBound`. It is **not** a
  proved canonical declaration.
- Proved reduction: `letwinCompactBound_of_regularClass` in
  [KLS/BKL/LetwinApproximation.lean](../../formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean)
  reduces the compact bound to laws `1_K e^{-W} dx` with compact convex `K` and smooth uniformly
  convex `W`. The regular-class bound remains an explicit premise.

Supports proved on the weak C^{1,1} route (each with its own scope; none proves the stage):

| Support | Lean owner |
| --- | --- |
| R0: regular-class moment potential (C^1, Lipschitz gradient, a.e. Monge-Ampere data) | [KLS/CEK/MomentRegularity.lean](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean) |
| Pointwise Hessian identification; N11e weak third-derivative symmetry (assumes the weak tensor) | [Probability/Stein/HessianKernel.lean](../../formalization/FunctionalInequalities/Probability/Stein/HessianKernel.lean) |
| N10b: weak generator identities (Letwin (2.2)) and their integrability | [Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean) |
| N11b: integrated Hessian-increment energy estimate | [Analysis/Convex/HessianIncrement.lean](../../formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean) |

Next actual obligation: N11d, the actual local `L²` weak third derivatives of the Hessian
entries. N11e only consumes such a tensor, and `C^1` never implies `C^2`. Then local `H¹` and
chain-rule bridges, weak Hessian evolution and the integrated trace estimate, weak
Brascamp-Lieb, Stein/`H^{-1}` transport and the spectral constant-8 assembly.

## Stage 2: stochastic localization (queued)

The Eldan localization family is in
[KLS/BKL/Localization/](../../formalization/FunctionalInequalities/KLS/BKL/Localization/): the
cutoff process and its Dynkin identity (`Process.lean`), the cumulant and energy generators,
Lemma 5.1 in generator form (`EnergyGenerator.lean`), Lemma 5.2 in cutoff form
(`EnergyIntegral.lean`), Lyapunov moments and the induction (`CutoffInduction.lean`,
`CutoffInductionStep.lean`). This stage will be re-reviewed against its source-specific
stochastic inputs before any completion claim.

## Stage 3: BKL Theorem 4.1 (queued)

`theorem41` and `theorem41Compact` in
[KLS/BKL/Theorem41.lean](../../formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean)
prove the all-order cumulant bound, conditionally: both take `LetwinCompactBound` as an explicit
hypothesis. The unconditional source theorem is open.

## Stage 4: the KLS main theorem (queued)

`conjecture_of_letwinCompact : LetwinCompactBound → KLS.Conjecture` in the same file composes
Theorem 4.1 with the certified Taylor/suspension reduction. The statement `KLS.Conjecture` is in
[KLS/Statement.lean](../../formalization/FunctionalInequalities/KLS/Statement.lean); the
intentional open target `KLS.kls` is in
[KLS/Target.lean](../../formalization/FunctionalInequalities/KLS/Target.lean) and stays outside
every certificate closure.

## How to read status

- A stage is complete only when its exact statement is proved in Lean with standard axioms and
  recorded with verification evidence; see [AGENTS.md](../../AGENTS.md) for the coverage rule.
- Conditional theorems and supports do not complete a stage, a paper or KLS.
- For current evidence (receipts, acceptance records) read the [handoff](../../HANDOFF.md).
