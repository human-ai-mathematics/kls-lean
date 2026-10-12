# BKL / Letwin Theorem 2.5 continuation goal

Created 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420` (from 2026-10-12; predecessor root thread `01a12b29-a858-7c43-9bb3-b28e3d038b05`, historical), continuing the owner-authorized Goal after the bounded
[Stage 2A goal](2026-10-11-bkl-a4-goal.md) (historical) and the file-management batch. The
[BKL primary scope](2026-10-10-bkl-primary-scope.md) and [API-first policy](2026-10-09-api-first-goal.md) continue to govern
mathematical scope and construction roles.

## Exact source objective

Letwin, arXiv:2607.24164v1, Theorem 2.5 (Section 2.1), for the regular class of Lemma A.1: for an isotropic log-concave law
with density `e^{−V}` on a bounded open convex `K`, `V` smooth and convex near `closure K`, the actual moment map `φ` and
`ν = e^{−φ} dy`, every real symmetric `B` (indefinite and singular included) satisfies
`∫ tr(B ∇²φ B ∇²φ) dν ≤ 2 tr(B²)`. It is a prerequisite of BKL arXiv:2610.05474v1 Lemma 4.2 through Letwin Theorem 1.2
(constant 8), on the chain A.4 → A.5 → Theorem 2.5 → Theorem 1.2 → BKL Lemma 4.2 → Theorems 4.1/1.1.

## Proof obligations (open unless stated)

- The actual moment map of the source law and its regularity (Lemmas 2.1–2.2): a source-law producer, not a supplied potential.
- For the actual moment-map potential of the source law: the source Hessian bound, the mean-Hessian identity (Lemma 2.3) for
  the actual moment relation, the trace evolution (2.8)–(2.10) with its nonnegative terms (formalized below for a given
  potential satisfying the Monge–Ampère relation), the noncompact integration (A.4/A.5 applied to the real trace test), the
  tensor comparison (2.12) for nonidentity `H`, and Brascamp–Lieb (A.6) for the actual potential (formalized below for a given
  potential with positive definite Hessian).
- The positive semidefinite bound from these, then the extension to all symmetric `B`.
- Already integrated supports (not completion): Stage 2A (A.4 for every source-class potential; A.5 for given cutoffs; the
  uniform-interval potential client, whose pushforward to the uniform law is not proved); the Jordan/trace-energy matrix
  algebra (`Analysis/Matrix/{Trace,Sign}.lean`); the extension step under a measure conditional on the positive
  semidefinite bound (`Analysis/Matrix/Integral.lean`). The centered range density of compact smooth diffusion images
  (`KLS/LogConcave/HeatSemigroup/Range.lean`), finite-energy Brascamp–Lieb infrastructure for A.6. Ordinary-diffusion coercivity
  and the inverse-quadratic Young inequality (`Analysis/BakryEmery/Curvature.lean`, `Analysis/Matrix/Positivity.lean`),
  further A.6 supports. The pointwise trace identity (2.8) for the actual Hessian field
  (`Analysis/BakryEmery/HessianTrace.lean`); its given-potential Monge–Ampère substitution and (2.10) are listed below, the
  trace bound remains open.
  A weak normalized convex Lipschitz primal for bounded isotropic sources (`KLS/CEK/BoundedPrimal.lean`): the gradient
  push-forward, regularity and the Monge–Ampère equation of the moment map remain open.
  Scalar Brascamp–Lieb (A.6) for a given potential with positive definite Hessian (`KLS/LogConcave/BrascampLieb.lean`,
  finite-energy C² and extended-energy C^∞ forms); A.6 for the source law needs the moment map and remains open.
  (2.9)–(2.10) with nonnegative remainders for a given potential (`Analysis/BakryEmery/HessianTrace.lean`, section
  `MongeAmpereTrace`): a pointwise condition; its A.4–A.5 integration and the source trace bound remain open.
  The pointwise first variation of the Legendre transform, CEK (42) (`Analysis/Convex/LegendreVariation/`): the integral
  Euler–Lagrange identification for the source law and the gradient push-forward remain open.

No conclusion-bearing replacement assumption, conditional or partial result completes the target. A supplied potential with
the desired moment relation is a supporting contract, not the source theorem.

## Roles and boundaries

Codex (root thread) decomposes and independently accepts; strong existing API models construct proofs (actual gpt-6-astra
high preferred; no weaker automatic fallback, provider change or blind retry of consumed requests); the original reviewed
Claude conversation is the sole canonical integrator, working in sequenced writer windows. Candidates and evidence stay in
`build/reviews/2026-10-12-bkl-letwin-t25-continuation/` until accepted and integrated. Preserve the dirty tree and the real
index; generate progress views only from task-local temporary indexes; run the full local verifier on frozen snapshots in a
clean Git environment. No commit, push, tag, remote CI or credential exposure without specific owner authorization.

## Completion

The exact source statement in Lean, standard transitive axiom closure, real source-law clients as applicable, reviewed
canonical integration, aligned English literature/progress/handoff records and a fresh full local receipt for the exact
integrated snapshot. Letwin Theorems 2.5 and 1.2, BKL and KLS remain open until their exact statements pass.
