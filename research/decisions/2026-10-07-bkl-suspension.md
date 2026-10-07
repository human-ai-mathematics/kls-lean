# BKL Proposition 7.1: suspension

Current target: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Proposition 7.1,
pp. 28–30, with pinned PDF SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
The owner's current priority is the BKL formalization. Letwin and stochastic
analysis are prerequisites of that target, rather than independent campaigns.

## Placement and scope

- Object and role: the convex potential of the finite-copy suspension in
  equations (109)–(110), a supporting construction for Proposition 7.1.
- Scope: prove convexity from a positive Hessian lower bound on `V`, a
  uniform operator-norm bound on the Hessian of `f`, and the source's
  `beta * M / sqrt N <= a` condition; prove that a positive finite `N`
  satisfying that condition exists. This does not prove the joint-law
  identification, isotropy, (111)–(112), density or Proposition 7.1.
- Owner and destination: the existing `KLS/LogConcave` potential family,
  `KLS/LogConcave/Suspension.lean`, namespace `KLS.LogConcave.Suspension`.
  The previously decided per-paper migration remains a separate task.
- Imports: the existing `Analysis/BakryEmery/Curvature.lean` Hessian-to-convexity
  theorem and elementary convex-function tools. No stochastic dependencies.
- Decision: create a substantive suspension module; do not change existing
  curvature APIs or move modules in this task.
- API: additive potential definition and convexity/existence results; no
  compatibility aliases or changes to the already certified criterion.
- Validation: strict module compilation, an independent source-form client,
  nonvacuity including a non-affine perturbation, axiom audit, source-paper
  mapping and progress regeneration, then the applicable local verifier.

The dirty index and working tree were saved under
`build/reviews/2026-10-07-bkl-suspension/` before editing. No commit, push,
remote verification or platform submission is authorized by this task.

## Source review and accepted scope

The production theorem follows the two convex branches of the source
potential exactly and keeps `beta / sqrt N * M <= a`. The bound on `f`
uses the operator norm of its continuous bilinear Hessian. Only `C²` is
needed for convexity, rather than the source's smoothness; no mean, variance,
isotropy or probability hypotheses are needed for this step. The scale
`sigma` is arbitrary and the source's `sqrt (1 + 2 / beta²)` is an audit
specialization. The theorem additionally permits `beta = 0`; the source
uses `beta > 0`. The positive copy number is constructed separately.

The independent Lean client `research/audits/BKLSuspensionAudit.lean`
instantiates the source scale and a non-affine quadratic perturbation
`V(x) = f(x) = |x|²`, `a = M = 2`, `beta = N = 1`. The Hessian
condition is an equality. Its hypotheses concern convexity only; the
quadratic example does not assert the separate normalization (108).
Strict compilation and the printed axiom closures use only `propext`,
`Classical.choice` and `Quot.sound`.

The paper map retains Proposition 7.1 as partial and Theorem 1.1 as open.
There is no new paper-target certificate. Full verification receipts and
logs for this source snapshot are recorded under `build/verification/`;
the delivery pointer is in `build/reviews/2026-10-07-bkl-suspension/FINAL.md`.
