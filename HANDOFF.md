# Current KLS handoff

Updated 2026-10-07. This file holds the current state only; earlier versions are preserved in the
[handoff history](research/decisions/2026-10-07-handoff-history.md) and
[earlier history](research/decisions/2026-10-02-handoff-history.md), and are not current task
authorization. Exact results, scopes and certificates are in the
[paper register](research/progress/LITERATURE.md) and the [node register](research/progress/STATUS.md).

## State

- `main` = `origin/main` = `36e7c78` (BGL ergodicity and the BGL Corollary 4.8.2 certificate).
  Remote Lean certification passed for it
  ([run 37516844384](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/37516844384),
  2026-10-07).
- 28 ledger certificates. `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is the one
  intentional hole, outside every certificate closure. Dimension-free KLS is open.
- Covered papers: Ambrosio–Di Marino–Gigli Theorem 3.6 (`thm:relaxed-minkowski-content-perimeter`)
  and Bakry–Gentil–Ledoux 2014 Corollary 4.8.2 (`thm:bakry-emery-poincare`, relation `⇑`, that
  corollary only).
- **Uncommitted working tree (2026-10-07 eight-hour block):** first dependencies of
  Bizeul–Klartag–Lehec, arXiv:2610.05474v1 (pinned PDF SHA-256 `86824722…bb0db`). Execution record,
  worker provenance, Codex reviews and the final report:
  `build/reviews/2026-10-07-bkl-eight-hour/` ([dated log](research/decisions/2026-10-07-bkl-foundations.md)).
  - Lemma 2.2 (partial tensor symmetrization, `4^d`) in the source form:
    `Analysis/Tensor/{Symmetrization,Coordinate}.lean`.
  - Lemma 3.6 for scalar and tensor-valued `u ∈ 𝒜` (Mathlib `HasTemperateGrowth`) and Corollary 3.7
    (for every pair satisfying the relation (30)), both in reviewed stronger forms (relation `⇑`):
    `Analysis/BakryEmery/{Tilt,TemperateTilt,TensorTilt}.lean`.
  - (15) and (16) on `𝒜` for scalar and tensor fields, with the curvature form used in Lemma 3.4
    (`Analysis/BakryEmery/{TemperateIBP,TemperateBochner,TensorBochner}.lean`), and (48) (all `⇑`).
  - Restricted counterparts: Lemma 2.1, operator-domain inverse in the heat model
    (`Analysis/Semigroup/Generated/Inverse.lean`, `KLS/LogConcave/HeatSemigroup/Inverse.lean`); steps of
    Proposition 7.1 (linear functions; continuity of `T_d` on `L²`, also in the Hilbert–Schmidt norm)
    (`Analysis/BakryEmery/{Cumulant,SquareIntegrableTilt}.lean`).
  - Infrastructure: symmetry of iterated derivatives of `C^∞` maps (Mathlib has it only for analytic
    maps), the Leibniz rule with a linear factor, Hilbert–Schmidt coefficient arrays of multilinear
    maps (`Analysis/Tensor/{Multilinear,Coefficients}.lean`).
  - Audit client `research/audits/BKLFoundationsAudit.lean` (nonvacuity on the constructed Gaussian,
    nonzero tensors, `d = 0`, `n = 0`). No paper is newly covered.

## Next

1. Owner decision on the new BKL work: commit/push and optional remote certification (no
   authorization was extended to it).
2. BKL priority 1 (Theorem 3.1 route): Lemma 2.1 on the class `𝒜` (smooth representatives,
   pointwise equation, the tensor lift) and the first-eigenfunction facts of Section 2 (compact
   resolvent, an eigenfunction attaining `λ₁`); they construct the iterates `h_i` used by
   Lemmas 3.2–3.4 and 3.8.
3. Lemma 4.2 conditionally on the Letwin bound: a frozen candidate
   (`build/reviews/2026-10-07-bkl-eight-hour/workers/N-ThirdCumulant.frozen.lean`) has two open steps
   (the second derivative of the tilt average at `0`, and the Cauchy–Schwarz conclusion); it is not in
   the library. Theorem 4.1 needs Eldan localization; the Letwin theorem stays an explicit dependency.

## Open owner decisions

- Stochastic calculus for Theorem 4.1 and priorities 5–6: build it here or build on external Lean
  efforts; evidence and a recommendation are in
  [the options record](research/decisions/2026-10-03-stochastic-calculus-options.md).
- Commit and push of the 2026-10-07 BKL working tree.
- E. Milman Lemma 4.1 is recorded as `same`, although the real-infimum quantile differs from the
  paper's `−∞` in the degenerate case `f = 0`, `1 − ε < 0`; accept the convention or relabel it.
- Upstreaming generic infrastructure to Mathlib after an API cleanup (the `C^∞` symmetry of
  iterated derivatives is a candidate).
- CI cost: project build cache or a self-hosted runner while the repository is private.

## Delivery

Follow [research/workflow.md](research/workflow.md): select work by paper and target theorem,
run change-appropriate checks, stage canonical metadata and regenerate progress with
`python3 research/progress/update.py`. Remote CI is Lean-only, on manual dispatch or a
`milestone/**` tag.
