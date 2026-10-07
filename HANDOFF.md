# Current KLS handoff

Updated 2026-10-07. This file holds the current state only; earlier versions are preserved in the
[handoff history](research/decisions/2026-10-07-handoff-history.md) and
[earlier history](research/decisions/2026-10-02-handoff-history.md), and are not current task
authorization. Exact results, scopes and certificates are in the
[paper register](research/progress/LITERATURE.md) and the [node register](research/progress/STATUS.md).

## State

- `origin/main` = `ca59365` (path-only family-directory move, on top of the two 2026-10-07 BKL commits
  and `36e7c78`, BGL ergodicity and the BGL Corollary 4.8.2 certificate). Local `main` = `b401a9f`
  (step 1 of the BKL operator route, unpushed); the Theorem 3.1 block is staged on top, uncommitted.
  Remote Lean certification passed for `36e7c78` only
  ([run 37516844384](https://github.com/numina-functional-inequalities/kls-lean/actions/runs/37516844384),
  2026-10-07); later commits are verified locally (receipts in the block evidence), not remotely.
- 29 ledger certificates (the 29th, `thm:bkl-taylor-criterion` = BKL Theorem 3.1, from the uncommitted
  2026-10-07 eight-hour block). `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is the one
  intentional hole, outside every certificate closure. Dimension-free KLS is open.
- Covered papers: Ambrosio–Di Marino–Gigli Theorem 3.6 (`thm:relaxed-minkowski-content-perimeter`)
  and Bakry–Gentil–Ledoux 2014 Corollary 4.8.2 (`thm:bakry-emery-poincare`, relation `⇑`, that
  corollary only).
- **Committed (2026-10-07 eight-hour block):** first dependencies of
  Bizeul–Klartag–Lehec, arXiv:2610.05474v1 (pinned PDF SHA-256 `86824722…bb0db`). Execution record,
  worker provenance, Codex reviews and the final report:
  `build/reviews/2026-10-07-bkl-eight-hour/` ([dated log](research/decisions/2026-10-07-bkl-foundations.md)).
  - Lemma 2.2 (partial tensor symmetrization, `4^d`) in the source form:
    `Analysis/Tensor/{Symmetrization,Coordinate}.lean`.
  - Lemma 3.6 for scalar and tensor-valued `u ∈ 𝒜` (Mathlib `HasTemperateGrowth`) and Corollary 3.7
    (for every pair satisfying the relation (30)), both in reviewed stronger forms (relation `⇑`):
    `Analysis/BakryEmery/Tilt/{Basic,Temperate,Tensor}.lean`.
  - (15) and (16) on `𝒜` for scalar and tensor fields, with the curvature form used in Lemma 3.4
    (`Analysis/BakryEmery/{IntegrationByParts,Bochner}/Temperate.lean`, `Analysis/BakryEmery/Bochner/Tensor.lean`), and (48) (all `⇑`).
  - Restricted counterparts: Lemma 2.1, operator-domain inverse in the heat model
    (`Analysis/Semigroup/Generated/Inverse.lean`, `KLS/LogConcave/HeatSemigroup/Inverse.lean`); steps of
    Proposition 7.1 (linear functions; continuity of `T_d` on `L²`, also in the Hilbert–Schmidt norm)
    (`Analysis/BakryEmery/Cumulant.lean`, `Analysis/BakryEmery/Tilt/SquareIntegrable.lean`).
  - Infrastructure: symmetry of iterated derivatives of `C^∞` maps (Mathlib has it only for analytic
    maps), the Leibniz rule with a linear factor, Hilbert–Schmidt coefficient arrays of multilinear
    maps (`Analysis/Tensor/{Multilinear,Coefficients}.lean`).
  - Audit client `research/audits/BKLFoundationsAudit.lean` (nonvacuity on the constructed Gaussian,
    nonzero tensors, `d = 0`, `n = 0`). No paper is newly covered.
- **Committed (2026-10-07 four-hour block, on top of the above):** evidence in
  `build/reviews/2026-10-07-bkl-four-hour/` ([dated log](research/decisions/2026-10-07-bkl-four-hour.md)).
  - Lemma 4.2 conditionally on the Letwin bound (`LetwinQuadraticBound`, an explicit premise) for
    centered isotropic laws with all exponential moments, relation partial
    (`Analysis/BakryEmery/Cumulant.lean`); the uniform law on `[−√3, √3]` and a skewed two-point law
    (`κ₃ = 3/2`) discharge every premise (`research/audits/BKLThirdCumulantWitnessAudit.lean`).
  - Regular potentials (12): `KLS.RegularPotential` derives the probability normalization, Gaussian
    tails, all exponential moments and growth of `∇V`; the tensor Lemma 3.6, curvature form of (16) and
    Lemma 2.1 (operator domain, `C = 1/a`, also componentwise) hold for regular laws
    (`KLS/LogConcave/Regular.lean`).
  - Lemmas 3.2–3.4 (3.3 for `q = 2` only), Corollary 3.5, (35)–(36) and steps of Lemma 3.9 as
    partial counterparts for supplied iterates: (39), (46), (47) and (45) for every pair satisfying
    (30) and (33), summability and `v_N → 0` for sequences of tensor iterates, the energy drops
    `v_i − v_{i+1} = ‖∫∇h_i‖²`, the near-symmetric gradient under `α² ≥ λ > 0`, (61), and
    `p₁ ≤ λ²K` for a centered eigenfunction (`Analysis/BakryEmery/TensorEnergy.lean`).
  - Lemma 2.1, componentwise tensor lift (operator domain) with Parseval in `L²(ν; G)`
    (`L2/Components.lean`, `KLS/LogConcave/HeatSemigroup/Inverse.lean`).
  - Lemma 2.1 on `𝒜`, bridge part: temperate functions lie in the generator domain with
    `A[f] = [−ℒf]`, so a centered temperate solution is the operator-domain inverse; Poincaré on `𝒜`,
    `‖∇h‖² ≤ C‖ℒh‖²`, the source's (32), and Lemmas 3.2 and 3.3 (`q = 2`) with the bound `C χ` for
    supplied pairs, `C ≥ C_P` (`KLS/LogConcave/HeatSemigroup/Temperate.lean`).
  - Audit client `research/audits/BKLRegularLawAudit.lean` (the scaled Gaussian as a regular
    potential; consumers of every new endpoint, including a sharp instance of the `p₁` bound).

## Next

1. Owner decision: optional remote Lean certification of the BKL commits (manual dispatch or a
   `milestone/**` tag); no BKL paper target is covered, so no milestone is due.
2. **BKL Theorem 3.1 is certified** (`thm:bkl-taylor-criterion`, `solutions/ThmBklTaylorCriterion.lean`,
   uncommitted; block record `build/reviews/2026-10-07-bkl-operator-route/`): the exact source statement,
   proved by the operator route (iterates in `D(A)`, `KLS/LogConcave/HeatSemigroup/PoissonIterate/`;
   approximate eigenfunction). Next for Theorem 1.1: Theorem 4.1 (Eldan localization; stochastic
   calculus decision below), Proposition 7.1 (suspension), the regular approximation; the Letwin theorem
   stays an explicit dependency of Lemma 4.2. Nonvacuity: dimension 0 and the standard Gaussian on `ℝ¹`
   (R = 8, `KLS/LogConcave/GaussianTaylor.lean`).
3. Owner decision recorded below: per-paper folders after this block.

## Decided, pending execution

- Per-paper folders (owner, 2026-10-07): after the current BKL block, move audit clients and route
  statements to `research/audits/{BKL,Letwin,SongZhang}/` and paper-specific library modules (the
  BKL Poisson iterates, Lemmas 3.2–3.9, Theorem 3.1) to a per-paper folder such as `KLS/BKL/`;
  generic tools stay in their object families. Amend `research/naming.md` rule 5 and record a
  module map; path-only migration with full verification.

## Open owner decisions

- Stochastic calculus for Theorem 4.1 and priorities 5–6: build it here or build on external Lean
  efforts; evidence and a recommendation are in
  [the options record](research/decisions/2026-10-03-stochastic-calculus-options.md).
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
