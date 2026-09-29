# `prop:weighted-spectator-obstruction` and `lem:relative-perimeter-smoothing` Infrastructure Verification: Both are `missing`

Date: 2026-09-11 (Asia/Shanghai). Baseline: local `main` commit `5e5c704`, working tree containing four nodes of 2026-09-10 and the same-day `lem:conditional-fiber-form` (see [closed conditional fiber form record](2026-09-11-conditional-fiber-form.md)). Lean/Mathlib is v4.33.0, Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The user's order is to first verify `lem:conditional-fiber-form`, then verify `prop:weighted-spectator-obstruction` (expected only product exponent rule and cylinder set computation) and `lem:relative-perimeter-smoothing` (expected `missing`). The two verifications are read-only of Blueprint, internal module, and Mathlib source code, without altering mathematical state; the conclusions are written to tasks.json (`unchecked → missing`, with sources hashes and specific gaps), without entry into ledger, without certification, and without modification of Blueprint or route configuration.

## `prop:weighted-spectator-obstruction` (Blueprint Chapter 50, historically refuted weighted bundle)

Blueprint statement: For any `C, T₀, γ > 0`, `η ∈ (0, 1/2)`, `δ > 0`, there exists a balanced cylinder set in an isotropic product of centered one-sided exponential laws, with initial excess ≤ δ, but at some `0 < T ≤ T₀` the weighted excess estimate is violated `E∫₀^{T∧τ_η} e_t (1 + ‖A_t‖_op)^{5/2} dt ≤ C₂(T e₀ + T^{1+γ})`; thus `ass:weighted-package` is false under its global quantifier.

**Conclusion: `missing`.** The difference from user expectations lies in the fact that the negated proposition concerns the quantity of the random localization process along time, not just the initial data.

- The `ass:weighted-package` to be negated has no Lean statement: the Eldan random localization process `μ_t` (Brownian motion-driven tilted measure), the balanced finite perimeter cut and its excess along the process `e_t`, the weighted covariance `A_t` and its operator norm, stopping times `τ_η`, and the "paired absorbing weighted Stein-trace estimate" are undefined; the latter is not even displayed in this repository (only in upstream `modules/kls/20-eldan-statements.tex`).
- The pinned Mathlib includes only Brownian motion characterized by finite-dimensional distributions (`IsBrownianReal`, `Probability/BrownianMotion/Basic.lean`) and stopping times, hitting times (`Probability/Process/{Stopping,HittingTime}.lean`); it lacks stochastic integrals, Itô's formula, or existence and uniqueness of SDE solutions, so process quantities cannot currently be defined.
- The upstream proof file `solutions/prop-weighted-spectator-obstruction.tex` (kls-exploration) is not present in this repository; violations occur at positive times `0 < T ≤ T₀`, so computations of exponential products and cylinder sets must be rederived along the process, not just based on initial data.

Node retains upstream `proved / checked_by: agent`, not a Lean certificate; `ass:weighted-package` retains `refuted` (`excluded`).
Feasible alternatives (not executed, user decision required): first write an explicit Lean proposition for `ass:weighted-package` (abstracting process quantities as parameters or structural fields), then express the refutation as the negation of that proposition; this requires prior confirmation from upstream records on the precise definition of process quantities.

## `lem:relative-perimeter-smoothing` (Blueprint Chapter 60, Appendix A)

Blueprint statement: For each smooth region `U` (an open set, locally situated on one side of its C^∞ boundary), and `P_ρ(U) = ∫_{∂U∩Ω} ρ dH^{n−1} < ∞`,
there exists a globally smooth Lipschitz function `0 ≤ u_j ≤ 1`, `u_j → 1_U` on `L¹(ν)` and `limsup ∫‖∇u_j‖ dν ≤ P_ρ(U)`; the region and its convex hull may be unbounded.
Proof: Expand outward and smooth, control the gradient integral by comparing log-concave densities `(M/b₀)^{(1−s)/s}` with the blown-up scale of surface measure `s^{1−n}`.

**Conclusion: `missing` (as expected).**

- Smooth domains and relative perimeter `P_ρ(U)` have no Lean definition. Mathlib provides Hausdorff measure `μH[d]` and the scaling law `hausdorffMeasure_smul₀`,
  But there is no surface measure theory for C¹ hypersurfaces (area formula, local finiteness on smooth boundaries `μH[n−1]`).
- The gradient of the indicator function distribution equals the oriented surface measure (Gauss–Green) whose total variation is controlled by `P_ρ`: the Mathlib divergence theorem applies only to boxes
  (`MeasureTheory/Integral/DivergenceTheorem.lean`); no finite perimeter sets or multivariable BV functions `Analysis/BoundedVariation.lean`
  is one-dimensional).
- Convolution estimate `∫‖∇(η_ε * v_s)‖ dν ≤ s^{1−n}(M/b₀)^{(1−s)/s} P_ρ(U)`: Mathlib's convolution can differentiate with respect to smooth factors, but there is no "gradient integral ≤"
  Bound for the total variation of the other factor; on unbounded boundaries, Tonelli requires locally finite surface measure.
- Available portion: `thm:borell-logconcave-density` (`\uses`) has been certified for density representation, bilateral bounds on compact subsets, and convexity inside the support;
  The smoothed `L¹(ν)` convergence and the ν-zero measure principle of `∂U` can be obtained from it. The Kurin `KLS.Isoperimetry.boundaryContent` is the Minkowski boundary
  Content, not `P_ρ`.

Downstream `lem:relative-perimeter-cheeger-infimum`, `thm:klartag-density-frontend-identification`,
`thm:logconcave-cheeger-poincare-comparison` maintains `blocked`.

## Metadata

tasks.json Two nodes: `mathematics` unchanged (`local_argument`), `infrastructure` changed to `missing`, `mathlib_revision` is pinned as a commit,
evidence consists of the Blueprint section read, internal module, and Mathlib source code hashes, gaps are listed individually above. HANDOFF and `verification.md` each gain one sentence pointing to this record. Final verification receipt is regenerated by `python3 research/verify.py` after this record.
