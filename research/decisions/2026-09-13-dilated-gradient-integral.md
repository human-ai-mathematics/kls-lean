# Weighted Gradient Integral Bound for Outer Blunt Smoothing

Date: 2026-09-13. Taking over [pointwise gradient bound record](2026-09-13-mollified-gradient-bound.md).
Starting HEAD is `2965b32`; the 368 files passed in the previous verification receipt match all files in the current snapshot.
Retaining prior uncommitted and untracked results; no commit or push in this round; historical decision records are not rewritten.

## Goals and Scope

`KLS.RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le` proven and from WIP
Migrate into `formalization/FunctionalInequalities/KLS/Geometry/RelativePerimeter.lean`.
The statement text is consistent with the original target, including `hr`, internal closed balls, lower bound of positive density, global upper bound of density, `0<s<1`,
bump radius condition and Lebesgue volume benchmark; namespace and declaration names are retained, with no compatibility aliases.

For `H(y)=a+(y-a)/s`, `η=φ.normed volume`, `n=finrank ℝ V`, `Ω=interior ν.support`,

```
∫ ‖∇(η⋆1_{H(U)})‖ dν ≤ s^(1-n) (M/b₀)^((1-s)/s) relativePerimeter ρ Ω U.
```

No boundedness requirement for domains or carriers, no finite total boundary measure, and **no requirement for finite relative perimeter**; the right-hand side is allowed to be infinite.
Zero-dimensional case preserved. No coarea, Sard, Cheeger infimum, or general singular law comparisons are assumed as premises.
This round reduces direct proof holes from 18 to **17**: RelativePerimeter **1**, AnalyticPrerequisites **3**,
CheegerInfimum **8**, Energy/WIP/Cheeger **5**. Certification remains **24**, the infrastructure for relative perimeter chains remains `missing`; `exists_smooth_recovery_sequence` is the only remaining proof hole in this module.

## Actual proof

1. **Normalization of boundary measures change of variables.** New module `Geometry/SurfaceHomothety.lean` from Mathlib
   `map_homothety_hausdorffMeasure` obtains `map_inv_homothety_surfaceMeasure`:
   `map H⁻¹ σ = |c|^(n-1) • σ`, here `H` is a homothety with ratio c, and the exponent is first used as a natural number `n-1`.
   The normalization constant is preserved under scalar actions, without replacing `surfaceMeasure` with the unnormalized Hausdorff.
   `setLIntegral_image_homothety_surfaceMeasure` Using inverse homeomorphism, `setLIntegral_map` and measurability of functions
   Obtain a change of variables on any measurable set and any measurable ENNReal weights; without the assumption of finite integrability.
   `SmoothDomain.setLIntegral_frontier_homothety` applies this to the frontier.
   This resolves the gap in the original `hausdorff_frontier_homothety` which could only compare total masses and could not perform change of variables for weighted integrals.
2. **Zero contribution outside Ω.** `IsBorellDensity.interior_pos_subset` proof
   `interior {ρ>0} ⊆ interior ν.support`. No need for continuity: any point lying inside the positivity set
   Every small open neighborhood O has positive Haar measure; `withDensity_apply` and `setLIntegral_pos_iff` give `ν(O)>0`,
   Hence all these points lie within the support, and openness further provides the interior of the support. Combined with the already proven `interior_support_subset`.
   When `η(x-H(y))≠0`, set `z=x-H(y)`, `b=a-s/(1-s)•z`. The radius condition places b inside the closed ball,
   and `y=s•x+(1-s)•b`. If `ρ(x)>0`, `convex_pos.combo_self_interior_mem_interior`
   Let y lie in the interior of the positivity set, and then by the new inclusion we obtain `y∈Ω`.
   Thus, when y is not in Ω, the product of the kernel and the density is indeed zero; there is no direct elimination `∂U\Ω`.
3. **Nuclear average weight.** `RelativePerimeter.lintegral_normed_mul_density_le` uses the previous step,
   Existing `IsBorellDensity.le_rpow_mul_of_combination`, nuclear non-negativity, translation invariance, and normalization
   `φ.integral_normed`, given
   `A(H(y)) ≤ ofReal((M/b₀)^((1-s)/s)) * 1_Ω(y) ofReal(ρ(y))`,
   Among which `A(q)=∫⁻x ofReal(η(x-q)) ofReal(ρ(x)) dx`.
   The real/ENNReal conversion of nuclear integrals uses actual `φ.integrable_normed` and non-negativity.
4. **Tonelli gluing.** For an outer extended domain W, let `σ=(surfaceMeasure V).restrict (frontier W.carrier)`.
   By the established boundary local finiteness, establish an instance, second countability gives σ-finiteness. The joint measurability of continuous kernels gives
   Tonelli's assumption; the density rewrite is only for integrals over kernels, no need to assume integrability of the gradient.
   After pointwise gradient bound integration, swap ν and σ, then use `hρ.withDensity_eq` to replace the inner integral with A.
   The measurability of A is obtained from the measurability of the product integrand and `Measurable.lintegral_prod_left`.
   After applying boundary substitution and kernel averaging estimation, the indicator strictly restricts the boundary integral to `frontier U ∩ Ω`.
5. **Exponent and zero-dimensional.** `n>0` at time `Nat.cast_sub` aligns the exponent, transforming `|s⁻¹|^(n-1)` into `s^(1-n)`.
   `n=0` at finite-dimensional zero-dimensional case yields `Subsingleton V`, the outer expansion frontier is empty, and the pointwise bound already integrated
   Set the left side to zero. Do not use incorrect real exponent substitutions for `n=0`.
   `hr` and the density lower bound at the closed-ball center give `M>0`, supplying nonnegativity when combining ENNReal coefficients.

## Layering, Migration, and Consumers

* `Geometry/SmoothDomain.lean` Publicly expose the only existing `homothetyHomeomorph` and two coercion theorems,
  add `frontier_homothety`, and replace the existing total boundary scaling lemma with it; do not copy the homeomorphism definition.
* `Geometry/SurfaceHomothety.lean` is a new weighted pullback layer with no holes, depending only on the smooth domain foundation.
* `LogConcave/DensityBounds.lean` migrates into the original WIP's `exists_le`, `le_rpow_mul_of_combination`, and their original private auxiliary proofs, and adds the above positivity interior inclusion.
  It only imports `BorellRepresentation`, without importing domain, perimeter, or WIP.
* `Geometry/RelativePerimeter.lean` migrates into `relativePerimeter`, the empty boundary zero perimeter interface, `tendsto_indicator_homothety`, and places a kernel average bound and current round goal; imports DensityBounds, SurfaceHomothety, MollifiedBoundary. Its transitive local imports are closed under **29 modules, zero WIP import**.
* `WIP/RelativePerimeter.lean` directly imports the new module, retaining only the original recovery sequence goal.
  `WIP/CheegerInfimum` still requires a recovery sequence, so continuing to import this WIP application layer is intentional.
  Each original name has one declaration site, with no forward declarations or compatibility aliases.

## Verification

* New goals, weighted transfer, density inclusion, and the transitive axioms of already migrated key theorems are all
  `propext / Classical.choice / Quot.sound`, without `sorryAx`.
* Ten related hole-free modules are directly compiled via `lake env lean -DwarningAsError=true`.
  Independent `build/audit/DilationAudit.lean` includes 7 clients and 17 axiom reports: the average of the outer core Ω is exactly zero;
  zero perimeter yields zero gradient integral; finite relative perimeter yields finite gradient integral without requiring finite total boundary; for three-dimensional scale 2, the weighted surface area integral coefficient is 4; for one-dimensional negative scale -2, the boundary weight coefficient is 1; zero-dimensional space; for one-dimensional s=1/2, the complete gradient integral coefficient is exactly `M/b₀`.
  The 22 reports from the Gauss-Green clients are also re-run, preserving symbol, half-space, and interval endpoint checks.
* Four WIP files are actually recompiled in ordinary mode; expected diagnosis is **1/3/8/5** direct proof holes, still not passing strict mode.
* After default `lake build` and root directory `python3 research/verify.py` are completed, `build/verification/latest.json` is issued as the final source code verification receipt; infrastructure evidence hash is synchronized and refreshed.
  Detailed strict check logs are available at `build/audit/dilation-*`.

Verification is local compilation, axiom auditing, and local kernel replay under a fixed third-party compiler dependency, not remote CI.

## Next step: work remaining to be done in restoring the sequence

The only remaining goal is `RelativePerimeter.exists_smooth_recovery_sequence`, with the original assumption of finite relative perimeter preserved. Now the gradient budget is in place, and the next step is to select parameters and prove convergence:

1. From a general IsBorellDensity, obtain a point and an internal closed ball in Ω, use `exists_bounds_of_isCompact` to obtain `b₀>0`, and use the migrated `exists_le` to obtain M.
`DensityBounds` already has a private `nonempty_interior_pos`, combined with the current round's `interior_pos_subset` yields that Ω is non-empty; if a subsequent consumer needs this interface, they should publish/migrate the unique existing proof, without repeating the proof.

2. Fix `0<s<1`, prove that the smoothing of the outer expansion indicator converges to `L¹(ν)` as the bump radius tends to zero.
For smooth domains, this can directly use the local constancy of the frontier external indicator and `ContDiffBump.normed_convolution_eq_right` to establish final equality; no need to reprove the Lebesgue differentiation theorem.
The convolution order is aligned with the publicly available `mollifiedIndicator_eq` and the commutative law.
Using the absolute continuity derived from `addHaar_frontier` and `withDensity_eq` gives ν-a.e. outside the boundary, further apply `[0,1]` and the probability measure to perform dominated convergence. Do not assume the indicator is integrable over the full space volume.

3. Take `s_j↑1`, reuse `tendsto_indicator_homothety`; select ε_j by index j, simultaneously satisfying `s_j ε_j/(1-s_j)<r` and the smoothing error tending to zero, and combine the outer expansion and smoothing errors using the triangle inequality in L¹.

4. Use the established smooth/Lipschitz/`[0,1]` interface to provide regularity for each term. Prove that the budget coefficient tends to 1, and combine the current step bound with the assumption of finite relative perimeter to obtain an ENNReal limsup bound, including the case of zero perimeter.

These steps still do not require coarea or Sard. The recovery sequence has not been proven, therefore the entire relative perimeter chain cannot be registered.
