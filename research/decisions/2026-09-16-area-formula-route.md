# Exploration of a Nonlinear Area Formula Path

2026-09-16. This round only performs route exploration: **no new theorems are proven, no modifications to any `.lean` library source code are made**, no hole migration, no commit, no push. Direct proof holes remain **8 (1/2/5)**, certification remains **24**.
New files include only this decision, one file containing only a **`#check`** statement, and a JSON evidence file.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T132852.139911Z/report.json`: 10 gates, 202 local module kernel replay,
518 entries, snapshot `8b8056f523c6324ccac139eb21d90c844d27d3ecb068625966e8c2f3c970bc52`.

## Boundary

The log-concave Cheeger–Buser line belongs to collaborator **Haocheng Wang** and is untouched this round.

## Judgments and Recommendations

**Goal A0** (injective C¹ parametrized Federer area formula) **cannot be completed in one round on the current library**,
and following the textbook general route encounters a specific obstruction. **We recommend instead taking the route B1**,
i.e., first prove the area formula for the graph of codimension m, then reduce the general case to this local graph case.

The reason is that repository has already traversed the co-dimension one via the graph route with a complete toolchain, while the general path is missing exactly the piece that Mathlib does not provide.

## Obstacle Localization (General Route Alpha)

The textbook approach is: use `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` to partition the domain into countably many pieces, on each piece `g` differs from some fixed linear `A` by ε, then squeeze between the two sides of `A`. The piecewise lemma exists in Mathlib and has the exact form, and moreover guarantees that each `A n` is indeed a differential at some point.

**Exact barrier at the lower bound of squeezing.** Mathlib's `ApproximatesLinearOn.antilipschitz` signature requires a linear model
is `f' : E ≃L[𝕜] F`, i.e. **continuous linear equivalence**, i.e. **same dimension**. When dimension is reduced, `fderiv g y : H →L V` is injective
But not equivalent, this lemma is not usable. A usable alternative is
`ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`,  but it only gives
`∃ K, AntilipschitzWith K f`, the constant is attained by `Classical.choose`, and **does not possess** the required squeezing property.
A quantitative control of the constant as ε tends to the reciprocal of `normDet A`. Completing this step has to be done independently.
Argument of "value range decomposition `A = incl ∘ A₀`, projecting `g` onto `range A`, then controlling the orthogonal components"
This is exactly A3, estimated rows 250–500, high risk.

Mathlib has no area formula for dimension reduction (full library search for "area formula" yields no hits),
and has no `normDet` continuity, so the measurability of the integrand A1 is also a genuine obligation.

## Why graph paths are more feasible

The graph map `y ↦ ι y + κ (γ y)` has two good properties that generally do not hold:

1. **Natural injection**, no `InjOn` assumption required, and no multiplicity handling needed;
2. **Has an explicit left inverse**: the parameter projection `ιᵀ` satisfies `ιᵀ ∘ graphMap = id`,
thus the quantitative lower bound missing in A3 can be directly computed, without going through `Classical.choose`.

The volume factor was ready prior to this round: `Analysis.normDet_graphMapLinear` given
`√det (1 + Aᵀ A)`, and `Analysis.normDet_graphLinear` proves that it reduces to the repository’s `graphJacobian` in codimension one. The normalization ledger of fiber measures is given by `KLS.hausdorffNormalized_fiber`.

**Cost anchor**: repository proves the co-dimension one graph area formula using `Analysis/AreaFormula.lean` **957 lines**,
accompanied by `Analysis/ImplicitGraph.lean` **859 lines**. The analogy for co-dimension m will not be cheaper.

## List of required lemmas

The number of lines is an approximate count of new Lean proofs, excluding reused modules, and does not represent fulfillment of commitments.
All precise Lean statements are in `research/audits/AreaFormulaRouteStatements.lean`,
this file contains **only `#check`**, with no declarations, no proofs, no placeholder axioms, and compiles successfully with `-DwarningAsError=true`.

| Number | Content | Exists in Mathlib | Estimated lines | Risk |
|---|---|---|---:|---|
| A0 | Goal: Area formula for injective C¹ parametrizations | **None** | — | — |
| A1 | `normDet` continuous, hence the integrand is measurable | **none** (`measurable_fderiv` has) | 60–120 | Medium |
| A2 | Countable additivity on the image (requires `InjOn` and measurability of the image) | None | 80–160 | Medium |
| A3 | Sandwiching of injective linear models | None; `ApproximatesLinearOn.antilipschitz` requires equivalent dimensionality, not applicable | 250–500 | High |
| A4 | image of the differentiable non-injective part has zero measure | none | 100–200 | Medium |
| A5 | Local area formula assembled into global | None | 80–160 | Medium |
| B1 | **m-codimensional graph area formula** (recommended focus) | None; the repository has proved the codimension-one version and can serve as a template | 600–1000 | High |
| B2 | Normalized version of B1 `hausdorffNormalized` | None; constant elimination pattern already present in this round | 20–40 | Low |

Following the B route still requires A1, A2, A5; A3, A4 can be avoided or greatly simplified—explicit left inverses of the graph map, and the differential of the graph map is always injective, so A4 does not appear in the B route.

## Phased Recommendations

1. **Preparation of A1 + B2**: `normDet` continuity and measurability, purely algebraic/topological, preliminary and low-risk.
2. **Main focus of B1**: Construct the codimension m version following the structure of `Analysis/AreaFormula.lean`, planned over 2–3 rounds.
3. **A5 + A2**: Gluing from local to global and additivity on the image side.
4. Then return to the regular case of codimension m coarea.

**Not recommended** to fill in A3 now. It is a critical gap in the general route, but the B route can bypass it;
if in the future a general C¹ injective mapping area formula is actually needed, then treat it as a separate item.

## This round explicitly did not do

* **No theorem has been proven**, nor has any of the above statements been marked as completed.
* No modifications have been made to any `.lean` library source code; `research/audits/AreaFormulaRouteStatements.lean` is
  **containing only `#check`** and is not a proof.
* No holes have been migrated, no expansion of certification or Blueprint `leanok` scope has occurred.
* **No commit, no push**, the real Git index has not been changed.

## Verification

* `research/audits/AreaFormulaRouteStatements.lean` compiles with `-DwarningAsError=true`, all nine statements pass type checking; the axiom audit for new results is empty (**no new results were added in this round**), not "proven area formula".
* Re-runs all 29 audit clients (`research/audits` 22, `build/audit` 7), all strictly pass, with no modifications.
* Each of the three WIPs compiles directly, direct proof hole **1/2/5, total 8**, unchanged.
* Default `lake build` and root directory `python3 research/verify.py` pass; JSON evidence is
  `research/explorations/2026-09-16-area-formula-route.json`, final verification saved
  `build/audit/area-formula-route/final-snapshot.json`.
