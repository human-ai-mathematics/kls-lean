# Approximate right inverse: Rank-deficient paths R3 (pointwise version and neighborhood-consistent version)

2026-09-17. This round **proves a new theorem**: the **`R3`** on the rank-deficiency path obligation list, pointwise and locally consistent in two versions.
Together with `R1` and `R2` from the previous round, three out of the thirteen numbered path statements have been fulfilled.
**Only `R3` is proven**; `R0`, `R4`–`R10`, `N1`, `N2` remain unproven,
the rank-deficient part of coarea dimension m is still open. This round **proves no coarea formula, no slice theorem, no Sard theorem**.
No hole migration, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260917T052110.430244Z/report.json`: 10 gates, 216 local module kernel replay,
577 entries, snapshot
`b4e02d7478fc4364645dfdd1845bd48b7ec9b678977cbaecb4717b7826093422`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## What is `R3` for?

The path slices the fiber of the regular component `v = P ∘ u`, and the chord within the fiber is not a tangent vector:
Two points in the same fiber only yield `‖Dv (b − a)‖ ≤ ε ‖b − a‖`, not `Dv (b − a) = 0`.
To make it `‖Du (b − a)‖` small, a quantitative statement is needed that "vectors almost annihilated by the surjection are close to the kernel"—
this is precisely the norm bound of a surjective right inverse.

**Neighborhood consistency is a hard requirement, not a convenience.** In Eilenberg's argument, each scale in `ε → 0` uses a *different* piecewise approximation,
constants depending on the piecewise partition are utterly useless; the bound must hold with the same constant over the entire neighborhood.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/RightInverseBound.lean`
(168 line, **only depends on Mathlib**, local import closure **1 modules**, no WIP).

* **`exists_mem_ker_norm_sub_le`** (core estimate): as long as `R` is a right inverse of `L`,
  `z − R (L z)` is annihilated by `L` and is at most `‖R‖ · ‖L z‖` away from `z`.
  **Without surjectivity, without finite dimensionality, without completeness** — only the existence of a right inverse.
* **`exists_rightInverse_bound`** (pointwise `R3`): a map `L` surjective onto a finite-dimensional space has a single constant `C`,
  Each vector is at most `C ‖L z‖` away from the kernel. Mathlib's
  `ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional` gives a continuous right inverse.
* **`rightInverse_comp_inverse`** (Perturbation Lemma): If `A ∘ R₀` is the unit of an operator ring,
  Then `R₀ ∘ (A ∘ R₀)⁻¹` is a right inverse of `A`.
* **`exists_nhds_uniform_rightInverse_bound`** (`R3` consistent version):
  Around a point of a differential surjection, there exists a neighborhood carrying the **same** `M` bound on the differential, and the **same** `C` nuclear estimate.
  The proof involves a single right inverse perturbation at a base point: `Units.isOpen` ensures it remains unit near `A ∘ R₀`.
  `NormedRing.inverse_continuousAt` gives the norm of the inverse within a neighborhood no more than `2`, hence `C = 2‖R₀‖`.

**Both statements are stronger than the route requires**: **no inner product needed**, **no requirement for finite-dimensional domain**—
the domain is an arbitrary real normed space, while the target space is finite-dimensional. In the route,
`coareaJacobian (fderiv ℝ v x₀) ≠ 0` is replaced by the surjectivity established in `coareaJacobian_ne_zero_iff`,
the inner product assumption appears only at this step of the conversion.

## What exactly is surjectivity needed for—accurately recorded, not exaggerated

* **It is the reason why a right inverse exists**: The audit's `no_right_inverse` shows that a rank-one projection on the plane **has no right inverse**, so the construction used in proof `R3` is inapplicable to it (`proj₀_not_surjective`).
* **But the pointwise version does not characterize surjectivity.** `pointwise_conclusion_does_not_imply_surjective`:
  The zero map satisfies this conclusion (take `C = 0`, every vector is already in the kernel), while the zero map to a non-zero target space is not surjective.
  **Therefore, one cannot say that 'surjectivity is necessary for `R3`'**—surjectivity is a sufficient condition for constructing a right inverse, not something forced by the conclusion.
  This round **does not** prove that "every linear map satisfies the pointwise conclusion in finite dimensions", even though that is indeed true.
* **The assumption of consistency at a base point is indeed doing work**: `uniform_constant_degenerates` shows that
  the smallest possible constant along `t • id` is `|t|⁻¹`, and it collapses when this family approaches a non-surjective `0`,
  so no neighborhood of a non-surjective point can carry a single constant.

## Boundary cases

* **Zero-dimensional target space**: Each map is surjective, `C = 0` is available, each vector is originally in the kernel (`zero_dimensional_target`).
* **Linear isomorphism**: A right inverse is an inverse (`linear_equiv`).
* **Constant map**: The differential is identically zero, and the statement is uniformly valid and trivial when the target space is zero-dimensional (`constant_map`).
* Core estimate **does not require** surjectivity (`core_needs_only_a_right_inverse`).

## What was not done in this round

* **No proof `R0`**: The rank-deficient part (intermediate rank of `m ≥ 2`) remains unchanged.
* **No proof `R4`**—the next step is it, and it is a **non-regular point**: after `R2 + R3` is in place, `R4` is self-sufficient;
  if it fails to produce or if the constant is inconsistent, the entire route is incorrect.
* No proof for `R5`–`R10`, `N1`, `N2`.
* **No proof of any coarea formula**, nor any improvement to the applicability range of the coarea of codimension m.
* **No proof of any Sard theorem**; no assertion is made regarding the measure of the critical value set.
* No modification to any existing `.lean` (including `FunctionalInequalities.lean`,
  `research/audits/RankDeficientRouteStatements.lean`, and `AreaFormulaRouteStatements.lean`,
  the latter two maintaining the original bytes); no hole migration; no expansion of certificate or Blueprint `leanok` scope;
  no new compatible alias added; no weakening of established conclusions.
* **No commit, no push**, the real Git index remains unchanged.

## Route statement file

`RankDeficientRouteStatements.lean` preserve original bytes; `R3`'s two statements are verified by the new client
`research/audits/RightInverseBoundAudit.lean` **verbatim copied and proven**
 (`route_R3_pointwise`, `route_R3_uniform`).
This round of rerun `AreaFormulaRouteStatements.lean`, **no new errors are found**.

## Verification

* The new module and new client both compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **16 axiom report** for `research/audits/RightInverseBoundAudit.lean` only uses `propext`, `Classical.choice`, and `Quot.sound`.
* Re-running all **43 existing audit clients** plus the new client, a total of **44**, all pass strictly, with 0 failures; the axiom report contains 594 entries, of which 12 entries `sorryAx` remain entirely within the four clients that intentionally report unresolved WIP results.
* Each of the three WIPs is compiled in practice, with direct proof holes **1/2/5, total 8**, unchanged; `research/check_ledger.py` issues **24** certificates.
* Default `lake build` and root directory `python3 research/verify.py` pass; the evidence JSON is
  `research/explorations/2026-09-17-right-inverse-bound.json`,
  and the final verification is saved as `build/audit/right-inverse-bound/final-snapshot.json`.
