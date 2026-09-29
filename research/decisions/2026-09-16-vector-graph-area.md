# B1 completion: the C¹ graph area formula in codimension m

2026-09-16. This round **proves new theorems**, completing the fifth stage of obligation **B1**.
**The codimension-m C¹ graph area formula is proved with both raw and normalized measures.**
No hole migration, commit, or push. Direct holes remain **8 (1/2/5)**; certificates remain **24**.

Starting point: `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; starting passed receipt:
`build/verification/20260916T144943.423764Z/report.json`: 10 gates, 205 local modules replayed by the kernel,
533 entries.

## Boundary

The log-concave Cheeger–Buser line belongs to collaborator **Haocheng Wang** and was untouched.

## Exact results

`Analysis/VectorGraphArea.lean` (10 modules in its local import closure, **no WIP**):

* **`hausdorffMeasure_image_vectorGraphMap`**:
  `μH[k] (graph '' s) = ∫⁻ y in s, ofReal (normDet (graphMapLinear ι κ (Dγ y))) ∂μH[k]`.
* **`hausdorffNormalized_image_vectorGraphMap`**: the normalized version, integrating against **Lebesgue measure** on the right.
  This is the version needed by the codimension-m coarea program.

Only measurability of `s` is required: **no finite-measure, boundedness, or injectivity assumption**; the graph map is injective by construction.

## A genuine obstacle absent in codimension one

The codimension-one proof uses the fact that the Jacobian `√(1+‖a‖²)` is **globally 1-Lipschitz** in the slope,
so close derivatives imply close Jacobians. In **codimension m, `√det(1+AᵀA)` is not uniformly Lipschitz**:
on a two-dimensional parameter space, `A = t·id` gives growth like `1+t²`, with derivative unbounded in `t`.

The preceding partition was therefore insufficient. This round makes the partition **control the Jacobian directly**
via `exists_approximating_partition_with_jacobian`, using Jacobian continuity (the preceding A1 result,
through `continuous_graphMapLinear_normDet`). The rest follows the codimension-one structure.
The limit lemmas `tendsto_aux` and `tendsto_aux'` do not depend on the graph and are **reused unchanged, without reproving them**.

## An error in route statement B1 that must be recorded

The **B1 statement from the preceding route exploration is false**: it pairs **raw** `μH[k]` on the left with
**Lebesgue** measure on the right. They differ by a normalization constant:
`Analysis.hausdorffMeasure_finrank_eq_smul_volume` gives `μH[k] = (2^k/ω_k) • volume`, whereas
`2^k = ω_k` only for `k ≤ 1` (`ω_0=1`, `ω_1=2`). **The literal statement is therefore false for `k ≥ 2`**;
it is not the statement proved this round.

Both correct pairings are proved and audited:

* `corrected_B1`: raw with raw (`μH` with `μH`);
* `route_B2`: normalized with Lebesgue. **B2 was stated correctly in the route** and is fulfilled verbatim.

Following the convention of preserving historical evidence, `research/audits/AreaFormulaRouteStatements.lean`
**keeps its original bytes**. The correction is recorded here and in `research/audits/VectorGraphAreaAudit.lean`.

## Scope of this result

This is an area formula for **graphs**. It is **not** the Federer area formula `A0` for arbitrary injective C¹ parametrizations;
that result and `A2`–`A5` remain open. The route recommended the graph version precisely because graph maps are injective
by construction and have an explicit left inverse.

## Work excluded from this round

* No proof of `A0`, `A2`–`A5`, or any coarea formula.
* No hole migration; sharp Sard, the two Cheeger comparisons, and the five Energy holes are untouched.
* No expansion of certificate or Blueprint `leanok` scope.
* **No commit or push**; the real Git index is unchanged.

## Program status and next step

Completed in the codimension-m coarea program: the coarea Jacobian, linear area formula and affine fibers,
graph Jacobian in arbitrary codimension, A1, and **B1/B2 graph area formulas**.
Next is the **regular case** of codimension-m coarea (analogous to scalar L9): on the open set where
`coareaJacobian ≠ 0`, use a parametric implicit function theorem to represent fibers as a family of graphs,
then apply B2 from this round.

## Validation

* The new module and client compile with `-DwarningAsError=true`, without `sorry`.
* The 10 axiom reports in `research/audits/VectorGraphAreaAudit.lean` use only
  `propext`, `Classical.choice`, and `Quot.sound`; cases include the whole space (without finiteness) and zero-dimensional parameter spaces.
* All 33 audit clients were rerun (26 in `research/audits`, 7 in `build/audit`) and passed strict checks.
* The three WIP files were compiled separately: direct holes remain **1/2/5, total 8**.
* Default `lake build` and root-level `python3 research/verify.py` pass. Evidence JSON:
  `research/explorations/2026-09-16-vector-graph-area.json`; final snapshot check:
  `build/audit/vector-graph-area/final-snapshot.json`.
