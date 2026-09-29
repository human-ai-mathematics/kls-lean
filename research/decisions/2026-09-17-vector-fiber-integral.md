# m-dimensional change of variables in fiber direction

2026-09-17. This round of **proving a new theorem**, completes the **third subblock** of the m-codimensional coarea regular case:
**m-dimensional change of variables in the fiber direction**, and its direct realization—the **ambient side of the local coarea equation**.
**No coarea formula has been proven yet.**
No hole-filling, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T163322.273570Z/report.json`: 10 gates, 208 local module kernel replay,
545 entries, snapshot
`9f415ea90a30a962ef13bff80995e84f7d3d30c3110785b7f4b3752ace00370d`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## A Gap in Mathlib Must Be Fixed First

The change-of-variable formula `lintegral_image_eq_lintegral_abs_det_fderiv_mul` in Mathlib is a statement of a self-map:
`f : E → E`, volume factor `|det (f' x)|`. The fiber map `t ↦ ψ (y, t)` goes from the **level space `W`** to the **normal factor `K`**, which are both the same dimension but distinct spaces, and that determinant is not closed.

* **`lintegral_image_eq_lintegral_normDet_fderiv_mul`** (new proof in this round):
  The change-of-variables formula between two spaces of the same dimension has a volume factor of `LinearMap.normDet`—it is inherently defined between different spaces.
  The proof brings the target space back via a linear isometry: isometries preserve measure, and the determinant of its norm is `1`, so nothing is added;
  the chosen isometry **appears only in the proof and does not enter any statement**.
  `f` only needs pointwise derivatives within `s` and injectivity on `s`, with an arbitrary `ℝ≥0∞` weight function,
  **no integrability, no finiteness, no continuity assumptions**.

**The dimension assumption is not removable**: the audit `equal_dimension_necessary` provides a counterexample—
the linear map from `ℝ` to the plane restricted to the unit interval, with left-hand side `0` (image lying in a proper subspace), and right-hand side `1` (the isometric volume factor is `1`).

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/VectorFiberIntegral.lean`
 (266 line, local import closure of 18 modules, **no WIP**). It is an m-codimensional analogy of `FiberIntegral.lean`.

* **`fderiv_snd_eq`, `continuous_normDet_fderiv_snd`**: The horizontal directional derivative is the joint derivative restricted to the horizontal factor,
  Its volume factor is continuous in two coordinates (the measurability of the integrand stems from this).
* **`setLIntegral_image_vectorVerticalMap`**: **Vertical change of variables of codimension m**. For `T (y,t) = (y, ψ (y,t))`,
  On any injective Borel sheet
  `∫⁻ over T''A = ∫⁻_A normDet (Dₜψ) · f ∘ T`.
  The level space `W` and the normal factor `K` are fully distinguished throughout.
* **`splitVectorEquiv`**: Orthogonal splitting as a continuous linear equivalence, inverse is contraction of the two components, explicit.
* **`setLIntegral_image_levelGraphMap`**: change of variables for the graph map along the level family——
  Transfer the vertical change of variables, using the already-proved **measure-preserving splitting** in the upper layer, to the ambient space `V`.
* **`setLIntegral_coareaJacobian_levelGraphFamily`**: **the ambient side of the local coarea formula**.
  On any Borel slice of the level family, the ambient coarea density integrated against any weight equals
  The integral of the **graph area density** over the parameter–level domain—exactly matches the normalized area formula `B2` that has been proven and consumed.
  The substitution is the vertical substitution above, and the change of density is pointwise application of the fiber Jacobian identity from the previous round.

## m = 1 revert proven result

The audit `codimension_one_verticalMap` derives literally from the current codimension-m statement **verbatim** repository already proven
`Analysis.setLIntegral_image_verticalMap` (its own proof is a one-dimensional Jacobian theorem),
Bridges are `normDet_fderiv_eq_abs_deriv`: the one-dimensional volume factor is the absolute value of the derivative.

## What was not done in this round

* No proof of any coarea formula; the codimension-m-regular case remains incomplete.
* No proof of the weighted codimension-m-area formula (analogous to `setLIntegral_image_graphMap`) — the fiber measure in the previous round had only unit weight.
* No Tonelli composition on level variables, no countable gluing from local to global, no measurability of weighted codimension-m-slices.
* No migration of holes; no expansion of certification or Blueprint `leanok` scope; no new compatible aliases added; no weakening of established conclusions.
* No unnecessary assumptions added: no boundedness, finite volume, integrability, regular values, SFinite.
* No commit, no push; the actual Git index remains unchanged.

## Route statement verification

This round of re-execution found no new route statement errors. The two recorded issues remain `B1` and the falsified `A0`;
`A5` has consistent mismatching on both sides, thus not false.
`research/audits/AreaFormulaRouteStatements.lean` continues to preserve the original bytes.

## Remaining work (regular case of codimension m)

1. **Weighted co-dimension m graph area formula**: `setLIntegral_image_graphMap` analogy,
   promoting `B2` from "measure of the graph" to "weighted integral over the graph";
2. Tonelli on level variables, connects the ambient side of this round to the fiber side of step 1,
   yielding a local coarea formula (scalar counterpart `setLIntegral_coarea_graph_family`);
3. Countable cover + disjoint gluing, together with measurability of weighted slices of co-dimension m
   (scalar counterpart `OpenSliceMeasurable.lean`), yields
   `coarea_of_contDiffOn_of_coareaJacobian_ne_zero`.

## Verification

* The new module and new client both compile successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **16 Axiom Report** for `research/audits/VectorFiberIntegralAudit.lean` only uses `propext`, `Classical.choice`, and `Quot.sound`; includes zero-dimensional fibers, the full space (without finiteness), self-consistency checks under linear isometries preserving measure, m = 1 returning scalar vertical substitution, and counterexamples under the assumption of equal dimension.
* All **36 audit clients** are rerun (`research/audits` 29 and `build/audit` 7), all passing strictly.
* Each of the three WIPs is compiled in practice, with direct proof holes **1/2/5, total count 8**, unchanged; `research/check_ledger.py` issues 24 certificates.
* Default `lake build` and root directory `python3 research/verify.py` pass; the JSON evidence is
  `research/explorations/2026-09-17-vector-fiber-integral.json`, and the final verification is saved as
  `build/audit/vector-fiber-integral/final-snapshot.json`.
