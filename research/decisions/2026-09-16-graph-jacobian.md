# Codimension-m program, step 2 (linear layer): graph Jacobians in arbitrary codimension

2026-09-16. This round **proves new lemmas**, giving the volume factor of a graph map in arbitrary codimension and connecting the repository's proved codimension-one
`graphJacobian` to Mathlib's `normDet`. **This round proves neither the area formula nor any coarea
formula**. No holes migrated, no commit or push. Direct holes remain **8 (1/2/5)**; certificates remain **24**.

Starting point: `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`;
starting passed receipt `build/verification/20260916T124243.885687Z/report.json`: 10 gates,
kernel replay of 201 local modules, 514 entries, snapshot
`a4ae471ae89cf4112376538ba0e54b7be6baaae2e3b96bfee329c87190998cc1`.

## Boundary

The log-concave Cheeger–Buser line belongs to collaborator **Haocheng Wang** and was deliberately untouched in this round.

## Confirmed fact: the repository's area formula covers only codimension one

The graph map in `Analysis/AreaFormula.lean` is `y ↦ ι y + g y • e`, with **real-valued `g`**. Its linear model is
`graphLinear ι e a v = ι v + ⟪a, v⟫ • e`, with volume factor `graphJacobian a = √(1 + ‖a‖²)`.
This is **codimension one**. Codimension-m fibers need a `K`-valued graphing function (`dim K = m`), absent from the repository.
Thus the preceding round's plan to localize the general C¹ area formula to the existing graph formula works only for m = 1.
General m first requires a codimension-m graph model. This round supplies that layer.

## Exact results

`Analysis/GraphJacobian.lean` (local import closure of 6 modules, **no WIP**):

* `graphMapLinear ι κ A = ι + κ ∘ A`: the linear graph map for slope `A : H →L[ℝ] K` and two isometric embeddings with orthogonal ranges;
  when `K = ℝ`, it is `graphLinear`.
* **`adjoint_comp_graphMapLinear`**: the graph map's Gram operator is `1 + Aᵀ A`, **on the parameter space H**.
  Each isometry contributes an identity, and the cross terms vanish by orthogonality of the ranges.
* `normDet_graphMapLinear_sq`: `normDet² = det (1 + Aᵀ A)` (no square root or positivity argument needed).
* **`normDet_graphMapLinear`**: `normDet = √det (1 + Aᵀ A)`. This is the volume factor in **arbitrary codimension**,
  a determinant on the parameter space, **independent of the ambient embedding**.
* **`normDet_graphLinear`**: `normDet (graphLinear ι e a) = graphJacobian a`.

## Why the codimension-one identification matters

The final result identifies the repository's `graphJacobian` with Mathlib's `normDet`.
Thus **the proved codimension-one area formula is the m = 1 case of the general volume factor**; the two frameworks agree.
The proof avoids determinants: the repository's proved linear codimension-one area formula and Mathlib's linear area formula describe the scaling factor of the same map.
The volume factor of a linear map is unique (there exists a set of finite positive measure), so the two agree.
This avoids the rank-one determinant lemma.

## Work not done in this round

* **No area formula was proved**: all results concern linear maps. The nonlinear Federer area formula remains unproved.
* **No coarea formula was proved**.
* No holes migrated: direct holes remain **8 (1/2/5)**; sharp Sard, the two Cheeger comparisons, and Energy's five holes were untouched.
* No certificate or Blueprint `leanok` scope was expanded.
* **No commit or push**; the real Git index was unchanged.

## Exact next target pinned down

The end of `research/audits/GraphJacobianAudit.lean` records the next round's target with `#check`
(**proposition type checking only, not a proof**, following the same convention as `WeightedCoareaRouteStatements.lean`):

```lean
∀ {H V} [...] {g : H → V} {s : Set H}, ContDiff ℝ 1 g → Set.InjOn g s → MeasurableSet s →
  μH[finrank ℝ H] (g '' s) = ∫⁻ y in s, ENNReal.ofReal (normDet (fderiv ℝ g y))
```

This is the Federer area formula for injective C¹ parameterizations. It remains unproved and is not counted as completed in this round.

## Verification

* The new module and client compiled with `-DwarningAsError=true`, without `sorry`.
* The 11 axiom reports in `research/audits/GraphJacobianAudit.lean` use only
  `propext`, `Classical.choice`, and `Quot.sound`; boundary clients include flat graphs, codimension zero (subsingleton target),
  and zero-dimensional parameter space.
* All 28 audit clients were rerun (21 in `research/audits`, 7 in `build/audit`) and passed strictly.
* Each of the three WIP files was compiled: direct holes remain **1/2/5, totaling 8**.
* The default `lake build` and root `python3 research/verify.py` passed; evidence JSON is
  `research/explorations/2026-09-16-graph-jacobian.json`, with the final check separately saved in
  `build/audit/graph-jacobian/final-snapshot.json`.
