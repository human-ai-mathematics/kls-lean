# B1, stage four: two-sided sandwich estimates for vector-valued graphs

2026-09-16. This round **proves new lemmas**, completing **stage four** of the codimension-m graph area formula (obligation **B1**),
plus the approximation partition needed for stage five. **The area formula itself remains unproved.**
No holes migrated, no commit or push. Direct holes remain **8 (1/2/5)**; certificates remain **24**.

Starting point: `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; starting passed receipt
`build/verification/20260916T143055.790878Z/report.json`: 10 gates, kernel replay of 204 local modules,
529 entries.

## Boundary

The log-concave Cheeger–Buser line belongs to collaborator **Haocheng Wang** and was untouched in this round.

## Exact results

`Analysis/VectorGraphSandwich.lean` (local import closure of 9 modules, **no WIP**):

* **`norm_add_sq_of_perp`**: `‖ι y + κ z‖² = ‖y‖² + ‖z‖²`. The two embeddings have orthogonal ranges,
  giving the Pythagorean identity across the factors. This is the common basis of all estimates in this round.
* `norm_sub_vectorGraphMap_sq`, **`norm_sub_le_norm_sub_vectorGraphMap`**:
  the graph map **never brings points closer together**. This supplies the lower-bound input that the general route would need from an inverse map it does not have.
* `norm_le_norm_graphMapLinear`, `injective_graphMapLinear`: the linear model is likewise distance-expanding and injective.
* **`hausdorffMeasure_image_vectorGraphMap_le`** (upper bound) and
  **`le_hausdorffMeasure_image_vectorGraphMap`** (lower bound): if the graph map is ε-close to a linear model,
  its image's k-dimensional measure is bounded on both sides by the linear image's measure within a factor `(1+ε)^k`.
* **`exists_approximating_partition_vectorGraph`**: a countable measurable partition of H, on each piece of which the graph map
  is ε-approximated by a linear graph map and its derivative is ε-close to that slope. This is the input for stage five.

## Reuse

Both directions reduce to the same generic comparison, `Analysis.hausdorffMeasure_image_le_of_norm_le`,
a **graph-independent** lemma already proved in the codimension-one file. It is reused directly, without reproving it.
The linear case of the area formula comes from Mathlib's linear area formula.

## Work not done in this round

* **No area formula was proved**: stage five (the `ε → 0` limit and assembly of countably many pieces, about 280 lines in the codimension-one file)
  remains undone. The client's `exact_at_zero` merely makes the two-sided bounds coincide at `ε = 0`;
  **this validates the degenerate sandwich, not the area formula**.
* Route obligations A2–A5 and B2 were untouched.
* No holes migrated; sharp Sard, the two Cheeger comparisons, and Energy's five holes were untouched.
* No certificate or Blueprint `leanok` scope was expanded.
* **No commit or push**; the real Git index was unchanged.

## Next round: the final step of B1

Use this round's partition and two-sided estimates to take `ε → 0`, following `graphMap_estimates` (132 lines) and the final assembly
(148 lines) in the codimension-one file. The required limit lemmas `tendsto_aux` and `tendsto_aux'` are already
**graph-independent** generic lemmas there and should be reusable directly, so the remaining work is estimated below the codimension-one version's 280 lines.

## Verification

* The new module and client compiled with `-DwarningAsError=true`, without `sorry`.
* The 15 axiom reports in `research/audits/VectorGraphSandwichAudit.lean` use only
  `propext`, `Classical.choice`, and `Quot.sound`.
* All 32 audit clients were rerun (25 in `research/audits`, 7 in `build/audit`) and passed strictly.
* Each of the three WIP files was compiled: direct holes remain **1/2/5, totaling 8**.
* The default `lake build` and root `python3 research/verify.py` passed; evidence JSON is
  `research/explorations/2026-09-16-vector-graph-sandwich.json`, with the final check separately saved in
  `build/audit/vector-graph-sandwich/final-snapshot.json`.
