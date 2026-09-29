# Eilenberg slice inequality of codimension m

2026-09-17. This round's **new theorem proof**: the requested **m-codimensional Eilenberg slice inequality**, and its zero-measure slice corollary (under both original and normalized conventions).
**This is not slice measurability, nor a general m-codimensional coarea formula**—the gap is specified at the end.
No hole-filling, no commit, no push. The direct proof hole remains **8 (1/2/5)**, the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260916T172603.078138Z/report.json`: 10 gates, 212 local module kernel replay,
558 entries, snapshot
`d4d668e06556962f439a2f52fb79f6a0b5cb092481447265e9bd7696ad8cc731`.
The start workspace drift is empty, and concurrent sessions have not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/VectorHausdorffSlicing.lean`
 (357 line, local import closure **2** modules—its own and `KLS/Geometry/SurfaceMeasure.lean`,
**no WIP**; all other dependencies only Mathlib).
It is an m-codimensional analogue of `Analysis/HausdorffSlicing.lean`.

* **`exists_measurable_majorant_vector`**: **Eilenberg slice inequality of codimension m**, measurable optimal form.
  A function on `S` that is K-Lipschitz and takes values in the m-dimensional inner product space `W` `u`,
  The slice function `t ↦ μH[d] (S ∩ {u = t})` is controlled by some **measurable** `F`, and
  `∫⁻ F ≤ volume (closedBall 0 1) · K^m · μH[d+m] S`.
  The measurability of the optimal function is part of the conclusion, not an assumption on the slice functions—the slice functions are not yet known to be measurable at this stage.
* **`exists_levelBall`**: The only place where the codimension is uniquely entered in the proof.
  In the real-valued case, the image of each covering sheet lies within the interval of length `2K·diam`;
  In codimension m, the image lies in a **ball** of radius `K·diam`, with volume `volume(closedBall 0 1)·(K·diam)^m`,
  This is the source of the `m`th power.
* **`ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`**: zero-measure slice——
  `μH[d+m]`-zero measure set has `μH[d]`-zero measure slice almost everywhere.
* **`hausdorffNormalized_eq_zero_iff`, `ae_hausdorffNormalized_inter_levelSet_eq_zero_vector`**:
  The same conclusion under normalization conventions, namely the form of the coarea layer's actual consumption.

**The argument is a covering argument, not Rademacher**: Almost everywhere differentiable says nothing about a single level set.
At each scale, take the infimum formula of `μH[d+m]` to obtain an approximately optimal covering, and pack each piece's image into a ball via Lipschitz property,
summing the contributions from pieces containing `t` yields the measurable optimal function at that scale,
`Measure.hausdorffMeasure_le_liminf_tsum` provides pointwise bounds, and Fatou's lemma gives the closeout.

Degenerate data are handled by branching rather than exclusion: when `K = 0` and `m ≥ 1`, `u` is constant on `S` with bound `0`; when `K^m ≠ 0` and the covering cost is infinite, the bound is `∞`; the zero-dimensional target space is also included in the statement, and in this case `K^m = 1`, each ball is the entire space, and the inequality degenerates into `μH[d] S · volume univ ≤ volume univ · μH[d] S`. `S` does not require measurability, boundedness, or non-emptiness, `u` does not require global Lipschitz, differentiability, or measurability, `d = 0` is allowed, and zero diameter and empty covering sheets are harmless.

## m = 1 literally retract the proven scalar bound, the constant as well

On the real axis `volume (closedBall 0 1) = 2` and `K^1 = K`,
so the constant of co-dimension m `volume(closedBall 0 1)·K^m` is **exactly** the scalar's `2K`.
Audit the client's `codimension_one_majorant` word-for-word rewrite
`Analysis.exists_measurable_majorant` the statement and derive it from the theorem of co-dimension m.

## What was not done in this round

**This is not slice measurability.** From the Eilenberg inequality to "slice measurability without regularity assumptions"
**Not yet complete:** further work is needed on m-dimensional compact slice measurability, namely
`Analysis.measurable_hausdorffMeasure_inter_levelSet` analogy,
while the latter concerns real-valued functions, and this round does not extend it.

Thus:
* The m-codimensional slice measurability of the coarea layer still carries the regularity assumption (from the previous round of graph path);
* The critical set has not yet been addressed;
* The general m-codimensional coarea formula remains open.

Moreover: no sharp finite regular Sard, two Cheeger comparisons, five holes in Energy;
no migration holes; no expansion of certification or Blueprint `leanok` scope; no new compatible alias added; no weakening of already proven conclusions;
no modification to `Analysis/HausdorffSlicing.lean`—it remains unchanged, the m-codimensional version is a **parallel new module**.
**No commit, no push**, the real Git index is unchanged.

## Route statement verification

This round of re-execution found no new route statement errors. The two recorded issues remain `B1` and the falsified `A0`.
`research/audits/AreaFormulaRouteStatements.lean` continues to preserve the original bytes.

## Remaining work

1. **Measurability of a compact slice of codimension m**: The cost of scaling open cover of `Analysis/HausdorffContent.lean`
   Rather than extending the upper semicontinuity to vector-valued `u` (where `isOpen_setOf_slice_subset` is key,
   It is a pure topological statement, which should be amenable to literal generalization);
2. Use it together with the zero-measure slice of the current round, following `KLS/Geometry/SurfaceSlicing.lean`
   Compact exhaustion + monotone simple functions yield **regularity-free** weighted slice measurability;
3. Localize again `KLS/Geometry/OpenSliceMeasurable.lean` to an open C¹ domain;
4. Only afterwards can one discuss critical sets and the general coarea formula of codimension m (further requiring a codimension m Sard or critical slice).

## Verification

* The new module and new client have been compiled successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **15 Axiom Report** of `research/audits/VectorHausdorffSlicingAudit.lean` only uses
  `propext`, `Classical.choice`, `Quot.sound`; contains `K = 0`, `d = 0`, zero-dimensional target space,
  Zero-measure slice, together with m = 1 constant, returns scalar bound
  (The final report is for the repository’s proved scalar Eilenberg bound itself, for comparison).
* Reran all **39 audit clients** (32 in `research/audits`, 7 in `build/audit`); all passed strict compilation.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports 24 certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-vector-hausdorff-slicing.json`, final verification and save
  `build/audit/vector-hausdorff-slicing/final-snapshot.json`.
