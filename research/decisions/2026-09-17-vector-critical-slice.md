# Critical slices of codimension m: the part where the derivative is zero

2026-09-17. This round of **proving a new theorem**: the slice zero-measure property of the critical set where the derivative is zero in the case of codimension m, and the extension of the coarea formula from the regular case to the entire space
(assuming "the derivative is zero at points where the differential is not surjective").
This is **not a complete critical set** (it is strictly smaller than `m ≥ 2`), **nor any Sard theorem**;
the gap is not asserted but **provided by counterexamples**.
No hole-filling, no commit, no pushing. The direct proof hole remains **8 (1/2/5)**, and the certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260917T034956.058840Z/report.json`: 10 gates, 214 local module kernel replay,
566 entries, snapshot
`e87a9add07bbc20692efd7891719dcf6b8cdf6d1bf027fe3f36fd05b7f90b019`.
The start workspace drift is empty, and concurrent sessions have not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**,
this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS also untouched.

## Exact Results

New module `formalization/FunctionalInequalities/Analysis/VectorCriticalSlice.lean`
 (275 line, local import closure 28 modules, **no WIP**).

* **`exists_lipschitzOnWith_zeroDeriv_cover`**: Mathlib's approximation piecewise
  `{x | fderiv ℝ u x = 0}` covers into countably many pairwise disjoint measurable pieces, `u` each piece is `ε`-Lipschitz.
  The linear mapping used for approximation takes the value of the derivative, and is zero on this set, so the linear part vanishes, and the approximation becomes a true Lipschitz estimate.
  This step precisely addresses the locations where the derivative fails due to rank deficiency.
* **`ae_hausdorffMeasure_zeroDeriv_inter_levelSet_eq_zero`** (and its normalized version):
  At `m ≥ 1`, **almost every intersection with the level set of `{Du = 0}` has measure zero with respect to `ℋ^{n−m}`**.
  The argument and scalar are identical, except that the constant is replaced by the two previous rounds' co-dimension m Eilenberg bound,
  `volume (closedBall 0 1) · ε^m`, while `ε^m → 0` is due to `m ≥ 1`.
  `0 < finrank W` is a true assumption: when the target space is zero-dimensional, each derivative is zero, and the set is the entire space.
* **`coarea_of_contDiff_of_critical_eq_zeroDeriv`**:
  Under the assumption that "the derivative is zero at differential non-surjective points," extend the already-proven regular case coarea formula to the entire space—
  Measurability comes from the slice measurability in the previous round without regularity, and the contribution from the critical part is zero on both sides.

## m = 1 Literally retract the proven scalar L10 and L11

`m = 1` At the time "non-surjective" and "zero" are the same thing regarding real differential forms, the above assumption holds automatically. In auditing:
* `scalar_L10` retrieves each word from `KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero`;
* `scalar_L11` retrieves each word from `KLS.coarea_of_contDiff`.

Both require an additional `1 ≤ finrank V`—the same *accurate difference recorded* as in the previous two rounds:
The statement of codimension m assumes the hypothesis "fiber dimension + codimension = ambient dimension".

## The gap is given, not asserted.

For `m ≥ 2`, the coarea critical set is `{x | fderiv ℝ u x is not surjective}`, **strictly larger** than the set where the derivative vanishes.
The audit `rank_deficient_witness` provides a counterexample: a rank-one linear map in the plane
(the orthogonal projection along the first coordinate axis), whose derivative is **nowhere zero** and **nowhere surjective**——
Thus the set where the derivative is zero is empty, and the critical set of coarea is the entire space,
The assumption of `coarea_of_contDiff_of_critical_eq_zeroDeriv` does not hold at any point.

**This round has proven nothing about the rank-deficient part.** That part requires iterative slicing along the survival direction,
and is entirely different from the "small Lipschitz constant" technique used in this round— the latter strictly depends on the zero derivative.

## What was not done in this round

* **No proof of any Sard theorem**; no assertion is made about the measure of the critical value set,
  merely that the set of critical values for a C¹ map can have positive measure.
* **No proof of the general coarea formula of codimension m**: the rank-deficient part is not covered.
* No modification to `KLS/Geometry/CriticalSlice.lean` or `KLS/Geometry/SmoothCoarea.lean`—
  the codimension m version is a parallel new module.
* No touch of the sharp finite positive regular Sard, the two Cheeger comparisons, or five energy holes;
  no hole migration; no extension of the certificate or Blueprint `leanok`; no new compatible alias added; no weakening of already proven conclusions.
* **No commit, no push**, the real Git index is unchanged.

## Route statement verification

This round of re-execution found no new route statement errors. The two recorded issues remain `B1` and the falsified `A0`.
`research/audits/AreaFormulaRouteStatements.lean` continues to preserve the original bytes.

## Remaining work

**Rank-deficient parts** are the only structural gaps left by the coarea formula of dimension m. Possible approaches:
Layer by rank `{rank Du ≤ r}`, and on each layer use approximation piecewise to squeeze the image of `u` near an affine subspace of dimension `r`,
then along the surviving `m − r` directions use Eilenberg's bound—however, it requires slicing simultaneously along `r` "good" directions,
i.e., iterative slicing; this is precisely the difficulty in the degenerate part of Federer's coarea formula,
repository and Mathlib currently lack corresponding tools. If a project is to be initiated, a round of route exploration should be conducted first.

## Verification

* The new module and new client have been compiled successfully with `-DwarningAsError=true`, with no `sorry`, no `axiom`, and no placeholders.
* The **17 Axiom Report** of `research/audits/VectorCriticalSliceAudit.lean` only uses
  `propext`, `Classical.choice`, `Quot.sound`; contains constant maps (global critical), derivative identically zero in zero-dimensional target space,
  Rank-deficient counterexample, and for m = 1 step-by-step rollback of `L10` and `L11`
  (The last two reports are repository-proved scalar `L10`, `L11`, for reference.)
* Reran all **41 audit clients** (34 in `research/audits`, 7 in `build/audit`); all passed strict compilation.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports 24 certificates.
* Default `lake build` and root directory `python3 research/verify.py` are connected; evidence JSON is
  `research/explorations/2026-09-17-vector-critical-slice.json`, final verification and save
  `build/audit/vector-critical-slice/final-snapshot.json`.
