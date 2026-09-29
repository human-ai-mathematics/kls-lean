# Route exploration of rank-deficient parts: the only structural gap of m-codimension coarea

2026-09-17. This round is a **route probing**, with **no theorem proven**, no new library modules added, and no modification to any existing `.lean`. The deliverables are: precise localization of obstacles, accurate retrieval of Mathlib and this repository, a numbered list of obligations (each with an exact Lean statement, line number, and risk), and a route statement file containing only `#check`. `research/audits/RankDeficientRouteStatements.lean`.
A proposition passing type checking is not a proof; none of the following 15 propositions is proven in this repository. No hole migration, no commit, no push. Direct proof holes remain **8 (1/2/5)**, and certification remains **24**.

Start `HEAD = origin/main = 34b92695ece4f636a1a7f1eafbbf41c685ee0348`; start verification receipt
`build/verification/20260917T040643.447621Z/report.json`: 10 gates, 215 local module kernel replay,
570 entries, snapshot
`269225e023675a7cac5a1f69eae2980bcf7d9e96bd073111871dfe6b8e9e9efb`.
The start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) are attributed to author **Haocheng Wang**, this round untouched. Sharp finite regular Sard, Energy's five holes, dimension-free KLS have also not been touched.
This round has **not** extended to any Sard theorem.

## One, Precise Localization of Obstacles

Recall `n = finrank V`, `m = finrank W`, `k + m = n`. The critical set of coarea is
Σ = {x | fderiv ℝ u x is not a surjection}, stratified by rank `Σ_r = {x | rank (Du x) = r}`, `0 ≤ r ≤ m − 1`.
The previous proof was about `Σ_0 = {Du = 0}` that layer.

**Why does the established method exactly cover `r = 0`?** Approximation piecewise
The approximation linear map of `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` takes the value of the derivative;
it is zero on `Σ_0`, so the linear part entirely vanishes, and thus `u` is truly `ε`-Lipschitz on each piece,
the Eilenberg constant `ε^m` tends to zero as `ε → 0`. At `r ≥ 1`, the derivative is nonzero,
**on `r` directions in the image space, `u` is completely not small Lipschitz**, this step directly fails.

"The projection along the survival direction yields incorrect dimensions." Let `Q` be the orthogonal projection from `W` to `(range Du)ᗮ` (dimension `m − r`), then `Q ∘ u` is indeed `ε`-Lipschitz on pieces. Applying the already proven Eilenberg bound `exists_measurable_majorant_vector` to it, the shape is

```
∫⁻ τ, μH[d] (S ∩ {Q ∘ u = τ}) dτ ≤ C · ε^(m−r) · μH[d + (m−r)] S
```

Thus for the Lebesgue positive measure `S`, the right-hand side finite is *approached* `d + (m − r) = n`, i.e. `d = k + r`:
The conclusion is `μH[k + r]` null, not the desired `μH[k]` null. The direction is reversed—
A set being `μH[k+r]` null can certainly have infinitely many `μH[k]`. This is exactly what the route statement `N1` wrote.

Conversely, if we insist on `d = k`, the right-hand side becomes `μH[k + (m−r)] S = μH[n − r] S`,
and when `r ≥ 1`, as long as `S` has positive Lebesgue measure, this quantity is `∞` (route statement `N2`),
the bound is completely hollow. **Therefore, a single slice does not hold regardless of how we choose the units, and iteration of slicing is required.**

## Two. Route to Fixing Dimensions: First Slice Along r "Good" Directions

At a point in `Σ_r`, take `W₁ = range (Du x₀)` (dimension `r`), `P` and `Q` are the orthogonal projections from `W` to `W₁` and `W₁ᗮ` respectively. Then near that point, `v := P ∘ u` is *immersed* into `W₁`, and the **proven** regular coarea formula `coarea_of_contDiffOn_of_coareaJacobian_ne_zero` applies to it.

Key facts of linear algebra (obligation `R2`): `P ∘ Du x` surjective onto `W₁` and `rank (Du x) = r`, then `P` is injective on `range (Du x)`, hence `ker (P ∘ Du x) = ker (Du x)`—
**On sheaves, the differential along the fiber direction of the regular part is exactly zero**. So `Q ∘ u` restricts to the fiber with zero derivative.

Thus apply the Eilenberg bound to the **interior of the fiber**: take `d = k`, target space dimension `W₁ᗮ` is `m − r`,
`d + (m − r) = k + m − r = n − r`, **exactly the dimension where the fiber has finite measure** (obligation `R5`).
The dimensions match. Finally, use Fubini on the orthogonal decomposition of the target space to combine "almost every `s`, almost every `τ`" into "almost every `t`" (obligation `R6`).

This is the *iterative slicing*: first slice along `v` in codimension `r`, then within each fiber slice along `Q ∘ u` in codimension `m − r`.

A technical point only became clear after a round: the **string of a fiber is not a tangent vector**. `a, b` The same applies in `v` for a fiber that only provides
`‖P A (b−a)‖ ≤ ‖P‖ ε ‖b−a‖`, to make it small `‖A (b−a)‖`, requires a norm bound of the right inverse of `P ∘ A`
(Obligation `R3`), and this bound must be uniform on the neighborhood, since each scale of `ε → 0` uses a different piecewise definition.
Together this is the obligation `R4`: `Q ∘ f` is `P ∘ f`-Lipschitz on each fiber of `c·ε`,
`c` depends only on `‖A‖,‖P‖,‖Q‖` and the right inverse bound, not on `ε`.
**`R4` is the new analytical content of this route, and also the single-point criterion for whether the route holds.**

## Three. What Mathlib and this repository have and lack (honest retrieval)

**Not in Mathlib**:
* **No coarea formula** (zero hits in full library search `coarea`);
* **No constant rank theorem** (`constantRank`/`ConstantRank` appear only in the context of `RingTheory`'s commutative algebra, unrelated to constant rank theorems for immersions/immersions);
* **No degenerate parts of Federer area/upper area formulas**;
* No Morse–Sard; the two statements called "special cases of Sard" in `HausdorffDimension.lean` (`ContDiffOn.dense_compl_image_of_dimH_lt_finrank`, `ContDiff.dense_compl_range_of_finrank_lt_finrank`) only assert the complement of the image is **dense**, not zero measure.

**Mathlib has, the ones needed for this path**:
* `isOpen_setOfPred_nat_le_rank`: `{f : E →L[𝕜] F | r ≤ rank f}` is an open set — the rank's lower semicontinuity,
  Directly provide the layered measurability of `R1`;
* `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` and `ApproximatesLinearOn` on a line:
  Only provide "approximation + countable disjoint measurable piecewise";

no rank structure is given;
  `ApproximatesLinearOn.antilipschitz` requires linear models to be *equivalent*, and is inapplicable when rank-deficient.
  It provides exactly what `R4` inputs, neither more nor less;
* `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`: Sard's lemma for **same dimension**
  (`E → E`, the image at differential irreversibility has zero measure) —— this exactly yields `R10`;
* `Submodule.orthogonalDecomposition : E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ)`,
  `LinearIsometryEquiv.measurePreserving`, `WithLp.volume_preserving_ofLp`—all components of `R6`;
* `hausdorffMeasure_of_lt_dimH`——components of `N2`.

**This repository has**: the m-Eilenberg codimension bound (`VectorHausdorffSlicing.lean`),
the regular coarea formula (`VectorRegularCoarea.lean`), measurability of slices without regularity
(`VectorSliceMeasurable.lean`), critical slices where the derivative is zero (`VectorCriticalSlice.lean`),
`coareaJacobian` and the associated one-form (`CoareaJacobian.lean`, including `ker_adjoint`,
`coareaJacobian_ne_zero_iff`), `isometryEquivOfFinrankEq` (`VectorFiberIntegral.lean`).

**Missing**: the following `R1`–`R10` entirely, none at all.

## Section Four: Obligations List

Precise Lean statements at `research/audits/RankDeficientRouteStatements.lean`,
listed by the table number; this file contains only `#check`, no declarations, no proofs, no placeholder axioms,
passed by `-DwarningAsError=true`. Type checking passing is not a proof.

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `R0` | **Goal**: Rank-deficient critical sets have `μH[k]` zero measure almost everywhere on each level | — | Composed from `R1`–`R8` |
| `R1` | the rank stratification is measurable; the critical set is a finite union of the layers of `r < m` | 60 | low |
| `R2` | Core lemma: the differential on a stratum vanishes along the fiber direction (pure linear algebra) | 40 | Low |
| `R3` | Approximate right inverse of a surjection: pointwise + uniformly on a neighborhood | 50 + 120 | low / medium |
| `R4` | **Lipschitz estimates on fibers** (new analysis content) | 120 | Medium |
| `R5` | The fiber of the regular part has finite `ℋ^{n−r}` measure | 150 | center |
| `R6` | Fubini on orthogonal decomposition of target space | 150 | Medium |
| `R7` | **Local slice per layer** (assembly of `R1`–`R6`) | 450–600 | High |
| `R8` | Local zero-measure slice extended to global (second-countable + countable intersection) | 90 | Low / Medium |
| `R9` | Consumer: m-coarea formula without the two-point assumption | 60 | Low |
| `R10` | degeneracy in same dimension `n = m` (independent corroboration) | 80 | **low, cheap** |
| `N1` | Statement of obstacle: the error exponent given by the small Lipschitz method | 120 | Low / Medium |
| `N2` | Quantitative obstacle: exponential decay cannot be achieved, right end is `∞` | 40 | low |

The entire program consists of **1500 lines**.

Reasons and risk sources for each item:

* **`R1`** (low). Mathlib's `isOpen_setOfPred_nat_le_rank` gives `{r ≤ rank}` a,
  A stratum is the difference of two open sets. The decomposition requires "surjective ⟺ rank = m", directly in finite dimensions.
* **`R2`** (low). `P` is surjective on `range L` and has the same dimension on both sides ⟹ injective ⟹ the two kernels are equal.
* **`R3`** (pointwise low, uniformly medium). Pointwise using `CoareaJacobian.lean`'s existing adjoint pseudo-inverse
  `L*(L L*)⁻¹`. The consistent version requires the continuity of `x ↦ (Du (Du)*)⁻¹`, i.e., the continuity of taking inverses on invertible operators;
  Mathlib has it, but to establish a uniform bound on a neighborhood of an open set in `coareaJacobian ≠ 0`, is routine but trivial.
* **`R4`** (Chinese). Estimate chain itself two lines of mathematics: `‖P A z‖ ≤ ‖P‖ε‖z‖` ⟹ by taking `R3` with `w`,
  `‖z − w‖ ≤ C‖P‖ε‖z‖` ⟹ by `R2` we get `A w = 0` ⟹ `‖A z‖ ≤ ‖A‖C‖P‖ε‖z‖` ⟹
  `‖Q f b − Q f a‖ ≤ ‖Q‖(1 + ‖A‖C‖P‖)ε‖b−a‖`. Risks are all on `ℝ≥0` arithmetic and
  The interface of `LipschitzOnWith`/`ApproximatesLinearOn`, is not mathematical.
* **`R5`** (Chinese). The coarea formula with weight `1` has been established: the integrand is continuous and bounded on a relatively compact set, and the total integral is finite,
  Hence, almost every level fiber has finite fiber measure. Additionally, a `hausdorffNormalized` and the finiteness of the original `μH`
  Mutual implication (currently only having zero-measure mutual implication `hausdorffNormalized_eq_zero_iff`), is a new lemma.
* **`R6`** (Chinese). Components are complete, risks are in the instance pipeline: `WithLp 2 (W₁ × W₂)`
  whether the `MeasurableSpace`/`BorelSpace`/`volume` instances align with `Measure.prod`,
  And `volume` instances on subspace types. It is recommended to use abstract `W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)` statements
  (The route file says this), leave the hassle of subspace instances to the call site.
* **`R7`** (high). The only revival in this round. Note two common mistakes:
  (i) Neighborhoods are taken only from points on the layer—there is no fixed `r`-dimensional `P` available near points of lower rank,
  Even if the points of the layer approach arbitrarily; this suffices for `R8`, since it only requires covering the cut set;
  (ii) The approximation of piecewise functions must be done directly on **`u` itself**, with a single piecewise set serving both `P ∘ u` and `Q ∘ u`.
  And the `A n = Du y` approximation of the linear map `y` lies on the stratum, `R2` can then be used;
  (iii) `c` must be consistent across leaves, so the consistent version of `R3` is a hard requirement, not a convenience.
* **`R8`** (low/medium). `VectorRegularCoarea.lean` has already been used
  `TopologicalSpace.isOpen_iUnion_countable`, copy verbatim.
* **`R9`** (low). Take the proof of `coarea_of_contDiff_of_critical_eq_zeroDeriv` verbatim,
  Change `hcrit` to `R0`. Among these, `0 < finrank ℝ W` is **inherited verbatim from previously proven statements**, not a new assumption.
* **`R10`** (low, **cheap**). When `n = m`, `k = 0`, `μH[0]` zero measure is the **empty set**.
  So the statement is "almost no level value is a critical value." The same-dimensional Sard lemma in Mathlib directly gives,
  Carry along this repository's `isometryEquivOfFinrankEq`. Just transport it. **This round does not certify it**——
  See the following "Why nothing was proven in this round".
* **`N1`/`N2`** (low/medium). Both are provable diagnostic statements, used to pin obstacles to paper,
  Not a step toward `R0`. Both boundary conditions of `N1` are true: `S` must be measurable in order to sum the control functions over each piece,
  `0 < finrank W₂` only makes the Eilenberg constant `ε^(dim W₂)` tend to zero—`r = m` when there is no direction to project, the statement is false.

## Five. Recommended Priority Order, and Parts Not Recommended to Do Now

**Suggested order**:

1. `R2` (Nucleus Lemma). Minimal, cheapest, and it is the geometric heart of the entire design; once it holds,
"zero derivative along fiber directions" becomes a fact, not just an intuition.
2. `R1` (Layering). Small, and without it, no statement involving `R7` can be written.
3. `R3` (Do both versions together).
4. `R4`. **This is a dead end**: after `R2 + R3` is in place, `R4` is self-sufficient,
if `R4` cannot be achieved or if constants are inconsistent, the entire path is wrong and must be known before investing in `R7`.
5. `R5` and `R6` (independently, and parallelizable).
6. `R7`, then `R8`, `R9`.

**Not recommended to do now**:

* **Do not do `R7` first**. It depends on all five above; doing it first would only yield a skeleton full of `sorry`.
* **Do not treat `R10` as progress**. It's cheap and can serve as standalone audit evidence,
  but it **is not on the path to `R0`**: at `n = m`, `r` still needs to traverse all intermediate ranks of `r < m`,
  and the same-dimensional Sard lemma provides no information about intermediate layers. Calling it "a partial proof for rank deficiency" is misleading.
* **Do not touch Sard**. This route provides a critical slice of zero measure, but says nothing about the measure of the critical value set;
  the critical value set of a mere `C¹` map can still have positive measure. These are two distinct issues.
* **Do not attempt to complete Federer's degenerate coarea in one go**, nor extend it casually to `C¹` Morse–Sard.
* Do not touch the log-concave Cheeger–Buser line (Haocheng Wang), the sharp finite regular Sard, or the five holes of Energy.

## Why nothing has been proven in this round

`R10` Indeed cheap. But getting it certified into the library requires adding a new library module, and the new module must be included in
The aggregation import of `formalization/FunctionalInequalities.lean` will be default `lake build` coverage,
That means **modifying the existing `.lean`**—this round of directive does not do so. Thus, this round marks `R10` **accurately as cheap but unproven**,
Rather than violating boundaries for the sake of "producing output". This round proved no theorems.

## Seven. Route Statement File Review

This round of re-run `research/audits/AreaFormulaRouteStatements.lean`, **no new errors were found**,
the file continues to **preserve original bytes**. The two recorded issues remain `B1`'s normalization mismatch and the previously refuted `A0`.

A new observation (not a new error): `A5` (localization) uses the same `μH` paired with Lebesgue's mismatch at both ends as in `A0`. However, `A5` is an implication whose proof relies only on the countable additivity of sets at the endpoints and is independent of the normalization constant. Thus, `A5` itself is not falsified and remains a true statement; only its conclusion is literally false, `A0`, meaning the premise cannot be satisfied under this normalization. Record this fact accurately, do not modify the file.

## Eight, Verification

* New client `research/audits/RankDeficientRouteStatements.lean` (row 309, 15 entries `#check`)
  Approved with `-DwarningAsError=true`, **no declarations, no proofs, no `sorry`, no `axiom`, no placeholders**.
  Its local import closure imports **28 modules, no WIP**.
Because there are no new declarations of proofs, **no new axiom reports**; the existing client's axiom reports remain unchanged:
  558 reports use the standard three axioms; the 12 reports containing `sorryAx` all come from four clients that **deliberately** report unresolved WIP results
   (`LevelSetMeasurableAudit`, `IsoperimetryCoareaAudit`, `LipschitzCoareaMigrationAudit`,
  (`build/audit/SuperlevelSardScope`), consistent with the 12 entries recorded in the semantic alignment section.
* Retest all existing audit clients (**41** in total, **`research/audits` 34** and **`build/audit` 7**)
  Add new client: total **42**, all strictly passed by `-DwarningAsError=true`, 0 failed.
* Three WIPs are compiled individually, direct proof hole **1/2/5**, total **8**, unchanged; `research/check_ledger.py` reports **24** certificates.
* The default `lake build` is connected to the root directory `python3 research/verify.py`;
  Evidence JSON is `research/explorations/2026-09-17-rank-deficient-route.json`,
  Final verification and save `build/audit/rank-deficient-route/final-snapshot.json`.
* **No commit, no push**, the real Git index remains unchanged.

---

## Addendum (2026-09-17, later the same day; main text unchanged)

The reason given in Section Six above, "Why Nothing Has Been Proven in This Round," is wrong, and is corrected here in truth, while the original text remains unchanged.

The construction and core replay scope of `research/verify.py` is computed by `replay_sources` from the **source tree**,
the original comment of `build_replay_inputs` is
"Build the exact replay scope, including modules outside default import closures";
The existing `Analysis/Vector*.lean` modules are likewise not included in the aggregated import of `formalization/FunctionalInequalities.lean`,
and are equally covered by the replay gate.
Therefore, the addition of the `Analysis/` module does not require modification of the aggregated import, and the inference of "cannot be proven" above does not hold.

Thus, the subsequent round of proof on the same day established the obligation `R1` and `R2`, without modifying any existing `.lean`;
see `research/decisions/2026-09-17-rank-stratification.md`.
`R10` remains **unproven**, and this addendum does not alter this fact, nor does it change the record of "no theorems proven in this round".
