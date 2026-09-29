# Sharp finite regular Sard's route exploration: Morse decomposition, not hypersurface dimension reduction

2026-09-19. This round is a **route exploration**, with **no proof of any theorem**, and no addition of any library modules,
No modifications made to any existing `.lean`. The deliverable is: why can't the direct proof hole `Analysis.sard` be carried over along the smooth version?
a precise account of where the dimension-reduction induction for `sard_smooth` fails, a factual search of Mathlib and this repository,
Numbered obligation list (each entry with precise Lean statement, line number, and risk), along with a route statement file containing only `#check`
`research/audits/SharpSardRouteStatements.lean`.
**The proposition passing type checking is not a proof**; none of the following obligations is proved in this repository.
No migration, no commit, no push. Direct proof holes remain **8 (1/2/5)**, certification remains **24**.

Start `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; start verification receipt
`build/verification/20260918T113053.092417Z/report.json`: 10 gates, 224 local module kernel replay,
614 entries, snapshot `ab7dbfd7775b140596404611efbaa12b7b863a7c9ef3f2f86065976b79d8f80b`.
Start workspace drift is empty, and concurrent session has not modified the workspace.

## Boundary

Log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) are attributed to author **Haocheng Wang**, untouched in this round. The five holes of Energy, as well as dimension-free KLS, have also not been touched.
This round only addresses the sharp `C^n` Sard for real-valued targets; vector-valued targets, Hausdorff measures at critical values, and the Whitney counterexample (sharpness itself) are outside the scope of this approach.

## Zero: What does this hole mean for downstream processing?

The [2026-09-15 route exploration](2026-09-15-smooth-sard-route.md) established that the only consumer of `Analysis.sard` is
`ae_forall_fderiv_ne_zero`, whose only consumer, `SmoothDomain.ae_exists_superlevel`, assumes `C^∞`,
And version `C^∞` of `sard_smooth` and `ae_forall_fderiv_ne_zero_of_contDiff_top` have been proven.
So this hole does not block any KLS chain; closing it is `Analysis/` the completion of the layer analysis foundation,
Profit is a direct proof hole 8 → 7 (1/2/5 → 0/2/5), `KLS/WIP/AnalyticPrerequisites.lean` cleared and deleted by precedent,
and `ae_forall_fderiv_ne_zero` detached from `sorryAx`. The statement itself unchanged.

## One. Precise Localization of Obstructions: Dimensional Reduction and Loss of Regularity in Intermediate Layers

`Analysis/Sard/Smooth.lean`'s `sard_smooth_pi` stratifies the critical set by the order of vanishing of derivatives
(`critical_subset_layers`): The flat stratum is handled by the covering count `volume_image_flat_pow_univ_eq_zero`;
the `j`-th layer (`1 ≤ j < n`, `≤ j`-th derivative zero, `j+1`-th non-zero) takes a `j`-th derivative component `w`
(`exists_flat_direction`), which vanishes on that layer but has non-zero differential, so the layer locally lies on the regular zero set of `w`,
which is a hypersurface image (`exists_local_graph`), and `u` is restricted to this image, then inductively on dimension.

At finite regularity, **this step fails at `j ≥ 2`**. At `u ∈ C^n`, `w ∈ C^{n−j}`, the image map `C^{n−j}`,
restriction `u ∘ ψ ∈ C^{n−j}` (the route file's `D1` records this regularity ledger: composition only preserves the lower order);
and the `n−1`-dimensional induction hypothesis requires `C^{n−1}`. `j = 1` is exactly sufficient, `j ≥ 2` falls short by `j−1` orders.
This is precisely why Milnor's proof requires `C^∞`, and also why 2026-09-15 changed the target to `C^∞`
(it then concluded "`n = 4, j = 2` is the first case that cannot be covered," which is consistent).
**Any scheme that first restricts `u` and then reduces dimension must pay the regularity cost here; changing the stratification won't save it.**

## II. Path: Morse (1939) Decomposition—Induction on Sets, Not Dimension Reduction of Functions

According to A. P. Morse, *The behavior of a function on its critical set*, Ann. of Math. 40 (1939) 62–70,
state A. Norton, *The Zygmund Morse–Sard theorem*, J. Geom. Anal. 4 (1994) 403–424
reducing from the Zygmund class to the version of `C^k`. The core object is not `u`, but rather the **Morse decomposition** of an arbitrary set `A ⊆ ℝⁿ`:

* **`C¹` Parameter disk**: A `C¹` map `φ` from `Fin p → ℝ` to `Fin n → ℝ`, which is anti-Lipschitz on the closed unit ball;
  The body `φ '' closedBall 0 1`; the **parametric segment** from `φ a` to `φ b` is the image of the line segment `[a, b]`.
* **Along the disk `k` order flatness**: uniformly small o sense, `x, y ∈ S` is sufficiently close, `z` on the parameter segment when `|f z| ≤ ε ‖x − z‖^k`.
*Morse vanishing lemma (`M3`): Any `A` has a decomposition of arbitrary order `k`—a countable set `A₀` plus countably many pieces supported by disks*
  Cover `A`, such that every `C^k` function vanishing on `A` is flat to order `k` along its disk in each piece.
  The proof is a double induction on `(n, k)`, with **no loss of regularity in either direction**:
  - `k = 0`: uniformly continuous on a compact body; `n = 0`: trivial.
  - `k → k+1` (fixed `n`, **critical part**): split `A` into `U` (where every `C^{k+1}` function vanishing on `A` is critical) and `V`.
    `U` uses `U`'s own `k`-order decomposition: the coordinates of `fderiv f` are `C^k`, zero on `U`, hence `k`-order flat,
    Then by the mean value step along the parameter segment `M2` one order higher.
  - `n → n+1` (fixing `k`, **regular part**): at each point of `V` there is some `g ∈ C^k` differential form that is nonzero and vanishes on `A`,
    `A`—thus `V`—is localized on the graph of a `n`-coordinate function `C^k` (`M1`);
    Use `n`-dimensional, the same `k` induction hypothesis for the preimage of the image, then push forward along the image map.
    Image mapping **1-anti Lipschitz** (`M1'`), all estimation constants remain unchanged. Second-countability allows local decomposition to be reduced to countably many.
  This is the essential difference from dimension-reduction induction: the induction hypothesis quantifies over **all sets**, the order `k` remains unchanged,
  So what is restricted is never `u`, but rather the class of "functions that are zero on `A`"—it remains `C^k` in the image, exactly sufficient.
* **Morse critical lemma (`M4`)**: the critical set of a `C^{k+1}` function `f` is covered by a countable set and countably many bounded pieces,
  On each piece, `|f y − f x| ≤ ε ‖y − x‖^{k+1}` is uniformly small o——`fderiv f`'s coordinates are `C^k`, and zero on the critical set,
  `M3` makes it `k`-flat, `M2` provides an estimate for `f`. After this step, both the disk and flatness have vanished, leaving only the Mathlib concepts.
* **Closeout (`M5`)**: `k + 1 = n`, each piece using **already proven** covering count `volume_image_eq_zero_of_oscillation_pow`
  (Bounded set with uniform `o(‖y−x‖ⁿ)` modulus ⟹ image has zero measure), countable set image is countable, countable union of zero measure sets; `n = 0` when image is a point.
* **Transport (`M6`)**: from `Fin n → ℝ` to any finite-dimensional normed space along `ContinuousLinearEquiv.ofFinrankEq`,
  Identical to `sard_smooth` in transfer. The statement of `M6` must be identical to `KLS/WIP/AnalyticPrerequisites.lean`
  The `Analysis.sard`'s `pp.all` prints byte-by-byte consistently, and during migration, machine-by-machine comparison follows the precedent.

**No** Whitney extension, **no** Kirszbraun, **no** manifold framework, **no** approximation piecewise.

## Three. What Mathlib and this repository have and lack (honest retrieval)

**Not in Mathlib**: No version of Morse–Sard (zero hits in the full library `Morse`);
In `HausdorffDimension.lean`, the two statements called "special cases of Sard" give density of the complements of the images, not zero measure;
No Morse decomposition, no "flat along a disk".

**Mathlib has, on the current path to be used**: `C^k` Inverse Function Theorem `ContDiffAt.to_localInverse`
(`M1`'s core, the smooth version of `exists_local_graph` is exactly used this way); `Fin.insertNth` / `Fin.removeNth`
(only definitions and pointwise lemmas; their `ContDiff` and 1-anti-Lipschitz properties need to be proven, the latter being `M1'`); `ContDiff.fderiv_right`, `ContinuousLinearMap.apply`'s `ContDiff` (the coordinates of `fderiv f` are `C^k`); the mean value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` along a line (`M2`); `Set.Countable` and second countability
(`M3`'s countable cover).

**This repository is known: `volume_image_eq_zero_of_oscillation_pow` (`M0`, `Analysis/QuadraticCover.lean`, proven); `exists_contDiff_eventuallyEq`, `exists_local_graph` (`C^∞` version image, `Analysis/Sard/Smooth.lean`, `M1`'s template); `sard_smooth`'s transport segment (`M6`'s template); `sard_plane` (independent verification of `n = 2`).**

**Missing**: `M1`–`M6` all.

## Section Four: Obligations List

Precise Lean statements at `research/audits/SharpSardRouteStatements.lean`, listed by the table number;
This file contains only `#check`, with no declarations, no proofs, no placeholder axioms, passed by `-DwarningAsError=true`.
**Type checking passage is not a proof.**

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `M0` | coverage count: uniform `o(‖y−x‖ⁿ)` ⟹ image zero measure | — | **proven** |
| `M1` | `C^k` Image characterization of the regular zero set: `w x = 0 → x = insertNth i (θ (removeNth i x)) (removeNth i x)` | 250 | Low–medium |
| `M1'` | image mapping 1-anti Lipschitz | 20 | low |
| `M2` | Mean value step: `fderiv f` each coordinate along disk `k` order flat ⟹ `f` along disk `k+1` order flat | 250 | Mid |
| `M3` | **Morse vanishing lemma**: Any set has an arbitrary-order Morse decomposition | 300 | **High** (double induction; pushforward decomposition along image) |
| `M4` | Morse critical lemma: the critical set of a `C^{k+1}` function is covered by a countable set plus countably many bounded pieces, each uniformly `o(‖y−x‖^{k+1})` | 60 | low (`M2`+`M3`) |
| `M5` | `Fin n → ℝ` Sard on real-valued functions on `C^n` | 40 | Low (`M4`+`M0`) |
| `M6` | **Objective**: `Analysis.sard`, word-for-word | 40 | Low (same as `sard_smooth`) |
| `D1` | Diagnosis (true, and trivial): The `C^k` function restricted to the image of `C^k` remains only `C^k`—records the loss of order in dimensionality reduction scheme | — | Not a step |

Total of approximately **1000 lines**. Recommended order: `M1'`, `M1`, `M2`, `M3` (first `k = 0` and `n = 0` as bases, then critical step, then regular step), `M4`, `M5`, `M6`. `M3` is the only high-risk item and serves as the sole deciding criterion for the validity of the route:
Once proven, `M4`–`M6` are mechanical.
During implementation, additional modules can be added under `Analysis/Sard/` and auxiliary definitions such as `Disk`, `FlatAlong`, `HasDecompRel` can be introduced;
the route statement is deliberately **not** written using these definitions, to enable audit clients to reproduce it word for word and discharge it.

## Five. Clarify What Has Not Been Proven

* **No proof of any Sard theorem**; `Analysis.sard` remains a direct proof hole, statement and position unchanged.
* Only real-valued target discussed; vector-valued target (`C^{n−m+1}`), Hausdorff measure of critical values, and Whitney's `C^{n−1}` counterexample are not included.
* Cheeger two holes belong to Haocheng Wang, Energy five holes untouched; dimension-free KLS remains open.

## Section 6. Verification

`research/audits/SharpSardRouteStatements.lean` passed via `lake env lean -DwarningAsError=true`,
11 `#check` (3 cited proven statements, 8 obligations and diagnostic propositions), 0 errors, 0 warnings;
local import closure does not include WIP files.
No library source code was modified, no aggregation import was changed. The root directory `python3 research/verify.py` was rerun at the end of this round,
the final verification receipt is recorded at `build/audit/sharp-sard-route/final-snapshot.json`, snapshots and workspaces were recalculated individually, drift is empty.
See details in `research/explorations/2026-09-19-sharp-sard-route.json`.

## Note (2026-09-19, after implementation)

* **`M2` is literally false.** The proof session provides a pen-and-paper counterexample (`n = 2, p = 1, k = 0`): `C¹` spiral
  `φ t = (t³ cos(1/t), t³ sin(1/t))`, `S` takes its intersection point with the positive `x` axis (infinitely many scales), `f` has a gradient on the `m`-th loop
  approximately `m^{-1/2}` and monotonically along the spiral; the arc length of the parametrized segment is approximately `m` times the chord length, and the ratio on both sides diverges according to `m^{1/2}`.
  The statement in the route record "`M2` does not need `φ`'s anti-Lipschitz constant" is incorrect. The counterexample is **not formalized**.
* After adding the anti-Lipschitz bound for the disk (`M2`), `route_M2_antilipschitz`, `MorseSard.abs_sub_le_of_flat_fderiv` is proven,
  and each disk in the Morse decomposition carries this bound, so `M3`–`M6` remains unaffected. The route statement file retains unchanged byte count (historical snapshot).
* The remaining seven (`M1`, `M1'`, `M3`–`M6`, `D1`) are all proven; `Analysis.sard` has been migrated to `Analysis/Sard/Sharp.lean`,
  see [implementation record](2026-09-19-coarea-sard-proofs.md).
