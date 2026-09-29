# Sard Intermediate Layer Route Exploration

2026-09-15, route exploration round. **This round proves no new theorems** and makes no changes to any Lean source code.
The initial verification receipt `build/verification/latest.json` (`20260914T161103.875998Z`) is passed,
recomputed confirmation of byte-level consistency in the workspace. HEAD remains `2965b32`; no commit, no push.
Output includes: a clearly defined rewrite target, a precise inductive statement, a list of lemmas (all type-checked),
and a sharp version of a **real obstacle** identified.

## Conclusion First: The goal should be changed from sharp C^n to C^∞

Trace the consumers of `Analysis.sard`:

* `Analysis.sard` ( `WIP/AnalyticPrerequisites.lean:59` , direct proof hole, sharp `C^(finrank)` )
  Used exclusively by `Analysis.ae_forall_fderiv_ne_zero`;
* `ae_forall_fderiv_ne_zero` is used exclusively by `SmoothDomain.ae_exists_superlevel`
  ( `WIP/CheegerInfimum.lean:161` );
* Whereas the assumption of `ae_exists_superlevel` is **`ContDiff ℝ ∞ u`**, which upon invocation first uses `hu.of_le ENat.LEInfty.out` to reduce ∞ to `finrank`.

That is to say: **No point along the entire chain actually requires a sharp `C^n` Sard**.
Prove the `C^∞` version and supplement a `C^∞` variant of `ae_forall_fderiv_ne_zero`,
thus allowing `ae_exists_superlevel` to escape `sorryAx`, without resorting to the sharp version.

This is not replacing obligation with something weaker: the `Analysis.sard` statement maintains the same direct proof hole identity,
the hole count remains 11, only the actual blocking point of the chain is bypassed. If a sharp version is to be added later, it remains in the same place.

## Sharp C^n version of the obstacle, precisely localized

Let `A_j := {x | all derivatives of orders 1..j vanish}`; the critical set is `= A_1 ⊇ A_2 ⊇ … ⊇ A_n`.
Dimension `d`, handling layer `A_j \ A_{j+1}`, there are two paths:

**(A) Elementary collapse** (the one used in the planar setting of this repository). This layer is locally contained in a Lipschitz graph over some coordinate, projected to `d-1` dimensions; on the layer there is a fixed constant `|u y − u x| ≤ C‖y−x‖^{j+1}` (requiring `C^{j+1}`). The `d-1`-dimensional, fixed constant, exponential `m` covering lemma requires `m > d-1`, i.e., **`j ≥ d-1`**.

**(B) Dimensional Reduction Induction**. Take the `j`-th order derivative `w` (`w(x₀)=0`, `Dw(x₀)≠0`), `{w=0}` is a hypersurface,
Restrict `u` to this hypersurface and apply Sard in `d-1` dimensions. But `w` only has `C^{n-j}`, and the graph and the restricted function have only `C^{n-j}`,
And the `d-1 = n-1`-dimensional real-valued Sard requires `C^{n-1}`, hence the requirement of **`j ≤ 1`**.

The two paths together cover `j ≤ 1` or `j ≥ n-1`. Thus:

| `n` | required strata | coverage situation |
|---|---|---|
| 2 | j=1 | `j ≥ n-1 = 1`, so method A applies; **proved** (`Analysis.sard_plane`) |
| 3 | j=1, j=2 | j=1 uses B (restricted function `C^2`, exactly using the previously proven planar `C^2` Sard); j=2 uses A |
| 4 | j=1,2,3 | j=1 uses B, j=3 uses A; **j=2 neither works** |

So the first genuine obstacle in the sharp version is **n=4, j=2**: restricting to the hypersurface yields a `C^2` function on an 3-dimensional space,
while 3-dimensional real-valued Sard requires `C^3`; dropping one dimension further fails, regularity has already been exhausted.
This is precisely the difficulty in the Whitney–Morse–Sard finite-smoothness version—**this issue remains unresolved and is not recommended to address now**.
As a side result, we obtain an optional intermediate achievement: **sharp 3-dimensional Sard is now achievable** (as per the row n=3 in the table),
and if a purely sharp milestone is needed in the future, this is the cheapest one.

For `C^∞`, method B never runs out of regularity, so the induction closes directly. This is the entire reason for changing the target.

## Exact Inductive Statement

All statements have passed strict type checking at `build/audit/SmoothSardRouteStatements.lean`
(except `#check`, with no declarations, no proofs, no placeholder axioms).

Induction takes place on an open set, because the induction step provides exactly "a `C^∞` on some open set":

```lean
∀ (n : ℕ) {O : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ},
    IsOpen O → ContDiffOn ℝ ∞ u O →
    (volume : Measure ℝ) (u '' {x ∈ O | fderiv ℝ u x = 0}) = 0
```

`O = univ` The goal in coordinates is obtained; after applying an affine isomorphism, the general finite-dimensional form is obtained.
`O` Openly achieved `fderivWithin = fderiv` (`fderivWithin_of_isOpen`),
`ContDiffOn` is pointwise given on the open set `ContDiffAt` (`ContDiffOn.contDiffAt` + `IsOpen.mem_nhds`),
so the statement can uniformly use the global `fderiv` / `iteratedFDeriv`, without introducing the `within` version.

Inductive step (dimension `n+1`, `x₀` belongs to layer `j`, `1 ≤ j < n+1`):

1. Take the direction family `m` from `iteratedFDeriv (j+1) u x₀ ≠ 0`, and let `w x := iteratedFDeriv j u x m`.
   Then `w` is `C^∞`, identically zero over the entire `A_j`, and `fderiv w x₀ ≠ 0`. (L4)
2. The implicit function theorem gives the neighborhood `x₀` in the open set `U`, `ℝⁿ`, `O'` and the `O'` on `C^∞` of `γ`,
   Let `{x ∈ U | w x = 0} ⊆ γ '' O'`. (L5)
3. `h := u ∘ γ` on `O'` at `C^∞`; all points of `A_j ∩ U` are critical points of `h`
   (Because they are inherently critical points of `u`, `Dh = Du ∘ Dγ = 0`).
4. By the `n`-dimensional induction hypothesis applied to `h`, the image of this layer in the neighborhood has zero measure.
5. Lindelöf (`TopologicalSpace.isOpen_iUnion_countable`) takes a countable subcover of pointwise neighborhoods,
   assemble with `measure_biUnion_null_iff`, exactly the same gluing pattern as the preceding two rounds.

The top `A_{n+1}` is handled by the proven covering lemma (see L3). Base case `n = 0`: the domain is a subsingleton, and the image has at most one point.

## List of required lemmas

| Number | Content | Status | Estimate |
|---|---|---|---|
| L1 | The inductive statement for the open set above | To be proven (assembly) | ~80 row |
| L2 | Critical set decomposed by layer `A_n ∪ ⋃_{j∈Ico 1 n} (A_j \ A_{j+1})` | To be proven, pure set and logic | ~20 row |
| L3 | **Open set version** top zero measure | Need to widen the already proven `Analysis.volume_image_flat_pow_eq_zero` from global `ContDiff` to open sets `ContDiffOn` | ~60 line |
| L4 | Construct a scalar `w` from a nonzero derivative of order `(j+1)` | Pending; the `j=1` case was already done in `PlanarSard.lean` | ~40 lines |
| L5 | Local `C^∞` diagram of regular zero set | To be proven; **Mathlib has all the ingredients** | ~100 line |
| L6 | Transitive axioms between finite-dimensional spaces and coordinates | To be proven; `Analysis/Sard.lean` one-dimensional case exists | ~30 row |
| L7 | `C^∞` version `ae_forall_fderiv_ne_zero` | To be proven; copy existing `ae_iff` proof | ~10 line |

Search results (Mathlib, the pinned version in this repository):

* **L5 has complete raw materials**: `Mathlib/Analysis/Calculus/ImplicitContDiff.lean` is available,
  `ContDiffAt.implicitFunction`, `ContDiffAt.contDiffAt_implicitFunction`
  (implicit function preserves smoothness class) and `ContDiffAt.eventually_apply_eq_iff_implicitFunction`
  (the **graph characterization** of `f v = f u ↔ ψ v.1 = v.2`, not just inclusion).
  A splitting is also needed at the coordinate where the derivative is non-zero, `(Fin (n+1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ)`
  (a family of `Equiv.funSplitAt` / `Fin.insertNthEquiv`), and `fderiv w x₀ ≠ 0` must be translated into `(fderiv ℝ f u ∘L .inr).IsInvertible`. This is the **only new infrastructure** in this route, and also the main risk point.
* **The `Analysis/ImplicitGraph.lean` in this repository is still not usable**: it requires `C^∞` **and** an inner product space's
  `IsGraphSplitting`, targeting the graphical representation of the coarea formula, with a different interface than required here;
  it was previously confirmed to be inapplicable to `C¹`'s `Du`, so we instead use the general version from Mathlib, avoiding redundant framework construction.
* **There is no** ready-made "smooth on a neighborhood ⇒ existence of global smooth extension" lemma. This is precisely the reason for writing the induction in open set form (rather than using bump functions to extend each local function globally): the former only requires a slight relaxation in L3, while the latter requires an additional extension lemma. **It is recommended to use the open set form**.

## The Verification and Boundary of This Round

* `build/audit/SmoothSardRouteStatements.lean` passes via `-DwarningAsError=true`,
  9 statements `#check` are all valid propositions; there are **no** declarations, proofs, or placeholder axioms within the file.
* No modifications were made to any Lean source code under `formalization/`; no new modules were added.
  Existing results and hole count remain unchanged: direct hole **11** (3/3/5), certificate **24**,
  perimeter infrastructure **missing**, `Analysis.sard` and two consumers still inherit `sorryAx`.
* Default `lake build` and root directory `python3 research/verify.py` pass again; final snapshot verification receipt is
  `build/verification/latest.json`. Evidence hash is recorded at
  `research/explorations/2026-09-15-smooth-sard-route.json`.

**Clear non-assertion**: This round provides no proof of `C^∞` Sard, no proof of any intermediate layer, no resolution of any `sorryAx`, and no reduction of the statement `Analysis.sard`. The number of rows in the table above is an estimate, not a commitment.
The weighted coarea, the measurability of its level sets, and the reverse Cheeger comparison are entirely untouched.
