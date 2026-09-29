# Three Pieces of the C^∞ Sard: Layering, Flat Directions, Local Charts

2026-09-15, taking over from the same day's[route investigation](2026-09-15-smooth-sard-route.md), advancing in the order L2 → L4 → L5.
Initial verification receipt `build/verification/latest.json` (`20260914T162757.518089Z`) is passed,
recomputing to confirm byte-by-byte consistency of the work area. HEAD remains `2965b32`, retaining all uncommitted results, no commit, no push.

## Scope of completion

Add `formalization/FunctionalInequalities/Analysis/SmoothSard.lean`, three public results:

```lean
theorem critical_subset_layers {n : ℕ} (u : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) :
    {x ∈ O | fderiv ℝ u x = 0} ⊆
      {x ∈ O | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0} ∪
        ⋃ j ∈ Finset.Ico 1 n,
          {x ∈ O | (∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x = 0) ∧
            iteratedFDeriv ℝ (j + 1) u x ≠ 0}

theorem exists_flat_direction {n j : ℕ} {u : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hu : ContDiff ℝ ∞ u) (h : iteratedFDeriv ℝ (j + 1) u x₀ ≠ 0) :
    ∃ m : Fin j → (Fin n → ℝ),
      ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ j u x m) ∧
        fderiv ℝ (fun x => iteratedFDeriv ℝ j u x m) x₀ ≠ 0

theorem exists_local_graph {n : ℕ} {w : (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ}
    (hw : ContDiff ℝ ∞ w) (hx₀ : w x₀ = 0) (hd : fderiv ℝ w x₀ ≠ 0) :
    ∃ (p : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (γ : (Fin n → ℝ) → (Fin (n + 1) → ℝ))
      (O : Set (Fin n → ℝ)),
      Continuous p ∧ IsOpen O ∧ p x₀ ∈ O ∧ ContDiffOn ℝ ∞ γ O ∧ γ (p x₀) = x₀ ∧
        ∀ᶠ x in 𝓝 x₀, w x = 0 → p x ∈ O ∧ γ (p x) = x
```

All three depend only on `propext / Classical.choice / Quot.sound`, with no direct holes, placeholders, or new axioms.
Corresponding to the **L2, L4, L5** entries in the route record.

## Route correction: L5 must provide the neighborhood version, not just a point.

In the exploration record, L1 is written as a `ContDiffOn ℝ ∞` over an open set. A detail that must be corrected was discovered during this round of implementation:
`ContDiffAt ℝ ∞ f x` **cannot** be upgraded to a `ContDiffOn ℝ ∞ f` over some neighborhood—
Mathlib's `ContDiffAt.contDiffOn` comes with the side condition `m = ∞ → n = ω`,
and this is not an interface flaw: the infinitesimal at a point's `ContDiffAt` is inherently "for each `k`, there is a neighborhood",
but the intersection of such neighborhoods need not itself be a neighborhood.

Thus, the implicit/inverse function theorem only provides a `ContDiffAt` at the base point is **insufficient**, and the conclusion of L5 is strengthened to a `ContDiffOn ℝ ∞ γ O` over a parameter open set. The method is to shrink the region to
`W := {x | fderiv ℝ w x (Pi.single i 1) ≠ 0}` (by `fderiv` continuity and openness),
reconstruct the invertible differential at every point of `W`, and then apply `OpenPartialHomeomorph.contDiffAt_symm` at **each point** of `H.target ∩ H.symm ⁻¹' W`, composing the resulting `ContDiffAt` pointwise into a `ContDiffOn`.
This step does not alter the inductive statement provided by the probe records, but merely raises the burden of L5 by one level; the line count estimate changes from ~100 to actually ~90.

## Actual proof

**L2**: `fderiv u x = 0` is equivalent to `iteratedFDeriv 1 u x = 0` (equal norms). If not all of `1..n` order are zero,
take `Nat.findGreatest` to capture the maximum `j` where all `1..j` order are zero, obtain `j ≥ 1` from the `1` order being zero, obtain `j < n` from the assumption being false, and by maximality obtain that `(j+1)` order is non-zero. Pure combinatorial, no analysis.

**L4**: `iteratedFDeriv (j+1) u x₀ ≠ 0` gives a direction set `v : Fin (j+1) → ℝⁿ` with nonzero values;
`iteratedFDeriv_succ_apply_left` writes it as
`(fderiv (iteratedFDeriv j u) x₀ (v 0)) (Fin.tail v)`. Take `m := Fin.tail v`,
`HasFDerivAt.continuousMultilinear_apply_const` yields
`fderiv (fun x => iteratedFDeriv j u x m) x₀ = (fderiv (iteratedFDeriv j u) x₀).flipMultilinear m`,
acting nontrivially on `v 0`. Smoothness is given by the composition of `ContDiff.iteratedFDeriv_right` and
`ContinuousMultilinearMap.apply`.

**L5**: Take `i` such that `fderiv w x₀ (Pi.single i 1) ≠ 0` (nonzero functionals must be nonzero on some basis vector).
Define `Φ x := Function.update x i (w x)`—replace the `i`-th coordinate with `w`.
`Φ` is global `C^∞`; its differential `ContinuousLinearMap.pi (fun k => if k = i then fderiv w x else proj k)`
is injective on `W`, and in finite dimensions it is a bijection, `LinearEquiv.ofInjectiveEndo` plus `LinearEquiv.toContinuousLinearEquiv` yields the required `≃L`.
The inverse function theorem `ContDiffAt.toOpenPartialHomeomorph` provides a local homeomorphism `H`.
The parameter map takes `p := Fin.removeNth i` (a **fixed continuous linear projection**, so when zeros are close, parameters are close),
the embedding takes `Fin.insertNth i 0`; when `w x = 0`, there is exactly `Φ x = insertNth i 0 (removeNth i x)`,
thus `γ := H.symm ∘ insertNth i 0` satisfies `γ (p x) = x` (`H.left_inv`) at the origin.
**No** manifold or chart framework is introduced, and **no** new implicit function framework is constructed; the repository's own `Analysis/ImplicitGraph.lean` remains unused (it requires `C^∞` data plus inner product graph splitting).

## Verification and Axiomatic Boundaries

* New module `lake env lean -DwarningAsError=true` strictly passes, `lake build` target module passes (2560 jobs).
* `build/audit/SmoothSardIngredientsAudit.lean` strictly passes: 7 clients and 3 main theorems produce 10 axiom reports in total, all containing only standard three axioms. Among them, `layers_dim_zero` covers zero-dimensional (intermediate layer set is empty); `flat_direction_one` corresponds to the planar case used in `j = 1`; `local_graph_plane` provides a concrete instance of a regular zero set `{x | x 0 = 0}`; `top_layer` confirms that the already-proven top-level interface to be combined with it remains unchanged.
* `QuadraticRemainderAudit`, `QuadraticCoverAudit`, `PlanarSardAudit`, `HigherSardAudit`, `SardLowDimAudit`, `AreaFormulaAudit`, `SuperlevelSardScope` all pass strictly again, **without modifications**.
  `SuperlevelSardScope` again confirms general `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero`, `SmoothDomain.ae_exists_superlevel` **still inherit `sorryAx`**.
* Three WIP files are compiled individually; diagnosis remains **3/3/5** direct proof holes. Total direct proof holes remain **11**; certificate remains **24**; perimeter infrastructure remains **missing**.
* Default `lake build` passes (3393 jobs). The final snapshot verification receipt for root directory `python3 research/verify.py` is `build/verification/latest.json`. Evidence hash is recorded at `research/explorations/2026-09-15-smooth-sard-ingredients.json`.
* This round **has no** expansion of any certificate or `leanok` scope, **has no** lifting of any `sorryAx`.

## Explicitly incomplete work

This round only delivers **three puzzle pieces**, `C^∞` Sard itself has not yet been proven. According to the route record numbers:

* **L3**: Topological zero measure on open sets—relaxing the already proven `Analysis.volume_image_flat_pow_eq_zero`
  from global `ContDiff` to open sets `ContDiffOn`. Requires relaxing the domain assumption of `Analysis.exists_uniform_pow_remainder` (finite order, `ContDiffOn.of_le` suffices, no triggering the side condition `∞` above). **Not started**.
* **L1**: Inductive assembly by dimension (layered + iterative dimension reduction via L4/L5 + Lindelöf gluing). **Not started**.
* **L6 / L7**: Transfer between finite-dimensional spaces and coordinates, and `C^∞` version of `ae_forall_fderiv_ne_zero`. **Not started**.
* **Sharp `C^n` `Analysis.sard`**: Statement and direct proof hole identity unchanged; both consumers inherit `sorryAx`. The `n = 4, j = 2` obstacle identified in the route record **was not encountered in this round**.
* Weighted coarea, measurability of its level sets, and reverse Cheeger comparison are completely untouched.

The entire chain is not closed.
