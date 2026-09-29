# Gradient integral estimation with distance truncation

Date: 2026-09-13. Taking over [distance-truncated path and state correction](2026-09-13-cutoff-route-audit-correction.md),
this correction supersedes the corresponding path and state descriptions in [one-way Cheeger comparison record](2026-09-13-cheeger-infimum-one-sided.md).
The starting HEAD remains `2965b32`; the 381 entries from the previous passed verification receipt `build/verification/latest.json` match the workspace snapshot exactly at the outset (`snapshot.sha256` identical). Previous uncommitted and untracked results are retained; no commit or push is made in this round; historical decision records are not rewritten.

## Goals and Scope

`KLS.Isoperimetry.lintegral_enorm_gradient_distanceCutoff_le` has been proven that the statement text matches the original target word for word:

```
theorem lintegral_enorm_gradient_distanceCutoff_le (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) (B : Set V) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r
```

Seven statements before and after migration (`distanceCutoff`, `distanceCutoff_mem_Icc`, `lipschitzWith_distanceCutoff`,
`distanceCutoff_eq_one_of_mem_closure`, `distanceCutoff_eq_zero_of_notMem_thickening`,
`tendsto_distanceCutoff_indicator`, and this target) have byte-identical `pp.all` signatures and an empty `diff`, including this target’s
By itself, it was previously `sorry`, and thus all section variables were retained, with no changes to the interface after filling.

All mathematical domains and interfaces are preserved: any finite-dimensional real inner product space contains the zero-dimensional case; `B` Any, without requiring non-empty, measurable, closed, bounded, or boundary zero-measure; `m` and Haar instances along with `hac` are retained exactly in the signature, even though the proofs do not use them; `distanceCutoff` is defined and the right-hand side `ν (closure B)` remains unchanged, without reverting to a weaker `ν B` upper bound, nor modified to closed thickening. The proof does not introduce coarea, Sard, or any dependency involving `sorryAx`.

This round reduces the direct proof hole from **13** to **12**: AnalyticPrerequisites **3**, CheegerInfimum **4**,
Energy/WIP/Cheeger **5**. The formal certification remains **24**. This is merely a gradient estimate along the reverse chain:
`smoothConstant_le_minkowskiConstant` is still a direct proof hole, `minkowskiConstant_eq_smoothConstant` has
`le_antisymm` proof body but inherits via the reverse direction `sorryAx`, the equality of the two Cheeger constants is **unproven**, the entire comparison chain is **incomplete**.

## Actual proof

1. The empty set is a separate branch. Mathlib's convention is `Metric.infDist x ∅ = 0`, so
   `distanceCutoff ∅ r x = max 0 (1 - 0 / r) = 1`— is the constant **1**, not `0`.
   `gradient_fun_const` gives gradient zero, left end integral is `0`; `Metric.thickening r ∅ = ∅` and
   `closure ∅ = ∅` makes the right-hand side equal to `(0 - 0) / ofReal r = 0`. Therefore there is **no** need to add the declaration to circumvent this case.
   `B.Nonempty`.
2. **Annulus.** Take `A = Metric.thickening r B \ closure B` when the `B` is non-empty. Its measurability is because
   Thicken open, closed envelope (`Metric.isOpen_thickening.measurableSet.diff isClosed_closure.measurableSet`),
   **Independent of whether `B` is measurable**. By the existing `distanceCutoff_eq_one_of_mem_closure` and
   `distanceCutoff_eq_zero_of_notMem_thickening` (both require `B` to be nonempty),
   `closure B = {d = 0}`, `thickening r B = {d < r}`.
3. **The gradient is pointwise zero outside the annulus.** This is the core of this route, and it is a **pointwise** conclusion, not an almost everywhere conclusion:
   By `distanceCutoff_mem_Icc` with range `[0,1]`, truncated on `closure B` attaining the **global maximum 1**.
   attains its **global minimum 0** outside the thickening. Thus `Filter.Eventually.of_forall` directly gives
   `IsLocalMax` / `IsLocalMin`, `IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero`
   Given `fderiv = 0`, and by the definition of `gradient` (`(toDual).symm` acting on `fderiv`, `map_zero`)
   Get `gradient = 0`. **Neither API requires additional `DifferentiableAt` assumptions**, because Mathlib at non-differentiable points
   Define `fderiv` and `gradient` to be zero. The level sets `{d = 0}` and `{d = r}` are thus naturally covered,
   Not mistakenly regarded as the interior of some open set: `{d = r}` remains a global minimum point.
   Classified as `by_cases x ∈ thickening r B`: Any point inside the thickening but not in `A` must be in `closure B`.
4. Pointwise upper bound inside an annulus. `lipschitzWith_distanceCutoff` (already has, constant `Real.toNNReal r⁻¹`) paired
   `norm_fderiv_le_of_lipschitz` (similarly without differentiability) for `‖fderiv‖ ≤ r⁻¹`,
   `LinearIsometryEquiv.norm_map` converts this to `‖gradient‖ ≤ r⁻¹`,
   Handle `Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)` to `ℝ≥0` to `ℝ` coercion,
   `ofReal_norm` Replace the real norm with `enorm`, `ENNReal.ofReal_le_ofReal` closeout. Together we obtain
   `‖gradient w_r x‖ₑ ≤ A.indicator (fun _ ↦ ENNReal.ofReal r⁻¹) x`, holds for **each** `x`.
5. **Integration and closeout.** `lintegral_mono` Using pointwise bounds from steps 3 and 4,
   `lintegral_indicator_const hAmeas` gets `ENNReal.ofReal r⁻¹ * ν A`;
   `measure_sdiff (Metric.closure_subset_thickening hr B) isClosed_closure.nullMeasurableSet
   (measure_ne_top _ _)` gives `ν A = ν (thickening r B) - ν (closure B)` (finiteness comes from probability measure);
   Finally `ENNReal.ofReal_inv_of_pos hr` and `ENNReal.div_eq_inv_mul` replace `ofReal r⁻¹ * X` with the original statement's
   `X / ENNReal.ofReal r`.

The route thus does not use Rademacher's theorem, the Lebesgue density theorem, any general lemma stating that the gradient is almost everywhere zero on level sets, nor uses
`hac`. The non-use of `hac` and `m` is a result of this stronger route, not a weakening: the conclusion, the right-hand side, and all assumptions remain unchanged.
As required, **no** unused assumptions are deleted, and **no** false usage is created; only a local overlay is applied to `set_option linter.unusedSectionVars false in` and `set_option linter.unusedVariables false in`, with the reason clearly documented in the comments, without disabling warnings for the whole file. The statement "gradient is zero at non-differentiable points" is a definitional convention in Mathlib, serving only for this estimate, and **does not** constitute any result regarding a general comparison of singular measures.

## Layering and Migration

* New module `formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean` is hole-free,
  **local import closure comprises 0 modules**: depends only on Mathlib, and is on the same level as `Geometry/MinkowskiContent.lean`.
* Migrated complete distance truncation base according to actual dependencies: definitions `distanceCutoff`, `distanceCutoff_mem_Icc`, `lipschitzWith_distanceCutoff`, `distanceCutoff_eq_one_of_mem_closure`, `distanceCutoff_eq_zero_of_notMem_thickening`, and existing `L¹(ν)` convergence `tendsto_distanceCutoff_indicator`. The first four are direct dependencies of this goal; `tendsto_distanceCutoff_indicator` is also moved down because it is hole-free, has no `sorryAx`, and all its dependencies exactly match the above four—leaving it separately in WIP would split the same `distanceCutoff` API across two modules. Proof of direct movement, with full name and `pp.all` signature unchanged word for word, with no compatibility aliases, forwarding proofs, empty shell modules, or duplicate implementations.
* **No** mechanical copying of the entire WIP file: `exists_smooth_approximation_lipschitz` remains in place. It has been proven (no need for reimplementation), but belongs to a smooth proxy interface rather than a truncation base, and would bring in the irrelevant import `Energy.Euclidean.LipschitzApproximation` into the new geometric module; its consumers are still incomplete reverse comparisons. Similarly, the two KLS side obligations for Sard/coarea, `smoothConstant_mul_lintegral_min_superlevel_le`, `smoothConstant_le_minkowskiConstant`, `minkowskiConstant_eq_smoothConstant`, and the affine support transfer segment remain in `KLS/WIP/CheegerInfimum.lean`, with one additional import line added to that file.
* `Geometry/MinkowskiConstant.lean`, `Geometry/CheegerInfimum.lean`, and `Geometry/PerimeterRecovery.lean` remain unchanged: no recovery sequences or any irrelevant geometric dependencies are introduced into the base layer.

## Verification

The transitive axioms of the seven statements (definitions, four truncation lemmas, `L¹` convergence, and this goal) are all
  `propext / Classical.choice / Quot.sound`, no `sorryAx`.
* The new module and `Geometry/{CheegerInfimum,MinkowskiConstant,MinkowskiContent}` both have
  `lake env lean -DwarningAsError=true` compilation passed (`build/audit/distance-cutoff-strict-*.log`).
* The pre- and post-migration `#check` (`set_option pp.all true`) outputs byte-by-byte `diff` are empty, confirming the section variable has not changed,
  The interface has not been accidentally modified.
* New standalone client `build/audit/DistanceCutoffAudit.lean` compiles strictly pass, containing 7 clients and 14 axiom reports
  Report: in all cases, only using the standard three axioms, with general situations assuming explicitly "`B` non-measurable" and "`B` unbounded".
  **The empty set truncation is always 1** (and by the theorem, the left end is zero); the full space (thickening and closure are both the full space, with endpoints zero);
  0-dimensional; `closure B` at every point the gradient is zero (including level sets at internal endpoints `{d = 0}`);
  `{d = r}` At every point of the level set of the external endpoint, the gradient is zero; and the migrated `L¹(ν)` convergence remains usable.
* Has client-side `CheegerInfimumAudit`, `MinkowskiConstantAudit`, `MinkowskiCoareaAudit`,
  `RecoveryAudit`, `DilationAudit`, `GaussGreenAudit` and route verification document `CutoffRouteReview`
  Rerun, strict mode passes, 14 + 17 + 18 + 14 + 17 + 22 axiom reports still only use the standard three axioms.
* Three WIP files actually undergo regular-mode recompilation, diagnosed with **3/4/5** direct proof holes, no other diagnoses
  (`build/audit/distance-cutoff-wip-*.log`); still not a strict mode pass.
* Default `lake build` passes, then from root directory `python3 research/verify.py`; final source code verification receipt is
  `build/verification/latest.json`. `research/tasks.json` contains `lem:relative-perimeter-smoothing`
  The evidence is added to the new module entry, gaps are rewritten as actual gaps in the next step, status remains `missing`.

Verification is local compilation, axiom auditing, and local kernel replay under a fixed third-party compiler dependency, not remote CI.

## Classification of Reverse Residual Dependencies

`smoothConstant_le_minkowskiConstant` There were five things before that, which must be recorded separately, not combined into "assembly":

1. **Weighted coarea formula**: `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
   (`WIP/AnalyticPrerequisites`, **direct proof hole**) — Lipschitz `u`'s
   `∫ g ‖∇u‖ dvolume = ∫_ℝ (∫_{u=t} g dℋ^{n-1}) dt`.
2. **Measurability of integral over level sets**: `Analysis.aemeasurable_lintegral_levelSet`
   (`WIP/AnalyticPrerequisites`, **direct proof hole**) — `t ↦ ∫⁻_{u=t} g dℋ^{n-1}` with respect to Lebesgue measure
   `AEMeasurable`. It is a meaningful premise at the right end of the 1th statement, and is a standalone piece.
3. **Sard**: `Analysis.sard` (`WIP/AnalyticPrerequisites` , **direct proof hole**) —— `C^n` critical values of real-valued functions
   Lebesgue null, `C^n` is the sharp regularity in the one-dimensional target dimension.
   `Analysis.ae_forall_fderiv_ne_zero` is a **filled entity**, but inherits `sard` from `sorryAx`.
4. **Encapsulation from Sard to smooth hypersurface level sets**: `SmoothDomain.ae_exists_superlevel`
   (`WIP/CheegerInfimum`, **still a direct proof hole, not already filled**).
5. **Final assembly**: `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
   (the `C¹` specialization, a direct hole), `smoothConstant_mul_lintegral_min_superlevel_le` (a direct hole), and
   `smoothConstant_le_minkowskiConstant` (direct proof hole).

Among the 1, 2, 3 are truly large-scale analysis infrastructure, for which Mathlib has no ready-made conclusions. The first item of 5 is merely a specialization of 1 to `C¹`; after completion, it merely replaces a direct proof hole with a filled one inheriting `sorryAx`, providing no help for actual gaps.

### Selected minimum next goal: `SmoothDomain.ae_exists_superlevel`

The boundary is clearest and indeed advances the structure is Axiom 4. Current statement (at `KLS/WIP/CheegerInfimum.lean`, unchanged in this round):

```
theorem ae_exists_superlevel {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x}
```

**It is now a direct proof hole, not a filled one.** After completion, it will become a filled one and inherit `Analysis.sard` from `sorryAx`—
Thus, it eliminates the structural gap of "the packaging from Sard to smooth regions," **not** the Sard itself, and will not cause any downstream conclusions to lose `sorryAx`. The direct proof hole will drop from 12 to 11 (3 / 3 / 5).

Dependencies and paths (fields of `SmoothDomain` see `KLS/Geometry/SmoothDomain.lean`):

* Take `carrier = {x | t < u x}`, `isOpen` from `isOpen_lt continuous_const hu.continuous`.
* `exists_defining`: for `x ∈ frontier carrier`, the proven `SmoothDomain.frontier_superlevel_subset`
  (`WIP/CheegerInfimum`, hole-free) is given to `u x = t`.
* Regularity: `Analysis.ae_forall_fderiv_ne_zero` requires `ContDiff ℝ (Module.finrank ℝ V) u`,
  derived from `hu.of_le` by descending from `ContDiff ℝ ∞ u`; note the side condition is
  `(Module.finrank ℝ V : WithTop ℕ∞) ≤ ∞`, **`∞` is not of this type of `⊤` (`ω` is)**,
  the same pit as in the previous round `ContDiff.of_le`. Thus we obtain `fderiv ℝ u x ≠ 0`.
* Take `W = {y | fderiv ℝ u y ≠ 0}`, it is an open set: `hu.continuous_fderiv` yields `y ↦ fderiv ℝ u y` continuity,
  `W` is the preimage of `{0}ᶜ`. `x ∈ W` follows from the previous statement.
* Take `φ = fun y ↦ t - u y`, `ContDiff ℝ ∞ φ` from `contDiff_const.sub hu`;
  `fderiv_const_sub` gives `fderiv ℝ φ y = -fderiv ℝ u y`, `neg_ne_zero` gives `W` non-zero above;
  `carrier ∩ W = {y ∈ W | φ y < 0}` because of `t - u y < 0 ↔ t < u y` is a pure set rewrite.
* Finally, the `ae_forall_fderiv_ne_zero`'s `∀ᵐ t` is combined with the above construction via `filter_upwards`.

After completion `WIP/CheegerInfimum` only remains the `C¹` specialization of coarea and two compositions; the true bottleneck in the reverse direction is still the 1, 2, 3
statements. Before these are completed, `smoothConstant_le_minkowskiConstant`, `minkowskiConstant_eq_smoothConstant`,
`constant_eq_smoothConstant_intrinsic`, and `inverseScale_eq_inv_smoothConstant_intrinsic` continue to pass dependencies on `sorryAx`, and cannot be expressed as reverse comparisons, Cheeger constant equality, or the entire chain being proven.
