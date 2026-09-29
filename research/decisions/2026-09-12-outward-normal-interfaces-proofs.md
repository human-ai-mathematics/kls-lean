# 2026-09-12 — Outward normal and boundary integral interface: fill sorry (4/4 completed)

This follows the same-day [interface statements and sorry prompt](2026-09-12-outward-normal-interfaces-sorry-prompt.md). This round changes only
`formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` a file: four additional boundary regularity statements
All obligations are proved, the types of the four remain unchanged word for word, the rest 17 statements, two `def` definition bodies, and existing proof bodies remain unchanged.
Not supplemented C1/C2, coarea, Sard, not modified `RelativePerimeter.lean` / `CheegerInfimum.lean`, not registered ledger/tasks,
No certificate entry modification, aggregated import, or Blueprint update; not submitted, not pushed.

## Overview

| Obligation (namespace `FunctionalInequalities.KLS.SmoothDomain`) | Completed | None `sorryAx` | Key API | Remaining barriers |
|---|---|---|---|---|
| `continuousOn_outwardNormal` | is | is | the continuous equivalence of `outwardNormal_eq`, `ContDiff.continuous_fderiv`, `InnerProductSpace.toDual`, `ContinuousAt.inv₀`, `ContinuousWithinAt.congr_of_eventuallyEq` | — |
| `measurable_outwardNormal` | is | is | `ContinuousOn.measurable_piecewise`, `isClosed_frontier.measurableSet`, `Set.piecewise_eq_of_mem/notMem` | — |
| `isLocallyFiniteMeasure_surfaceMeasure_frontier` | is | is | `Analysis.exists_hausdorffMeasure_levelSet_lt_top`, `SmoothDomain.frontier_inter_eq`, `Measure.restrict_apply'`, `Nat.cast_sub`, `Module.finrank_zero_iff` | — |
| `integrableOn_smul_outwardNormal` | is | is | `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`, `Continuous.integrable_of_hasCompactSupport`, `Integrable.mono`, `norm_outwardNormal` | — |

The four `#print axioms`s each only have `propext / Classical.choice / Quot.sound`.

## Route

### 1. `continuousOn_outwardNormal`

Pointwise proof `ContinuousWithinAt`. At `x ∈ frontier` take `U.exists_defining` given `(W, φ)`,
`outwardNormal_eq` writes the normal on `frontier ∩ W` as normalized gradient `h y = ‖∇φ y‖⁻¹ • ∇φ y`.
`∇φ = (InnerProductSpace.toDual ℝ V).symm ∘ fderiv ℝ φ` is continuous (`hφ.continuous_fderiv`),
`hφ' x hxW` passes through `toDual_gradient` + `map_zero` to give `∇φ x ≠ 0`, so `h` is `ContinuousAt` at `x`.
`frontier ∩ W` is a member of `𝓝[frontier] x` (intersection of `self_mem_nhdsWithin` and `hW.mem_nhds hxW`),
transported via `ContinuousWithinAt.congr_of_eventuallyEq`. No countable subcover is needed, and no claim of global continuity is made.

### 2. `measurable_outwardNormal`

`outwardNormal = (frontier U.carrier).piecewise outwardNormal 0` (depending on whether `x ∈ frontier` holds,
expansion of non-boundary branches `outwardNormal` of `dif_neg`), then use the 1th, `continuousOn_const`, and
`isClosed_frontier.measurableSet` to adjust `ContinuousOn.measurable_piecewise`.
The decidability instance of `Set.piecewise` is provided by the declaration prior to `open Classical in`, consistent with the definition of `outwardNormal`.

### 3. `isLocallyFiniteMeasure_surfaceMeasure_frontier`

Pointwise construction of a finite measure neighborhood.

* `x ∉ frontier`: Take `(frontier U.carrier)ᶜ` (`isClosed_frontier.isOpen_compl`),
  After `Measure.restrict_apply'`, the set is `∅`, so its measure is zero.
`x ∈ frontier`: Boundary non-empty excludes zero-dimensional—if `finrank = 0`, `Module.finrank_zero_iff` is given to `Subsingleton V`,
  Thus `carrier` must be either `∅` or `univ`, and in both cases `frontier` is `∅`, contradicting `hx`. Hence `1 ≤ n`,
  `Nat.cast_sub` aligns `surfaceMeasure`'s natural number exponent `((n - 1 : ℕ) : ℝ)` to the pointwise lemma's `(n : ℝ) - 1`.
  Take `U.exists_defining`'s `(W, φ)`, `Analysis.exists_hausdorffMeasure_levelSet_lt_top` gives
  `N ∈ 𝓝 x` and `μH[(n:ℝ)-1] (N ∩ {φ = φ x}) < ⊤`; neighborhood takes `N ∩ W`,
  `frontier_inter_eq` Given `φ x = 0` and `N ∩ W ∩ frontier ⊆ N ∩ {φ = φ x}`.
  After expanding `surfaceMeasure`/`hausdorffNormalized`, it is a finite `ENNReal.ofReal` coefficient multiplied by a finite raw measure,
  Finish with `ENNReal.mul_lt_top`.

Dimension zero is not assumed to be excluded, but proven to not occur in this branch; the total measure of unbounded frontier is not asserted to be finite.
This statement does not invoke `RelativePerimeter.isLocallyFiniteMeasure_hausdorff_frontier` (it remains `sorry`),
so the import direction remains unchanged, and the axiom audit is clean.

### 4. `integrableOn_smul_outwardNormal`

Set `μ := (surfaceMeasure V).restrict (frontier U.carrier)`. After the 3th axiom is introduced as a local instance,
`isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure` is automatically assigned to `IsFiniteMeasureOnCompacts μ`, hence `hη.integrable_of_hasCompactSupport hηc : Integrable η μ`.
Measurability comes from the 2th axiom and `hη.measurable.smul` (since `V` is finite-dimensional, `SecondCountableTopology` holds, and `Measurable.aestronglyMeasurable` is applicable). Dominance is pointwise: on the boundary, `norm_outwardNormal` gives `‖ν‖ = 1`, outside the boundary `outwardNormal` is zero, so over the entire space `‖η x • ν x‖ ≤ ‖η x‖`, `Integrable.mono` is closed out.
`IntegrableOn` by definition is `Integrable _ μ`, no additional retracing is needed.

## Signature and linter

The output of four `#check` is identical word for word to the fill of `sorry` before (compared in the current verification round).
The `isLocallyFiniteMeasure_surfaceMeasure_frontier` `[CompleteSpace V]` is unused within the proof body—
`FiniteDimensional ℝ V` already provides completeness for each step—yet it is part of the signature fixed in the statement,
at `sorry` time, `unusedSectionVars` does not verify, and the deficiency is revealed only after completion. According to existing precedent in this repository
(`KLS/WIP/CheegerInfimum.lean:676`, `KLS/LogConcave/ConditionalFiber.lean:92`) a local `set_option linter.unusedSectionVars false in` is added before this declaration, with a comment, without modifying the signature or closing the linter in the file header.

## New declarations and import

No new declarations (private or public) are added, no new import is introduced. The four proofs only use existing API.

## Counting

The target module directly `sorry` is reduced from 9 to 5 (weighted coarea and its measurability, Sard, two Gauss–Green).
Among the 21 obligations, 16 have proofs, of which 14 rely only on standard axioms; `Analysis.ae_forall_fderiv_ne_zero` (relies on `sard`)
and `KLS.SmoothDomain.gradient_mollifiedIndicator_eq` (relies on C2) still input with `sorryAx`.
The count of remaining WIP files remains unchanged: `RelativePerimeter` 5, `CheegerInfimum` 9, `Energy/WIP/Cheeger` 5;
the total count of four files is reduced from 28 to 24. The count and phrasing of module documentation have been synchronized.

## Verification

Under `formalization/`:

* `lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites` — 3,088 jobs succeeded,
  the target module produced exactly 5 `declaration uses 'sorry'` warnings, no error, no linter warnings.
* `lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` — same as above, 5 warnings.
* `lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean` —
  failed as expected, and 5 errors **all** are retained `sorry`, no other errors or escalated warnings.
* Independent without `sorry` client (not in database, temporary files) made four real calls, each writing one:
  `ContinuousWithinAt`, `Measurable (‖ν ·‖ₑ)`, on a compact set `surfaceMeasure (K ∩ frontier) < ⊤`,
  and `integral_inner` exchanging boundary vector integral with inner product (exactly the step needed for C2);
  this client passed under `-DwarningAsError=true`, and the `#print axioms` of the four client conclusions has only the standard three.
* Each of the four target theorems was individually `#check` / `#print axioms`: types remained consistent with those before this round, axioms are
  `[propext, Classical.choice, Quot.sound]`.
* `git diff --check` is clean; diff contains only four proof fillings in the target module, one linter comment, `set_option`,
  updated module documentation count, and this record.

## Relation to C1/C2

This round has not completed C1 or C2. The four interfaces merely prepare the regularity and integrability on the boundary side:
After taking `F(x) = η(x) • e` and `div F = ⟪∇η, e⟫`, the gradient on the volume side is continuous with compact support, and on the boundary side, integrability is provided by the 4th condition,
only then can `integral_inner` and `ext_inner_right` be used to promote the scalar equation of C1 into the vector equation of C2.
C1 itself (the scalar form of Gauss–Green) remains open, and coarea and Sard remain open.
