# 2026-09-12 — Outward normal and boundary integral interface: statement supplementation and sorry hint

Owner requirement: Add missing interfaces; for this round, only write the statement, and all proof bodies are `by sorry`; generate proof prompting text.
This round adds the following four public obligations in `KLS/WIP/AnalyticPrerequisites.lean`; the original types, definitions, and proof bodies are retained.
No additional assumptions of C1/C2 are introduced, no WIP is registered, and Gauss–Green is not completed.

| Name (namespace `FunctionalInequalities.KLS.SmoothDomain`) | Conclusion and Boundary |
| --- | --- |
| `continuousOn_outwardNormal` | The normal vector is continuous on `frontier U.carrier`; does not claim continuity over the entire space; no requirement for finite dimensionality |
| `measurable_outwardNormal` | The normal vector field outside the boundary is Borel measurable over the entire space; no requirement for finite dimensionality |
| `isLocallyFiniteMeasure_surfaceMeasure_frontier` | **Normalization** `surfaceMeasure V` is locally finite when restricted to a smooth region with a closed boundary; does not claim the surface measure of the environment is locally finite |
| `integrableOn_smul_outwardNormal` | `η` When continuous and having compact support, `η • outwardNormal` is integrable with respect to the normalized boundary measure; local finiteness is a preliminary conclusion and not assumed separately. |

Locally defined functions and proven `outwardNormal_eq` suffice to establish pointwise boundary continuity, and subsequently measurable properties via piecewise closed sets; no countable subcover needs to be constructed. The two measurable/continuous interfaces alone cannot substitute for integrability. The difficulty of deriving C2 from C1 should be stated as: after completing the boundary regularity and integrability interfaces, the shorter vector integral assembly can proceed.

The current direct `sorry` count for the four WIP files is `5 + 9 + 9 + 5 = 28` (in order: RelativePerimeter, CheegerInfimum, AnalyticPrerequisites, Energy/WIP/Cheeger). AnalyticPrerequisites has 21 obligations, 12 existing proof bodies already filled, 9 direct holes; among the original 12 proof bodies, only 10 still have transitive dependencies without `sorryAx`. This increase in count comes from explicit decomposition of preconditions, and does not indicate degradation of existing proofs. Previous audit records are retained as snapshots at that time.

Current statement check: target module `lake build` passed (3,088 jobs), the module has exactly 9 expected `sorry` warnings;
Independent API client passed under `-DwarningAsError=true`, all four newly declared axioms in audit include `sorryAx`, not as proven results. `research/tasks.json` refreshes only the digests of affected inputs and incomplete explanations, infrastructure state remains `missing`.

The following code block can be directly passed to the proof session. This prompt applies only to the addition of four new statements, replacing the old 17 prompts in this subtask; the existing C1/C2, Sard, coarea, and other files' `sorry` are left for another task.

```text
Repository: /Users/lyuyuwei/Documents/ChatGPT/KLS
Lake root directory: formalization/
Target file: formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
First check git status, formalization/lean-toolchain and lake-manifest.json, do not use historical version numbers to replace the current environment.
First read HANDOFF.md, research/naming.md, the description of the target module, and
research/decisions/2026-09-12-outward-normal-interfaces-sorry-prompt.md.

Task: Only fill in sorry for the following four new theorems, all in namespace
FunctionalInequalities.KLS.SmoothDomain:
1. continuousOn_outwardNormal
2. measurable_outwardNormal
3. isLocallyFiniteMeasure_surfaceMeasure_frontier
4. integrableOn_smul_outwardNormal

Scope and rules:
- Keep the four theorems and all existing statements' types unchanged, keep all def definition bodies and existing proof bodies unchanged.
  Do not strengthen SmoothDomain, nor add caller assumptions such as bounded region, positive dimension, measurable normal, and finite boundary measure.
- Only edit the target Lean file; allow necessary import and private auxiliary lemmas. Additional public API additions require separate justification for necessity.
  A proofs record can be appended, listing completion status, verification commands, axioms, and remaining obstacles.
- Do not fill in C1/C2, coarea, Sard, or RelativePerimeter/CheegerInfimum old sorry.
  Do not reorder modules or reverse import AnalyticPrerequisites into RelativePerimeter to avoid cycles.
- Do not add new axioms, opaque fake proofs, unsafe code, disabled checks, or hidden sorry. Do not move a hole from a new theorem into an auxiliary lemma and claim completion. If the statement has issues, keep sorry and provide a counterexample, do not arbitrarily modify the type.
- Not recording ledger or task completion status, not modifying certificate entry, aggregate import, Blueprint lean/leanok.
  Do not submit or push. Unresolved goals may be retained, but must be reported accurately.

Route 1: Boundary continuity (no need for countable cover)
For any x ∈ frontier U.carrier, use U.exists_defining to obtain W, φ, hW, hxW, hφ, hφ', hU.
On W ∩ frontier, U.outwardNormal_eq gives ν(y) = ‖gradient φ y‖⁻¹ • gradient φ y.
- Gradient continuity: gradient φ is the composition of (InnerProductSpace.toDual ℝ V).symm and fderiv ℝ φ;
  hφ.continuous_fderiv provides continuity. Note the namespace of toDual.
- At x, hφ' x hxW gives nonzero fderiv, via toDual_gradient and map_zero, implying nonzero gradient.
- Using ContinuousAt.norm, inv₀, and smul, we obtain continuity of the normalized gradient at x.
- By hW.mem_nhds hxW and self_mem_nhdsWithin, we get eventually equal on relative neighborhoods, and transfer via ContinuousWithinAt.congr_of_eventuallyEq_of_mem.
No proof of ν's continuity over the entire space; zero extension is generally discontinuous at the boundary.

Route 2: Measurability over the full space
Use statement 1, continuous_const.continuousOn, and isClosed_frontier.measurableSet, and invoke
ContinuousOn.measurable_piecewise. Divide into cases based on whether x lies in the frontier, expand the zero branch of outwardNormal, align the piecewise function with outwardNormal. No measurable selection is needed for locally defined functions.

Route 3: Local finiteness of normalized boundary measure (this is a geometric assembly independent of measurability)
This file has proven Analysis.exists_hausdorffMeasure_levelSet_lt_top.
For boundary points, use U.exists_defining and U.frontier_inter_eq to include a neighborhood of the boundary within a regular zero level set, then obtain a finite raw Hausdorff measure in some neighborhood via the pointwise result.
For non-boundary points, take a neighborhood disjoint from the boundary using the frontier's closedness, and restrict the measure to zero.
Thus, for every point in the full space, construct a finite measure neighborhood, establishing IsLocallyFiniteMeasure.
- The target measure is always (surfaceMeasure V).restrict (frontier U.carrier).
- The dimension of surfaceMeasure is a natural number n - 1; the pointwise input is a real number (n : ℝ) - 1.
  When the dimension is positive, handle Nat.cast_sub; when n = 0, the space is a single point and the frontier is empty, so the restricted measure is zero.
  Do not exclude zero-dimensional cases by adding Nontrivial V or 0 < n.
- Expand surfaceMeasure/hausdorffNormalized, multiplying the raw measure by a finite ENNReal.ofReal coefficient.
  Measure scaling preserves the required local finiteness; the interchange of restriction and scaling must be explicitly handled.
- It is not necessary to first prove that the total measure of the unbounded frontier is finite, as this is generally not true.
- RelativePerimeter already has isLocallyFiniteMeasure_hausdorff_frontier, but it still has sorry.
  It cannot be used as an unconditional certification input to complete this entry; ultimately, #print axioms must have no sorryAx.
  Using the pointwise level-set lemma proven in this file allows maintaining the current one-way import and avoids contaminating the old hole.

Route 4: Integrability of boundary integrals
Let μ := (surfaceMeasure V).restrict (frontier U.carrier). Using statement 3 to install the locally finite instance,
we obtain IsFiniteMeasureOnCompacts μ. hη.integrable_of_hasCompactSupport hηc gives η ∈ L¹(μ).
- Statement 2 and hη.measurable.smul provide the measurability of η • ν; the strong measurability required for finite-dimensional spaces under topological conditions is achieved via aestronglyMeasurable.
- On the boundary, norm_outwardNormal = 1; outside the boundary, outwardNormal = 0, so throughout the full space we have ‖η(x) • ν(x)‖ ≤ ‖η(x)‖. Using Integrable.mono domination, we then return to IntegrableOn.
- If we first establish a private version for a finite measure μ on compact sets, we still need to instantiate it to the boundary measure above; we cannot prove only the conditional version and omit the current public conclusion.

The relationship for C2 (this task does not fill in C2):
Take F(x) = η(x) • e, the trace of a rank-one operator gives div F = ⟨gradient η, e⟩, using C1.
The volume-side gradient is continuous and has compact support, and the boundary-side is integrable by the 4th lemma, only then can integral_inner and ext_inner_right be applied.
Elevated to a vector equation. Do not consider the completion of these four preliminary interface reports as the completion of C1 or C2.

Verification and reporting:
Run in formalization/:
  lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites
  lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
Normal mode should have no error; only declarations that retain 'sorry' are allowed as warnings.
When all four statements are completed, the direct sorry in this module should decrease from 9 to the original 5; all other file counts remain unchanged.
Check each one individually in a separate client with #check and #print its full type, and #print axioms; completed items are allowed only
propext / Classical.choice / Quot.sound, and the standard axiom list may be a subset thereof.
Do not consider a statement complete simply because its proof body contains no sorry; the transitive dependencies must be verified.

When there are still old sorrys, directly running -DwarningAsError=true on the entire WIP file is expected to fail;
record whether the error is merely the retained sorrys, and do not require passing by suppressing warnings to produce a green result.
One can run -DwarningAsError=true on an independent, sorry-free client that imports a built WIP to check actual API calls,
but the client's successful compilation alone cannot substitute the above axioms check.

Finally git diff --check, and verify that the diff contains only four target proofs, fillings of necessary auxiliary items/import, and new reports.
Report listed item by item: name | whether completed | whether sorryAx absent | key API | remaining obstacles.
```
