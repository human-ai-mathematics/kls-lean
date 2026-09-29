# Smooth domain construction of regular hypersurface level sets and Sard interface encapsulation

Date: 2026-09-14. Taking over [gradient integral estimation with distance truncation](2026-09-13-distance-cutoff-gradient-integral.md).
The starting HEAD remains `2965b32`; at the start, `build/verification/latest.json` (passed) of 383 file entries match the workspace snapshot exactly (`snapshot.sha256` identical, `head` identical). Retain previously uncommitted and untracked results; no commit or push in this round; historical decision records are not rewritten.

## Goals and Scope

This round turns `KLS.SmoothDomain.ae_exists_superlevel` from a **direct proof hole** into a **body-filler**, with the declaration text unchanged:

```
theorem ae_exists_superlevel {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x}
```

This is the geometric construction from regular values to smooth domains, with Sard interface encapsulation, not a proof of Sard. Must be recorded separately:

* The newly added `KLS.SmoothDomain.ofSuperlevel` (including `ofSuperlevel_carrier`) in the hole-free geometry module `KLS/Geometry/SmoothDomain.lean`, `#print axioms` has only
  `propext / Classical.choice / Quot.sound`, **no `sorryAx`**.
* `ae_exists_superlevel`, although already filled, is inherited through `Analysis.ae_forall_fderiv_ne_zero` from `Analysis.sard`'s `sorryAx`, **and thus cannot be included in the list of no `sorryAx`**. It only closes the structural gap in "Sard to smooth regions", but `Analysis.sard` itself remains a direct proof hole, and no downstream conclusions have been derived to escape `sorryAx`.

The mathematical scope preserves the original statement: for any finite-dimensional real inner product space, including zero-dimensional; for any function on the full space `C∞` of real values;
the strict superlevel set `{x | t < u x}`. No additional assumptions such as positive dimension, compact support, boundedness, non-emptiness of the superlevel set, global regularity of level sets, or compactness of the boundary are made.

## Hole-free geometric constructions

`SmoothDomain.ofSuperlevel` takes the weakest natural conditions truly needed by the structure: only requires
`∀ x ∈ frontier {x | t < u x}, fderiv ℝ u x ≠ 0`, **not** requiring the level set `{x | u x = t}` to be regular,
nor requiring the entire space to be non-zero. Each field is verified one by one:

* `carrier := {x | t < u x}`, `isOpen := isOpen_lt continuous_const hu.continuous`.
* `exists_defining`: at the boundary point `x`, take `W = {y | fderiv ℝ u y ≠ 0}`, which is the preimage of `{0}ᶜ` under the continuous map `y ↦ fderiv ℝ u y` (i.e., `hu.continuous_fderiv`), hence it is an open set; `x ∈ W` is exactly the assumption.
* Define the function to take `φ = fun y ↦ t - u y` according to the convention of negative sublevel, `contDiff_const.sub hu` provides smoothness; `fderiv_const_sub` provides `fderiv ℝ φ y = -fderiv ℝ u y` (Mathlib's statement without the differentiability assumption); `neg_ne_zero` provides non-zero on `W`.
* `carrier ∩ W = {y ∈ W | φ y < 0}` is a pure set rewriting: `t - u y < 0 ↔ t < u y` ( `sub_neg` ).

The boundary and level sets are not identified. Regularity is constructed only at `frontier {t < u}` points; empty boundary, empty carrier, full carrier, and zero-dimensional cases are naturally covered by the construction, without additional assumptions or branches: in these cases the boundary is empty, and the premise of `exists_defining` is false, so the construction proceeds as usual to yield a smooth domain.

Construct placed at `KLS/Geometry/SmoothDomain.lean` (structure and other constructors `empty`, `univ`, `homothety`
in the respective module), using only the existing `NormedAddCommGroup` + `NormedSpace ℝ` context:
No completeness, measure structure, or finite dimension is required, and no manifold framework is introduced. The module does not import `WIP/AnalyticPrerequisites`, nor does it depend on any declaration with `sorryAx`.

## WIP Layer Encapsulation

`KLS/WIP/CheegerInfimum.lean` retain `ae_exists_superlevel`, the proof is two lines:

```
filter_upwards [Analysis.ae_forall_fderiv_ne_zero (hu.of_le ENat.LEInfty.out)] with t ht
exact ⟨ofSuperlevel hu fun x hx ↦ ht x (frontier_superlevel_subset hu.continuous t hx), rfl⟩
```

* The reduction of side conditions is `(Module.finrank ℝ V : WithTop ℕ∞) ≤ ∞`. **`le_top` does not apply** (this type of `⊤` is `ω` rather than `∞`), `by simp` also does not hold (empirical evidence shows “`simp` made no progress”); what holds is `ENat.LEInfty.out`. This is based on actual compilation results, recorded to prevent recurrence in the next round.
* The regular value condition has not leaked into new external assumptions: `ht` is used only internally within the proof, with signature unchanged.
* No new axioms, new type class assumptions, or "certified" black boxes have been introduced; `Analysis.sard` remains unchanged.

This file adds a single line `import FunctionalInequalities.KLS.WIP.AnalyticPrerequisites`—previously no module had it. Importing it makes `Analysis.ae_forall_fderiv_ne_zero` out of scope. This is an edge from WIP → WIP, the hole-free base layer is unaffected.

## Migration and Ordering

* **No** module migration. `frontier_superlevel_subset` remains in `KLS/WIP/CheegerInfimum.lean`:
  Its only consumer is `ae_exists_superlevel` in the same file, and the hole-free construction does not require it under the assumption of boundary forms, so it is handled by minimizing based on actual consumers, without moving, copying, or leaving compatible aliases.
* The only change is the **order within the same file**: `frontier_superlevel_subset` is moved before `ae_exists_superlevel` (previously after it, causing `Unknown identifier`). The `omit ... in` prefix is moved along with the declaration, with scope unchanged.
* After `ae_exists_superlevel` fill, `unusedSectionVars` will report `CompleteSpace`, `MeasurableSpace`, `BorelSpace`, `SecondCountableTopology` as unused (`sorry` body is exempt from this linter check, so no warnings were previously issued).
  **No** use of `omit` to narrow the signature—that would change the interface; only one declaration is augmented with `set_option linter.unusedSectionVars false in` and the reason is documented in the comment, without fully disabling it across the file.

## Verification

* `ofSuperlevel`, `ofSuperlevel_carrier`, and `frontier_superlevel_subset`'s `#print axioms`
  Contains only the three standard axioms.
* `ae_exists_superlevel` together with its client's `#print axioms` contains `sorryAx`, and with
  `Analysis.ae_forall_fderiv_ne_zero`, `Analysis.sard` are consistent; see evidence in
  `build/audit/superlevel-sard-scope.log`.
* `Geometry/SmoothDomain.lean` and a new independent client `build/audit/SuperlevelDomainAudit.lean`
  By `lake env lean -DwarningAsError=true` via (`build/audit/superlevel-domain-audit-strict.log`),
  Client 8 axiom report contains only the standard three axioms, covering: the general case requiring only regularity of the boundary;
  Define the *symbolic direction* of a function (`{t < u}` rather than `{u < t}`, the domain within `W` is exactly `{φ < 0}`);
  The critical case of a level set being horizontal with empty boundary (constant functions, `t = 0`, `fderiv` identically zero, empty support);
  Full carrier (also pointwise critical); zero-dimensional; and the non-zero linear functional half-space with explicit "carrier unbounded" "boundary unbounded" assumptions.
* Before and after migration, the `set_option pp.all true` output of `#check` with respect to `ae_exists_superlevel` and
  `frontier_superlevel_subset` byte-by-byte `diff` is empty
  (`build/audit/superlevel-signature-{before,after}.log`), section variables and interfaces unchanged.
* `KLS/WIP/CheegerInfimum.lean` actual ordinary mode recompilation, diagnosis exactly equals **3 direct proof holes**, with no other diagnoses
  (`build/audit/superlevel-wip-cheegerinfimum.log`). The number of direct proof holes decreased from **12** to **11**:
  AnalyticPrerequisites **3**, CheegerInfimum **3**, Energy/WIP/Cheeger **5**.
  This does not mean that Sard or any of its transitive dependencies have been eliminated.
* Affected existing clients rerun: `BoundaryChartAudit`, `CheegerInfimumAudit`, `CutoffRouteReview`,
  `DilationAudit`, `DistanceCutoffAudit`, `GaussGreenAudit`, `MinkowskiCoareaAudit`,
  `MinkowskiConstantAudit`, `MollifiedBoundaryScope`, `PerimeterInterfaceAudit`, `RecoveryAudit`,
  `SubgraphDivergenceAudit` All strict modes passed, axiom report contains no `sorryAx`.
  `build/audit/AreaFormulaAudit.lean` still fails to compile, because it references `Analysis.divergence`
  In an earlier round of migration to `Analysis/Divergence.lean` where the client did not import it—this is an outdated statement that **existed previously**.
  Audit script, unrelated to the current changes (this round only adds declarations and cannot cause `Unknown identifier`),
  This round does not modify it.
* Default `lake build` passes, then from root directory `python3 research/verify.py`; final source code verification receipt is
  `build/verification/latest.json`.
The formal certificate remains **24**, the perimeter infrastructure remains `missing`. This round **does not** register Sard's proven,
  Two Cheeger constants are equal or the entire comparison chain is proven.

Verification is local compilation, axiom auditing, and local kernel replay under a fixed third-party compiler dependency, not remote CI.

## Reverse Residual Dependencies: Actual Declarations and Classification

1. **Weighted coarea**: `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
   (`WIP/AnalyticPrerequisites`, direct proof hole)
   ```
   theorem lintegral_enorm_gradient_mul_eq_lintegral_levelSet {u : V → ℝ} {K : ℝ≥0}
       (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
       ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
         ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ)
   ```
   Mathlib has no coarea formula (`grep -rl coarea Mathlib/` is empty). This is a large, independent block of analysis infrastructure.
2. **Measurability of integral over level sets**: `Analysis.aemeasurable_lintegral_levelSet`
   (`WIP/AnalyticPrerequisites`, **independent direct proof hole**) — `t ↦ ∫⁻_{u=t} g dℋ^{n-1}` for Lebesgue
   `AEMeasurable` with respect to the measure. This makes the right-hand side of item 1 meaningful and is usually obtained during the coarea construction,
   Proving alone is not encapsulation work.
3. **Sard**: `Analysis.sard` (`WIP/AnalyticPrerequisites`, direct proof hole)
   ```
   theorem sard {u : V → ℝ} (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
       (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0
   ```
   Mathlib has only two types of related conclusions, **neither of which implies** this statement: `Mathlib/MeasureTheory/Function/Jacobian.lean`
   The `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` is the *same dimension* (`E → E`) Sard's lemma;
   the `Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
   `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` Only gives density for complements, not for zero measure, and under the condition that
   Domain dimension less than target dimension. Target dimension one Morse–Sard (`C^n` sharp regularity) requires induction on dimension,
   Estimates of Taylor remainders on small cubes and covering arguments, Mathlib has no existing foundation.
4. **Final assembly**: `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (Clause 1')
   the `C¹` specialization, a direct hole; filling it would only replace the direct hole by a proof body inheriting `sorryAx`),
   `smoothConstant_mul_lintegral_min_superlevel_le` and `smoothConstant_le_minkowskiConstant`
   (All are direct proof holes, all must first have the 1, 2 statements.)

Among them, the first 1, 2, and 3 are genuine independent analytical difficulties; the 4 statement could only be implemented as a wrapper prior to them.

### The next target selected: Sard's low-dimensional base case

The suggested next boundary clear goal is to add a **hole-free** lemma.

`Analysis.sard_of_finrank_le_one` (tentative name, placed at `Analysis/` level): when `Module.finrank ℝ V ≤ 1`,
`volume (u '' {x | fderiv ℝ u x = 0}) = 0`.

* **Reusable foundation (confirmed to exist in Mathlib)**: `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`
  The image of a differentiable map under a "differentially irreversible" set has zero measure; `LinearIsometryEquiv.measurePreserving`
  (`Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`) the measure is preserved under isometries.
* **New mathematics required**: Convert `u : V → ℝ` along `V ≃ₗᵢ[ℝ] ℝ` (dimension one) into `ℝ → ℝ`,
  and prove the one-dimensional case `(fderiv ℝ u x).det = 0 ↔ fderiv ℝ u x = 0`; the zero-dimensional case is handled separately
  (the image is at most a point, hence zero measure).
* **What it is not**: This is the **base case** of a general Morse–Sard argument by dimension induction, **not** a general Sard theorem for arbitrary `n`,
  and thus **does not** fill `Analysis.sard`, nor does it allow `ae_exists_superlevel` or any downstream conclusions to escape `sorryAx`.
  Before the general case is fully proven, `smoothConstant_le_minkowskiConstant`, `minkowskiConstant_eq_smoothConstant`, `constant_eq_smoothConstant_intrinsic`, and `inverseScale_eq_inv_smoothConstant_intrinsic` continue to depend on `sorryAx`,
  and cannot be expressed as reverse comparisons, Cheeger constant equality, or a fully proven chain.
