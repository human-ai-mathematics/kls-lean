# Minkowski Cheeger infimum product coarea bound

Date: 2026-09-13. Taking over [Minkowski coarea record](2026-09-13-minkowski-coarea-inequality.md).
The starting HEAD remains `2965b32`; the 376 entries from the previous pass with verification receipt `build/verification/latest.json` match the workspace snapshot at start exactly (`snapshot.sha256` identical). Retain previous uncommitted and untracked results; no commit or push in this round; historical decision records are not rewritten.

## Goals and Scope

`KLS.Isoperimetry.minkowskiConstant_mul_lintegral_min_superlevel_le` has been proven, the statement text is identical to the original target:

```
theorem minkowskiConstant_mul_lintegral_min_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u)
    (hu01 : ∀ x, u x ∈ Set.Icc (0 : ℝ) 1) :
    minkowskiConstant ν *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          min ((ν : Measure V) {x | t < u x}) (1 - (ν : Measure V) {x | t < u x}) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V)
```

The signatures before and after migration `pp.all` (`minkowskiConstant`, `minkowskiConstant_eq_top_of_subsingleton`, and this target) are byte-for-byte identical, `diff` is empty. All mathematical domains are preserved: any finite-dimensional real inner product space; **any** probability measure, allowing singularities and atoms; `u` only requires the original `C¹`, global Lipschitz, and `[0,1]` range. No additional assumptions such as density, absolute continuity, non-atomicity, positive dimension, `minkowskiConstant` finiteness or non-zero, or zero-measure boundaries of superlevel sets are made. The admissible sets of `minkowskiConstant` (Borel, `0 < ν B < 1`) and the definition of `minkowskiContent` remain unchanged. The proof does not use smooth recovery sequences, weighted coarea, Sard, nor any WIP theorem involving `sorryAx`.

This round reduces the direct proof hole from **15** to **14**: AnalyticPrerequisites **3**, CheegerInfimum **6**,
Energy/WIP/Cheeger **5**. The formal certification remains **24**, `lem:relative-perimeter-smoothing`'s
infrastructure remains `missing`, the entire Cheeger comparison chain is **not** completed.

## Actual proof

Record `m(a) = min {a, 1 - a}`, `A_t = {x | t ≤ u x}`, `I = ∫⁻_{Ioo 0 1} m(ν{u > t}) dt`.

1. **The mass of open and closed superlevel sets is almost everywhere consistent** (`ae_measure_superlevel_lt_eq_le`). The statement uses the weakest assumptions actually needed: for any `[SFinite μ]` of `Measure V` and any measurable `u` (no need for continuity, bounded range or
   (density)
   `∀ᵐ t ∂volume, μ {x | t < u x} = μ {x | t ≤ u x}`.
   Proof using Mathlib's `MeasureTheory.Measure.countable_meas_level_set_pos` (level sets)
   `{u = t}` pairwise disjoint, an s-finite measure assigns only positive masses to countably many sets, `Set.Countable.measure_zero` maps a countable set to
   Lebesgue null measure, and by `{u ≥ t} ⊆ {u > t} ∪ {u = t}` and `measure_union_le` we obtain equality.
   The conclusion holds on the entire real axis, and in step 3, it is restricted to `Ioo 0 1` via `ae_restrict_of_ae`.
2. **Product form of the infimum** (`minkowskiConstant_mul_min_le`). For any measurable `B`
   `minkowskiConstant ν * m(ν B) ≤ minkowskiContent ν B`.
   There are only two cases: `m(ν B) = 0` leads to direct closeout when `mul_zero`, `⊤ * 0 = 0` holds in ENNReal, thus zero mass.
   The layer with full mass does not require substitution of the infimum; admissible sets have not been relaxed; `m(ν B) ≠ 0` at time
   The two components of `min` being nonzero imply `0 < ν B` and `ν B < 1` (using `prob_le_one`), `iInf_le` added three times
   `iInf_pos` Given `h_M ≤ ν⁺(B) / m(ν B)`, then use `ENNReal.le_div_iff_mul_le`
   (Relative conditions `m ≠ 0`, `m ≠ ⊤`, the latter from `m ≤ 1`) replaced with multiplicative form. No division elimination of `h_M` throughout.
3. **Measurability of balanced mass** (`measurable_min_measure_superlevel`). `t ↦ ν {x | t < u x}` is antitone,
   and `t ↦ 1 - ν {x | t < u x}` is monotone; apply `Antitone.measurable.min Monotone.measurable`. For **any**
   `u : V → ℝ` holds without requiring `u` to be measurable. This was originally inline in `tendsto_lintegral_min_superlevel`
   `hFmeas` Here; extract it as a public lemma in this round and **migrate the original consumer**, the three lines in WIP are replaced with a call to the new lemma,
   No copy proof.
4. **Assembly**. `lintegral_const_mul` (the integrand is measurable by Step 3) brings `h_M` into the integral—this is the only place where
   Where `⊤ * I` appears, after insertion, `⊤` only encounters `m = 0` pointwise and is absorbed by `mul_zero`;
   `lintegral_mono_ae` Pair pointwise bounds with the closed superlevel set content from Steps 1 and 2;
   `setLIntegral_le_lintegral` Lift the integral on `Ioo 0 1` to the entire real axis; then connect it to the previously proven
   `lintegral_minkowskiContent_superlevel_le`. The integrand on the right-hand side
   `t ↦ minkowskiContent ν {u ≥ t}` **not** assumed measurable: `lintegral_mono_ae` and
   `setLIntegral_le_lintegral` Holds for any function. No division is used throughout; no ENNReal continuity or multiplication/division rules with missing side conditions.

`hu01` is part of the original declaration's fixed mathematical scope, and the proof only uses restricting the layer-cake integral to `Ioo 0 1`, so this assumption was not used in the proof. Following the existing practice in this repository, use `set_option linter.unusedVariables false in` silent linter,
**do not narrow the declaration scope**, do not rename, do not add an underscore prefix.

## Layering and Migration

* The new module `formalization/FunctionalInequalities/KLS/Geometry/MinkowskiConstant.lean` is hole-free,
  locally importing the closure exactly equals **1** modules: `Geometry/MinkowskiContent.lean` (whose own closure is empty), both hole-free.
  No recovery sequence, Sard, weighted coarea, relative perimeter, or any WIP dependencies are restored.
* `minkowskiConstant` and `minkowskiConstant_eq_top_of_subsingleton` are migrated verbatim from `KLS/WIP/CheegerInfimum.lean`
  into the new module, retaining the namespace `FunctionalInequalities.KLS.Isoperimetry`, with full names and `pp.all` signatures unchanged word for word, thus no compatibility aliases, forward declarations, stub modules, or duplicate proofs. `minkowskiConstant` This round of descent
  is precisely because the current conclusion must be hole-free, and the completed theorem cannot import the WIP module back into the completed layer.
* The three foundational lemmas added (steps 1, 2, 3) are placed together with the current result in this module.
* `smoothConstant`, `smoothConstant_eq_top_of_subsingleton`, the layer integral identity `lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff`,
  `tendsto_lintegral_min_superlevel`, distance truncation, and two incomplete comparisons remain in the application layer `KLS/WIP/CheegerInfimum.lean`; this file now imports the new module (`MinkowskiContent` is provided by the new module via inheritance).
  `smoothConstant` does not descend: its current purpose remains the unfinished comparisons.
* Placed in `KLS/Geometry/` rather than `Analysis/`: migrated are the existing public definitions under the `KLS.Isoperimetry` namespace,
  moving them into `Analysis/` would entail renaming.

## Verification

* `minkowskiConstant`, `minkowskiConstant_eq_top_of_subsingleton`, `minkowskiConstant_mul_min_le`,
  `ae_measure_superlevel_lt_eq_le`, `measurable_min_measure_superlevel`,
  `minkowskiConstant_mul_lintegral_min_superlevel_le`, `minkowskiContent`,
  The transitive axioms of `lintegral_minkowskiContent_superlevel_le` are all
  `propext / Classical.choice / Quot.sound`, no `sorryAx`.
* New module and the existing `Geometry/MinkowskiContent.lean` both have
  `lake env lean -DwarningAsError=true` Direct compilation passes
   (`build/audit/minkowski-constant-strict-MinkowskiConstant.log`,
  `build/audit/minkowski-constant-strict-MinkowskiContent.log`).
* The new standalone client `build/audit/MinkowskiConstantAudit.lean` is also strictly compiled, containing 9 clients and
  17 Axiom report, all using only the standard three axioms: explicitly with "not absolutely continuous with respect to each Haar measure" and "existence of atoms"
  The singular atom law still yields the conclusion; the zero-balanced measure of the empty set and the whole space (`⊤ * 0 = 0`, the infimum is not substituted into unattainable sets);
  Zero-dimensional (`Subsingleton V`, `h_M = ⊤`) **implies** that the layer-cake balanced-mass integral is zero; constant functions likewise reduce the layer-cake balanced-mass integral to zero.
  The right-hand side of Dirac's law becomes the norm of the gradient at that point; explicitly assuming `h_M = ⊤` and finite right-hand side, the layer balance integral must be zero (a valid `⊤`).
  Usage (without division); open and closed superlevel sets on Dirac laws are almost everywhere consistent; any `u` balanced quantity is measurable; `V = ℝ`'s
  One-dimensional instance.
* Both client sides `MinkowskiCoareaAudit`, `RecoveryAudit`, `DilationAudit`, `GaussGreenAudit` rerun,
  The strict mode passes, 18 + 14 + 17 + 22 axiom report still only uses the standard three axioms.
* Three WIP files actually undergo regular-mode recompilation, diagnosed as 3/6/5 direct proof holes, with no other diagnoses
  (`build/audit/minkowski-constant-wip-*.log`); still not a strict mode pass.
* Default `lake build` passes, then from root directory `python3 research/verify.py`; final source code verification receipt is
  `build/verification/latest.json`. `research/tasks.json` contains `lem:relative-perimeter-smoothing`
  The evidence is added to the new module entry, gaps are rewritten as actual gaps in the next step, status remains `missing`.

Verification is local compilation, axiom auditing, and local kernel replay under a fixed third-party compiled dependencies, not remote CI.

## Next: Precise Assembly of `minkowskiConstant_le_smoothConstant`

Goal `minkowskiConstant ν ≤ smoothConstant ρ (interior ν.support) ν`. This round's conclusion is its final one.
Analysis of input; all APIs have been verified, and the remainder are indeed compositions, but the composition itself has five side conditions that must be explicitly stated—**cannot**
treat it as completed.

1. **Three outer `le_iInf` steps.** `smoothConstant` is `⨅ U, ⨅ (0 < ν U.carrier), ⨅ (ν U.carrier < 1), …`.
   Fixing such `U`, let `m = min (ν U.carrier) (1 - ν U.carrier)`. By `0 < ν U.carrier` and
   `ν U.carrier < 1` gets `m ≠ 0`, and from `m ≤ 1` we get `m ≠ ⊤`, thus
   `ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)` replace the target with `h_M * m ≤ P_ρ(U)`.
   Here neither the finiteness of `h_M` is assumed nor division is performed.
2. **The case of relative perimeter being `⊤`.** The third argument of `exists_smooth_recovery_sequence` is
   `relativePerimeter ρ (interior ν.support) U ≠ ⊤`, so we must first classify: `P_ρ(U) = ⊤` when
   `h_M * m ≤ ⊤` By `le_top` being trivial, the recovery sequence is never called; only the branch of `P_ρ(U) ≠ ⊤` takes the sequence.
3. **Three-term unpacking of the recovery sequence.** `exists_smooth_recovery_sequence hρ U hPne` gives `u : ℕ → V → ℝ` and
   `∀ j, ContDiff ℝ ∞ (u j) ∧ (∃ K : ℝ≥0, LipschitzWith K (u j)) ∧ ∀ x, u j x ∈ Icc 0 1`,
   `Tendsto (fun j ↦ ∫⁻ ‖u j - 𝟙_{U.carrier}‖ₑ dν) atTop (𝓝 0)`, and
   `limsup (fun j ↦ ∫⁻ ‖∇(u j)‖ₑ dν) atTop ≤ P_ρ(U)`.
   Applying the current theorem term by term requires reducing `ContDiff ℝ ∞` to `ContDiff ℝ 1`: the side condition of `ContDiff.of_le` is
   `(1 : WithTop ℕ∞) ≤ ∞`, **`le_top` does not apply** (`∞` is not of this type of `⊤`, `ω` is), has been verified
   `(by simp)` can be provided. The Lipschitz constant should be extracted from `∃ K`. Thus
   `h_M * I_j ≤ ∫⁻ ‖∇(u j)‖ₑ dν`, where `I_j = ∫⁻_{Ioo 0 1} m(ν{u_j > t}) dt`.
4. **Pass L¹ convergence to the balanced quantity.** The proven `tendsto_lintegral_min_superlevel` gives
   `Tendsto I_j atTop (𝓝 m)`, it requires each `u j` to be measurable (by `ContDiff → Continuous → Measurable`),
   `[0,1]` values, `B = U.carrier` measurable (`U.isOpen.measurableSet`, `SmoothDomain`'s `isOpen` field),
   And the L¹ convergence mentioned above. Note that this lemma currently resides in `KLS/WIP/CheegerInfimum.lean`, but it itself is hole-free,
   No transitivity `sorryAx`.
5. **The limit of constant multiplication and limsup comparison.** `ENNReal.Tendsto.const_mul` (signature verified
   `Tendsto m f (𝓝 b) → b ≠ 0 ∨ a ≠ ⊤ → Tendsto (fun x ↦ a * m x) f (𝓝 (a * b))`) using
   `Or.inl hm0` as a side condition—this is exactly where `h_M = ⊤` remains valid, because the limit `m` is non-zero;
   `Filter.Tendsto.limsup_eq` (`atTop` on `ℕ` `NeBot`) writes `h_M * m` as
   `limsup (fun j ↦ h_M * I_j)`, `Filter.limsup_le_limsup` (`ℝ≥0∞` complete, two
   (The boundedness side condition of `autoParam` is automatically given by `isBoundedDefault`, together with the pointwise bound from Step 3,)
   `h_M * m ≤ limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ P_ρ(U)`.

Thus, what remains is not new mathematics, but the concrete formulation of the side conditions mentioned above 2, 3, 5, together with a **layered decision**: after assembly, `minkowskiConstant_le_smoothConstant` will have no transitive `sorryAx`, but it will still depend on
`tendsto_lintegral_min_superlevel`, `lintegral_measure_symmDiff_superlevel`,
`min_measure_le_add_measure_symmDiff`, `smoothConstant`,
which will remain in the WIP module. At that point, the established practice of this repository should be followed to move this group along with its consumers into the hole-free layer, rather than leaving it in WIP with already filled content.

The other direction `smoothConstant_le_minkowskiConstant` still requires `WIP/AnalyticPrerequisites`'s Sard and weighted
coarea, as well as `lintegral_enorm_gradient_distanceCutoff_le` and
`smoothConstant_mul_lintegral_min_superlevel_le`; there has been no progress in this round. Therefore, this round cannot be stated as
the coarea formula, Cheeger constant equality, or the entire comparison chain being proven.
