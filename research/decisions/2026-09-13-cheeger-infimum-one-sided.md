# A Direction on Cheeger Infimum: `h_M ≤ h_S`

Date: 2026-09-13. Taking over [Minkowski constant record](2026-09-13-minkowski-constant-coarea-product.md).
The starting HEAD remains `2965b32`; the 378 entries from the previous pass with verification receipt `build/verification/latest.json` match the initial workspace snapshot word for word (`snapshot.sha256` identical). Retain previous uncommitted and untracked results; no commit or push in this round; historical decision records are not rewritten.

## Goals and Scope

`KLS.Isoperimetry.minkowskiConstant_le_smoothConstant` has been proven that the statement text matches the original target word for word:

```
theorem minkowskiConstant_le_smoothConstant {ν : ProbabilityMeasure V} {ρ : V → ℝ}
    (hρ : IsBorellDensity (ν : Measure V) volume ρ) :
    minkowskiConstant ν ≤ smoothConstant ρ (interior (ν : Measure V).support) ν
```

Six statements before and after migration (`smoothConstant`, `smoothConstant_eq_top_of_subsingleton`,
`lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff`,
`tendsto_lintegral_min_superlevel`, the signature of the target) has byte-by-byte identical `pp.all`, and `diff` is empty— including the target
Itself: It was previously `sorry`, and all section variables are thus retained; after filling, `unusedSectionVars` reported no unused items.
Variables, so types and hypotheses remain unchanged, none added.

All mathematical scope preserved: any finite-dimensional real inner product space, including zero-dimensional; for Lebesgue `volume` any Borel probability density;
no assumptions of bounded support, bounded region, finite boundary measure, finite constant, or positive value, existence of intermediate mass smooth domain, or finite relative perimeter;
any assumption; `smoothConstant`'s `iInf` definition, `relativePerimeter`'s normalization,
`Ω = interior ν.support` and all admissible sets unchanged in every detail. The proof does not use reverse comparison, weighted coarea, Sard, nor any WIP theorem involving `sorryAx`.

This round reduces the direct proof hole from **14** to **13**: AnalyticPrerequisites **3**, CheegerInfimum **5**,
Energy/WIP/Cheeger **5**. The formal certification remains **24**. **Only one direction is proven**:
`smoothConstant_le_minkowskiConstant` and `minkowskiConstant_eq_smoothConstant` are still `sorry`/
transitively dependent on `sorryAx`, the infrastructure of `lem:relative-perimeter-smoothing` remains `missing`,
the entire Cheeger comparison chain is **not** completed, equality of the two Cheeger constants is **not** proven.

## Actual proof

Recall `m = min (ν U.carrier) (1 - ν U.carrier)`, `P = relativePerimeter ρ (interior ν.support) U`.

1. **Expansion and division transformation.** `simp only [smoothConstant]` After the third time `le_iInf` is fixed arbitrarily
   `U : SmoothDomain V` and `0 < ν U.carrier`, `ν U.carrier < 1`. `lt_min hUpos (tsub_pos_of_lt hUlt)`
   Given `m ≠ 0`, `m ≤ 1` and `prob_le_one` to `m ≠ ⊤`,
   `ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)` replace the target with `h_M * m ≤ P`.
   **There is no** addition of non-emptiness or positive dimension assumption: when no smooth domain is available, the premise of `le_iInf` is empty, and the target is automatically
   `h_M ≤ ⊤`, covered by the `iInf` structure itself.
2. **Branch of `P = ⊤`.** `rcases eq_or_ne P ⊤`, one branch is directly closed by `⊤`, receiving `le_top`.
   `RelativePerimeter.exists_smooth_recovery_sequence` **Only called** in `P ≠ ⊤`'s one branch.
   Its finite perimeter parameter is thus always a local fact within the branch, never elevated to a theorem's premise.
3. **Recovery sequence and termwise bounds.** Unpack `u : ℕ → V → ℝ`, each term `ContDiff ℝ ∞`, each existing
   `∃ K : ℝ≥0, LipschitzWith K (u j)` (no requirement for consistency with `j`), `[0,1]` value, `L¹(ν)` converges to `𝟙_{U.carrier}`,
   `limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ P`. Reduction uses `ContDiff.of_le`, with the side condition is
   `(1 : WithTop ℕ∞) ≤ ∞`——Note `∞` is not of this type `⊤` (`ω` is), `le_top` does not apply; the one actually used in this round is
   `(by simp)`. Applying term by term the `minkowskiConstant_mul_lintegral_min_superlevel_le` from the previous round gets
   `h_M * I_j ≤ ∫⁻ ‖∇(u j)‖ₑ dν`, where `I_j = ∫⁻_{Ioo 0 1} min (ν{u_j > t}) (1 - ν{u_j > t}) dt`.
4. **Balanced quantity convergence.** Directly reuses the already proven `tendsto_lintegral_min_superlevel`, with the premise given by the existing regularity:
   Measurability `(hureg j).1.continuous.measurable`, `[0,1]` value `(hureg j).2.2`,
   `U.carrier` measurable `U.isOpen.measurableSet`, and the `L¹` convergence in Step 3. We obtain `I_j → m`.
   No reproof of layer-cake or balanced quantity convergence.
5. **Constant multiplication and limsup.** `ENNReal.Tendsto.const_mul hItend (Or.inl hm0)`——The side condition is given by `m ≠ 0`,
   This is exactly where `h_M = ⊤` holds, throughout the entire process with **no** assumption or division by `h_M` or `h_M`.
   Then `Tendsto.limsup_eq` (`atTop` on `ℕ` `NeBot`) writes `h_M * m` as
   `limsup (fun j ↦ h_M * I_j)`, `limsup_le_limsup (Eventually.of_forall hstep)` (`ℝ≥0∞` complete,
   Two `autoParam` boundedness side conditions are automatically connected to `limsup ∫⁻ ‖∇(u j)‖ₑ dν`, and finally connected to the upper bound of the recovery sequence to obtain `≤ P`.
   One cannot interchange an unproven limit and an integral.

## Layering and Migration

* The new module `formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean` is hole-free,
  locally imports a closure of 32 modules, **with no WIP modules among them**; it only exists atop the two existing hole-free chains
  `Geometry/PerimeterRecovery` (recovery sequence) and `Geometry/MinkowskiConstant` (product coarea bound).
* The set of modules migrated into this module is the minimal set actually required by the current round's conclusion: `smoothConstant`,
  `smoothConstant_eq_top_of_subsingleton`, `lintegral_measure_symmDiff_superlevel`,
  `min_measure_le_add_measure_symmDiff`, `tendsto_lintegral_min_superlevel`. The proof is moved verbatim,
  the namespace remains `FunctionalInequalities.KLS.Isoperimetry`, and the full name with `pp.all` signature is unchanged word for word,
  thus there are no compatible aliases, forwarded proofs, empty shell modules, or copied auxiliary proofs.
* `Geometry/MinkowskiConstant.lean` **is unchanged**: smooth recovery, relative perimeter, and any WIP dependencies are not introduced
  into this base layer; its local closure remains only `Geometry/MinkowskiContent`.
* What remains in the application layer `KLS/WIP/CheegerInfimum.lean` is: the two KLS obligations of Sard and weighted coarea,
  distance truncation `distanceCutoff` and its lemma along with `lintegral_enorm_gradient_distanceCutoff_le`,
  the already proven `exists_smooth_approximation_lipschitz`, the reverse direction of
  `smoothConstant_mul_lintegral_min_superlevel_le` and `smoothConstant_le_minkowskiConstant`,
  the equation `minkowskiConstant_eq_smoothConstant` and the affine support transfer segment. This file now only imports the new module
  (`MinkowskiConstant` and `PerimeterRecovery` are provided by the new module).
* Placed in `KLS/Geometry/` rather than `Analysis/`: the migration involves existing public definitions under the `KLS.Isoperimetry` namespace,
  moving them into `Analysis/` would entail renaming. File names matching WIP but at different paths have their roles explicitly stated in the respective module docstrings.

## Verification

* `smoothConstant`, `smoothConstant_eq_top_of_subsingleton`, `lintegral_measure_symmDiff_superlevel`,
  `min_measure_le_add_measure_symmDiff`, `tendsto_lintegral_min_superlevel`,
  `minkowskiConstant_le_smoothConstant`, `RelativePerimeter.exists_smooth_recovery_sequence`,
  The transitive axioms of `minkowskiConstant_mul_lintegral_min_superlevel_le` are all
  `propext / Classical.choice / Quot.sound`, no `sorryAx`.
* New module and `Geometry/MinkowskiContent`, `Geometry/MinkowskiConstant`,
  `Geometry/PerimeterRecovery` all compiled with `lake env lean -DwarningAsError=true`
   (`build/audit/cheeger-infimum-strict-*.log`).
* The pre- and post-migration `#check` outputs (`set_option pp.all true`) byte-by-byte `diff` are empty, confirming the section variable is not
  Variation, without unintended increase of assumptions or change of type.
* New standalone client `build/audit/CheegerInfimumAudit.lean` compiles strictly pass, containing 6 clients and 14 axiom reports
  Report, all using only the standard three axioms: general case (explicitly with the "support unbounded" assumption); zero-dimensional (both infima are `⊤`,
  Compare to `⊤ ≤ ⊤`; **no** smooth domain available `smoothConstant = ⊤` (by the structure itself `iInf`, existence is not required)
  Assumption); when the relative perimeter of a single admissible domain is `⊤`, the ratio is `⊤` with no constraint on the infimum; when the relative perimeter of a certain admissible domain is `0`,
  Prove `minkowskiConstant = 0`; when `minkowskiConstant = ⊤` is established, each relative perimeter of a smooth domain is `⊤`
  (Legal usage of `⊤`, without division). The client does not add any assumptions to production theorems for testing.
* Has client-side `MinkowskiConstantAudit`, `MinkowskiCoareaAudit`, `RecoveryAudit`, `DilationAudit`,
  `GaussGreenAudit` rerun, strict mode passes, 17 + 18 + 14 + 17 + 22 axiom reports still only use the standard three axioms.
* Three WIP files actually undergo regular-mode recompilation, diagnosed as 3/5/5 direct proof holes, with no other diagnoses
  (`build/audit/cheeger-infimum-wip-*.log`); still not a strict mode pass.
* Default `lake build` passes, then from root directory `python3 research/verify.py`; final source code verification receipt is
  `build/verification/latest.json`. `research/tasks.json` contains `lem:relative-perimeter-smoothing`
  The evidence is added to the new module entry, gaps are rewritten as actual gaps in the next step, status remains `missing`.

Verification is local compilation, axiom auditing, and local kernel replay under a fixed third-party compiler dependency, not remote CI.

## Reverse Directional Exact Dependencies

The route of `smoothConstant_le_minkowskiConstant` is: for each Borel set of intermediate mass `B`, use distance truncation
`w_r = (1 - d(·,B)/r)₊` approximation `𝟙_B`, replace `w_r` with a smooth substitute, then use the coarea inequality on the `h_S` side.
Its dependence is divided into three categories, which must be distinguished:

**(a) Inputs already possessed, no need for further proof.** `exists_smooth_approximation_lipschitz` **Proved**
(By `Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`, this conclusion is certified and has no
`sorryAx`): It replaces the global Lipschitz, `[0,1]`-valued `w` with a pointwise `C^∞`, Lipschitz, `[0,1]`-valued and
`L¹(ν)` convergent sequence with convergent gradient integrals, requiring only `ν ≪ m` (where `m` is Haar). The range of distance truncation, Lipschitz constants, taking `closure B` on `1` and `thickening r B` outside `0`, as well as
`tendsto_distanceCutoff_indicator` have all been proven. The side of `tendsto_lintegral_min_superlevel` in the current proof can also be directly reused.

(b) Three places still requiring independent proofs. Gradient integral estimate under distance truncation
`lintegral_enorm_gradient_distanceCutoff_le`; weighted coarea formula
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and measurability of its level set integral
`Analysis.aemeasurable_lintegral_levelSet`; and Sard `Analysis.sard`
(`Analysis.ae_forall_fderiv_ne_zero` and `SmoothDomain.ae_exists_superlevel` are filled in, but transitively dependent on
`sorryAx`, and eliminated together with Sard). The latter two constitute genuine large-scale analysis infrastructure.

**(c) Assembly layer.** `smoothConstant_mul_lintegral_min_superlevel_le` Requires both Sard and weighted coarea, and above that comes `smoothConstant_le_minkowskiConstant`.

### Selected minimum next goal: `lintegral_enorm_gradient_distanceCutoff_le`

The boundary is clearest and does not rely on Sard or coarea, as in (b) the first statement. The original claim (in `KLS/WIP/CheegerInfimum.lean`, unchanged in this round):

```
theorem lintegral_enorm_gradient_distanceCutoff_le (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) (B : Set V) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r
```

The gaps it eliminates are the distance truncation gradient estimates along the reverse chain—`smoothConstant_le_minkowskiConstant` three gaps
The only part independent of Sard/coarea, thus can be completed independently, and after completion the direct proof hole of `WIP/CheegerInfimum`
From 5 to 4, while the Sard and coarea states remain unchanged.

Key dependencies and paths (verified against Mathlib names, `v4.33.0`):

1. `B = ∅` Single branch: `Metric.infDist_empty` to `d ≡ 0`, so `w_r ≡ 1` is a constant function, left-hand side is `0`;
   The right-hand side is `(0 - 0)/ofReal r = 0`. Therefore **no** nonemptiness assumption is needed for the declaration.
2. `B` write `d x = Metric.infDist x B` (`1`-Lipschitz, continuous) when nonempty.
   By `Metric.mem_closure_iff_infDist_zero` and `Metric.mem_thickening_iff_infDist_lt`:
   `closure B = {d = 0}`, `thickening r B = {d < r}`, and
   `{x | 0 < w_r x ∧ w_r x < 1} = {0 < d < r} = thickening r B \ closure B`, **is an open set** (`d` continuous).
3. **A key step does not require the Lebesgue density theorem**: The range of `w_r` is `[0,1]`, attained globally on `closure B`
   The maximum `1`, attained globally at the minimum `{d ≥ r}` on `0`. Therefore at any differentiable point on these two sets,
   `IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero` (both confirmed to exist in Mathlib) are given directly.
   `fderiv = 0`, thus `gradient = 0`. Mathlib does not have "the gradient of a Lipschitz function is almost everywhere zero on level sets"
   The general lemma, and in fact we don't need it at all—this is the reason the boundary of the goal is clear.
4. Differentiability: Mathlib’s `LipschitzWith.ae_differentiableAt` (Rademacher) applies **to any
   The `[μ.IsAddHaarMeasure]`'s `μ` statement, so we can directly take `μ = m` to get `∀ᵐ x ∂m, DifferentiableAt ℝ w_r x`,
   Then by `hac : ν ≪ m` it becomes `ν`-almost everywhere. No comparison is needed between Haar and `volume`,
   `hac` It is exactly here, and only here, that it is used.
5. Finish: `lintegral_mono_ae` replaces the integrand by `(A.indicator fun _ ↦ (1/r in ENNReal))`, where
   `A = thickening r B \ closure B`; `lipschitzWith_distanceCutoff` (proven, constant `1/r`) at differentiable points
   `‖∇w_r‖ ≤ 1/r` (`LipschitzWith` to `‖fderiv‖ ≤ K`); `lintegral_indicator_const` gets
   `(1/r) * ν A`; `measure_diff` (`closure B ⊆ thickening r B` by `Metric.closure_subset_thickening hr`,
   Measurability is given by closed and open sets, finiteness by probability measure) `ν A = ν (thickening r B) - ν (closure B)`;
   Finally, conversions such as `ENNReal.div_eq_inv_mul` align the right-hand side.

The other two (weighted coarea and Sard) are outside the scope of this goal, and there has been no progress in this round; before they are completed,
`smoothConstant_le_minkowskiConstant`, `minkowskiConstant_eq_smoothConstant`,
`constant_eq_smoothConstant_intrinsic` and `inverseScale_eq_inv_smoothConstant_intrinsic`
remain transitively dependent on `sorryAx`, and cannot be expressed as Cheeger constants being equal or the entire comparison chain having been proven.
