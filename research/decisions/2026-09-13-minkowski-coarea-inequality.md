# Minkowski Coarea Inequality

Date: 2026-09-13. Taking over [smooth recovery sequence record](2026-09-13-smooth-recovery-sequence.md).
Starting HEAD is `2965b32`; the 374 files from the previous pass and the initial workspace snapshot are matched one by one
(including the deleted `KLS/WIP/RelativePerimeter.lean`, whose entries are recorded as `null`).
Retain previous uncommitted and untracked results; no commit or push in this round; historical decisions remain unchanged.

## Goals and Scope

`KLS.Isoperimetry.lintegral_minkowskiContent_superlevel_le` has been proven that the statement text matches the original target word for word:

```
theorem lintegral_minkowskiContent_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V)
```

All mathematical scope preserved: any finite-dimensional real inner product space; **any** probability measure, allowing singular and atomic components; `u` only requiring the original
`C¹` and global Lipschitz, without additional assumptions of bounded range, compact support, non-zero dimension, density, absolute continuity, positive dimension, extra integrability, or zero-measure boundary of superlevel sets; the left side is a **closed** superlevel set, integration traverses the entire real axis; `minkowskiContent` definition
(open thickening, ENNReal truncation subtraction, `𝓝[>] 0`-based liminf) unchanged in any detail. The proof does not use weighted coarea, Sard, or any
bearing `sorryAx` WIP theorem.

This round reduces the direct proof hole from **16** to **15**: AnalyticPrerequisites **3**, CheegerInfimum **7**,
Energy/WIP/Cheeger **5**. The formal certification remains **24**, `lem:relative-perimeter-smoothing`'s
infrastructure remains `missing`, the entire Cheeger comparison chain is **not** completed.

## Actual proof

Recall `A t = {x | t ≤ u x}`, `v_r = ballSup u r`, `q_r = (v_r - u)/r`.

1. **Local supremum.** Added `ballSup u r x = sSup (u '' closedBall x r)`. Global Lipschitz provides
   `bddAbove_image_closedBall` (`u y ≤ u x + K r`, holds for any real `r`, the empty ball case is trivial),
   Thus `le_ballSup` (`u x ≤ v_r x`, `0 ≤ r`) and `ballSup_le_add` (`v_r x ≤ u x + K r`),
   Together give `0 ≤ q_r ≤ K`. `lipschitzWith_ballSup` uses translation `z ↦ z + (y - x)` to take a member of a closed ball
   Send into another closed ball, obtaining `v_r` and `u` with constant Lipschitz, thus continuous and measurable. No new compactness is introduced,
   The supremum or measurability infrastructure, nor the use of finite-dimensional compact balls or Sard.
2. **Nearest-neighbor witnesses and strips.** `thickening_superlevel_subset`:
   `thickening r (A t) ⊆ {x | u x < t ∧ t ≤ v_r x} ∪ A t`. The proof only uses
   Take `Metric.mem_thickening_iff` and witness `dist x z < r` and `t ≤ u z`'s `z`, which lies in `closedBall x r`.
   Thus for each `t`
   `ν(A_t^r) - ν(A_t) ≤ ν(S_r t)`, where `S_r t = {x | u x < t ∧ t ≤ v_r x}`;
   Completed with `tsub_le_iff_right` and `measure_union_le`; no prior proof
   `ν(A_t^r) - ν(A_t) = ν(A_t^r \ A_t)`, hence no need for complement measurability.
3. **Joint measurability of strips and Tonelli.** A strip is written as a measurable set on `ℝ × V`
   `T_n = {p | u p.2 < p.1 ∧ p.1 ≤ v_{r_n} p.2}` (`u`, `v_{r_n}` continuous).
   `measurable_measure_prodMk_left` gives measurability of `t ↦ ν (S_{r_n} t)`, precisely bypassing
   At the place of "Is `t ↦ minkowskiContent ν (A t)` measurable?": **Fatou applies only to the strip quotient**, the original integrand
   Entry only through `lintegral_mono` pointwise comparison, `∫⁻` is defined for any function, without requiring it to be measurable.
   `Measure.prod_apply` and `Measure.prod_apply_symm` given
   `∫⁻ t, ν (S_{r_n} t) = ∫⁻ x, volume (Ioc (u x) (v_{r_n} x)) dν = ∫⁻ x, ofReal (v_{r_n} x - u x) dν`,
   The constant factor is moved in and out of the integral sign using `lintegral_mul_const'` (`(ofReal r_n)⁻¹ ≠ ⊤`).
   `ENNReal.ofReal_div_of_pos` Complete the conversion between real number quotients and ENNReal quotients.
4. **Radius sequences and liminf in two directions.** Take `r n = 1/(n+1) > 0`,
   `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` Given `r → 0` in `𝓝[>] 0`;
   `Tendsto.liminf_le_liminf_comp` Give the correct direction
   `liminf_{𝓝[>]0} f ≤ liminf_n f(r n)` (sequence filters are finer, liminf is larger),
   Thus the original neighborhood definition is only enlarged, not replaced by a sequence limit.
   Then `lintegral_mono` + `lintegral_liminf_le` (Fatou, using the measurability of step 3) compares pointwise
   Transfer integral.
5. **Gradient control.** `limsup_ofReal_ballSup_le`: Only prove the upper bound. By
   `hasGradientAt_iff_isLittleO_nhds_zero` and `Metric.eventually_nhds_iff` take `δ`,
   For `‖h‖ ≤ r < δ` has `u(x+h) ≤ u x + ⟪∇u x, h⟫ + ε‖h‖ ≤ u x + (‖∇u x‖+ε) r`
   (`real_inner_le_norm`), hence `q_{r_n}(x) ≤ ‖∇u x‖ + ε` ultimately holds,
   Finish with `ENNReal.le_of_forall_pos_le_add`. We **do not** prove `q_r → ‖∇u‖`: the integral upper bound needs only the upper-semicontinuity direction.
   By the probabilistic nature of `0 ≤ q_{r_n} ≤ K` and `ν`, the dominating function `ofReal K` (with integral `ofReal K < ⊤`),
   `limsup_lintegral_le` move `limsup` into the integral, finally `liminf_le_limsup`.
   The right-hand side is therefore precisely the original statement's `∫⁻ ‖gradient u‖ₑ dν`, not any crude upper bound on a `K`.

## Layering, Migration, and Naming

* New module `formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean` is hole-free,
  **locally transitively imports a closure of 0 modules**: it only depends on Mathlib and imports no KLS or WIP layers.
* `minkowskiContent`, `measure_closure_eq_of_minkowskiContent_ne_top`, and the new theorem are migrated into this module together,
  the namespace remains `FunctionalInequalities.KLS.Isoperimetry`, **the full name is unchanged word-for-word**,
  thus there are no compatibility aliases, forward declarations, or stub modules, and no duplicate proofs.
  The proof of `measure_closure_eq_of_minkowskiContent_ne_top` is moved verbatim, unchanged.
* The unfinished Cheeger infimum comparison (`minkowskiConstant`, `smoothConstant`, two product inequalities,
  infimum comparisons in both directions) remains in the application layer `KLS/WIP/CheegerInfimum.lean`, and this file is now directly importing the new module.
  `minkowskiConstant` does not follow down: its current sole use is for those unfinished comparisons.
* Placed in `KLS/Geometry/` rather than `Analysis/`: migrated are the existing public definitions under the `KLS.Isoperimetry` namespace,
  moving into `Analysis/` would entail renaming. The theorem itself is indeed an analysis conclusion independent of KLS, as evidenced by zero local import closure.
* `lintegral_minkowskiContent_superlevel_le`'s `[FiniteDimensional ℝ V]` becomes unused
  section variable after the proof. Following the existing practice in this repository (`constant_eq_minkowskiConstant_intrinsic`),
  `set_option linter.unusedSectionVars false in` is used to silence the linter, **without altering the mathematical scope of declarations**.

## Verification

* `lintegral_minkowskiContent_superlevel_le`, `minkowskiContent`,
  `measure_closure_eq_of_minkowskiContent_ne_top`, `ballSup` and four `ballSup` lemmas,
  The transitive axioms of `limsup_ofReal_ballSup_le` are all `propext / Classical.choice / Quot.sound`, with no `sorryAx`.
* The new module compiles directly through `lake env lean -DwarningAsError=true`
   (`build/audit/minkowski-strict-MinkowskiContent.log`).
* The new standalone client `build/audit/MinkowskiCoareaAudit.lean` is also strictly compiled, containing 8 clients and
  18 Axiom report, using only the standard three axioms: any probability law (explicitly accompanied by "not absolutely continuous with respect to each Haar measure")
  and the assumption that `u` has unbounded range) still yields the conclusion; constants give zero, as does dimension zero (`Subsingleton V`);
  Atom law (Dirac) right endpoint becomes the gradient norm at that point; `ballSup u 0 = u`; near-neighbor witness;
  An arbitrary positive radius growth quotient `≤ K`; the real axis `u = id` provides the full axis integral `≤ 1`.
* Both `RecoveryAudit`, `DilationAudit`, and `GaussGreenAudit` clients have been rerun, passing under strict mode,
  14 + 17 + 22 axiom reports still only use the standard three axioms.
* Three WIP files actually undergo regular-mode recompilation, diagnosed with **3/7/5** direct proof holes, no other diagnoses
  (`build/audit/minkowski-wip-*.log`); still not a strict mode pass.
* Default `lake build` passes (3393 jobs), then from root directory `python3 research/verify.py`;
  The final source code verification receipt is `build/verification/latest.json`.
  Add the new module to the evidence for `lem:relative-perimeter-smoothing` in `research/tasks.json`,
  gaps rewritten as the next-step actual gap, status remains `missing`.

Verification is local compilation, axiom auditing, and local kernel replay under a fixed third-party compiler dependency, not remote CI.

## Next: `minkowskiConstant_mul_lintegral_min_superlevel_le` What's still missing

Objective:
```
minkowskiConstant ν * ∫⁻ t in Ioo 0 1, min (ν {u > t}) (1 - ν {u > t}) ≤ ∫⁻ ‖∇u‖ₑ dν
```
On `C¹`, Lipschitz, and `[0,1]` values of `u`. The current conclusion is its sole analytical input; the rest is measure-theoretic assembly.

1. The mass of open and closed superlevel sets is almost everywhere identical. What is required is
   `ν {x | t < u x} = ν {x | t ≤ u x}` holds for Lebesgue-almost every `t`.
   The difference of two sets is `{u = t}`, where these sets are pairwise disjoint for different `t`, and `ν` is finite.
   So `{t | ν {u = t} ≠ 0}` is countable, and countable sets have Lebesgue measure zero.
   Equivalent paths are: `t ↦ ν {x | t < u x}` anti-monotone, anti-monotone functions have at most countably many discontinuity points,
   and `ν {u ≥ t} = lim_{s↑t} ν {u > s}`. Neither does it require `u` to be bounded or dense.
   This is the only new lemma truly needing to be proven in the next round.
2. **The layer of zero mass and full mass.** The infimum of `minkowskiConstant` only runs `0 < ν B < 1`.
   When `ν(A_t) ∈ {0, 1}` then `min (ν A_t) (1 - ν A_t) = 0`, the pointwise inequality degenerates to
   `h_M * 0 ≤ ν⁺(A_t)`, holds true in ENNReal (`mul_zero` also holds for `⊤`).
   Therefore, no additional classification of these sheaves is needed, and no extra assumptions are required.
3. **The `⊤ * 0` in ENNReal.** Danger is only on the outer layer: if `h_M = ⊤` and the entire integral is `0`, the left endpoint is `⊤ * 0 = 0`,
   The conclusion is trivial; if the integral is regular, one must avoid removing `h_M` from the integral. The correct way is **no division**:
   First use `lintegral_const_mul` to move the constant `h_M` inside the integral (the integrand needs to be measurable,
   And `t ↦ ν {u > t}` is anti-monotone hence measurable, `min` and `1 - ·` preserve measurability—`tendsto_lintegral_min_superlevel`
   The proof already contains this `hFmeas`, then use `lintegral_mono_ae` together with the pointwise bounds from step 1 and 2,
   Finally `Measure.restrict_le_self` amplifies the integral on `Ioo 0 1` to the entire axis and connects it with the current theorem.
   Thus `⊤` appears only once at the pointwise level and is correctly absorbed by `mul_zero`.
4. **Infimum expansion.** For levels with `0 < ν(A_t) < 1`, by the definition of `iInf` we get
   `h_M ≤ ν⁺(A_t) / min (ν A_t) (1 - ν A_t)`, then use `ENNReal.le_div_iff_mul_le`
   (Denominator non-zero, not `⊤`) replaced with multiplicative form. Requires `MeasurableSet {x | t ≤ u x}`, continuously provided by `u`.

## Next step: Assembly of `minkowskiConstant_le_smoothConstant`

With the 2 item, this theorem no longer requires any new analysis: for a smoothly embedded domain fixing intermediate mass `U`,
`P_ρ(U) = ⊤` the quotient is `⊤` trivial; otherwise, take the already proven
`RelativePerimeter.exists_smooth_recovery_sequence` (each item `C^∞`, globally Lipschitz, `[0,1]` valued),
apply item 2 term by term to obtain `h_M * I_j ≤ ∫ ‖∇u_j‖ dν`; the already proven
`tendsto_lintegral_min_superlevel` transforms `L¹(ν)` convergence into `I_j → min (ν U) (1 - ν U)`;
`ENNReal.Tendsto.const_mul` (side conditions given by `ν U > 0` `min ≠ 0`) is passed to the left end,
on the `limsup` side use the `limsup ∫ ‖∇u_j‖ ≤ P_ρ(U)` of the recovery sequence, and finally `ENNReal.le_div_iff_mul_le`
is closed out with `le_iInf`.

The other direction `smoothConstant_le_minkowskiConstant` still requires `WIP/AnalyticPrerequisites`'s Sard and weighted coarea, as well as `lintegral_enorm_gradient_distanceCutoff_le`; there has been no progress in this round. Therefore, this round cannot be stated as the coarea formula, Cheeger constant equality, or the entire comparison chain being proven.
