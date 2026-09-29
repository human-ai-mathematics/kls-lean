# 2026-09-12 — Analytical prerequisites for relative perimeter chains: Independent Lean statements (only statements, no proofs)

Take over the [feasibility judgment and prompt](2026-09-12-relative-perimeter-prerequisites-statement-prompt.md) on the same day.
In this round, write the missing analytical premises for the chain `lem:relative-perimeter-smoothing` → `lem:relative-perimeter-cheeger-infimum` as a **KLS-independent** Lean statement, with all proof bodies being `sorry`, and place them into a new WIP module. No registration, no commit, no push, and no modification to any existing declarations (the `RelativePerimeter.lean` 5 clause and the `CheegerInfimum.lean` 9 clause of `sorry` are retained in their original types).

## Decision

- New file `formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean`, 17 item `sorry`,
  Two `def` (`Analysis.divergence`, `KLS.SmoothDomain.outwardNormal`, both having real definition bodies).
  General statements are placed in the namespace `FunctionalInequalities.Analysis` (five sections: `Isodiametric`, `LipschitzGraph`,
  `LevelSet`, `Coarea`, `Sard`, along with `Divergence`), only the Gauss–Green set is placed at `FunctionalInequalities.KLS.SmoothDomain`
  Below, because the divergence theorem requires a region.
- Only import `FunctionalInequalities.KLS.WIP.RelativePerimeter` (taking `SmoothDomain`, `unitBallVolume`,
  `surfaceMeasure`, `mollifiedIndicator` and `Mathlib.LinearAlgebra.Trace` (divergence defined using trace).
- Group A chooses the **Brunn–Minkowski path** instead of Steiner symmetrization (reason see below).
- Group B **rejects** the statement that "the `μH[n−1]` restricted to level sets is a locally finite measure" (which is false), and instead adopts a pointwise assertion.
- E group uses Sard's **sharp index** `C^n` (`n = finrank`) instead of `C^∞`: stronger and textbook original; the repository-required `C^∞` case is given by
  `ContDiff.of_le` obtained.

## Statement list (17 items + 2 definitions)

The following table's "Corresponds to" column refers to `RelativePerimeter.lean` (RP) and `CheegerInfimum.lean` (CI) having `sorry`.
The "Feasibility" column lists what is present and what is missing in the pinned Mathlib (v4.33.0, `db584cd6`).

### A. Isoperimetric diameter inequality (section `Isodiametric`)

| Full name (omitted `FunctionalInequalities.`) | Content | Source | Corresponds to | Feasibility |
|---|---|---|---|---|
| `Analysis.prekopaLeindler` | n-dimensional Prékopa–Leindler on `V`: `(∫f)^t (∫g)^{1−t} ≤ ∫h`, `f x^t g y^{1−t} ≤ h(t x + (1−t) y)`, and the one-dimensional version `Probability.Line.prekopaLeindler` is word-for-word isomorphic (replacing `*` with `•`) | Prékopa 1971/73, Leindler 1972; Gardner, *The Brunn–Minkowski inequality*, Bull. AMS 39 (2002) §7 | No direct correspondence; Intermediate products of Group A | One-dimensional base case has been proven (`Probability/Line/BrunnMinkowski.lean`). Induction requires `V ≃ W × ℝ`'s orthogonal decomposition and Fubini along lines, warehouse has `Probability.lineEquiv`/`exists_lintegral_line`; Mathlib has no PL for dimension ≥ 2. Moderate emphasis |
| `Analysis.volume_rpow_mul_le_volume_combination` | Multiplicative Brunn–Minkowski: `vol S^t · vol T^{1−t} ≤ vol{t x + (1−t) y}`, `S, T` measurable and non-empty, outer measure on the right-hand side; combinatorial set notation consistent with `KLS.LogConcave` | Gardner 2002 §4; Schneider, *Convex Bodies* §7.1 | No direct correspondence | Derived from PL taking indicator functions + inner regularity (on compact subsets), following the same pattern as one-dimensional `le_volume_combination`. Intermediate |
| `Analysis.volume_rpow_add_le_volume_add_rpow` | Additive Brunn–Minkowski: `vol S^{1/n} + vol T^{1/n} ≤ vol(S+T)^{1/n}`, `S, T` compact and non-empty, `[Nontrivial V]` (when `n = 0` `1/0 = 0` and `x^0 = 1` make the inequality false) | Same as above | No direct correspondence | Obtained from the multiplicative type via homogeneity. Moderate difficulty |
| `Analysis.isodiametric` | `vol S ≤ ofReal(ω_n (diam S/2)^n)` for any bounded `S` (outer measure); use `Metric.diam` + `Bornology.IsBounded`, since unbounded sets have `Metric.diam` equal to 0 | Bieberbach 1915 (n=2), Urysohn 1924; Evans–Gariepy §2.2 Thm 1; Federer 2.10.33 | Core input for `KLS.hausdorffNormalized_finrank_eq_volume` (RP:119) | Absent from Mathlib. Route: `vol S ≤ vol(closure S)`, `½S + ½(−S) ⊆ closedBall 0 (diam/2)`, multiplicative BM (`t = ½`, `vol(−S) = vol S`), and `InnerProductSpace.volume_closedBall`. Short given BM |
| `Analysis.volume_le_ofReal_mul_hausdorffMeasure` | `vol S ≤ ofReal(ω_n/2^n) · μH[n] S` (half of the normalization identity) | Evans–Gariepy §2.2 Thm 2 first half | Same as above | By summing over the coverings defined by `isodiametric` for `μH` (`mkMetric`), we obtain the result. Easy (given A1) |
| `Analysis.hausdorffMeasure_finrank_eq_smul_volume` | `μH[n] = ofReal(2^n/ω_n) • volume`, with explicit `V` | Evans–Gariepy §2.2 Thm 2; Federer 2.10.35 | **General form of `KLS.hausdorffNormalized_finrank_eq_volume`**: unfold `hausdorffNormalized`, then use `smul_smul` + `ENNReal.ofReal_mul`. The type of the RP theorem is unchanged | Haar uniqueness (`isAddHaarMeasure_hausdorffMeasure`, `isAddLeftInvariant_eq_smul`) gives `μH[n] = c • volume`; the preceding result gives `c ≥ 2^n/ω_n`. The upper bound additionally requires Vitali/Besicovitch covering (`Besicovitch.exists_disjoint_closedBall_covering_ae` is in Mathlib). Medium |

**Steiner vs. Brunn–Minkowski.** Choose the BM route because: (i) the one-dimensional base case is already in the repository and does not require boundedness assumptions; (ii) the intermediate products (n-dimensional PL, two versions of BM) are themselves independent contributions at the Mathlib level, while the intermediate lemmas of Steiner symmetrization (measure preservation, diameter non-increase, measurability preservation under n iterations) in Lean are both redundant and lack reusability; (iii) the final step of the BM route only uses `volume_closedBall` and `t = ½`, without requiring "equality attained only at balls". The cost is that the A group has two additional intermediate statements, but they are justified (the log-concave theory will eventually require BM).

**Load-bearing explanation (reaffirming the judgment from Section 1).** Group A does not unlock any downstream nodes: `hausdorffNormalized_finrank_eq_volume` throughout the warehouse
no usage points, `relativePerimeter` only uses `ℋ^{n−1}`. It is written in because `surfaceMeasure`'s normalization convention must be anchored by a statement rather than a comment, and the general form of that statement is A2.

### B. The area measure of C¹ hypersurfaces is locally finite (section `LipschitzGraph`, `LevelSet`)

| Full name | Content | Source | Corresponds to | Feasibility |
|---|---|---|---|---|
| `Analysis.exists_lipschitzOnWith_levelSet_subset_image` | `φ` is `C¹`, `Dφ x ≠ 0`: there exists `N ∈ 𝓝 x`, a bounded `s ⊆ ker(Dφ x)`, Lipschitz on `s`, `g : ker(Dφ x) → V`, such that `N ∩ {φ = φ x} ⊆ g '' s`. Only requires `[NormedSpace ℝ V] [CompleteSpace V]`, no need for finite dimension | Implicit function theorem's Lipschitz graph form (any analysis textbook) | No direct correspondence; B1's path | Mathlib has `HasStrictFDerivAt.implicitFunction` (`Analysis/Calculus/Implicit.lean`, `ImplicitFunctionData`), providing `C¹` implicit function; `C¹` ⇒ local Lipschitz by `ContDiff` + bounded derivative. Medium |
| `Analysis.exists_hausdorffMeasure_levelSet_lt_top` | Same hypotheses: `∃ N ∈ 𝓝 x, μH[n−1] (N ∩ {φ = φ x}) < ⊤` | Evans–Gariepy §2.4.1 / Federer 2.10.11 (`ℋ^k` bound for Lipschitz images) | **General statement underlying `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` (RP:418)**: at boundary points take a defining neighborhood `(W, φ)`; `frontier ∩ W = {φ = 0} ∩ W` (`frontier_inter_eq`), so use `N ∩ W`. Away from the boundary, use the complement of the closed frontier | Given B2: `LipschitzOnWith.hausdorffMeasure_image_le` (available), and `μH[k]` is Haar on a `k`-dimensional inner product space (`ker` with its induced submodule structure), by `isAddHaarMeasure_hausdorffMeasure` (available), hence finite on bounded sets. `LinearMap.finrank_range_add_finrank_ker` gives `finrank ker = n − 1`. Easy |

**Why pointwise statements.** "`μH[n−1].restrict {x ∈ W | φ x = c}` is `IsLocallyFiniteMeasure`" is **false** for regular level sets inside an open set `W`: `n = 2`, `W = {x > 0}`, `φ(x, y) = y − sin(1/x)`, `Dφ ≠ 0` hold everywhere, yet the level sets have infinite length in every neighborhood of the origin.
It holds for smooth regions with closed frontier because each frontier point has its own defined neighborhood; this is exactly the reason why RP:418 holds but its "generalization" does not.

### C. Gauss–Green / Divergence Theorem (namespace `KLS.SmoothDomain`, section `Normal`, `GaussGreen`)

| Full name | Content | Source | Corresponds to | Feasibility |
|---|---|---|---|---|
| `Analysis.divergence` (def) | `div F x := tr (fderiv ℝ F x)`, using `LinearMap.trace`, independent of basis; at non-differentiable points is 0 | — | — | definition |
| `KLS.SmoothDomain.outwardNormal` (def) | Take the defined function `φ` selected by `exists_defining` at boundary points, value `‖∇φ x‖⁻¹ • ∇φ x`; outside the boundary is 0 | — | — | Definition (`Classical.choose`) |
| `KLS.SmoothDomain.outwardNormal_eq` | For any defined pair `(W, φ)`, `outwardNormal x = ‖∇φ x‖⁻¹ • ∇φ x` (well-definedness) | The gradients of two defined functions are parallel and point in the same direction on their common zero set (both negative within `U`) | No direct correspondence; requires premises of C1–C3 | Requires "two `C¹` functions having the same local zero set and same side ⇒ gradients are positively proportional", which can be obtained from the graphical representation in B2 or one-dimensional monotonicity along the normal direction (an argument previously used in RP `addHaar_frontier`). Moderate |
| `KLS.SmoothDomain.norm_outwardNormal` | frontier above `‖ν‖ = 1` | — | Same as above | Directly from definition and `fderiv ≠ 0`. Easy |
| `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` | `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n−1}`, for a compactly supported `C¹` vector field `F`, with `ℋ^{n−1} = surfaceMeasure V` (standard normalization); `U` and `∂U` may be unbounded | Maggi, *Sets of Finite Perimeter*, Ch. 9 (Gauss–Green for open sets with `C¹` boundary); Evans–Gariepy §5.8 | No direct counterpart; main theorem of group C | Mathlib’s `integral_divergence_of_hasFDerivAt_off_countable` only treats boxes in `Fin (n+1) → ℝ`. Route: partition of unity (`SmoothPartitionOfUnity`, available) + change of variables in graph coordinates (`integral_image_eq_integral_abs_det_fderiv_smul`), or one-dimensional integration by parts in the normal direction + Fubini. Identifying `√(1+|∇g|²)` with `ℋ^{n−1}` still requires an area formula for Lipschitz graphs (Mathlib only has the equal-dimensional formula). **The heaviest item in this chain** |
| `KLS.SmoothDomain.setIntegral_gradient_eq_integral_smul_outwardNormal` | `∫_U ∇η = ∫_{∂U} η ν dℋ^{n−1}`, `η` are `C¹` compactly supported scalars, i.e. `D𝟙_U = −ν ℋ^{n−1}⌊∂U` | Maggi Ch. 9; Ambrosio–Fusco–Pallara §3.3 | No direct correspondence; C1 scalar form | Obtained by component-wise projection onto C1 for `F = η • e` (taking an orthogonal basis for `e`). Easy (given C1) |
| `KLS.SmoothDomain.gradient_mollifiedIndicator_eq` | `∇(η ⋆ 𝟙_U)(x) = −∫_{∂U} η(x−y) ν(y) dℋ^{n−1}(y)`, `η = φ.normed volume` | Same as above | **is the exact formula behind `SmoothDomain.enorm_gradient_mollified_le` (RP:580)**: take norm, `‖ν‖ = 1`, `norm_integral_le_lintegral_norm` to obtain | From C2 on `η_x := η(x − ·)` (`∇η_x(y) = −(∇η)(x−y)`) and the existing `hasFDerivAt_convolution_right`/[`convolution_precompR_apply`] in RP. Easy (given C2) |

### D. Weighted coarea formula (section `Coarea`)

| Full name | Content | Source | Corresponds to | Feasibility |
|---|---|---|---|---|
| `Analysis.aemeasurable_lintegral_levelSet` | `t ↦ ∫_{u = t} g dℋ^{n−1}` On Lebesgue measure a.e. measurable (`u` Lipschitz, `g` measurable) | Evans–Gariepy §3.4 (measurability part of the coarea theorem); Federer 3.2.12 | No direct correspondence; part of classical theorems, `lintegral` in form does not affect the meaning of D1 but downstream Fubini requires it | Mathlib has none. Intermediate |
| `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | `∫ ‖∇u‖ g dvol = ∫_ℝ ∫_{u=t} g dℋ^{n−1} dt`, `u` **only requires Lipschitz**, `gradient` is 0 (Rademacher null) at non-differentiable points | Evans–Gariepy §3.4 Thm 2 and its weighted corollary; Federer 3.2.12; Maggi Ch. 13 | **Stronger than `KLS.Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (CI:112)**: removes `ContDiff ℝ 1 u`; the latter is a direct specialization | Mathlib has: Rademacher (`LipschitzWith.ae_differentiableAt`), area formula in equal dimension (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`), and bound for Lipschitz images (`μH`). Missing: coarea itself. Standard proof (EG) requires local flattening on `{∇u ≠ 0}` + `C¹` approximation + area formula + approximation argument for Lipschitz. **Heavy** |

### E. Sard's Theorem (section `Sard`)

| Full name | Content | Source | Corresponds to | Feasibility |
|---|---|---|---|---|
| `Analysis.sard` | `u : V → ℝ` is `C^n` (`n = finrank ℝ V`, in Lean `ContDiff ℝ (Module.finrank ℝ V) u`), `volume (u '' {Du = 0}) = 0`; only requires `[NormedSpace ℝ V] [FiniteDimensional ℝ V]`, no measure needed on `V` | Sard 1942; Federer 3.4.3; Milnor, *Topology from the Differentiable Viewpoint* §3 (`C^∞` proof); Whitney 1935 (`C^{n−1}` counterexample) | No direct correspondence; source of E2 | Mathlib has only the same-dimensional version `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (`Function/Jacobian.lean`). Milnor's induction proof on dimension requires Fubini and Taylor remainder estimates, Mathlib has the materials but no ready-made framework. **Heavy** |
| `Analysis.ae_forall_fderiv_ne_zero` | Under the same premise: `∀ᵐ t, ∀ x, u x = t → Du x ≠ 0` ( a.e. `t` is a regular value) | Same as above | **Prove `SmoothDomain.ae_exists_superlevel` (CI: 87)**: at a regular value `t`, `U = {t < u}` is open, `frontier ⊆ {u = t}` (already proved `frontier_superlevel_subset`), define functions `φ = t − u` and `W = V` | By taking the complement of `sard`, we obtain the result. Trivial (given E1) |

## Correspondence Summary Table

| Existing `sorry` | Current statement | Relation |
|---|---|---|
| RP:119 `hausdorffNormalized_finrank_eq_volume` | `Analysis.hausdorffMeasure_finrank_eq_smul_volume` (← `isodiametric` ← BM ← PL) | General form, `smul_smul` immediately obtained; **not load-bearing** |
| RP:418 `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` | `Analysis.exists_hausdorffMeasure_levelSet_lt_top` (← `exists_lipschitzOnWith_levelSet_subset_image`) | General statement; assembly requires `frontier_inter_eq` |
| RP:580 `SmoothDomain.enorm_gradient_mollified_le` | `SmoothDomain.gradient_mollifiedIndicator_eq` (← C2 ← C1) | Exact formula, take norm to obtain |
| CI:87 `SmoothDomain.ae_exists_superlevel` | `Analysis.ae_forall_fderiv_ne_zero` (← `sard`) | Assembly requires `frontier_superlevel_subset` |
| CI:112 `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | direct specialization (removing `C¹`) |

**Uncovered existing `sorry` (9 items) in this round**, since they are not "general analysis premises" but rather analysis work or pure assembly within the repository:
RP's `lintegral_enorm_gradient_mollified_homothety_le`, `exists_smooth_recovery_sequence` (assembly);
CI's `lintegral_enorm_gradient_distanceCutoff_le` (Rademacher + gradient on level sets a.e is zero; Mathlib already has Rademacher),
`exists_smooth_approximation_lipschitz` (smoothing convergence), `lintegral_minkowskiContent_superlevel_le` (ADG 2017 Lemma 3.2),
`smoothConstant_mul_lintegral_min_superlevel_le`, `minkowskiConstant_mul_lintegral_min_superlevel_le`,
`minkowskiConstant_le_smoothConstant`, `smoothConstant_le_minkowskiConstant` (assembly).

## Content not stated in this form (and reasons)

1. **B group's "locally finite measure" form**: false statement, see above; has been changed to pointwise form.
2. **No restatement** `hausdorffNormalized_finrank_eq_volume` and `ae_exists_superlevel`: the two are each derived from A2, E2 after a few lines; restating would only create redundant obligations.
3. **Group C cannot fully detach from warehouse objects**: Gauss–Green requires a region class, and the warehouse already has `SmoothDomain`; redefining the "`C¹` boundary open set" would only produce a second parallel concept. If promoted later, `divergence`, `outwardNormal`, and C1–C3 should be moved together with `SmoothDomain` to `KLS/Isoperimetry/SmoothDomain.lean`; groups A, B, D, and E should be moved to a separate `FunctionalInequalities/Analysis/` directory (or directly upstream to Mathlib).
4. **Group A does not bear load** (see Section 1). Still written, as it anchors the normalization convention of `surfaceMeasure`; if the owner considers the convention check can be replaced by comments, the entire group can be deleted without affecting any downstream.
5. **Sard's `C^n` rather than `C^∞`**: stronger, textbook original form, natural goal of Mathlib PR; the repository only uses the `C^∞` special case. If review deems it necessary to match the prompt word for word, changing to `ContDiff ℝ ∞ u` is purely weakening and does not affect any downstream.
6. **Group D only requires Lipschitz**: More general than CI:112's `C¹ ∧ Lipschitz`, and is the original form of Evans–Gariepy. The weighted coarea formula holds for locally Lipschitz functions (e.g., `C¹` without Lipschitz bounds), but requires McShane extension arguments; we omit it here since the consumers of CI are all globally Lipschitz.

## Compilation

Under `formalization/` (native arm64 toolchain, no git wrapper script):

```
lake build FunctionalInequalities.KLS.WIP.AnalyticPrerequisites   # Build completed successfully
lake env lean FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
lake env lean -DwarningAsError=true FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean
```

Both `lake env lean` outputs exactly 17 `declaration uses 'sorry'`s, with no other warnings or errors.
Both section variables of `def` are used within the definition body, with no additional `omit` or `set_option linter.unusedSectionVars`.
`#check` verification: the order of `sard` is `↑(Module.finrank ℝ V)`; the `V` of `hausdorffMeasure_finrank_eq_smul_volume` is explicitly given;
`exists_lipschitzOnWith_levelSet_subset_image` carries only `NormedAddCommGroup`, `NormedSpace ℝ`, and `CompleteSpace`;
The inner product of Gauss–Green is displayed as `inner ℝ (F x) (U.outwardNormal x)`.

Two adjustments encountered during compilation: `LinearMap.ker` in this Mathlib version only accepts `LinearMap`, and for `fderiv ℝ φ x : V →L[ℝ] ℝ` it must be written as `(fderiv ℝ φ x).toLinearMap` (direct type lifting will timeout at `isDefEq`); `divergence` is likewise replaced with `.toLinearMap`.

## Toolchain Discovery (useful only for subsequent round statements)

- `unusedSectionVars` linter **skips proofs containing `sorry` declarations**: this is why RP:418, RP:580, CI:87 and so on have unused
  `[CompleteSpace V]`, `[SecondCountableTopology V]` however show no warnings under `-DwarningAsError=true`. Consequence: only statement files can use a lenient approach.
  `variable` blocks; but after each `sorry` is filled, unused section instances of this declaration will be immediately reported and require individual addition of `omit ... in`. This is also a hint in the prompt
  The mechanism of the «`unusedSectionVars` round-by-round report» phenomenon. Two `def`s with actual defined bodies are not protected by this, and thus each is placed in a section containing only the required instances.
- This Mathlib's `LinearMap.ker` only accepts `LinearMap`; for `fderiv ℝ φ x : V →L[ℝ] ℝ` we must write `(fderiv ℝ φ x).toLinearMap`,
  A direct type ascription `(… : V →ₗ[ℝ] ℝ)` exhausts 200000 heartbeats in `isDefEq` instead of producing a type error.

## Next steps

Hints for proof sessions see the same day's
[sorry prompt](2026-09-12-relative-perimeter-prerequisites-sorry-prompt.md) (four levels: assembly and pure Mathlib; intermediate; lacks infrastructure; empty).
HANDOFF, `research/verification.md`, `KLS/README.md` and the module documentation for two associated WIP modules have been updated with references to this module;
`tasks.json` has the same `infrastructure: missing` classification between two nodes because obligations are typed, not proven.

## Not done

- Unregistered: `FunctionalInequalities.lean` aggregate import, lakefile `Solutions` root, `research/a-series/ledger.yaml`, `research/check_blueprint.py`'s `CERTIFICATES`, `research/tasks.json`, Blueprint's `\lean{}`/[`\leanok`] remained unchanged.
- Not `git commit`, not `git push`.
- No attempt was made to prove any statement; no weakening of provability was applied to any statement. The WIP module only updated the module documentation; the declarations and proofs remained unchanged.
