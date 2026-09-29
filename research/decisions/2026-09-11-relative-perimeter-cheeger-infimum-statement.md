# 2026-09-11 — `lem:relative-perimeter-cheeger-infimum`: Statement (only statement, no proof)

## Decision

- Write a Lean statement for Appendix A of Blueprint at `lem:relative-perimeter-cheeger-infimum` (equality of two Cheeger infima), and concurrently write the `h_μ = h^{sm,rel}_ν` and `Ψ_KLS(μ) = ψ_ν` sub-statements of `thm:klartag-density-frontend-identification`. The entire proof body is `sorry`, placed in an independent WIP module `formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean`, imported from the same directory's `RelativePerimeter.lean` (whose olean is built using the `lake build FunctionalInequalities.KLS.WIP.RelativePerimeter` single module, without entering any library root).
- Coordinate space layer definition: `KLS.Isoperimetry.minkowskiContent ν B` (thickened open outer Minkowski content, coordinate space version of `boundaryContent`), `minkowskiConstant ν` (`h_M`), `smoothConstant ρ Ω ν` (`h_S`, infimum over `SmoothDomain`). All defined via `⨅`, and defaulting to `⊤` when no accessible set exists, consistent with the zero-dimensional convention of `KLS.Isoperimetry.constant`. The balance quantity `m(t) = min{t, 1−t}` is inlined as `min (ν B) (1 − ν B)`, following the same notation as `constant`.
- The main theorem states a stronger result than Blueprint's "full-dimensional log-concave law": it applies to "any probability law with Borell density (relative to Lebesgue `volume`)".
- Identified and corrected two statement errors in the previous node's skeleton (Hausdorff normalization, reference measure must be Lebesgue), see [smooth lemma record update](2026-09-11-relative-perimeter-smoothing-statement.md).
- Do not use sorry; do not register; do not submit or push; do not modify shared files.

## Lean Statement (formech style)

Assertions:
1. `KLS.Isoperimetry.minkowskiConstant_eq_smoothConstant (hρ : IsBorellDensity ν volume ρ) :
   minkowskiConstant ν = smoothConstant ρ (interior ν.support) ν` —— Core of the Blueprint Lemma.
2. `constant_eq_minkowskiConstant_intrinsic (μ) : constant μ = minkowskiConstant (intrinsicMeasure μ)` —— Definition of affine support
   with the transport defined in the coordinate space (for any `μ`).
3. `constant_eq_smoothConstant_intrinsic (hμ : LogConcave μ) (hρ : IsBorellDensity (intrinsicMeasure μ) volume ρ)`,
   `inverseScale_eq_inv_smoothConstant_intrinsic` —— `thm:klartag-density-frontend-identification`'s
   `h_μ = h^{sm,rel}_ν` and `Ψ_KLS = ψ_ν` clauses (Dirac law with both sides being `⊤` / `0`).

Does not assert: any relationship between the `ν⁺(B)` and `P_ρ(B)` of a single set (Blueprint statement "compares infima, not the two perimeters of each test set"), BV perimeter, Cheeger–Buser, Poincaré constant clauses.

Finite range: no additional dimensionality assumptions. `smoothConstant_mul_lintegral_min_superlevel_le` Depends on the Borell density hypothesis (needed for coarea formula).

0-dimensional: a set without `0 < ν B < 1`, with `⊤` on both sides (`minkowskiConstant_eq_top_of_subsingleton`, `smoothConstant_eq_top_of_subsingleton`).

Compilation: `lake env lean FunctionalInequalities/KLS/WIP/CheegerInfimum.lean` only 25 `sorry` warnings, no other warnings. `#check`:
`minkowskiConstant` Only requires `NormedAddCommGroup`, `MeasurableSpace`; `smoothConstant` and `relativePerimeter` are similarly only required up to `BorelSpace`;
Theorem with complete Euclidean instance table.

## Sentence-by-sentence alignment (Blueprint ↔ Lean)

| Blueprint | Lean | Conclusion |
|---|---|---|
| "For a full-dimensional log-concave probability" | `hρ : IsBorellDensity ν volume ρ` (log-concave law obtained from `exists_isBorellDensity`; density existence implies full dimension) | stronger |
| left `inf_{0<ν(B)<1} ν⁺(B)/m(ν(B))` | `minkowskiConstant ν`; `minkowskiContent` and 45 Chapter `def:isoperimetric-cheeger-scale`'s `μ⁺` (open thickening, `liminf_{r↓0}`) word-for-word correspondence | consistent |
| right `inf_{U smooth, 0<ν(U)<1} P_ρ(U)/m(ν(U))` | `smoothConstant ρ (interior ν.support) ν`, `P_ρ` are the corrected `relativePerimeter` (standard `ℋ^{n−1}`, Lebesgue density) | uniform |
| 45 Chapter `h_μ` defined on affine support (`KLS.Isoperimetry.constant`) | `constant_eq_minkowskiConstant_intrinsic` | Uniform (bridged as independent obligations) |
| Proof: "weighted coarea and Sard's theorem give `h_S ∫₀¹ m(ν{u>t}) dt ≤ ∫‖∇u‖dν`" | `SmoothDomain.ae_exists_superlevel` (Sard), `lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (weighted coarea), `smoothConstant_mul_lintegral_min_superlevel_le` | Uniform |
| Proof: "Minkowski coarea inequality `∫₀¹ ν⁺({u≥t}) dt ≤ ∫‖∇u‖dν`, Lemma 3.2 of ADG 2017" | `lintegral_minkowskiContent_superlevel_le` (all `t ∈ ℝ`, closed superlevels, `C¹` Lipschitz `u`) | Stronger (no `u ∈ [0,1]` requirement) |
| "Open and closed superlevel sets have the same measure for a.e. t" | absorbed into `minkowskiConstant_mul_lintegral_min_superlevel_le` | uniform |
| "`∫₀¹ ν({u_j>t} ∆ B) dt = ‖u_j − 𝟙_B‖_{L¹(ν)} → 0`", "Since m is 1-Lipschitz, the denominator integral tends to m(ν(B))" | `lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff`, `tendsto_lintegral_min_superlevel` | Aligned |
| "Applying the smoothing lemma to a smooth U proves `h_M m(ν(U)) ≤ P_ρ(U)`, hence `h_M ≤ h_S`" | `minkowskiConstant_le_smoothConstant` (using `RelativePerimeter.exists_smooth_recovery_sequence`) | uniform |
| "Finiteness implies `ν(B̄) = ν(B)`" | `measure_closure_eq_of_minkowskiContent_ne_top` | Uniform |
| "`w_j = (1 − d(·,B)/r_j)₊` … converge in L¹(ν) to 𝟙_B, and `∫‖∇w_j‖dν ≤ (ν(B^{r_j}) − ν(B))/r_j`" | `distanceCutoff`, `distanceCutoff_mem_Icc`, `lipschitzWith_distanceCutoff`, `_eq_one_of_mem_closure`, `_eq_zero_of_notMem_thickening`, `tendsto_distanceCutoff_indicator`, `lintegral_enorm_gradient_distanceCutoff_le` (right side uses `ν(closure B)`) | stronger (denominator uses closure) |
| "The bounded L¹ convolution assertion of lem:covariance-test-core-density gives smooth replacements preserving the limit of these gradient integrals" | `exists_smooth_approximation_lipschitz` (smooth, Lipschitz, `[0,1]`-valued, `L¹(ν)` convergence, gradient integral convergence) | uniform |
| "Weighted coarea now yields `h_S m(ν(B)) ≤ ν⁺(B)` … proving `h_S ≤ h_M`" | `smoothConstant_le_minkowskiConstant` | Consistent |
| 45 Chapter `h_μ = h^{sm,rel}_ν`, `Ψ_KLS(μ) = ψ_ν` | `constant_eq_smoothConstant_intrinsic`, `inverseScale_eq_inv_smoothConstant_intrinsic` | Uniform |

## sorry obligation (25)

See the same-day hint [2026-09-11-relative-perimeter-cheeger-infimum-sorry-prompt.md](2026-09-11-relative-perimeter-cheeger-infimum-sorry-prompt.md). Layering:

- Pure Mathlib can prove (13): `frontier_superlevel_subset`, two zero-dimensional, `measure_closure_eq_of_minkowskiContent_ne_top`, `lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff`, `tendsto_lintegral_min_superlevel`, `distanceCutoff` four properties, `tendsto_distanceCutoff_indicator`, `constant_eq_minkowskiConstant_intrinsic` (transmission).
- Intermediate (4): `lintegral_enorm_gradient_distanceCutoff_le` (Rademacher + gradient on level sets a.e is zero), `exists_smooth_approximation_lipschitz` (smoothing + Lipschitz partial integration of `WeakDerivative.lean`), `lintegral_minkowskiContent_superlevel_le` (elementary proof of ADG Lemma 3.2), `minkowskiConstant_mul_lintegral_min_superlevel_le`.
- Lacking infrastructure (3): `SmoothDomain.ae_exists_superlevel` (Sard's theorem for `ℝⁿ → ℝ` requires `C^n`; Mathlib only has the same-dimensional version), `lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (coarea formula; Mathlib only has the area formula), and those depending on them, `smoothConstant_mul_lintegral_min_superlevel_le`.
- Assembly (5): `minkowskiConstant_le_smoothConstant` (also requires the `exists_smooth_recovery_sequence` from the previous node), `smoothConstant_le_minkowskiConstant`, `minkowskiConstant_eq_smoothConstant`, `constant_eq_smoothConstant_intrinsic`, `inverseScale_eq_inv_smoothConstant_intrinsic`.

## Environment notes

Today 19:04 the system installed "Command Line Tools for Xcode 27.0" (only arm64). `~/.elan`'s lake/lean is x86_64 (Rosetta), they have been
`/usr/bin/git` failed because `libxcrun` lacked an x86_64 slice. At 19:1x, my `lake build` (the first subsequent lake invocation), while resolving dependencies again,
Treat being unable to read the remote URL as "URL changed" and remove `.lake/packages/checkdecls`; thereafter, any **any** `lake` command will repeatedly delete/clone fail.
Temporary fix: use the script with `GIT_EXEC_PATH=/Library/Developer/CommandLineTools/usr/libexec/git-core` set, then `exec` CLT real git wrapper
Run lake at the PATH frontend, have restored checkdecls and completed this compilation; the packaging script is not in the repository. Persistent fixes require user decision: to include this packaging directory in
shell PATH, or modify the native arm64 elan/toolchain.

## Not done

- Not registered; no commit, no push; no modification to shared files. `lake build` Single-module build only writes to `.lake/build`.
- If later promoted: module split to `KLS/Isoperimetry/{Minkowski,SmoothDomainInfimum}.lean`; `research/naming.md` joins `KLS.Isoperimetry.{minkowskiContent,minkowskiConstant,smoothConstant,distanceCutoff}` and `KLS.{unitBallVolume,hausdorffNormalized,surfaceMeasure}`.
