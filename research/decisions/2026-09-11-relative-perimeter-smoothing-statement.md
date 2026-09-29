# 2026-09-11 — `lem:relative-perimeter-smoothing`: Definition of Skeleton and Statement (only statement, no proof)

## Decision

- For Blueprint Appendix A's `lem:relative-perimeter-smoothing` (the infrastructure was cross-verified by another session on the same day as `missing`, see
  [review record](2026-09-11-spectator-and-relative-perimeter-infrastructure.md)), write the missing definition skeletons and Lean statements,
  The entire proof file is `sorry`, placed in a separate WIP module `formalization/FunctionalInequalities/KLS/WIP/RelativePerimeter.lean`.
- **Smooth region** `KLS.SmoothDomain V`: structure, fields `carrier` (open set), `isOpen`, `exists_defining` (each boundary point has an open neighborhood `W`
  With the global `C^∞` function `φ`, `fderiv ℝ φ ≠ 0` at `W`, `carrier ∩ W = {y ∈ W | φ y < 0}`). This is "open set, locally located within its `C^∞`"
  Preciseification of one side of the boundary; only `[NormedAddCommGroup V] [NormedSpace ℝ V]`.
- **Relative perimeter** `KLS.relativePerimeter ρ Ω U := ∫⁻ x in frontier U.carrier ∩ Ω, ofReal (ρ x) ∂μH[finrank ℝ V − 1]`,
  Use the Hausdorff measure from Mathlib `μH[d]` (the self-metric of `V`). Explicit parameters for weight `ρ` and open set `Ω`; in the lemma take Borell density and
  `Ω = interior ν.support`.
- Main lemma `KLS.RelativePerimeter.exists_smooth_recovery_sequence` for any probability law with Borell density (relative to Haar measure) `ν`
  Statement is stronger than Blueprint's "log-concavity law of internal law" (the latter provided with density by `KLS.LogConcave.exists_isBorellDensity`).
- Do not fill sorry; do not register; do not submit, do not push; do not modify shared files.

## Lean Statement (formech style)

Assertion (`KLS.RelativePerimeter.exists_smooth_recovery_sequence`): `hρ : IsBorellDensity ν m ρ` (`m` Haar),
`U : SmoothDomain V`, `relativePerimeter ρ (interior ν.support) U ≠ ⊤` ⇒
`∃ u : ℕ → V → ℝ`, each `u j` globally `C^∞`, globally Lipschitz, taking values in `[0,1]`;
`∫⁻ ‖u j − 𝟙_U‖ₑ dν → 0`; `limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ relativePerimeter ρ (interior ν.support) U`.

Intermediate obligations (all are explicit steps used in Blueprint proofs but missing in Mathlib):

- `SmoothDomain.frontier_inter_eq`: defines the neighborhood of `frontier U ∩ W = {φ = 0} ∩ W`;
- `SmoothDomain.homothety` (the perspective image remains a smooth region), `indicator_homothety` (`𝟙_{cU} = 𝟙_U ∘ homothety a c⁻¹`, i.e., Blueprint's `v_s`);
- `SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier` (surface measure is locally finite, used by Tonelli);
- `SmoothDomain.addHaar_frontier` (`∂U` Haar null, hence `ν`-null);
- `SmoothDomain.hausdorff_frontier_homothety` (blow-up scaling `‖c‖^{n−1}`, i.e., `s^{1−n}`);
- `SmoothDomain.mollifiedIndicator`, `enorm_gradient_mollified_le` (the only form of Gauss–Green used:
  `‖∇(η⋆𝟙_U)(x)‖ ≤ ∫_{∂U} η(x−y) dℋ^{n−1}(y)`, `mollifiedIndicator_contDiff_lipschitz_mem_Icc`);
- `IsBorellDensity.exists_le` (`M = sup ρ < ∞`, Blueprint section preface), `le_rpow_mul_of_combination`
  (`ρ x ≤ (M/b₀)^{(1−s)/s} ρ y`, `y = s x + (1−s) b`, `ρ b ≥ b₀`);
- `RelativePerimeter.tendsto_indicator_homothety` (`v_s → 𝟙_U` on `L¹(ν)`);
- `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le` (one-step quantitative bound
  `∫‖∇u_{s,ε}‖ dν ≤ s^{1−n}(M/b₀)^{(1−s)/s} P_ρ(U)`, under condition `sε/(1−s) < r`).

No claims: the general form of Gauss–Green, outward normal fields, finite perimeter sets/multivalued BV, comparison of perimeters with lower semicontinuity (`P_ρ(U) ≤ liminf ∫‖∇u_j‖`), `lem:relative-perimeter-cheeger-infimum`, and Minkowski boundary content `KLS.Isoperimetry.boundaryContent`.

Finite range: no additional assumptions; the `n ≥ 1` in the Blueprint preamble is not assumed as a premise.

0-dimensional: `V` is a point, the boundary of an open set is empty, `relativePerimeter = 0` (`relativePerimeter_eq_zero_of_frontier_eq_empty`), a constant sequence;
`u_j = 𝟙_U` satisfies the conclusion; `μH[−1]` takes value only on the empty set, is 0.

Compilation: `lake env lean FunctionalInequalities/KLS/WIP/RelativePerimeter.lean` only 17 `sorry` warnings, no other warnings.
`#check`: `SmoothDomain.mk` only requires `NormedAddCommGroup`, `NormedSpace ℝ`; `relativePerimeter` only requires
`InnerProductSpace`, `MeasurableSpace`, `BorelSpace` (Hausdorff measure); theorem with complete Euclidean instance table.
Import `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct` to obtain `HasContDiffBump V`.

## Sentence-by-sentence alignment (Blueprint ↔ Lean)

| Blueprint | Lean | Conclusion |
|---|---|---|
| Introduction: "a smooth domain is open and locally lies on one side of its smooth boundary" | `SmoothDomain`: open set + local defining function `φ`, `fderiv ≠ 0`, `U ∩ W = {φ<0} ∩ W`; `frontier_inter_eq` | Aligned; the defining function makes "one side" precise |
| Introduction: `P_ρ(U) = ∫_{∂U∩Ω} ρ dℋ^{n−1}`, `n = dim V ≥ 1` | `relativePerimeter ρ Ω U`, `d = (finrank ℝ V : ℝ) − 1`, Mathlib `μH[d]` | Aligned; `n ≥ 1` is not assumed (stronger, with dimension zero trivial) |
| Introduction: `M = sup ρ < ∞` (`ρ ≥ √(b₀ρ(x))` at half the radius ball) | `IsBorellDensity.exists_le` | Uniform |
| For every smooth domain U with P_ρ(U) < ∞" | `(U : SmoothDomain V) (hU : relativePerimeter ρ (interior ν.support) U ≠ ⊤)` | uniform |
| "globally smooth Lipschitz functions 0 ≤ u_j ≤ 1" | `ContDiff ℝ ∞ (u j) ∧ (∃ K, LipschitzWith K (u j)) ∧ ∀ x, u j x ∈ Icc 0 1` | uniform |
| "u_j → 𝟙_U in L¹(ν)" | `Tendsto (fun j ↦ ∫⁻ ‖u j x − 𝟙_U x‖ₑ ∂ν) atTop (𝓝 0)` | Uniform (`lintegral` form, equivalent to `eLpNorm 1`) |
| "limsup_j ∫‖∇u_j‖ dν ≤ P_ρ(U)" | `limsup (fun j ↦ ∫⁻ ‖gradient (u j) x‖ₑ ∂ν) atTop ≤ relativePerimeter …` | Uniform (ENNReal, without integrability assumption) |
| "The domain and the convex carrier may be unbounded" | no boundedness assumption | uniform |
| `\uses{thm:borell-logconcave-density}`; ν is the intrinsic law of log-concave laws, ρ its Borell density, Ω = int K_ν | premise `IsBorellDensity ν m ρ`, `Ω = interior ν.support` (`closure_convexHull_intrinsic_support` shows consistency between the two) | stronger: any law with Borell density |
| Proof: "v_s(x) = 𝟙_U(a + s(x−a)), its domain is the outward dilation of U by 1/s" | `SmoothDomain.homothety a (1/s)`, `indicator_homothety` | Aligned |
| Proof: "dilation multiplies its total variation by s^{1−n}" | `hausdorff_frontier_homothety` (`‖c‖^{n−1}`, `c = 1/s`) | Aligned |
| Proof: "The distributional derivative of 𝟙_U is its oriented surface measure … convolution, triangle inequality" | `enorm_gradient_mollified_le` (pointwise norm bound) | Aligned (states only the consequence needed by the proof) |
| Proof: `ρ(x) ≤ (M/b₀)^{(1−s)/s} ρ(y)`, `y = sx + (1−s)b` | `IsBorellDensity.le_rpow_mul_of_combination` | Uniform |
| Proof: `∫‖∇u_{s,ε}‖ dν ≤ s^{1−n}(M/b₀)^{(1−s)/s} P_ρ(U)`, condition `sε/(1−s) < r` | `lintegral_enorm_gradient_mollified_homothety_le` (`φ.rOut = ε`) | Uniform |
| Proof: "Tonelli on unbounded boundaries; local finiteness of the smooth surface measure suffices" | `isLocallyFiniteMeasure_hausdorff_frontier` | Aligned |
| Proof: "∂U is ν-null", "v_s → 𝟙_U away from ∂U" | `addHaar_frontier` + `ν ≪ m`; `tendsto_indicator_homothety` | Aligned |
| Proof: "a piece of ∂U on ∂K contributes no cost" | The restriction to `Ω` is in the definition of `relativePerimeter`; the comparison lemma uses `ρ x > 0 ⇒ y ∈ Ω` | Aligned |

## sorry obligation list (17 items, in file order)

See the same-day prompt file [sorry prompt](2026-09-11-relative-perimeter-smoothing-sorry-prompt.md), where statements are stratified by "directly provable / requires analysis infrastructure" and API suggestions are provided for each. Stratification conclusion:

- Can be directly proved in Mathlib (10 items): `frontier_inter_eq`, `empty`, `univ`, `homothety` (two fields), `indicator_homothety`, `measurableSet`, `relativePerimeter_eq_zero_of_frontier_eq_empty`, `IsBorellDensity.le_rpow_mul_of_combination`, `tendsto_indicator_homothety`;
- Medium difficulty (3 items): `hausdorff_frontier_homothety` (`hausdorffMeasure_homothety_image` + homeomorphism preserves boundary), `IsBorellDensity.exists_le` (already certified `exists_bounds_of_isCompact` + log-concave + spherical mass ≤ 1), `mollifiedIndicator_contDiff_lipschitz_mem_Icc` (Mathlib convolution / `ContDiffBump` API);
- Requires new infrastructure (4 items): `isLocallyFiniteMeasure_hausdorff_frontier`, `addHaar_frontier` (smooth hypersurface locally a Lipschitz graph + `hausdorffMeasure_image_le`/Fubini), `enorm_gradient_mollified_le` (Gauss–Green theorem, Mathlib divergence theorem only for boxes), and the ones depending on them, `lintegral_enorm_gradient_mollified_homothety_le` and main lemma `exists_smooth_recovery_sequence` (the latter two are assembled after the previous lemmas are given).

## Not done

- Unregistered (aggregation import, lakefile, ledger, `check_blueprint.CERTIFICATES`, Blueprint anchor points, tasks.json all unchanged);
  The tasks.json `infrastructure: missing` conclusion holds, and this module writes "missing" objects as sorry-ed Lean definitions and obligations.
- Uncommitted, unpushed. No changes made to any shared files.
- If eventually promoted: split the module to `KLS/Isoperimetry/SmoothDomain.lean`, `KLS/Isoperimetry/RelativePerimeter.lean`;
  Add `research/naming.md` to the table (`KLS.SmoothDomain` (`carrier` , `homothety` , `mollifiedIndicator`)),
  `KLS.relativePerimeter`, `KLS.IsBorellDensity.exists_le`/`le_rpow_mul_of_combination`,
  `KLS.RelativePerimeter.exists_smooth_recovery_sequence`.

## Note (evening 2026-09-11): Corrections to two statements

When writing the statement for `lem:relative-perimeter-cheeger-infimum`, it was found that the skeleton of this record has two inconsistencies with Blueprint, both of which have been corrected in
`KLS/WIP/RelativePerimeter.lean` (only the definitions and the still `sorry` statement were modified; the other completed proof in 13 is unaffected and recompilation passes).

1. **Hausdorff measure normalization.** Mathlib's `μH[d]` uses the normalized `diam^d`, while the classical definition uses `ω_d (diam/2)^d`; thus, in Euclidean space, `μH[d] = (2^d/ω_d) · ℋ^d_std` and `d ≥ 2` differ (`μH[n]` equals Lebesgue only on the sup norm's `ι → ℝ`). The original `relativePerimeter` directly uses `μH[n−1]`; when `n ≥ 3`, it is `2^{n−1}/ω_{n−1}` times larger than Blueprint's `P_ρ`: the smoothness lemma thus becomes weaker (the right-hand side is larger), and if the Cheeger infimums were equal, the resulting statement would be false. Fix: new `KLS.unitBallVolume d`, `KLS.hausdorffNormalized V d := ofReal (ω_d / 2^d) • μH[d]`, `KLS.surfaceMeasure V := hausdorffNormalized V (finrank − 1)` are added; `relativePerimeter` and `enorm_gradient_mollified_le` now use `surfaceMeasure V`; and sorry is used to state `hausdorffNormalized_finrank_eq_volume` (`ℋ^n_std = volume`, isodiametric inequality) to fix the convention. The already proven `hausdorff_frontier_homothety` still refers to `μH`, with the scaling constant passed via `smul`.

2. **The reference measure must be Lebesgue.** The reference measure for Borell density was originally an arbitrary Haar `m`. If `m = c·volume`, the density becomes `ρ/c`; `P_ρ` becomes `P/c`; `∫‖∇u‖dν` remains unchanged, so `limsup ∫‖∇u_j‖dν ≤ P_ρ(U)` is false when `c > 1`. Fix: the reference measure for `exists_smooth_recovery_sequence`, `lintegral_enorm_gradient_mollified_homothety_le`, `enorm_gradient_mollified_le` is fixed to the Lebesgue measure on an inner product space `volume` (`measureSpaceOfInnerProductSpace`), with the premise rewritten as `IsBorellDensity ν volume ρ`. The statements `mollifiedIndicator φ m`, `exists_le`, `addHaar_frontier`, etc., regarding a general Haar `m` remain unchanged.

Alignment table updates the corresponding rows as: `P_ρ(U) = ∫_{∂U∩Ω} ρ dℋ^{n−1}` ↔ `relativePerimeter` (`surfaceMeasure`, standard normalization) — consistent; `dν = ρ dLeb_V` ↔ `IsBorellDensity ν volume ρ` — consistent. Compilation: only 5 sorry (originally 4 plus convention check).
