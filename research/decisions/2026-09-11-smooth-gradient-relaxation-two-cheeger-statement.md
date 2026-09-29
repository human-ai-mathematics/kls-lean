# 2026-09-11 — `thm:smooth-gradient-relaxation-two-cheeger`: Statement Design (only statements, no proofs)

## Decision

- Write a Lean statement for the unique `\notready` node `thm:smooth-gradient-relaxation-two-cheeger` of Blueprint, with all proof bodies being
  `sorry`, placed in independent WIP module `formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean`.
- The convention for Cheeger energy, as specified in the Blueprint original, is the **local slope convention**: Ch_ν = ½ · (f ↦ ∫ |∇f|² dν for locally Lipschitz,
  Sequence on the class of test functions with finite slope energy in L²(ν). The asymptotic Lipschitz constant Lip_a is defined separately, and the two are equal as independent.
  Obligatory statement, without definitional equivalence. Selected actions are recorded only at `Energy.Cheeger.energy := Cheeger.ofLocalSlope`.
- Test class uses the existing literature test domain `Energy.LocalSlope.Admissible` (local Lipschitz, `MemLp 2`, `energy ≠ ⊤`),
  Do not introduce a third Lipschitz class.
- "lower semicontinuous relaxation" is realized by a sequence of project relaxations and is characterized by three statements as the lower semicontinuous envelope: `lowerSemicontinuous_relaxation`,
  `relaxation_toLp_le`, `le_relaxation_of_lowerSemicontinuous`.
- Affine support transport follows the same construction as `def:intrinsic-affine-energy`: `Cheeger.Intrinsic.energy μ :=
  (Cheeger.energy (intrinsicMeasure μ)).comap (toIntrinsicL2 μ)`.
- Do not fill sorry; do not add `FunctionalInequalities.lean` aggregate import, lakefile, ledger, `check_blueprint.CERTIFICATES`,
  Blueprint `\lean{}`/`\leanok`, `tasks.json`; no commit, no push.

## Lean Statement (formech style)

Namespace names are omitted `FunctionalInequalities`.

Claim:

1. `Energy.SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger (μ : ProbabilityMeasure E) (f : Lp ℝ 2 μ) :
   SmoothGradient.Intrinsic.energy μ f = 2 * Cheeger.Intrinsic.energy μ f` —— Blueprint theorem body, for finite-dimensional real inner product spaces
   For any Borel probability measure, the two sides allow `⊤`.
2. coordinate layer `Energy.SmoothGradient.relaxation_eq_localSlope (ν) : relaxation ν = LocalSlope.relaxation ν`
   And `relaxation_eq_two_mul_cheeger`.
3. unconditional direction `SmoothGradient.localSlope_relaxation_le`: smooth test is slope test and energy is the same
   (`Test.localSlope_admissible`, `Test.localSlope_energy`, no need for absolute continuity, since `LocalSlope.apply_eq_norm_gradient` holds pointwise).
4. The two Cheeger formulations are equal: `LocalSlope.relaxation_eq_asymptoticLipschitz`, `Cheeger.energy_eq_ofAsymptoticLipschitz`.

Does not assert: any Poincaré inequality, finiteness of constants, Cheeger–Buser comparison, consistency between the raw slope energy and relaxed energy on a single test, any relationship between `h_μ` (`def:isoperimetric-cheeger-scale`) and `Ch_μ`, defined by `Lip_a` to `Cheeger.energy`.

Finite range (versions provable with existing certified inputs): `relaxation_le_localSlope_of_absolutelyContinuous`,
`relaxation_eq_localSlope_of_absolutelyContinuous` (`ν ≪ m`, `m` Haar, without boundary zero measure),
`Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous`,
`KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` (log-concave law, via `hμ.intrinsic_absolutelyContinuous`).

Zero-dimensional: `LocalSlope.relaxation_eq_zero_of_subsingleton`, `Cheeger.energy_eq_zero_of_subsingleton`, `AsymptoticLipschitz.apply_eq_zero_of_subsingleton`; the main theorem includes an affine support at a point (`0 = 2 * 0`).

Compilation: `lake env lean FunctionalInequalities/Energy/WIP/Cheeger.lean` only 26 `declaration uses 'sorry'`
Warning, no other warnings (four `rfl` expansion lemmas added `omit ... in`). `#check` Verification: `LocalSlope.preEnergy/relaxation`,
`Cheeger.energy` is sufficient `[NormedAddCommGroup V] [MeasurableSpace V]`; `Cheeger.Intrinsic.energy` and
`SmoothGradient.Intrinsic.energy` Similarly does not contain `CompleteSpace E`; each sorry theorem comes with a complete Euclidean instance table
 (`InnerProductSpace`, `CompleteSpace`, `BorelSpace`, `SecondCountableTopology`, `FiniteDimensional`),
The zero-dimensional lemmas such as `relaxation_eq_zero_of_subsingleton` actually need only the first two; use `omit` as appropriate during proofs.

## Sentence-by-sentence alignment (Blueprint ↔ Lean)

| Blueprint sentence | Lean | Conclusion |
|---|---|---|
| "On the affine support" | `Cheeger.Intrinsic.energy μ` computed on `Probability.intrinsicMeasure μ` (direction space, inherited ambient metric) | uniform |
| "the standard metric Cheeger energy normalized as one half of …" | `Cheeger.ofLocalSlope ν = ⟨fun f ↦ LocalSlope.relaxation ν f / 2⟩`, `Cheeger.energy := ofLocalSlope` | consistency; ½ written in the definition |
| "… the lower-semicontinuous relaxation …" | `LocalSlope.relaxation := (preEnergy ν).sequentialRelaxation`; `lowerSemicontinuous_relaxation` + `relaxation_toLp_le` + `le_relaxation_of_lowerSemicontinuous` characterizes as the supremumlower semicontinuous lower bound | Uniform (Lean treats "lsc relaxation = sequence relaxation" as a provable obligation and does not define it) |
| "… of the squared local slope" | `Energy.LocalSlope.apply` (single-point slope), `LocalSlope.energy ν f = ∫⁻ apply f x ^ 2` | uniform |
| (test class not specified, "standard") | `Energy.LocalSlope.Admissible`: locally Lipschitz, L², finite slope energy | **To be clarified**: AGS uses (bounded/compact support) Lipschitz function classes; equality of relaxations for different Lipschitz classes is a standard truncation argument, but this module does not state this comparison |
| "After transporting it to ambient real L²(μ)" | `Cheeger.Intrinsic.energy μ := comap (toIntrinsicL2 μ)`, transported together with `SmoothGradient.Intrinsic.energy` | consistent |
| "prove 𝓔^can_μ = 2 Ch_μ" | `Intrinsic.energy_eq_two_mul_cheeger : energy μ f = 2 * Cheeger.Intrinsic.energy μ f`, ∀ `f : Lp ℝ 2 μ`, containing `⊤` | Uniform (Lean explicit coverage of infinity) |
| Note: "The factor 2 is part of the intended normalization" | Definition `/ 2`, theorem `2 *`; `Cheeger.two_mul_energy` | Consistent |
| Note: "relaxation of the local slope and asymptotic-Lipschitz relaxation must be distinguished" | Two independent definitions `Cheeger.ofLocalSlope`, `Cheeger.ofAsymptoticLipschitz` (the latter based on the new definition `AsymptoticLipschitz.apply = ⨅ r>0, ⨆ y z ∈ B(x,r), |f y − f z|/d(y,z)`); pointwise `LocalSlope.apply_le_asymptoticLipschitz`; relaxation comparison `relaxation_le_asymptoticLipschitz`, `relaxation_eq_asymptoticLipschitz` | Stronger: provides statements for distinction and comparison |
| Note: "their comparison for singular measures has no source recorded in the bibliography" | `relaxation_eq_asymptoticLipschitz` and `relaxation_eq_localSlope` are stated unconditionally, following the Blueprint theorem; `_of_absolutelyContinuous` versions give restricted scope | **Needs clarification**: the mathematical source for singular measures. `references.bib` already contains `AmbrosioGigliSavare2013Density` (Rev. Mat. Iberoam. 29, 2013); its weak-gradient equivalence theorem covers complete separable metric measure spaces with locally finite measures and should be the source of this comparison. This record does not edit the shared Blueprint chapter |
| `\uses{def:selected-canonical-frontend}` | `import …SmoothGradient.Intrinsic.Basic`, the left side of the theorem is `SmoothGradient.Intrinsic.energy` | uniform |
| 45 Chapter: "The isoperimetric number h_μ is not the metric energy Ch_μ" | `Energy.Cheeger` and `KLS.Isoperimetry` are mutually non-referenced; module header specified | Consistent |
| (zero-dimensional not mentioned) | Three zero-dimensional lemmas; main theorem without dimension assumption | Stronger |

## sorry obligation list (26 items, in file order)

File `formalization/FunctionalInequalities/Energy/WIP/Cheeger.lean`. "API" column suggests the recommended repository/Mathlib entry.

| # | line | Lean name (omitting `FunctionalInequalities.Energy`) | statement | corresponding Blueprint sentence | suggested API |
|---|---|---|---|---|---|
| 1 | 98 | `AsymptoticLipschitz.apply_const` | the `Lip_a` of a constant is 0 | Note: distinguish Lip_a | Affine `LocalSlope.apply_const`: `iInf_le_of_le 1`, `dist_self`, `div_zero`, `simp` |
| 2 | 103 | `AsymptoticLipschitz.apply_eq_zero_of_subsingleton` | on a point space `Lip_a = 0` | 0-dimensional | `Subsingleton.elim` becomes a constant + #1 |
| 3 | 108 | `AsymptoticLipschitz.apply_le_of_lipschitzWith` | `LipschitzWith K f → Lip_a f x ≤ K` | Note: Distinguish Lip_a | `LipschitzWith.dist_le_mul`, `div_le_iff₀`, `ENNReal.ofReal_le_ofReal`, `iInf_le_of_le 1` |
| 4 | 137 | `LocalSlope.apply_le_asymptoticLipschitz` | pointwise `|∇f| ≤ Lip_a f` | Note: distinguish Lip_a | expand two `⨅⨆`, `iInf_mono`, `le_iSup₂_of_le y hy x (by simpa)` (take `z = x`, `dist x x = 0 < r`) |
| 5 | 147 | `LocalSlope.energy_le_asymptoticLipschitz` | slope energy ≤ Lip_a energy | same as above | `lintegral_mono` + #4 + `pow_le_pow_left'` |
| 6 | 152 | `LocalSlope.Admissible.of_asymptoticLipschitz` | Lip_a test ⇒ slope test | Same as above | Structure fields one by one; finiteness by #5 and `ne_top_of_le_ne_top` |
| 7 | 175 | `LocalSlope.coe_preEnergy_energy` | `↑((preEnergy ν).energy f) = energy ν f.1` | "squared local slope" | `ENNReal.coe_toNNReal f.2.finite_energy` |
| 8 | 193 | `LocalSlope.lowerSemicontinuous_relaxation` | relaxationlower semicontinuous | "lower-semicontinuous relaxation" | `PreEnergy.lowerSemicontinuous_sequentialRelaxation (preEnergy ν)` |
| 9 | 198 | `LocalSlope.relaxation_toLp_le` | Relaxation ≤ Test raw energy | Same as above | `PreEnergy.sequentialRelaxation_toAmbient_le (preEnergy ν) ⟨f, hf⟩` + #7 |
| 10 | 205 | `LocalSlope.le_relaxation_of_lowerSemicontinuous` | Relaxation is the largest lsc lower bound | Same as above | `PreEnergy.le_sequentialRelaxation_of_lowerSemicontinuous`, rewrite `hQ` under #7 as a bound for `P.Test` |
| 11 | 214 | `LocalSlope.relaxation_eq_zero_of_subsingleton` | log-concave relaxation in zero dimension is 0 | zero-dimensional | on a one-point space `f : Lp ℝ 2 ν` a.e. equal to a constant `c := f default` (`Subsingleton.elim`), test `fun _ ↦ c` is admissible (`LocallyLipschitz` constant, `memLp_const`, energy 0 from `LocalSlope.apply_eq_zero_of_subsingleton` + `lintegral_zero`), its `toLp` equals `f` (the `Lp.ext` / `MemLp.toLp` of a.e. similar), then use `sequentialRelaxation_toAmbient_le` and `le_antisymm _ bot_le` |
| 12 | 246 | `LocalSlope.relaxation_le_asymptoticLipschitz` | Slope relaxation ≤ Lip_a relaxation | Note: distinguish Lip_a | `PreEnergy.sequentialRelaxation_comp_le (P := AsymptoticLipschitz.preEnergy ν) (Q := LocalSlope.preEnergy ν) id continuous_id`; map each Lip_a test to a slope test using #6, with energy bounded by #5 + `ENNReal.toNNReal_mono` |
| 13 | 256 | `LocalSlope.relaxation_eq_asymptoticLipschitz` | Equality of relaxations under the two conventions | Note: "must be distinguished … comparison for singular measures" | Direction ≤ is #12; direction ≥ needs an AGS 2013 Density argument. In Euclidean spaces one can bypass Hopf–Lax: for arbitrary `ν`, mollify locally Lipschitz `f` to `f * ρ_n` (the `mollify` mechanism in `Energy.Euclidean.LipschitzApproximation`); `‖∇(f*ρ_n)(x)‖ ≤ Lip(f, B(x, 2/n)) → Lip_a f x`, then use `sequentialRelaxation_le_of_recovery_sequences` (`Relaxation/LowerSemicontinuous.lean`). This gives `SmoothGradient.relaxation ≤ AsymptoticLipschitz.relaxation`; combined with #16 (unconditional `LocalSlope.relaxation ≤ SmoothGradient.relaxation`), it gives only `LocalSlope ≤ Smooth ≤ Lip_a`. The inequality `Lip_a relaxation ≤ slope relaxation` (the core of AGS Thm 6.2) remains missing. **This is a substantive open obligation for singular laws**; see below |
| 14 | 291 | `Cheeger.two_mul_energy` | `2 * (x / 2) = x` at `ℝ≥0∞` | Note: factor 2 | `ENNReal.mul_div_cancel'` ( `two_ne_zero` , `ENNReal.ofNat_ne_top` ) or `ENNReal.div_eq_inv_mul` + `ENNReal.mul_inv_cancel` |
| 15 | 297 | `Cheeger.energy_eq_ofAsymptoticLipschitz` | two agreed Cheeger energies are equal | same #13 | `Functional.ext` + #13 |
| 16 | 302 | `Cheeger.energy_eq_zero_of_subsingleton` | zero-dimensional Cheeger energy 0 | zero-dimensional | #11 + `ENNReal.zero_div` |
| 17 | 344 | `SmoothGradient.Test.localSlope_admissible` | smooth test ∈ `LocalSlope.Admissible` | "squared local slope" (test class contains) | `ContDiff.locallyLipschitz (f.contDiff.of_le le_top)` (Mathlib `Analysis/Calculus/ContDiff/RCLike`); `f.memLp_two`; finiteness by #18 |
| 18 | 349 | `SmoothGradient.Test.localSlope_energy` | `LocalSlope.energy ν f = ↑f.energy` | same as above | `LocalSlope.apply_eq_norm_gradient f x (f.contDiff.differentiable le_top).differentiableAt` (without measure assumption), `lintegral_congr`, `ofReal_integral_eq_lintegral_ofReal f.gradient_sq_integrable`, `ENNReal.ofReal_pow`, `Test.coe_energy` |
| 19 | 357 | `SmoothGradient.localSlope_relaxation_le` | unconditional `LocalSlope.relaxation ≤ SmoothGradient.relaxation` | theorem body (≥ direction) | `PreEnergy.sequentialRelaxation_comp_le (SmoothGradient.preEnergy ν) (LocalSlope.preEnergy ν) id continuous_id`, test map `f ↦ ⟨f, #17⟩`, `toL2` of the same type (`rfl`), energy by #18 + `ENNReal.toNNReal_coe` |
| 20 | 365 | `SmoothGradient.relaxation_le_localSlope_of_absolutelyContinuous` | `ν ≪ m` at reverse inequality | Main statement (≤ direction, finite range) | Using `PreEnergy.sequentialRelaxation_le_of_recovery_sequences (P := LocalSlope.preEnergy ν) (Q := SmoothGradient.preEnergy ν)`; for each admissible `g`, `LocalSlope.admissible_iff_memLp_gradient ν m hac` gives `MemLp (gradient g) 2`, `Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2 hac (ContinuousLinearMap.id ℝ V) g` gives a smooth compactly supported sequence `gSeq` (`ContDiff ℝ ∞`, `MemLp 2`, gradient L² convergence); construct `SmoothGradient.Test` (`gradient_sq_integrable` from `memLp_two_iff_integrable_sq_norm`), `toL2` convergence via `Lp.tendsto_Lp_iff_tendsto_eLpNorm''`; energy convergence: `‖·‖₂²` continuous + `LocalSlope.energy_eq_lintegral_gradient ν m hac g hlip` (or `Energy.LocalSlope.energy_eq_integral_gradient`, in `Poincare/LipschitzGradient/Comparison.lean`); `liminf` via `Tendsto.liminf_eq`. Reference the analogous argument in `Energy.LipschitzGradient.localSlope_holds_of_relaxation` |
| 21 | 373 | `SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous` | equality of relaxation at `ν ≪ m` | same as above | `Functional.ext` + `le_antisymm` #20 #19 |
| 22 | 381 | `SmoothGradient.relaxation_eq_localSlope` | Unconditional equality of relaxations | Main theorem (including singular laws) | ≥: #19. ≤: no repository input for the singular case. Possible routes: (a) for arbitrary `ν`, mollification gives `Smooth ≤ Lip_a relaxation` (see #13), then use AGS 2013 `Lip_a relaxation = slope relaxation`; (b) directly prove the AGS identity `|Df|_{*,slope} = |Df|_{*,Lip_a}`. Both require new analytic infrastructure (the Hopf–Lax semigroup or an equivalent weak-upper-gradient theory of Cheeger energy), currently absent from Mathlib |
| 23 | 387 | `SmoothGradient.relaxation_eq_two_mul_cheeger` | coordinate form `relaxation ν f = 2 * Cheeger.energy ν f` | "𝓔^can = 2 Ch" | #22 pointwise + `Cheeger.energy_apply` + #14 |
| 24 | 401 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger` | **Blueprint Theorem** | Theorem body | `SmoothGradient.Intrinsic.energy_apply`, `Cheeger.Intrinsic.energy_apply`, substitute #23 into `ν := intrinsicMeasure μ`, `f := toIntrinsicL2 μ f` |
| 25 | 407 | `SmoothGradient.Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous` | Theorem when intrinsic law `≪ m` is present | Theorem body (finite range) | Same as #24, use #21 instead of #22 |
| 26 | 432 | `KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | log-concave law theorem | Theorem body (KLS use case) | #25 with `m := Measure.addHaar`, `hμ.intrinsic_absolutelyContinuous Measure.addHaar` (`KLS/LogConcave/AbsoluteContinuity.lean`); contrasting the formulation in `KLS.LogConcave.intrinsicSmooth_constant_eq_localSlope` |

Suggested dependency order: 1–7, 14 → 8–12, 16–19 → 20, 21 → 25, 26 (up to this point, only authenticated inputs are used; proceed first);
13, 15, 22, 23, 24 are singular cases, determined by the underlying infrastructure.

## Missing Infrastructure and Sources

- Under the singular law, `Lip_a` relaxation equals slope relaxation (#13), and hence the unconditional main theorem (#22–#24): AGS 2013 Density Theorem with a local proof on Euclidean carriers. Mathlib (`db584cd6`) lacks the Hopf–Lax semigroup, weak upper gradient, or metric Sobolev space. `references.bib` already has `AmbrosioGigliSavare2013Density`; Blueprint 30 footnote "no source recorded" can be updated after verifying Theorem 6.2 (or corresponding number), and this session does not modify the shared Blueprint section.
- The relaxation equality for test class variants (global Lipschitz / bounded / compactly supported Lipschitz) is not stated; if future alignment with the AGS original is required, a new `PreEnergy` must be established for another test class and a truncation recovery sequence must be proven. `Energy.LipschitzGradient.relaxation` (operator form, requiring `≪ m`) is the third manifestation in the repository, and its relationship with `LocalSlope.relaxation` is also not stated.

## Not done

- Unregistered: not in `FunctionalInequalities.lean`, lakefile `Solutions` root, `research/a-series/ledger.yaml`,
  `check_blueprint.CERTIFICATES`, Blueprint `\lean{}`/`\leanok`, `tasks.json`; `\notready` marked for retention.
- Unsubmitted, unpushed.
- Made no changes to any shared files (HANDOFF, README, Blueprint section, ledger, tasks.json, naming.md). If promoted later, needs to
  Add `Energy.AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}` to the table in `research/naming.md`,
  `Energy.LocalSlope.{preEnergy,relaxation}`, `Energy.Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`,
  And move the module from `Energy/WIP/` to `Energy/Cheeger/` and `Energy/LocalSlope/`.
