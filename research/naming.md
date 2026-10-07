# Lean public naming and parameter organization

Before adding modules, splitting files, or migrating an API, follow the
[classification and delivery workflow](workflow.md). This document maintains detailed naming
and parameter conventions.

Public names express mathematical objects, operations, and conclusions. Namespaces may span
implementation modules; certificate entry points, ledger node IDs, and source labels retain
stable identities. See the complete mapping in the
[migration record](decisions/2026-09-08-mathematical-api-organization.md) and
[declaration map](api-migration/2026-09-08-name-map.json). `FunctionalInequalities` is omitted below.

## Short names do not repeat the namespace

Do not repeat an object or role already supplied by the namespace. Use operation names such
as `apply`, `energy`, `toL2`, and `constant`; theorem short names describe properties of those
operations. Do not encode every assumption in the name. See the
[short-name record](decisions/2026-09-08-namespace-short-names.md) and
[complete map](api-migration/2026-09-08-short-name-map.json). Examples:

- `WeightedGradient.IsTest.memLp_apply`, `apply_add_ae`, `apply_smul_ae`.
- `LocalSlope.apply`, `apply_const`, replacing the redundant `LocalSlope.slope`.
- `LipschitzApproximation.exists_smooth_weighted_L2`, without repeating `approximation`.
- `ConditionalFiber.energyAt` is energy at one base point; `energy` is integrated energy.
- `SmoothTest.linear`, `energy_linear`; `ProductVariance.decomposition`, `integral_le`.

Remove repetition according to mathematical meaning: still identify the other side of a
comparison, another operator, or another space. A helper about ordinary `gradient` inside
`WeightedGradient` must not be named as though it were a weighted-gradient result.
The `Equiv` in `pullbackEquiv` indicates an equivalence of L² pullbacks, distinct from the
underlying-space equivalence.

Comparison short names likewise do not restate their full types. Write the shared operation
`relaxation`, `constant`, or `holds` only once, with a distinguishable short name for the target;
retain complete mathematical premises in the type and documentation. Examples include
`CovarianceGradient.relaxation_eq_lipschitz`, `relaxation_eq_ofLinearPMap`,
`relaxation_le_mul_lipschitz`, and `SmoothTest.constant_eq_ambient`,
`constant_eq_intrinsic`, `constant_eq_lipschitz`. Multiplicative comparisons retain `mul`;
do not name an inequality with a coefficient as direct domination. See the
[comparison short-name record](decisions/2026-09-08-comparison-short-names.md).

## Energies, tests, and optimal constants

| Mathematical object | Public entry points | Carrier and test class |
| --- | --- | --- |
| Smooth-test Poincaré inequality | `Poincare.SmoothTest.Admissible`, `energy`, `Holds`, `constant` | Given measure; globally C∞, L², integrable squared gradient |
| Ordinary smooth-gradient relaxation | `Energy.SmoothGradient.Test`, `preEnergy`, `relaxation` | L² of the given law; ordinary gradient weight |
| Ambient ordinary-gradient constant | `Poincare.SmoothGradient.Ambient.Holds`, `constant` | Relaxation directly in the ambient space |
| Intrinsic ordinary-gradient energy and constant | `Energy.SmoothGradient.Intrinsic.energy`; `Poincare.SmoothGradient.Intrinsic.Holds`, `constant` | Ordinary-gradient relaxation on the intrinsic support, pulled back to L² of the original law |
| External weighted gradient | `Energy.WeightedGradient.apply B g`, `IsTest ν B g`, `operator ν B hac` | Given law and externally chosen continuous linear operator B; B need not be a covariance factor |
| Ordinary Lipschitz-gradient relaxation | `Energy.LipschitzGradient.relaxation ν m hac` | Relaxation of globally Lipschitz L² tests with B = id; distinct from smooth tests |
| Covariance-weighted gradient relaxation | `Energy.CovarianceGradient.Test`, `density`, `preEnergy`, `relaxation` | Given law; globally Lipschitz, L², integrable covariance-gradient density |
| Intrinsic covariance energy and constant | `Energy.CovarianceGradient.Intrinsic.energy`; `Poincare.CovarianceGradient.Intrinsic.Holds`, `constant` | Remains in L² of intrinsicMeasure, without pullback to ambient L² |
| Local slope | `Energy.LocalSlope.apply`, `energy`, `Admissible` | Integral of the squared pointwise local slope; no factor 1/2 |
| Finite local-slope bound | `Poincare.LocalSlope.Holds ν C` | Given coordinate law ν; does not automatically take the intrinsic law |
| Intrinsic local-slope optimal constant | `Poincare.LocalSlope.Intrinsic.constant μ` | First take intrinsicMeasure μ, then the infimum over finite nonnegative constants |
| Optimizer for arbitrary L² energy | `Poincare.L2Energy.Holds μ Q C`, `constant μ Q` | Explicit energy Q; retains infinite optima and zero-energy boundaries |
| Distribution function of a real probability law | `Probability.Line.cdf μ`, `map_cdf_eq_uniform`, `integral_cdf_sub_half_sq` | Given `ProbabilityMeasure ℝ`; continuity, derivatives, and uniform pushforward under a density are in the same namespace |
| Borell density of a real log-concave law | `KLS.LineDensity μ` (fields `ρ`, `isBorell`); `d.pos`, `d.mul_le_mul_of_add_eq`, `d.two_mul_cdf_le`, `d.smoothTest_holds`, `d.one_div_le_variance` | Density data in a structure, results invoked with `d.` dot notation; log-concavity `hμ` and median `hm` remain explicit |
| Density at a point of balanced mass | `KLS.LineDensity.ofReal_mul_eLpNorm_top_le`, `ae_mul_le`, `mul_le_of_mem_interior_support`, `mem_interior_support_of_measureReal_Ioi` | Invoked with `d.`; `ε ‖ρ‖_∞ ≤ ρ 0` when both half-lines carry mass at least `ε`, with `‖ρ‖_∞` the essential supremum |
| Cheeger constant on the line | `KLS.LineDensity.minkowskiConstant_eq_two_mul`, `minkowskiConstant_le_two_mul`, `minkowskiContent_Iic_le`, `inv_minkowskiConstant_sq_le_three_mul_evariance`; `KLS.LogConcave.inv_minkowskiConstant_sq_le_three_mul_evariance` | `Is = 2 ρ(m)` at a median; lower bound written `Is⁻² ≤ 3 Var`, exact in `[0, ∞]` |
| Grünbaum's lemma on the line | `KLS.LogConcave.exp_neg_one_le_measureReal_Ici`, `exp_neg_one_le_measureReal_Ioi`, `exists_le_mul_exp`, `measureReal_Ioi_rpow_mul_le`, `integral_Ioi_measureReal_Ioi_eq`, `reflect_logConcave` | Mean `0` written `∫ x ∂μ = 0`; having a density written as nonempty interior of the support; reflection through `Probability.mapContinuousLinearEquiv` with `ContinuousLinearEquiv.neg ℝ` |
| One-dimensional 4·Var bound | `KLS.LogConcave.localSlope_constant_le_four_variance`, `localSlope_constant_le_four_evariance`, `smoothTest_holds_four_variance`, `KLS.logConcave_dirac` | Results invoked with `hν.`; constant 4 appears in names, not as a separate parameter |
| One-dimensional 12·Var bound (historical corollary) | `KLS.LogConcave.localSlope_constant_le_twelve_variance`, `smoothTest_holds_twelve_variance`, `localSlope_constant_le_twelve_variance_of_four` | Independent proof retained in `Line/Poincare.lean`; versions derived from 4 have suffix `_of_four` |
| Affine quantile model | `Probability.Line.unitUniform`, `affineWeight a b`, `affineQuantile a b p`, `variance_affineQuantile`, `one_div_le_variance_affineQuantile` | Parameter order `a b p u`: weight `a²(1−u)+b²u`, integration origin `p`, variable `u` |
| Profile bounds and truncated tests | `d.variance_ge_of_affine_bound`, `d.cdf_mul_one_sub_cdf_le_sd_mul`, `KLS.clip a b f`, `clipCentered μ a b f`, `tailIntegral μ h`, `cdfProd μ`, `boundaryTerm μ h`; `d.variance_clip_le`, `d.variance_le_four_variance_mul` | `clip` is a top-level definition under `FunctionalInequalities.KLS`, with lemmas in namespace `clip` (`clip.of_le`, `clip.of_mem`); `LineDensity` results use `d.` |
| Anchored half-line Hardy bounds | `d.setIntegral_Iic_sq_sub_le_of_le hμ hi hm hf hpΩ hpm`, `d.setIntegral_Ioi_sq_sub_le_of_le`, `d.integral_sq_sub_mul_le_left_of_le` | Median version wraps `p = m`; `_of_le` indicates the order premise placing the anchor on the same side of the median |
| Local domination on open sets | `Probability.LocallyDominatesOn ν m Ω`; `LocallyDominates ν m` abbreviates `Ω = interior support` | Lemmas in `LocallyDominatesOn`, invoked with dot notation such as `h.exists_lintegral_le` |
| Local density assumptions and raw/core agreement | `Energy.SmoothGradient.LocalDensity ν m` (fields `Ω`, `ρ`, and five properties); `D.absolutelyContinuous`, `D.locallyDominatesOn`; `SmoothGradient.preEnergy_agreesOnTests ν m D` | Assumptions packaged in a structure; conclusions take explicit `(ν m D)`; intrinsic instances under `SmoothGradient.Intrinsic` |
| Normal-coordinate obstruction | `Energy.SmoothGradient.normalCoordinate μ n`, `Test.normalCoordinate`, `not_respectsAmbientFibers` | Named obstruction alongside `Poincare.Euclidean.dirac_raw_energy`, not a ledger node |
| Two-point variance identity | `Probability.two_mul_evariance_eq_lintegral_prod ν hX`, `integral_sub_sq_prod` | Probability law ν and a.e. strongly measurable X: `2·eVar[X] = ∬‖X t − X s‖ₑ² d(ν⊗ν)`; both sides are ⊤ when X ∉ L² |
| Lower quantile and Paley–Zygmund bound | `Probability.lowerQuantile μ g δ`, `le_lowerQuantile`, `lowerQuantile_nonneg`, `sq_mul_sq_integral_lt`, `mul_eLpNorm_one_le_lowerQuantile` | Real `sInf` of `{q : δ ≤ μ{g ≤ q}}` (E. Milman 2009, §4), so an empty or unbounded-below set gives `0`; distinct from the line quantile model `Probability.Line.affineQuantile` |
| Trace inequality for matrix powers | `Analysis.trace_rpow_mul_rpow_mul_le`, `trace_diagonal_rpow_mul_le`, `cfc_eq_mul_diagonal_mul`, `rpow_mul_rpow_add_rpow_mul_rpow_le` | Real square matrices; the real power of a positive definite `A` is `cfc (· ^ α) A`, not a new definition |
| Majorization Gronwall comparison | `Analysis.sum_le_sum_exp`, `sum_le_sum_exp_step`, `sum_mul_le_sum_mul_of_sum_le`, `exp_mul_sub_sum_le`, `le_of_hasDerivAt_nonpos` | Families indexed by `ℕ` with sums over `Finset.range k`; time functions on `[0, ∞)` given as `ContinuousOn … (Ici 0)` |
| Conditional-fiber form | `KLS.ConditionalFiber.functional μ ρ` (`Energy.Functional`, value `form μ ρ`); fiber layer `twoPointMeasure κ b`, `twoPointMeasure_swap`, `jump κ b f`, `energyAt_eq_jump_div`; form layer `energy_le_of_lipschitzWith`, `dense_domain`, `lowerSemicontinuous_form`, `closedQuadratic`, `markovian`, `dirichlet` | Fiber lemmas take explicit `(κ b)`, form lemmas explicit `(μ ρ)`; `jump` is the unnormalized squared-jump integral and `energyAt` divides it by `2·eVar[id]` |
| Conditional-fiber energy comparison | `KLS.ConditionalFiber.FiberBound μ ρ κ` (fiber Poincaré input); `energy_le_of_fiberBound μ ρ hρ m hac hfiber hf`, `literatureConstant_le_of_fiberBound μ ρ hρ m hac hfiber hform` | Input `κ : NNReal` and form-gap constant `C : NNReal` are implicit and inferred from hypotheses; Haar reference `m` and `hac : μ ≪ m` are explicit; `_of_fiberBound` records dependence on fiber input, without encoding the value of `κ` |
| One-dimensional Brunn–Minkowski and Prékopa–Leindler | `Probability.Line.volume_add_le_volume_add`, `le_volume_combination`, `prekopaLeindler` | Purely one-dimensional measure-theoretic tools, independent of log-concavity; combination-set notation agrees with `KLS.LogConcave`; the right side may be nonmeasurable (outer measure) |
| Haar Fubini splitting along lines | `Probability.lineMap`, `lineEquiv hθ`, `exists_lintegral_line` | `θ^⊥ × ℝ ≃ₗ E`; the scale depends on `θ` and is existential, neither computed nor required measurable in `θ` |
| From log-concave density to compact-set log-concavity | `KLS.LineDensity.logConcave` | Invoked with `d.`; converse to `KLS.LogConcave.exists_lineDensity` |
| Explicit line-slice kernel | `KLS.ConditionalFiber.sliceMass`, `SliceGood`, `sliceDensity`, `sliceKernel p hp`; `compProd_baseLaw_sliceKernel`, `ae_sliceKernel_eq`, `sliceKernel_mul_sliceMass` | Explicit measurability proof `hp : Measurable p` (`Kernel.piecewise` needs a measurable set); no log-concavity premise |
| Log-concave conditional fibers | `KLS.LogConcave.ae_conditionalFiber_logConcave`, `conditionalFiber_fiberBound_four`, `conditionalFiber_energy_le_four_mul`, `conditionalFiber_literatureConstant_le_four_mul`; `conditionalFiber_energy_le_twelve_mul_of_four`, `conditionalFiber_literatureConstant_le_twelve_mul_of_four` | Results use `hμ.`; 4 is in the name, and 12 derived from 4 has suffix `_of_four` |
| Relaxations of local slope and asymptotic Lipschitz energy | `Energy.AsymptoticLipschitz.{apply,energy,Admissible,preEnergy,relaxation}`; `Energy.LocalSlope.{preEnergy,relaxation}` | The two Cheeger conventions appear in parallel; at this recorded stage only unconditional `LocalSlope.relaxation ≤ AsymptoticLipschitz.relaxation` is proved, with equality an explicit obligation |
| Metric Cheeger energy | `Energy.Cheeger.{ofLocalSlope,ofAsymptoticLipschitz,energy,Intrinsic.energy}`; `Energy.SmoothGradient.relaxation_eq_localSlope_of_absolutelyContinuous`, `Intrinsic.energy_eq_two_mul_cheeger_of_absolutelyContinuous`; `KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` | Convention selected only at `Cheeger.energy := ofLocalSlope`; `_of_absolutelyContinuous` marks the restricted scope; the unconditional version remains WIP in this recorded stage |
| Partial tensor symmetrization (BKL Lemma 2.2) | `Analysis.Tensor.fixingOutside`, `blockAverage`, `norm_le_four_pow_mul_norm_blockAverage`; coordinate form `Tensor.Coord n k`, `slotPerm`, `slotRep`, `slots`, `symmetrize`, `norm_le_four_pow_mul_norm_symmetrize` | `Coord n k = EuclideanSpace ℝ (Fin k → Fin n)` carries the Hilbert–Schmidt norm (named `Coord`, not `Array`, which is a Lean core type); `symmetrize n k q` averages the first `q` index positions and fixes the trailing ones |
| Multilinear symmetrization and coefficient arrays | `Analysis.Tensor.symmetrizeML`, `appendInner`, `sum_perm_inner_init_last`, `coordTensor` | `symmetrizeML` averages all arguments of a real multilinear map; `appendInner Ψ` places the original index after the `d` Taylor indices; `coordTensor b Φ` is the coefficient array in an orthonormal basis `b` |
| Exponential tilts and Taylor tensors (BKL (26)–(28)) | `Analysis.BakryEmery.expTilt`, `tiltAverage`, `taylorTensor`, `logLaplace`, `cumulant`; identities `tiltAverage_neg_weightedLaplacian`, `taylorTensor_neg_weightedLaplacian` and their `_of_hasTemperateGrowth` versions | Total definitions: a zero tilted measure gives zero averages; `taylorTensor` is a continuous multilinear map whose `‖·‖` is the operator norm; the suffix `_of_hasTemperateGrowth` marks Mathlib's temperate-growth class (the source class `𝒜`) |
| Centered inverse of the closed generator (BKL Lemma 2.1, operator domain) | generic `Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap`, `eq_of_adjointComp_eq`, `norm_le_of_gap`; heat model `KLS.LogConcave.existsUnique_centered_adjointComp_eq`, `centered_adjointComp_bounds`, `norm_centered_gradient_le` | Gap constant `C` real in the generic layer and `NNReal` against the literature constant in the model; "centered" is `L2.mean ν u = 0` |
| Regular potentials and laws (BKL (12)) | `KLS.RegularPotential V a b` (fields `temperate`, `pos`, `lower`, `upper`), `hV.law`, `hV.isProbabilityMeasure`, `hV.integrable_exp_mul_norm`, `hV.existsUnique_centered_adjointComp_eq` | The structure holds only the assumptions of (12); consequences are theorems in the `RegularPotential` namespace used as `hV.`; `law` is `volume.tilted (-V)`, so the source's normalized potential is `V + log Z` |
| Tensor energies (BKL Lemmas 3.2, 3.4, Corollary 3.5, (35), (36)) | `Analysis.BakryEmery.gradCoord`, `gradCoord_gradCoord_symm`, `integral_norm_sq_weightedLaplacianVec_ge`, `summable_and_tendsto_zero_of_energy`, `summable_and_tendsto_zero_of_poisson_chain`, `integral_norm_sq_gradCoord_sub_eq_of_normalized`, `integral_norm_sq_gradCoord_eq_add_sum`, `exists_symm_integral_norm_sq_sub_le`, `swapFirstTwo`, `symmetrizeFirstTwo`, `integral_norm_sq_sub_symmetrizeFirstTwo_le` | `gradCoord f x ∈ PiLp 2 (Fin n → G)` puts the derivative index first and carries the Hilbert–Schmidt norm; "symmetric in the first two indices" is `T x i j = T x j i`; `_of_poisson_chain` and `_of_normalized` take the iterates and the relations (30), (33) as hypotheses |
| Conditional third cumulant (BKL Lemma 4.2) | `Analysis.BakryEmery.LetwinQuadraticBound`, `sum_sq_cumulant_three_le_of_letwin`, `cumulant_three_eq_integral` | `LetwinQuadraticBound μ` is a named `Prop` used only as a premise; the suffix `_of_letwin` marks the conditional result |
| Components of vector-valued `L²` | `L2.mean_compLp_innerSL`, `L2.sum_norm_sq_compLp_innerSL`; `KLS.LogConcave.existsUnique_centered_adjointComp_eq_components` | Components are `(innerSL ℝ (b k)).compLp g` for an orthonormal basis `b`; the suffix `_components` marks the componentwise tensor lift |
| Temperate functions in the generator domain (BKL Lemma 2.1 on `𝒜`, (20), (32)) | `KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth`, `exists_toLp_mem_adjointComp_domain_of_hasTemperateGrowth`, `centered_inverse_eq_toLp_of_hasTemperateGrowth`, `integral_sq_sub_integral_le_of_hasTemperateGrowth`, `integral_norm_sq_gradCoord_le_of_hasTemperateGrowth`, `one_le_mul_sq_of_poisson`, `exists_symm_integral_norm_sq_sub_le_mul` | `exists_toLp_mem_…` states membership with the `MemLp` witnesses existentially quantified; `_of_hasTemperateGrowth` marks the class `𝒜`; `_mul` marks the bound `C χ` (`λ = 1/C`) |

Both kinds of tests support `f.energy` and `f.toL2`; weighted-test properties support `hf.memLp`.
Do not merge mathematically distinct test classes, weights, carriers, or relaxations.
`ClosedQuadratic` does not itself include Markov/Dirichlet properties. For smooth-gradient
relaxation these are separate theorems `Energy.SmoothGradient.markovian`, `dirichlet`, and
`Intrinsic.dirichlet`, proved with the smoothed normal contraction `Energy.NormalContraction.smoothed`
and test composition `SmoothGradient.Test.compSmoothed`. Comparison of optimal constants for
ordinary gradients and local slopes does not automatically identify the energies.

## Transport and covariance

- Pushforward laws: `Probability.translateLaw`, `mapLinearIsometryEquiv`, `mapContinuousLinearEquiv`. Names distinguish general linear equivalences from Euclidean isometries.
- Pullback of L² classes: `L2.Translation`, `L2.LinearIsometry`, and `L2.ContinuousLinearEquiv` each provide `pullback`, `pullbackInv`, and `pullbackEquiv`. Pullback goes from the image law's L² to the source law's L²; `pullbackInv` composes with the inverse map. The implementation reuses Mathlib's `Lp.compMeasurePreservingₗᵢ`.
- Energy invariance belongs in `Energy.CovarianceGradient`; invariance of the corresponding optimal constant in `Poincare.CovarianceGradient`.
- `Poincare.CovarianceGradient.Intrinsic.constant_translateLaw` directly states ambient-law translation invariance. `constant_eq_translate_intrinsicMeasure` compares the optimal-constant expression after translating the intrinsic law.
- `Covariance.exists_inner_eq_norm_sq` and `exists_intrinsic_inner_eq_norm_sq` provide only `∃ B, ∀ v, ⟪Σ v,v⟫ = ‖B v‖²`. Their names do not assert B² = Σ, self-adjointness, positivity, or uniqueness. Whitening remains a self-adjoint W with WΣW = id, without promotion to a unique positive inverse square root.

## Property proofs and local names

Log-concave corollaries remain in `KLS.LogConcave`, inferring the measure from its property proof:

```lean
hμ.intrinsicSmooth_constant_eq_localSlope
hμ.intrinsicCovariance_closedQuadratic
hμ.intrinsicCovariance_energy_eq_operator m B hB
hμ.intrinsicCovariance_constant_eq_normSq m B hB
hμ.intrinsic_frontier_support_eq_zero
```

`ConditionalFiber.Nondegenerate` requires an orthogonal base point, a finite second moment,
and nonzero variance. `energyWithKernel` explicitly indicates an externally supplied kernel.
`Probability.memLp_id_two_iff_lintegral_enorm_rpow_lt_top` unifies second-moment criteria for
real laws and general Borel normed spaces. `LipschitzApproximation.kernelDerivativeMass` is
the integral of the kernel's derivative norm normalized by its mass.

## Scopes and parameters

1. Organize differential properties first, then introduce measure/L², Haar/absolute-continuity, and log-concavity assumptions. Group local sections by required structure; do not pile strong assumptions at the file top and disable `unusedSectionVars`.
2. Measures and tests inferred from objects or property proofs should be implicit. Chosen measures, weight operators, and required reference measures stay explicit; use instances for structure and explicit proof parameters for key mathematical premises.
3. `variable (hμ : LogConcave μ)` does not enter a theorem statement merely because its proof uses hμ. State it in the theorem header or use local `include hμ in`, then inspect elaborated parameters.
4. Local `omit ... in` is allowed when mixing levels of generality; keep checks enabled. Record and verify redundant-instance removal, parameter explicitness/order changes, and lemma mergers separately: they are not pure renames.
5. One-use proof helpers should be `private`. Keep `open`, notation, include, instances, and options local. Do not shorten variable lists by bundling all assumptions into a new structure or typeclass.
6. Retain mathematically meaningful weighted, L¹/L², ae, compact-support, boundary, finiteness, and directional qualifiers. Borel sets and Borell representation are different concepts. Names locate results; types and documentation give their complete assumptions and conclusions, rather than spelling out the theorem in its name.

Renaming updates all consumers, Blueprint anchors, guards, snapshots, and current documentation.
Do not rewrite historical decisions/explorations as part of renaming. Update golden files and
source hashes after review; provide no compatibility aliases for old names.

## File and declaration scope

Files belong to the family of their primary mathematical object: the smooth-test frontend in
`Poincare/SmoothTest/`, local-slope/gradient relations in `Energy/LocalSlope/Gradient.lean`, and
log-concave corollaries in `LogConcave/{Covariance,Translation,ClosedForm,WeightedGradient,Isotropic,Poincare}`.
Declarations for an object use its namespace. Declaration headers use short names, not
`_root_.FunctionalInequalities.…` to escape an incorrect outer namespace. Group cross-object
comparisons under their common parent namespace; do not add aliases just to shorten calls.

### Family names belong in directories, not filenames

Directory conventions (library-wide since 2026-09-20; see the
[directory reorganization](decisions/2026-09-20-formalization-directory-organization.md)):

1. **Three or more** modules for one mathematical object must form a family directory.
2. Two modules may form a family directory when they are a genuine foundational/extension pair. Two merely adjacent modules without that relationship remain at the existing level.
3. Do not keep both `X.lean` and `X/`; rename the foundational module to `X/Basic.lean`. The root aggregate `FunctionalInequalities.lean` alongside `FunctionalInequalities/` is standard Lean library-root layout and is exempt.
4. Retain at the root only cross-family infrastructure, stable public entry points, or modules that genuinely belong to no single object.
5. Organize directories by **primary mathematical object**, not a one-off proof route.
6. A file move must not change namespaces, declaration names, statements, proofs, assumptions, dimensional scope, or certificate status.
7. Do not provide old-path compatibility modules or aliases; resolve old references using the maps listed here.

For a family of three or more modules, put its name in the **directory** and retain only the
distinguishing term in filenames. Examples include `Poincare/SmoothTest/`,
`Energy/LocalSlope/Gradient.lean`, `Energy/CovarianceGradient/`, `KLS/LogConcave/Line/`,
`Resolvent/`, `Exponential/`, `Yosida/`, and `Generated/` under `Analysis/Semigroup/`, and
`ConditionalFiber/`, `Geometry/Cheeger/`, and `Geometry/Coarea/` under `KLS/`.
Do not repeat the family in each basename: use `LogConcave/Covariance.lean`, not
`LogConcave/AffineCovariance.lean` (see the
[module map](api-migration/2026-09-08-library-naming-module-map.json)).

**Place new `Analysis/` modules in family subdirectories using this rule**, removing the family
term from basenames. Historical flat modules were reorganized in batches: the 2026-09-17
`Graph`, `RankDeficient`, `Sard`, `Vector`, and `Whitney` moves are in the
[Analysis map](api-migration/2026-09-17-analysis-module-map.json); 2026-09-19 semigroup moves
in the [Semigroup map](api-migration/2026-09-19-semigroup-module-map.json) and KLS moves in the
[KLS map](api-migration/2026-09-19-kls-module-map.json). The 2026-09-20 library-wide reorganization
has three batches: [Analysis](api-migration/2026-09-20-analysis-module-map.json),
[Energy/Probability/Poincare](api-migration/2026-09-20-foundation-module-map.json), and
[KLS](api-migration/2026-09-20-kls-module-map.json). The 2026-10-07 batch forms
`Analysis/BakryEmery/{Tilt,Bochner,IntegrationByParts}/` and
`KLS/LogConcave/Density/GaussianSmoothing/` ([map](api-migration/2026-10-07-family-directories-map.json)).
Historical decisions and explorations retain
their original paths without retrospective migration; each reorganization must provide a path
map so old references remain resolvable.

Existing directories based on namespace or domain rather than family are exceptions to rule 5
and remain unchanged: `Poincare/Euclidean/`, `Poincare/FiniteProduct/`, `Poincare/LipschitzGradient/`.

Directories group files without changing mathematical identity. Pure file moves preserve every
existing namespace, including `FunctionalInequalities.Analysis` and its object subnamespaces;
do not flatten them or rename solely because a directory changes. Namespace/public-name changes
are separate API migrations with their own maps and validation. Directory reorganization still
requires import, evidence-path, Blueprint-link, and verification-snapshot checks.

For example, write `theorem apply_eq_norm_gradient` inside `Energy.LocalSlope`. Log-concave
proofs can still call `hμ.intrinsicCovariance_closedQuadratic`,
`hμ.intrinsicSmooth_constant_eq_localSlope`, and `hμ.intrinsicWeightedOperator m B`;
`weighted` retains the meaning of an arbitrary external weight B. See the
[library-wide naming cleanup](decisions/2026-09-08-library-naming.md).

## Semigroup interface layout (2026-09-20, after S0a)

File responsibilities and public API names are reviewed separately. Generic differential tools
belong in `BakryEmery/Calculus.lean`; the weighted Laplacian in `Laplacian.lean`; integration by
parts, Gamma and Bochner each retain their own module. Counterexamples to unrestricted operator
families belong in `Semigroup/Exponential/Counterexample.lean`, not inside `Yosida/Laws.lean`.
The closed-form normalization bridge belongs in `LogConcave/WeightedGradient/Energy.lean`.

The S0a public interfaces use `Analysis.Semigroup.Generated` and
`KLS.LogConcave.HeatSemigroup`, with short names such as `preserves_domain`, `generator_comm`
and `right_derivative`. Types retain the exact generator domain, right-limit direction and
arbitrary-weight scope. The final cleanup also migrates the construction, law and Markov APIs into these namespaces,
with an explicit old/new name map. Parameter order and mathematical scope are preserved. See the [layout record](decisions/2026-09-20-semigroup-layout.md) and
[complete migration map](api-migration/2026-09-20-semigroup-layout-map.json).

The curvature layer (2026-10-03) keeps the same split. Pointwise and integrated `Γ₂ ≥ ρ Γ` for a
potential with `∇∇U ≥ ρ` live in `BakryEmery/Curvature.lean` (`mul_gamma_le_gammaTwo`,
`integral_gammaTwo_eq`, `mul_integral_gamma_le`). Abstract energy decay under
`ρ ‖T y‖² ≤ ‖A y‖²` lives in `Semigroup/Generated/Curvature.lean` (`norm_map_apply_sq_le_exp`,
`norm_sq_sub_norm_apply_sq_le`). The heat-semigroup specialization lives in
`KLS/LogConcave/HeatSemigroup/Curvature.lean`. The curvature hypothesis is always written
`∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v`, never as a new definition.

Strong convergence (2026-10-03) lives in `Semigroup/Generated/Convergence.lean`: for `T` closed
and densely defined between real Hilbert spaces and `A = T†T`, `ker A = ker T` on the operator
domain (`adjointComp_eq_zero_iff`), and `P_t g → 0` for every `g` orthogonal to `ker T`
(`tendsto_apply_of_inner_eq_zero`, via `tendsto_apply_of_mem_closure_range`). It identifies no
concrete kernel and gives no rate; the heat-model kernel and ergodicity belong to the
`KLS/LogConcave` owners.

The heat-model kernel and ergodicity (2026-10-04) are split by object. A locally integrable
function with zero weak gradient is a.e. constant in `Energy/Euclidean/ZeroGradient.lean`
(`exists_ae_eq_const_of_integral_mul_fderiv_eq_zero`). The weak gradient of `D(T̄)` and
`T̄ h = 0 ⇒ h = mean` live in `KLS/LogConcave/WeightedGradient/Kernel.lean`
(`integral_mul_fderiv_eq_neg_integral_mul_inner`, `eq_const_mean_of_closedWeightedOperator_eq_zero`).
Tilted Haar laws (integrable density, Borell density, log-concavity from a convex potential, full
support) live in `KLS/LogConcave/Density/Tilted.lean`. The kernel iff, ergodicity and the
Corollary 4.8.2 statements extend `HeatSemigroup/Curvature.lean`.

The completed family migration and candidate decisions are recorded in
[the final cleanup](decisions/2026-09-20-final-cleanup.md), with the
[48-name API map](api-migration/2026-09-20-final-cleanup-map.json). Generic resolvent, Yosida
and weighted-operator helpers retain their own object identities. Name length or the absence of
an external library consumer alone is not grounds for renaming or privatizing a mathematical lemma.
