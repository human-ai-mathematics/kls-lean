# Lean public naming and parameter organization

Before adding modules, splitting files, or migrating an API, follow the
[classification and delivery workflow](workflow.md). This document maintains detailed naming
and parameter conventions.

Public names express mathematical objects, operations, and conclusions. Namespaces may span
implementation modules; certificate entry points, ledger node IDs, and source labels retain
stable identities. `FunctionalInequalities` is omitted below.

## Short names do not repeat the namespace

Do not repeat an object or role already supplied by the namespace. Use operation names such
as `apply`, `energy`, `toL2`, and `constant`; theorem short names describe properties of those
operations. Do not encode every assumption in the name. Examples:

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
do not name an inequality with a coefficient as direct domination.

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
| Inverse-Hessian quadratic form (Letwin Lemma A.4 support) | `Analysis.BakryEmery.sum_inverseHessianEntry_mul_mul_nonneg` | Owned by `Analysis/BakryEmery/MongeAmpere.lean` beside the inverse-Hessian positivity facts; coordinates in any orthonormal basis of any rank; the conclusion names the sum shape |
| Jordan parts and trace energy of real symmetric matrices (Letwin Theorem 2.5 support) | `Analysis.symmetric_jordan_decomposition`, `symmetric_jordan_trace_support`; `cfc_posSemidef_of_nonneg`, `trace_cross_nonneg`, `trace_energy_nonneg`, `jordan_trace_domination` | The Jordan parts extend `Analysis/Matrix/Sign.lean` (which now imports `Matrix/Trace/Power.lean`, owner of the spectral representation `cfc_eq_mul_diagonal_mul`); the PSD spectral function and the trace properties extend `Analysis/Matrix/Trace/Energy.lean`; arbitrary finite index types, factor order as stated, one-use helpers private, no aliases |
| Trace energy of a symmetric matrix field under a measure (Letwin Theorem 2.5 extension step) | `Analysis.symmetric_trace_integral_extension_mul`, `symmetric_trace_integral_extension_mul_of_ae_posSemidef`; `symmetric_trace_integral_extension`, `symmetric_trace_integral_extension_of_ae_posSemidef` | New leaf `Analysis/Matrix/Integral.lean` (imports `Matrix/Sign.lean` and Mathlib Bochner integration), keeping the pointwise `Trace`/`Sign` owners free of measure dependencies; the PSD bound is an explicit hypothesis, arbitrary measure/measurable space/finite index type; `_mul` takes an implicit real coefficient `C` with no sign condition (inferred from the hypothesis), and the unsuffixed and `_of_ae_posSemidef` names are its `C = 2` specializations |
| Centered range density of diffusion images (Letwin Lemma A.6 support) | `KLS.LogConcave.HeatSemigroup.compactSmoothDiffusionImage`, `centered_mem_closure_compactSmoothDiffusionImage`, `center_mem_closure_compactSmoothDiffusionImage` | New `KLS/LogConcave/HeatSemigroup/Range.lean` in the family namespace (imports the generator, kernel and convergence owners; keeping it out of `Generator.lean` avoids mixing the generator definition with this approximation property; distinct from the form range of `FormRange.lean`); `compactSmoothDiffusionImage` is the literal set of `−L f` classes, `f` smooth with compact support |
| Ordinary diffusion coercivity and inverse Young inequality (Letwin Lemma A.6 supports) | `Analysis.BakryEmery.compact_ordinary_diffusion_coercivity`; `Analysis.inverse_quadratic_young` | Coercivity extends `Analysis/BakryEmery/Curvature.lean` as the `ρ`-free sibling of `mul_integral_gamma_le` (private compact Hessian-square helper); Young extends `Analysis/Matrix/Positivity.lean`. Both sit in reopened namespace blocks carrying the candidate's verbatim, unused variable context, which fixes the accepted universe name (`ι : Type u_2`) and hygiene labels; `ordinary` distinguishes the weighted Laplacian from the inverse-Hessian operator |
| Inverse-Hessian energy (Letwin Lemma A.6) | `Analysis.BakryEmery.hessian_inverse_young`, `gradient_pairing_eq_fderiv`, `inverse_hessian_energy_eq_coordinate_sum`, `continuous_inverse_hessian_gradient_energy`, `inverse_hessian_gradient_energy_nonneg` | New `Analysis/BakryEmery/InverseHessianEnergy.lean` above `MongeAmpere.lean` (owner of the smooth inverse entries; placing it in `HessianOperator.lean` would need that import, a cycle); the energy is `⟪∇f, Ring.inverse (hessianOperator U x) ∇f⟫`; `gradient_pairing_eq_fderiv` is `⟪∇f x, v⟫ = Df(x) v`, used by the energy facts and the Gaussian audit |
| Scalar Brascamp–Lieb for a given potential (Letwin Lemma A.6) | `KLS.LogConcave.scalar_brascamp_lieb_finite_energy`, `scalar_brascamp_lieb_extended_energy`, `scalar_brascamp_lieb_extended_energy_of_bounded`, `compact_pairing_identity`, `compact_diffusion_toLp_mean_zero`, `compact_variational_estimate` | New `KLS/LogConcave/BrascampLieb.lean` consuming the range (`HeatSemigroup/Range.lean`) and coercivity (`Analysis/BakryEmery/Curvature.lean`) owners; `finite_energy` (C², integrable energy) and `extended_energy` (C^∞, `ℝ≥0∞` right side) are separate scopes; the one-use Hilbert-closure and `L²`-pairing helpers are private (API classification: public in the prototype) |
| Hessian trace evolution (Letwin (2.8), Theorem 2.5 support) | `Analysis.BakryEmery.StdBasisIndex`, `stdHessianMatrix`, `stdHessianMatrixDeriv`, `stdHessianMatrixGenerator`, `hessianInverseOperator_trace_stdHessianMatrix_sq` | New `Analysis/BakryEmery/HessianTrace.lean` above `MongeAmpere.lean` (owner of `hessianMatrixIn`) and below every per-paper consumer; `std` marks `stdOrthonormalBasis ℝ E`, indexed by `StdBasisIndex E = Fin (finrank ℝ E)`; `Generator` is the entrywise image under `hessianInverseOperator`; the candidate placeholder names are replaced by an explicit map; one-use operator rules (constant, scalar, sum, trace product) are private |
| Monge–Ampère substitution in the trace evolution (Letwin (2.9)–(2.10)) | `Analysis.BakryEmery.stdHessianConjugate`, `stdThirdGram`, `stdHessianConjugate_eq`, `stdHessianMatrixDeriv_isSymm`, `stdHessianMatrix_posSemidef`, `stdInverseHessian_posSemidef`, `stdHessianConjugate_posSemidef`, `stdThirdGram_posSemidef`, `posSemidef_mul_stdHessianMatrix_mul`, `stdHessianMatrixGenerator_apply_on_range`, `stdHessianMatrixGenerator_eq_on_range`, `traceGenerator_210_on_range`, `weightedDerivativeTrace_nonneg`, `hessianConjugateTrace_nonneg_on_range`, `thirdGramTrace_nonneg`, `traceGeneratorCondition_on_range`; `Analysis.sum_entry_mul_nonneg`, `trace_mul_nonneg`, `traceGram_posSemidef` | Section `MongeAmpereTrace` of `Analysis/BakryEmery/HessianTrace.lean` (above `MongeAmpere.lean`); the matrix pairings extend `Analysis/Matrix/Positivity.lean` beside `posSemidef_weightedGram`, in the candidate's variable context (accepted universe names); candidate `candidate*`/`actual*` names replaced by an explicit map; `_on_range` marks the local-`V` hypotheses on `closure K ⊇ range ∇φ`; the explicit interval-potential client and its helper `generator_const` stay in the audit |
| Conditional third cumulant (BKL Lemma 4.2) | `Analysis.BakryEmery.LetwinQuadraticBound`, `sum_sq_cumulant_three_le_of_letwin`, `cumulant_three_eq_integral` | `LetwinQuadraticBound μ` is a named `Prop` used only as a premise; the suffix `_of_letwin` marks the conditional result |
| Scalar cutoff profile (Letwin Lemma A.4, real-variable part) | `Analysis.smoothTransition_two_sub_cutoff`, `exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`, `monotone_and_tendsto_smoothTransition_two_sub_div_succ`, `inv_mul_intervalIntegral_div_three_cutoff`, `deriv_comp_sub_div_and_deriv_deriv`, `monotoneOn_and_tendsto_smoothTransition_two_sub_div` | Generic leaf `Analysis/Cutoff/Profile.lean` with three Mathlib imports; the profile is the lambda `fun s => Real.smoothTransition (2 - s)` (no new definition), and conjunctive results are named by their conclusions; no aliases |
| Letwin Lemma A.4 supports | `Analysis.exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`; `Analysis.BakryEmery.hessianInverseOperator_self`, `bounded_hessianInverseOperator_self`, `hessianInverseOperator_comp`, `sum_inverseHessianEntry_mul_fderiv_comp`, `abs_hessianInverseOperator_comp_sub_div_le`, `continuous_hessianInverseOperator`, `integral_hessianInverseOperator_self_mul_comp_eq_neg`, `integrable_and_neg_integral_deriv_comp_mul_le` | Coercivity is generic convex analysis in `Analysis/Convex/Coercivity.lean`; the pointwise operator facts extend `Analysis/BakryEmery/HessianOperator.lean`, the energy identity and bound extend `IntegrationByParts/InverseHessian/Basic.lean`; no hypothesis beyond each statement's own use |
| Letwin Lemma A.4 cutoffs | `Analysis.BakryEmery.exists_scaled_cutoffs_hessianInverseOperator` (real `R ≥ 1`), `exists_cutoffs_hessianInverseOperator` (natural index) | Sibling `IntegrationByParts/InverseHessian/Cutoff.lean` of the integration-by-parts owner (it needs coercivity and the scalar cutoff tools); the source-class properties are explicit hypotheses, `scaled` marks the real parameter; private one-use supports; no aliases |
| Letwin Lemma A.5 for given cutoffs | `Analysis.BakryEmery.integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs`; generic `Analysis.integrable_and_integral_eq_zero_of_cutoff_defect` | The operator form stays in `IntegrationByParts/InverseHessian/Basic.lean`; the generic Fatou/dominated-convergence core is the separate leaf `Analysis/Cutoff/Conservativity.lean`; `_of_cutoffs` marks the cutoff premise |
| Uniform-interval source law (Letwin Lemmas A.4–A.5 client) | `Analysis.BakryEmery.uniformInterval_momentPotential_{gradient, contDiff_convexOn, bilinearIteratedFDerivTwo, logDetHessian, integral_exp_neg, source_hypotheses}`, `uniformInterval_tanhSq_nonconstant_facts`; client `uniformInterval_tanhSq_integrable_and_integral_hessianInverseOperator_eq_zero` | Concrete specialization split by dependency level: potential and test-function facts in `Analysis/BakryEmery/UniformIntervalPotential.lean` (MongeAmpere level, no integration-by-parts import; one-use operator and derivative helpers private), the client in `IntegrationByParts/UniformIntervalClient.lean`; `φ`, `V`, `f` are written out, not new definitions |
| Components of vector-valued `L²` | `L2.mean_compLp_innerSL`, `L2.sum_norm_sq_compLp_innerSL`; `KLS.LogConcave.existsUnique_centered_adjointComp_eq_components` | Components are `(innerSL ℝ (b k)).compLp g` for an orthonormal basis `b`; the suffix `_components` marks the componentwise tensor lift |
| Temperate functions in the generator domain (BKL Lemma 2.1 on `𝒜`, (20), (32)) | `KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth`, `exists_toLp_mem_adjointComp_domain_of_hasTemperateGrowth`, `centered_inverse_eq_toLp_of_hasTemperateGrowth`, `integral_sq_sub_integral_le_of_hasTemperateGrowth`, `integral_norm_sq_gradCoord_le_of_hasTemperateGrowth`, `one_le_mul_sq_of_poisson`, `exists_symm_integral_norm_sq_sub_le_mul` | `exists_toLp_mem_…` states membership with the `MemLp` witnesses existentially quantified; `_of_hasTemperateGrowth` marks the class `𝒜`; `_mul` marks the bound `C χ` (`λ = 1/C`) |
| Approximate eigenvectors at the bottom of `T†T` (BKL operator route, replacing (19)) | generic `Analysis.Semigroup.Generated.exists_approx_eigenvector_of_gap`; heat model `KLS.LogConcave.exists_centered_approx_eigenfunction` | The gap `λ` is a hypothesis in the generic layer and `C_P⁻¹` in the model; "approx" names a quantitative near-eigenvector, not an eigenvector |
| Generator domain: weak Hessian, curvature form of (16), (48), Lemma 3.6 | `KLS.LogConcave.compLp_innerSL_mem_closedWeightedOperator_domain`, `compLp_innerSL_closedWeightedOperator_comm`, `sum_norm_sq_closedWeightedOperator_add_le`, `tiltAverage_adjointComp_eq`, `taylorTensor_adjointComp_eq`; `Analysis.Semigroup.tendsto_apply_of_tendsto_adjointComp`; `KLS.LogConcave.convexOn_of_eq_tilted` | Components `(innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp (T̄ F)`; `_adjointComp` marks statements about `F ∈ D(T̄†T̄)` |
| Tilt averages of `L²` classes | `Analysis.BakryEmery.tiltAverage_congr_ae`, `taylorTensor_congr_ae`, `memLp_exp_inner`, `tiltAverage_Lp_eq_inner`, `continuous_tiltAverage_Lp`, `inner_tiltAverage_Lp`, `contDiff_tiltAverage_Lp`, `taylorTensor_succ_of_eq_inner` | In `Tilt/SquareIntegrable.lean`; `_Lp` marks arguments that are `Lp` classes rather than functions |
| BKL Poisson iterates in `D(A)` (Section 3, operator route) | `KLS.LogConcave.PoissonIterate.{Field, normSq, weakGrad, gen, partialDeriv, centeredInv, gradField, grad0, genField, invField, scale, step, iter, energy, meanGradSq, defect, permField, symField, taylorField}`; results `iter_mem_domain_and_mean_eq_zero`, `genField_iter_succ`, `energy_iter_succ`, `normSq_genField_iter_succ_add_defect_le`, `normSq_grad0_iter_sub_symField_le`, `norm_taylorField_grad0_iter_sq_le`, `sum_meanGradSq_iter_le`, `taylorCriterion` | Fields are component families over `Fin k → Fin n` (standard basis), derivative index first; operators are total (`0` off the domain); `iter T f k` is the source's `h_{k+1}` |
| BKL Theorem 3.1 for regular laws | `KLS.RegularPotential.poincare_le_of_taylor`; certificate `Solutions.ThmBklTaylorCriterion.certificate` | Source form; `PoissonIterate.taylorCriterionConstant` is the explicit library constant |
| Gaussian instance of BKL (29) | `KLS.regularPotential_half_norm_sq`, `gaussian_taylor_hypotheses`, `norm_coordTensor_taylorTensor_tilted_half_norm_sq_le`, `gaussian_poincare_le_of_taylor_witness` | Standard Gaussian `volume.tilted (-‖x‖²/2)`; regularity, centering and covariance in every dimension, (29) with `R = 8` on `ℝ¹` |
| Generic tools for the final argument | `Analysis.Tensor.norm_coordTensor_eq` (Hilbert–Schmidt norm independent of the orthonormal basis), `Analysis.le_of_dyadic_recursion` | In `Analysis/Tensor/BasisChange.lean` and `Analysis/DyadicSummation.lean` |
| CEK Proposition 12 (variational attainment) | `KLS.CEK.exists_variational_maximum`, `exists_normalized_competitor`; `Probability.MomentMeasure.exists_coercivity_of_centered_probability`, `exists_convexified_lowerTruncate_variational_le_add`, `variationalFunctional_affineSubtract`; `Analysis.affineSubtract`, `exists_supporting_affine_at_zero`; `Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero` | Paper assembly in `KLS/CEK/`, generic properties in their families; full span written `∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤`; affine invariance needs a probability measure, finite measures get the mass correction |
| CEK maximiser for a bounded source (normalized Lipschitz primal) | `KLS.CEK.bounded_source_cap_lsc`, `bounded_source_cap`, `bounded_source_finite_conjugate`, `bounded_source_lipschitz_primal`, `bounded_source_real_density_client`; `Analysis.closedBallCap`, `closedBallCap_lowerSemicontinuous`, `exists_real_global_minimum_of_bounded_domain`, `legendre_le_of_real_lower_bound`, `legendre_finite_of_bounded_domain`, `real_convexOn_legendre`, `lipschitzWith_real_legendre`, `real_legendre_fenchel`; `Probability.MomentMeasure.real_legendre_normalization` | Split by dependency level: generic bounded-effective-domain geometry in the new `Analysis/Convex/BoundedConjugate.lean` (no probability or CEK import; the candidate's verbatim variable context, whose `omit` lines name measurable-space binders, needs only the Mathlib Borel-space import); the mass-one normalization beside the conjugate-mass results in `Probability/MomentMeasure/ConjugateMass.lean`; the source-law producers in the new `KLS/CEK/BoundedPrimal.lean`. `closedBallCap` (candidate `cap`) is `φ` on `closedBall 0 L` and `⊤` outside; `bounded_source` marks the `μ`-a.e. bound `‖y‖ ≤ L`; `real_` marks the finite real representative of the conjugate; the `_density_client` theorem is a generic consequence for every such `μ` |
| Legendre first variation (CEK (42), pointwise) | `Analysis.exists_finite_maximum_of_upperSemicontinuous_linear_decay`; `Analysis.conjugate_maximizer_eq_gradient`, `exists_coercive_tilt_of_mem_interior_legendre_domain`, `tiltedObjective_data`, `exists_legendre_maximizer_with_gradient_identity`; `Analysis.legendre_bounded_perturbation`, `legendre_bounded_perturbation_finite_curve`; `Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt`, `hasDerivAt_legendre_add_smul_of_dualDifferentiable` | The generic extremum is the cross-family root module `Analysis/Extremum.lean`; the three Legendre-variation modules form the family directory `Analysis/Convex/LegendreVariation/{Attainment,Perturbation,Derivative}.lean` (family rule: no `Legendre*` basenames, and `Convex/Legendre.lean` stays in place); `conjugate_maximizer_eq_gradient` moved from the scratch namespace `KLSConstruction.API.FirstVariation`; the one-use perturbation-term helper is private |
| Extended-real Legendre transform (CEK (61), Proposition 12 tools) | `Analysis.legendre`, `ConvexPotential`, `ProperPotential`, `legendre_antitone`, `fenchel_le`, `biconjugate_le`, `triconjugate_eq`, `lowerSemicontinuous_legendre`, `convex_epigraph_legendre`, `lowerTruncate`, `lowerTruncate_convexification`, `legendre_eq_interior_sup`; `affineMaximum`, `affineMaximum_coercive` | `φ : E → EReal`; `legendre φ y = ⨆ x, ⟪x, y⟫ - φ x` with no selected maximizer; measure-free, in `Analysis/Convex/` |
| Exponential-potential measure and CEK Lemmas 16–17 | `Probability.MomentMeasure.density`, `weightedMeasure`, `mass`, `PotentialIntegrable`, `variationalFunctional`, `limsup_mass_legendre_le`, `exists_subseq_integral_bounds_of_convex_epigraph`; `Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph`, `exists_subseq_lintegral_le_liminf_of_convex_epigraph` | `density φ = exp(-φ)` in `ℝ≥0∞`, zero and infinite mass retained, no normalization; Lemma 17 takes `0 ∈ interior (convexHull ℝ μ.support)` explicitly; no moment-measure predicate yet |
| Closed BKL cumulant producers | `KLS.BKL.Localization.cutoffEnergyClaim_of_letwinCompact`, `cumulantBound_of_letwinCompact` (in `KLS/BKL/Theorem41.lean`); `cutoffEnergyClaim_153`, `cumulantBound_153` (in `KLS/BKL/CumulantBound.lean`) | `_of_letwinCompact` marks the explicit compact Letwin hypothesis; `153` is the constant in the closed forms, which the certificates and `Poincare.lean` consume |
| One regular moment witness (Letwin regular class) | `Analysis.exists_regular_moment_hessian_trace_bound` | Flat conjunction of the properties used by `regularClass_matrix_variance_le_eight`, at the witness of `exists_regular_moment_weak_stein_coupling`, with the same hypotheses; no structure or class |

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
Record the old/new map with the change. Update golden files and
source hashes after review; provide no compatibility aliases for old names.

## Source documentation

Module comments and declaration docstrings describe mathematics, exact hypotheses and scope,
pinned source versions and locators, and useful proof explanations. Preserve paper attributions
and license/author notices. Keep task and route-node identifiers, rounds, worker allocation and
integration or failure logs out of source comments; such operational records stay in the local
archive, not in the published tree. When removing process text, keep the original passages in that
archive, preserve all non-comment code, and reassess matching source-evidence hashes without
changing proof or certificate status. Verification receipts continue to certify their recorded
snapshots.

## File and declaration scope

Files belong to the family of their primary mathematical object: the smooth-test frontend in
`Poincare/SmoothTest/`, local-slope/gradient relations in `Energy/LocalSlope/Gradient.lean`, and
log-concave corollaries in `LogConcave/{Covariance,Translation,ClosedForm,WeightedGradient,Isotropic,Poincare}`.
Declarations for an object use its namespace. Declaration headers use short names, not
`_root_.FunctionalInequalities.…` to escape an incorrect outer namespace. Group cross-object
comparisons under their common parent namespace; do not add aliases just to shorten calls.

### Family names belong in directories, not filenames

Directory conventions (library-wide since 2026-09-20):

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
`LogConcave/AffineCovariance.lean`.

**Place new `Analysis/` modules in family subdirectories using this rule**, removing the family
term from basenames. The historical flat modules were reorganized in dated batches between
2026-09-17 and 2026-10-12: the `Graph`, `RankDeficient`, `Sard`, `Vector` and `Whitney` moves,
the semigroup and KLS moves, the library-wide `Analysis`/`Energy`/`Probability`/`Poincare`/`KLS`
reorganization, `Analysis/BakryEmery/{Tilt,Bochner,IntegrationByParts}/`,
`KLS/LogConcave/Density/GaussianSmoothing/`, the CEK promotions into `Analysis/Convex/`,
`Probability/MomentMeasure/` and `KLS/CEK/` (moving no production API),
`Analysis/Matrix/{Trace,Positivity,DeterminantDerivative,Sign}`,
`Analysis/Cutoff/{Profile,Integrability,Conservativity}`,
`Analysis/BakryEmery/Cumulant/{Basic,Local,Leibniz}`, `Analysis/Extremum.lean` and
`Analysis/Convex/LegendreVariation/{Attainment,Perturbation,Derivative}`. Every move preserved
authored public declaration names and namespaces, with compiler-private ownership prefixes paired
explicitly. Old module paths have no forwarding files: the
[generated module directory](../formalization/MODULES.md) lists current paths, and each
reorganization must provide an old-to-new path map so old references remain resolvable.

Existing directories based on namespace or domain rather than family are exceptions to rule 5
and remain unchanged: `Poincare/Euclidean/`, `Poincare/FiniteProduct/`, `Poincare/LipschitzGradient/`.

**Per-paper folders (owner decision 2026-10-07, amendment to rule 5).** Constructions that only
make sense for one paper's proof — its iterates, its numbered lemmas stated for those objects, its
main-theorem assembly and witnesses — live in a per-paper library folder under `KLS/` (currently
`KLS/BKL/` and `KLS/CEK/`), and that paper's audit clients and route statements in `research/audits/<Paper>/`
(currently `research/audits/BKL/` and `research/audits/CEK/`, with the paper prefix dropped from filenames). Generic tools
used by a paper (Bochner, tilts, tensors, semigroups, summation lemmas, the heat-model generator)
stay in their object families, and an object-family module must never import a per-paper module.
Folders for other papers (Letwin, Song–Zhang) are created only with their first module. File moves
keep namespaces.

Directories group files without changing mathematical identity. Pure file moves preserve every
existing namespace, including `FunctionalInequalities.Analysis` and its object subnamespaces;
do not flatten them or rename solely because a directory changes. Namespace/public-name changes
are separate API migrations with their own maps and validation. Directory reorganization still
requires import, evidence-path, Blueprint-link, and verification-snapshot checks.

For example, write `theorem apply_eq_norm_gradient` inside `Energy.LocalSlope`. Log-concave
proofs can still call `hμ.intrinsicCovariance_closedQuadratic`,
`hμ.intrinsicSmooth_constant_eq_localSlope`, and `hμ.intrinsicWeightedOperator m B`;
`weighted` retains the meaning of an arbitrary external weight B.

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
with an explicit old/new name map. Parameter order and mathematical scope are preserved.

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

Generic resolvent, Yosida
and weighted-operator helpers retain their own object identities. Name length or the absence of
an external library consumer alone is not grounds for renaming or privatizing a mathematical lemma.

The 2026-10-12 filename review registers `Analysis/Operator/{Coordinates,Positive,InverseSqrt}` and `KLS/BKL/Suspension/{Basic,Law,Density,Moments,Cumulant,Derivatives}` as actual object families. `LocalThirdCumulant` retains its positive-radius distinction.

The 2026-10-17 filename review groups
`Analysis/Mollification/`, `KLS/LogConcave/Regular/` and
`Analysis/BakryEmery/IntegrationByParts/InverseHessian/` without renaming declarations.
The [complete filename directory](../formalization/MODULES.md) is generated from current sources.

The BKL responsibility review separates
`CumulantEnergy/`, `Posterior/` and the localization `Process/`, `Energy/`, `CutoffEnergy/`
and `Lyapunov/` families. `Theorem41.lean` retains the source-theorem entry and the conditional shared producers;
`CumulantBound.lean` holds the closed cutoff and cumulant producers, and `Poincare.lean` owns the final assembly. The generic cumulant moment estimate and diffusion
product rule live in their Analysis and Probability owners. Existing namespaces and public names
remain unchanged across the one-to-many file splits.

The cutoff and weak-derivative layout
places generic smooth/Lipschitz cutoffs in `Analysis/Cutoff/` and separates weak-derivative
foundations, mollification, approximation and calculus. Shared private product/testing supports
remain together. Existing public namespaces and names are preserved.

The generic Hessian owner review places the
existing matrix abbreviation in `Analysis/Operator/Coordinates.lean`, the coordinate Hessian
and C2 identities in `Analysis/BakryEmery/HessianOperator.lean`, and weak/C1 identification in
`Analysis/BakryEmery/WeakHessian.lean`. Qualified public names and exact definitions remain
unchanged; genuine kernel and pushforward adapters stay in `Probability/Stein/HessianKernel.lean`.

The trace/proximal responsibility review
separates `Analysis/Matrix/Trace/{Algebra,Power,Energy}.lean` and adds the substantive
`Analysis/Convex/Proximal.lean` sibling. Existing declaration names and assumptions are preserved;
the subgradient expansion stays with its actual Subgradient owner.
