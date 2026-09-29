# Affine Covariance Poincaré Constant: Definition-Node Implementation, Semantic Alignment, and Contract Proofs

Date: 2026-09-07 (Asia/Shanghai). Baseline: uncommitted worktree atop `575c82c`, immediately following
[Ambient/Intrinsic Covariance Record](2026-09-07-ambient-intrinsic-covariance.md). Lean/Mathlib is v4.33.0,
Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: complete `def:affine-poincare-constant` as per atlas `formalize`, which defines the node, making no claims about closedness, Markov property, or any Poincaré conclusion.
This decision does not perform commit, push, remote CI, or release.

## Node Selection

After atlas `lem:ambient-intrinsic-covariance` certification, `def:affine-poincare-constant` is listed as the sole
`verify_prerequisites` definition task: all of its `\uses` premises are either Lean-certified or implemented. It serves as a common premise for
`thm:affine-covariance-relaxation-closed`, `lem:affine-poincare-translation-invariance`,
`thm:affine-isotropic-reduction`, and two CMH route node premises.

## Statement Design

Three new modules, with type variables restricted to finite-dimensional, complete real inner product spaces, Borel, second countable.

| Module | Declaration | Content |
| --- | --- | --- |
| [Energy/Euclidean/CovarianceGradient/Basic.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Basic.lean) | `Energy.Euclidean.covarianceGradientDensity ν g x` | `⟪Σ ∇g x, ∇g x⟫`, `Σ = Covariance.operator ν`, `∇` are Mathlib's canonical Hilbert gradient (zero at non-differentiable points); pointwise non-negative |
| | `Energy.Euclidean.CovarianceGradientTest ν` | Structure: `∃ K, LipschitzWith K g`, `MemLp g 2 ν`, `Integrable (covarianceGradientDensity ν g) ν` |
| | `CovarianceGradientTest.covarianceEnergy`, `toL2` | `NNReal` energy `∫⟪Σ∇g,∇g⟫dν` and `L²(ν)` class |
| | `Energy.Euclidean.covariancePreEnergy ν`, `covarianceRelaxation ν` | `PreEnergy (Lp ℝ 2 ν)` and its `sequentialRelaxation` |
| | `Energy.Affine.preEnergy μ`, `Energy.Affine.energy μ` | Instance on `ν = intrinsicMeasure μ`: `P^aff_μ`, `𝓔^aff_μ` |
| | `gradient_ae_eq_of_ae_eq`, `CovarianceGradientTest.covarianceEnergy_eq_of_toL2_eq` | General premise version: when the boundary of the support has zero `ν`-measure, a.e.-equal continuous representatives have equal gradients a.e.; energy depends only on `L²` class |
| | `CovarianceGradientTest.ae_hasGradientAt` | General premise version: when `ν ≪ Haar` holds, test a.e. differentiable and `gradient` is its derivative (via `LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz`) |
| [Poincare/Euclidean/AffineCovariance.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/AffineCovariance.lean) | `Poincare.Affine.constant μ`, `Poincare.Affine.Holds μ C`, `holds_iff_constant_le` | `C_P^aff(μ) = L2Energy.constant ν (Energy.Affine.energy μ)` and finite constants are order equivalent |
| | `constant_eq_zero_of_subsingleton`, `constant_eq_zero_of_direction_eq_bot` | Zero-dimensional direction gives constant zero |
| [KLS/LogConcave/AffineCovariance.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/AffineCovariance.lean) | `hμ.intrinsic_memLp_id_two` | Intrinsic law has second moment, `Σ` is the actual covariance rather than Mathlib's zero convention |
| | `hμ.intrinsic_ae_hasGradientAt f` | Rademacher: each test `ν`-a.e. differentiable, `gradient` is the derivative |
| | `hμ.intrinsic_gradient_ae_eq_of_ae_eq`, `hμ.intrinsic_covarianceEnergy_eq_of_toL2_eq` | Representative independence: continuous representatives of the same `L²(ν)` class have equal gradients a.e. equal energy |

Two general lemmas are placed separately: `L2.variance_eq_zero_of_subsingleton` (`L2/MeanVariance.lean`) and
`Poincare.L2Energy.constant_eq_zero_of_subsingleton` (`Poincare/L2Energy.lean`): the optimal constant for any energy on a single-point carrier is zero. They are not included in the `Affine` namespace.

**What is claimed.** All declarations in the above table; defined for any Borel probability law; log-concave laws satisfy three well-defined contracts; zero-dimensional constants are zero; five StatementChecks type checks (expansion, test domain field, energy integral without 1/2 factor, `Fin 0`, `ℝ` Dirac laws).

**What is not claimed.** No claim is made about density of the realization of `P^aff_μ`, quadraticity, closedness, lower semicontinuity of relaxation, the Markov property, consistency between relaxed and raw energy on tests, translation invariance, comparison with `Poincare.Canonical.constant` or `KLS.literatureConstant`, finiteness of constants, or any KLS bound. These are independent nodes in the Blueprint.

**Finiteness scope and dimension zero.** Space is finite-dimensional; test is globally Lipschitz (not locally Lipschitz); when no second moment, Mathlib convention `Covariance.operator ν = 0` applies, energy is identically zero, this convention only arises in non-log-concave laws. Zero-dimensional direction space is included in each declaration: tests are constants, energy is zero, constant is zero; likewise for Dirac law on `ℝ`.

## Semantic Alignment

| Blueprint Clause | Lean | Conclusion |
| --- | --- | --- |
| μ is a log-concave probability law on a finite-dimensional Euclidean space | Defined for any `ProbabilityMeasure E`; log-concavity used only in the contract | Lean is stronger (weaker premise), recorded |
| ν is an intrinsic law on the affine support direction space V | `Probability.intrinsicMeasure μ` on `(affineSupport μ).direction` | Consistent |
| Σ = Cov_{μ,V} = Cov_ν | `Covariance.operator (intrinsicMeasure μ)`, i.e., Cov_ν; equivalence to restriction of Cov_{μ,V} is already proven `operator_coe_intrinsic`, not restated; log-concavity ensures `intrinsic_memLp_id_two` it is the true covariance | Consistent |
| Test: globally Lipschitz, g ∈ L²(ν), ∫⟨Σ∇g,∇g⟩dν < ∞ | Three structure fields; finiteness written as `Integrable`, integrand uses canonical gradient defined everywhere | Consistent; under log-concavity, integrand a.e. equals classical gradient expression |
| Implementation in L²(ν) class | `toL2` | Consistent |
| Energy is this integral | `covarianceEnergy`, `NNReal`, no 1/2 factor | Consistent |
| Borel absolute continuity and Rademacher ensure gradient ν-a.e. well-defined | `intrinsic_ae_hasGradientAt` (existence) and `intrinsic_covarianceEnergy_eq_of_toL2_eq` (representative independence); proof uses only `intrinsic_absolutelyContinuous` and `intrinsic_frontier_support` | Lean is stronger (also provides representative independence), recorded |
| 𝓔^aff_μ := (P^aff_μ).sequentialRelaxation | `Energy.Affine.energy μ`, `rfl` expanded | Consistent |
| C_P^aff(μ) := C_P(ν, 𝓔^aff_μ) | `Poincare.Affine.constant μ = L2Energy.constant ν (energy μ)`, `rfl` expanded | Consistent |
| Zero-dimensional constants are zero | `constant_eq_zero_of_direction_eq_bot`; general lemmas hold for any energy | Consistent (Lean is more general) |

No weakening of Lean statements relative to Blueprint was found. `Poincare.Affine.Holds` and `holds_iff_constant_le` are interfaces not listed in Blueprint, following the pattern of the constants `Canonical`/`Ambient`. The `\uses` `thm:borell-logconcave-density` in Blueprint `intrinsic_integrable_norm_pow` is indeed used in Lean: second-moment contracts invoke its moment conclusion a.e. the independence from representatives only relies on its absolute continuity.

## Proof Path

- Non-negativity: `Covariance.operator_inner` reduces to `covarianceBilin ν v v`, Mathlib `covarianceBilin_self_nonneg` (zero when second moment is absent, still non-negative).
- Rademacher: Global Lipschitz implies local Lipschitz, the repository interface provides Haar-a.e. differentiability, `ν ≪ Haar` passes to `ν`-a.e, `DifferentiableAt.hasGradientAt` gives the derivative.
- Independence from representatives: continuous functions a.e. equality implies equality on `ν.support` (the set of inequality is an open zero-measure set, `subset_compl_support_of_isOpen`); `ν`-a.e. a point lies in the support and not on the boundary (`support_mem_ae`, boundary has zero measure), a closed set minus its boundary is its interior (`IsClosed.frontier_eq`), so the two functions are equal in a neighborhood of that point, `Filter.EventuallyEq.fderiv_eq` gives `fderiv` equality, `gradient` follows; `integral_congr_ae` gives equal energy.
- Second moment: `memLp_two_iff_integrable_sq_norm` plus the already proven integrable second moment.
- Zero-dimensional: a probability measure gives a non-empty carrier, any `L²` element equals its constant value at a single point (`Lp.ext`), `variance_const`; `TestFamily.constant_eq_zero_of_variance_zero`; direction `= ⊥` is reduced via `Submodule.subsingleton_iff_eq_bot` to a single point.

## Metadata Synchronization

- Blueprint defines a block anchoring twelve declarations and marking `leanok`, the block end supplements the Lean implementation scope and non-asserted explanations; `\uses` remains unchanged. Definition nodes are not entered into ledger, `check_blueprint.CERTIFICATES` remains unchanged.
- `solutions/StatementChecks.lean` adds five named checks (`affine_constant_unfold`, `affine_test_fields`, `affine_energy_integral`, `zero_dimension_affine_constant`, `ambient_dirac_affine_constant`), adds standard axiom guards; additionally, four log-concave contracts and zero-dimensional theorems get guards. The `verify.py` `STATEMENT_CHECKS` is synchronized to twenty-five items.
- tasks.json: the note at this node is rewritten, adding `available` infrastructure records (three new modules, `LipschitzApproximation.lean`, `AbsoluteContinuity.lean`, and Mathlib `Rademacher`, `Gradient/Basic`, `CovarianceBilin`, `Support` hashes); the hashes of `StatementChecks.lean` and `L2/MeanVariance.lean` touched by this edit are refreshed in the hash records of two other task entries.
- Aggregation module: `Poincare/Foundation.lean` imports two new Energy/Poincare modules, the root module imports the log-concave contract module, and corrects the outdated description in the root module documentation: "Borell representation still contains sorry".
- Current guide sync: HANDOFF, README, `verification.md`, `solutions/README.md`, `formalization/README.md`, `KLS/README.md`, `KLS/LogConcave/README.md`, `Energy/README.md`, `Poincare/README.md`, `Poincare/Euclidean/README.md`, `naming.md`, `blueprint/README.md`. Statement golden and route configuration remain unchanged.

## Evidence Boundary

`lake build` passes, no new warnings. Final verification receipt is generated by `python3 research/verify.py` after this record and all guide edits, with its source code SHA recorded in the receipt itself, not written back to this file. Local kernel replay trusts third-party compiled imports; no isolated rebuild, remote CI, or release performed.
