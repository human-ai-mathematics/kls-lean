# Affine covariance relaxation is a closed covariance form: statement, semantic alignment, and proof

Date: 2026-09-08 (Asia/Shanghai). Base: uncommitted working tree on top of `575c82c`, immediately following
[Covariance core closure record](2026-09-08-covariance-core-closure.md). Lean/Mathlib is v4.33.0,
Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: "Proceed in this direction and in this style, but do not commit". This decision does not include commit, push, remote CI, or release.

## Node Selection

After `lem:covariance-core-closure` certification, all `\uses`
premises of `thm:affine-covariance-relaxation-closed` have been certified, becoming the only unblocked `inspect_infrastructure` leaf node in atlas, and it is a premise for
`lem:affine-poincare-translation-invariance`, `thm:affine-isotropic-reduction`, and
`thm:cmh-recovery-affine-poincare-bound`.

## Statement Design

Blueprint: For each log-concave law μ on a finite-dimensional Euclidean space, P^aff_μ is quadratic, densely realized, and closable; its sequence relaxation is a closed quadratic form and equals the original covariance energy on each global Lipschitz test; changing the affine origin translates ν, the pullback along translation preserves both variance and covariance energy in L² isometry; under this isometry, 𝓔^aff_μ is the closed covariance form used by CMH sources, and C_P^aff(μ) is the same optimal constant.

Lean is divided into four parts.

| module | declaration | content |
| --- | --- | --- |
| [Probability/CovarianceSqrt.lean](../../formalization/FunctionalInequalities/Probability/CovarianceSqrt.lean) | `exists_norm_sq_eq_inner_of_isSymmetric`, `Covariance.exists_sqrt μ` | For a finite-dimensional symmetric nonnegative operator T, there exists B with ⟪Tv,v⟫ = ‖Bv‖² (square root of the spectral theorem basis); the covariance operator is such a T, the zero operator and zero-dimensional when second moments are absent |
| [Energy/Relaxation/LinearPMap.lean](../../formalization/FunctionalInequalities/Energy/Relaxation/LinearPMap.lean) | `PreEnergy.normSqEnergy S`, `sequentialRelaxation_ofLinearPMap_eq_normSqEnergy` | The energy of a partially defined operator ‖S x‖² (outside the domain is ⊤); the relaxation of a closable T equals the energy of its closure |
| [Energy/Euclidean/CovarianceGradient/Translation.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Translation.lean) | `translateLaw ν c`, `translateL2 ν c`, `L2.variance_translateL2`, `Covariance.operator_translateLaw`, `CovarianceGradientTest.translate`, `covarianceRelaxation_translateLaw`, `Poincare.L2Energy.constant_covarianceRelaxation_translateLaw` | ν along the image of x ↦ c + x; pullback L² isometric equivalence; variance invariant; covariance operator invariant; test under translation corresponds and energy is equal; relaxation under isometry pullback; optimal constants are equal |
| [Poincare/L2Energy.lean](../../formalization/FunctionalInequalities/Poincare/L2Energy.lean) | `L2Energy.constant_eq_of_linearIsometryEquiv` | General: under L² isometric equivalence preserving variance and exchanging energy, optimal constants are equal |
| [Energy/Euclidean/CovarianceGradient/Core.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Core.lean) | `constantSmoothCore ν`, `constantSmoothCore_le_domain_gradientOperator` | The L² class formed by ℝ + C_c^∞(V) constitutes a submodule contained in the operator domain |
| [KLS/LogConcave/AffineClosedForm.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/AffineClosedForm.lean) | `exists_intrinsic_covariance_sqrt μ`, `hμ.affine_denseRealization`, `hμ.affine_closedQuadratic`, `hμ.affine_agreesOnTests`, `hμ.affine_isSequentialCoreFor`, `hμ.affine_respectsAmbientFibers` | Square root of intrinsic covariance B; P^aff has dense realization; `Energy.Affine.energy μ` is `ClosedQuadratic`; relaxation on test equals original energy, test being a sequential core |
| | `Energy.Affine.energy_translateLaw μ c`, `Poincare.Affine.constant_translateLaw μ c` | The covariance relaxation after translation of intrinsic law equals the affine relaxation pulled back along isometry; the affine constant equals the optimal constant of any translated law (without requiring log-concavity) |
| | `hμ.affine_energy_eq_normSqEnergy m B hB`, `hμ.affine_constant_eq_normSqEnergy m B hB` | Affine relaxation equals the squared-norm energy of the closure of B∇ restricted to the ℝ + C_c^∞ core (the CMH closed form); C_P^aff is the optimal constant of this closed form |

Certificate `Solutions.ThmAffineCovarianceRelaxationClosed.certificate`: For any log-concave μ, the certificate packages dense realization,
closed quadratic form, sequential core, and for each c ∈ V, four translation conclusions (covariance operator invariant, variance invariant, relaxation pullback, constant equality),
and there exists a square root B such that B∇ is closable, affine relaxation equals closed form obtained from the core, and affine constant equals its optimal constant. Two `example`:
any dimension on Fin n, Fin 0 (zero constant and still closed quadratic form).

**What is claimed.** All statements and certificates in the table above. **What is not claimed.** No Poincaré inequality or finite constant; no claim that μ under translation in ambient space E preserves C_P^aff (`lem:affine-poincare-translation-invariance`, next node);
no claim of isotropic reduction, whitening, or KLS; no claim of B symmetry or uniqueness; no making `CovarianceGradientTest` a Lean module (quadraticity expressed via operator representation). **Finiteness scope and dimension zero.** Space is finite-dimensional; tested globally Lipschitz; in zero dimension B = 0, all classes are constants, zero constant.

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| P^aff_μ quadratic | via B: P^aff and quadratic pre-energy `ofLinearPMap (B∇)` have the same realization and energy (`affine_energy_eq`, `isGradientTest_iff_exists_covarianceGradientTest`) | Consistent; different expression, recorded |
| Realization dense | `affine_denseRealization` | Consistent |
| Closable | `intrinsicGradientOperator_isClosable` (for B∇) | Consistent |
| Relaxation is closed quadratic form | `affine_closedQuadratic : ClosedQuadratic (Energy.Affine.energy μ)` | Consistent |
| Equal to original covariance energy on each globally Lipschitz test | `affine_agreesOnTests`, `affine_isSequentialCoreFor` | Consistent |
| Changing affine origin translates ν; pullback is L² isometry preserving variance and covariance energy | `translateL2`, `variance_translateL2`, `covarianceEnergy_translate`, `operator_translateLaw`, for any c ∈ V, any Borel law | Lean stronger (no log-concavity required), recorded |
| Under this identification, 𝓔^aff_μ is the CMH closed covariance form | `affine_energy_eq_normSqEnergy`: equal to the norm squared energy of B∇ on `constantSmoothCore` (ℝ + C_c^∞ class); `energy_translateLaw` gives the pullback under translation | Consistent; the "restriction to K_ν" from CMH source is automatically realized by L² class modulo ν |
| C_P^aff(μ) is the same optimal constant | `affine_constant_eq_normSqEnergy`, `constant_translateLaw` | Consistent |
| Final sentence: in zero dimension only constant classes, energy zero | Certificate `Fin 0` example: constant zero; `domain_gradientOperator_eq_top_of_subsingleton` | Consistent |

No weakening of Lean statements relative to Blueprint was found. The five premises of Blueprint `\uses` are all actually used in Lean: definition node's
`covariancePreEnergy`; Borell representation (via CovarianceClosure's local domination and second moment);
`lem:ambient-intrinsic-covariance` not directly invoked—Σ = Cov_ν is directly taken from `Covariance.operator (intrinsicMeasure μ)`,
no need for relationship with ambient covariance; `thm:quadratic-relaxation-closed` (`closedQuadratic_sequentialRelaxation`);
`lem:covariance-core-closure`.

## Proof path

- Square root: e is an orthogonal basis of eigenvectors of T, λ is an eigenvalue; λᵢ = ⟨T eᵢ, eᵢ⟩ ≥ 0; B v = ∑ √λᵢ ⟨eᵢ,v⟩ eᵢ; ‖Bv‖² = ∑ λᵢ⟨eᵢ,v⟩² = ⟨Tv,v⟫ ( `sum_repr'`, `apply_eigenvectorBasis`, `inner_right_fintype` ).
- Closed quadratic form: `affine_energy_eq` rewrites affine relaxation as `ofLinearPMap` relaxation, `ofLinearPMap_quadratic` is dense over the domain to `closedQuadratic_sequentialRelaxation`.
- Sequential core: `sequentialRelaxation_ofLinearPMap_toAmbient` gives ‖T [f]‖², `gradientOperator_apply` and `coe_covarianceEnergy_eq_norm_sq` are transformed into covariance energy; `SequentiallyGenerates` defines `rfl`.
- Translation: `measurePreserving_translate(_symm)`, `compMeasurePreservingₗᵢ`, and `AEEqFun.compMeasurePreserving_congr` give isometric equivalence; `variance_fun_comp` gives variance; `covarianceBilin_map_const_add` gives operator; `fderiv_comp_add_left` gives gradient translation; `sequentialRelaxation_comp_le` gives relaxation pullback in two directions; constants pass through `constant_eq_of_linearIsometryEquiv`.
- Closed form: `sequentialRelaxation_ofLinearPMap_eq_normSqEnergy` equals the closure of the core restriction `closure_domRestrict_intrinsicGradientOperator` (core between smoothCore and the domain).

## Metadata Synchronization

- ledger adds `thm:affine-covariance-relaxation-closed` (proved / lean, `kind: lemma` according to repository inheritance rules), fifteen proved nodes; `check_blueprint.CERTIFICATES` adds a mapping; lakefile `Solutions` root adds a certificate module.
- Blueprint theorem block anchors seventeen statements and certificates, statements and proofs marked `leanok`; tail of block supplements Lean expression format description; "pending Lean implementation" at end of proof is replaced with certified packaged content; `\uses` remains unchanged.
- Root aggregation module imports `KLS.LogConcave.AffineClosedForm`; `Poincare/Foundation.lean` imports Translation and   CovarianceSqrt.
- tasks.json: node changed to `available` and registered with twelve source code and Mathlib hashes; hash of other tasks touching files is refreshed.
- Current guide: HANDOFF, README, `verification.md`, `solutions/README.md`, `blueprint/README.md`, `Energy/README.md`, `KLS/LogConcave/README.md`, `naming.md`. statement golden, `STATEMENT_CHECKS`, route configuration unchanged.

## Evidence Boundary

`lake build` passed, certificate and ten library-level assertions have standard axiom guards. Final verification receipt generated by `python3 research/verify.py` after this record and all guide edits, with source code SHA recorded in the receipt itself, not written back to this file. Local kernel replay trusts third-party compiled imports; no isolated rebuild, remote CI, or release performed.
