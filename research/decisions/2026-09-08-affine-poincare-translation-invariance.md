# Ambient translation invariance of affine Poincaré constants: statement, semantic alignment and proof

Date: 2026-09-08 (Asia/Shanghai). Baseline: uncommitted working tree on top of `575c82c`, followed by
[affine closed form record](2026-09-08-affine-covariance-relaxation-closed.md). Lean/Mathlib is v4.33.0,
Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: proceed with `lem:affine-poincare-translation-invariance` as per atlas, inspect first then formalize, no commit, no push.
This decision does not include commit, push, remote CI, or release.

## Node Selection

`thm:affine-covariance-relaxation-closed` certified, the atlas lists `lem:affine-poincare-translation-invariance` as a de-blocked `inspect_infrastructure` leaf node; it is a premise of `thm:affine-isotropic-reduction` and `cor:cmh-recovery-sequence-suffices`. Inspect the conclusion: Mathlib already has `covarianceBilin_map` (the adjoint formula of covariance under linear maps), `LinearIsometryEquiv.adjoint_eq_symm`, `ContinuousLinearEquiv.comp_right_fderiv` (the chain rule for composition without differentiability assumptions), `AffineSubspace.map_direction`/[`map_le_iff_le_comap`], `LinearIsometryEquiv.ofEq`; the repository already has `translateLaw`/[`translateL2`] (intrinsic laws under translation in direction space), `LogConcave.of_affineIsometry_map` and `hμ.intrinsic_memLp_id_two`. The missing pieces are three local gluing segments: linear isometry transport between direction spaces, identification of affine supports after translation with intrinsic laws, and the ambient second-order moment of log-concave laws. All can be directly implemented, so `unchecked → available` does not require a separate proof.

## Statement Design

Blueprint: Let μ be a log-concave measure on a finite-dimensional Euclidean space E, and let b ∈ E. Define τ_b(x) = x + b. Then (τ_b)#μ is log-concave and
C_P^aff((τ_b)#μ) = C_P^aff(μ); in particular, translating to the negative barycenter yields a centered measure with invariant constant.

In Lean, (τ_b)#μ takes the existing `Energy.Euclidean.translateLaw μ b` (the pushforward of μ along x ↦ b + x; `translateLaw` is defined for any finite-dimensional Hilbert space, used directly here for E). Divided into three modules, starting general and then specific.

| module | declaration | content |
| --- | --- | --- |
| [Energy/Euclidean/CovarianceGradient/Isometry.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/Isometry.lean) | `gradient_comp_linearIsometryEquiv g L x` | ∇(g ∘ L)(x) = L⁻¹ ∇g(Lx), no differentiability assumption (both sides zero at non-differentiable points) |
| | `Covariance.operator_of_not_memLp`, `Covariance.operator_map_linearIsometryEquiv`, `Covariance.operator_mapLaw`, `inner_operator_mapLaw`, `inner_operator_mapLaw_apply` | Operator is zero when second moment does not exist; the covariance operator of the law is the conjugate L Σ L⁻¹; quadratic form is read through L⁻¹/L |
| | `mapLaw ν L`, `measurePreserving_mapLaw(_symm)`, `mapForward`/`mapBackward`, `mapL2 ν L`, `L2.variance_mapL2` | Image law under linear isometry equivalence L; pullback along L of L² isometric equivalence; invariant variance |
| | `CovarianceGradientTest.compLinearIsometryEquiv hmp hcov g`, `covarianceEnergy_compLinearIsometryEquiv`, `toL2_compLinearIsometryEquiv` | Test under composite correspondence, equal covariance energy, realized as pullback class |
| | `covarianceRelaxation_mapLaw`, `Poincare.L2Energy.constant_covarianceRelaxation_mapLaw` | Covariance relaxation pulled back along `mapL2`; optimal constants are equal |
| [Poincare/Euclidean/AffineTranslation.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/AffineTranslation.lean) | `Probability.coe_intrinsicMap_of_mem`, `affineSupport_translateLaw`, `direction_affineSupport_translateLaw` | affine support of the translation law is `(affineSupport μ).map (constVAdd b)`; directional submodule equality |
| | `Probability.translateDirectionEquiv μ b`, `translateShift μ b`, `intrinsicMap_translateLaw`, `intrinsicMeasure_translateLaw` | The `ofEq` linear isometry between the two direction submodules; coordinate shift b + supportPoint μ − supportPoint μ'; identification of the intrinsic law ν' = translateLaw (mapLaw ν L) c |
| | `Energy.Euclidean.integral_id_translateLaw`, `integral_id_translateLaw_neg_integral` | Center of translation law = c + center of mass; after translation to the negative center of mass, the mean becomes zero (premise `Integrable id`) |
| | `Energy.Affine.exists_translateLaw_isometry μ b` | There exists L²(ν') ≃ₗᵢ L²(ν) preserving variance and commuting with two affine relaxations |
| | `Poincare.Affine.constant_translateLaw_ambient μ b` | `Poincare.Affine.constant (translateLaw μ b) = Poincare.Affine.constant μ`, for any Borel law |
| [KLS/LogConcave/AffineTranslation.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/AffineTranslation.lean) | `hμ.translateLaw b` | Translation invariance of log-concave (inverse translation is affine isometry, `of_affineIsometry_map`) |
| | `hμ.memLp_id_two`, `hμ.integrable_id` | Environment second-moment: intrinsic second-moment + `reconstruct` as norm bound under affine isometries; centroid exists |
| | `hμ.integral_id_translateLaw_neg_integral` | has zero mean after translation to the negative barycenter |

Certificate `Solutions.LemAffinePoincareTranslationInvariance.certificate`: For any log-concave μ-pack, for each b: translation law is log-concave, environment covariance operator is invariant (already `Covariance.operator_translateLaw`), affine support direction is invariant, there exists a variance-preserving and exchangeable under two affine relaxations L² isometry equivalence, constants are equal; additionally `MemLp id 2 μ` and zero mean under negative barycenter translation. Two `example`: `Fin n` translated to negative barycenter preserves log-concavity, zero mean, and constant; `Fin 0` has both constants zero and translation law is log-concave.

**What is claimed.** All statements and certificates above. **What is not claimed.** No Poincaré inequality or finite constant; no isotropic reduction or whitening (`thm:affine-isotropic-reduction`); no invariance under non-translational affine mappings on E (intrinsic linear isometries are general, but ambient level only supports/identifies translation); does not make `exists_translateLaw_isometry`'s isometry into a named `def` (it is a combination resulting from rewriting `translateL2 ∘ mapL2` via intrinsic law `intrinsicMeasure_translateLaw`, expressed with ∃ to avoid type conversion along measure equality).

**Finiteness scope and dimension zero.** Finite-dimensional space; global Lipschitz test; zero-dimensional direction space is included in each conclusion (in this case, `mapLaw` and `translateLaw` L² are constant classes, both constants zero).

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| μ is log-concave | constant equality, covariance invariance, direction invariance, and L² isometry for any Borel law holds; log-concavity is used only for log-concavity of translation law and barycenter existence | Lean is stronger (weaker premise), recorded |
| τ_b(x) = x + b | `translateLaw μ b` is the image of x ↦ b + x (additive commutativity, same mapping) | consistent |
| (τ_b)#μ is log-concave | `hμ.translateLaw b`; proof uses inverse translation (affine isometry) to bring the translation law back to μ, compact set image as test set | consistent; Blueprint statement "compact sets and Minkowski sums commute with translation" is carried in Lean by the general affine isometry version `of_affineIsometry_map` |
| C_P^aff((τ_b)#μ) = C_P^aff(μ) | `Poincare.Affine.constant_translateLaw_ambient` | consistent |
| Statement "translation preserves covariance" | Environment: `Covariance.operator_translateLaw`; Intrinsic: `Covariance.operator_mapLaw` (conjugate L Σ L⁻¹, L being `ofEq`, value-wise identity) and `Covariance.operator_translateLaw` | consistent |
| Statement "identify two intrinsic laws via L² isometry" | `intrinsicMeasure_translateLaw` gives ν' = translateLaw (mapLaw ν L) c; isometry is `(translateL2 _ c).trans (mapL2 ν L)`; `exists_translateLaw_isometry` | consistent |
| Statement "isometry preserves variance and exchanges covariance pre-energy, hence exchanges relaxations and optimal constants" | `L2.variance_mapL2`/`variance_translateL2`; test corresponds to `compLinearIsometryEquiv`/`translate`; `covarianceRelaxation_mapLaw`/`_translateLaw`; `constant_covarianceRelaxation_mapLaw`/`_translateLaw` | consistent |
| In particular, translation to negative barycenter yields centralized law | `hμ.memLp_id_two` gives barycenter existence; `hμ.integral_id_translateLaw_neg_integral` gives ∫ x d(τ_{−m}#μ) = 0 | consistent; "centralization" takes the same form `KLS.Isotropic.mean_zero` ∫ x dμ = 0 |
| Barycenter existence given by `thm:borell-logconcave-density` | via `hμ.intrinsic_memLp_id_two` (Borell moment theorem) and `reconstruct`'s affine isometry norm bound passed to ambient law | consistent |
| Zero-dimensional | Certificate `Fin 0` example: both constants are zero | consistent |

No weaknesses of Lean were found compared to Blueprint. The four premises of Blueprint `\uses` are all actually used in Lean: `def:log-concave-law`
(`LogConcave`), `def:affine-poincare-constant` (`Poincare.Affine.constant`), `thm:borell-logconcave-density`
(with intrinsic second moment), `thm:affine-covariance-relaxation-closed` (its Translation module's `translateL2`, `covarianceRelaxation_translateLaw`, `constant_covarianceRelaxation_translateLaw`).

## Proof Path

- **Gradient Composition.** `toDual` is injective; `ContinuousLinearEquiv.comp_right_fderiv` gives fderiv (g∘L) x = fderiv g (Lx) ∘ L;
  for each v, ⟪∇g(Lx), Lv⟫ = ⟪L L⁻¹∇g(Lx), Lv⟫ = ⟪L⁻¹∇g(Lx), v⟫ (`inner_map_map`).
- **Covariance Conjugate.** With second moment: `covarianceBilin_map` + `adjoint_eq_symm` + `inner_map_map`; without second moment: the law also has no second moment (`memLp_map_measure_iff` composed with L⁻¹), both sides operators vanish (`covarianceBilin_of_not_memLp`).
- **L² Isometry and Relaxation.** Parallel to the Translation module entry by entry: `compMeasurePreservingₗᵢ` along L and L⁻¹, `compMeasurePreserving_comp_apply` and `AEEqFun.compMeasurePreserving_congr` provide inverses; `variance_fun_comp` provides variance; `sequentialRelaxation_comp_le` provides relaxation pullbacks in both directions; `constant_eq_of_linearIsometryEquiv` provides a constant.
- **Affine Support.** ≤: translation law a.e. falls into `map (constVAdd b)` (`ae_map_iff`), and the image is closed; ≥: `map_le_iff_le_comap`, μ a.e. a point translated lands in the affine support of μ' (`ae_of_ae_map`), and comap is closed. Direction: `map_direction` and `constVAdd` have identity as linear parts.
- **Intrinsic Law Recognition.** On the support, `intrinsicMap μ x = x − supportPoint μ` (`coordinateEquiv` is the inverse of `vaddConst`); intrinsicMap μ' (b + x) = (b + supportPoint μ − supportPoint μ') + (x − supportPoint μ) (`abel`); `ProbabilityMeasure.toMeasure_injective` + `Measure.map_map` + `Measure.map_congr` (a.e. on affine support).
- **Constant.** Expand `Poincare.Affine.constant`, `rw [intrinsicMeasure_translateLaw]` (motive is type-correct under `covarianceRelaxation ν'` form), then use `constant_covarianceRelaxation_translateLaw` and `constant_covarianceRelaxation_mapLaw`.
- **Ambient Second Moment.** ‖reconstruct v‖ ≤ ‖reconstruct 0‖ + ‖v‖ (`AffineIsometry.dist_map`), `MemLp.of_le` under intrinsic law, `memLp_map_measure_iff` pulls back μ, `reconstruct_intrinsicMap_ae` is replaced by identity.
- **Centroid.** `integral_map` and `integral_add`, `integral_const` (probability measure `probReal_univ`).

Pitfalls: the lemma for the value of `LinearIsometryEquiv.ofEq` should not be proved using `rfl` (kernel timeout); use Mathlib's `coe_ofEq_apply`; `closed_of_finiteDimensional` requires explicit specification of a subspace, otherwise instance problems get stuck due to metavariables; in example `Fin n`, `Measure _` must be fully typed, otherwise the integral variable is inferred as ℕ; in `have`, `∀ (W : Type*)` would freeze the universe; instead, use the top-level general lemma `Covariance.operator_of_not_memLp`.

## Metadata Synchronization

- ledger adds `lem:affine-poincare-translation-invariance` (proved / lean, `kind: lemma`), sixteen proved nodes;
  `check_blueprint.CERTIFICATES` adds a mapping; lakefile `Solutions` root adds a certificate module.
- Blueprint lemma block anchors sixteen statements and certificates, statements and proofs marked `leanok`; tail supplements the expression of (τ_b)#μ in Lean, intrinsic law identification, and the note "constant equality holds for any Borel law"; `\uses` remains unchanged.
- Root aggregation module imports `KLS.LogConcave.AffineTranslation`; `Poincare/Foundation.lean` imports `CovarianceGradient.Isometry` and `Poincare.Euclidean.AffineTranslation` and updates key documentation points.
- tasks.json: node changed to `available`, registers three new modules, `Translation.lean`, `Transport.lean`, `AffineSupport.lean`, `KLS/LogConcave/AffineCovariance.lean`, and Mathlib `FDeriv/Equiv`, `InnerProductSpace/Adjoint`, `CovarianceBilin`, `AffineSubspace/Basic`, `LinearIsometry` hashes; no changes were made to the evidence files of other tasks, all hash scans match.
- Current guide: HANDOFF, README, `verification.md`, `solutions/README.md`, `formalization/README.md`, `blueprint/README.md`, `Energy/README.md`, `KLS/README.md`, `KLS/LogConcave/README.md`, `Poincare/README.md`, `Poincare/Euclidean/README.md`, `naming.md` (adds two rows: "linear isometric transport" and "environment translation", and distinguishes between `_translateLaw` and `_translateLaw_ambient` suffixes). Statement golden, `STATEMENT_CHECKS`, route configuration unchanged.

## Evidence Boundary

`lake build` passes (via 3344 jobs), with twelve library-level statements guarded by standard axioms. Final verification receipt generated by `python3 research/verify.py` after all edits to this record and all guides, with the source code SHA recorded in the receipt itself, not written back to this file. Local kernel replay trusts third-party compiled imports; no isolated rebuilds, remote CI, or releases performed.
