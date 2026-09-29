# Affine and Isotropic KLS Representations: Equivalence via Inspection, Statement, Semantic Alignment, and Proof

Date: 2026-09-08 (Asia/Shanghai). Baseline: uncommitted working tree on top of `575c82c`, followed by
[translation invariance record](2026-09-08-affine-poincare-translation-invariance.md). Lean/Mathlib is v4.33.0,
Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: proceed to atlas ready after completing translation invariance,
each node to be inspected before formalized, no commit, no push. This decision does not include commit, push, remote CI, or release.

## Inspection of two candidate nodes

After certification of translation invariance, atlas lists two theorems lifting the blockage `inspect_infrastructure`:

- `thm:cmh-recovery-affine-poincare-bound`: Package two upstream agent review results (`lem:affine-poincare-w2-liminf`, `thm:cmh-implies-affine-poincare`). Locally available are only `Poincare.Affine.constant`, its closed form and translation invariance; neither the repository nor the fixed Mathlib contains the definition of quadratic Wasserstein distance and its convergence, CMH constants (including regular compact target moment mapping classes, canonical moment mapping kernels, and weak zero-flux closed Stein generator conventions) in Lean. Neither of the two upstream results provides a local proof. tasks.json is recorded as `missing`, listing these four specific gaps; no formalization is performed.
- `thm:affine-isotropic-reduction`: Blueprint proof is "Open." with a sketch. All required infrastructure can be fully implemented locally: transport under general continuous linear equivalence with covariance relaxation (non-isometric generalization of the isometry module), inverse square root of positive definite covariance (via spectral theorem, same method as `CovarianceSqrt`), bridge between unit-weight Lipschitz gradient relaxation constants and literature constants (replacing the smooth approximation argument in `LiteratureComparison` with Lipschitz testing), and relaxation comparison with constant factors. Mathlib already has `covarianceBilin_map`, `ContinuousLinearEquiv.comp_right_fderiv`, `LinearEquiv.ofInjectiveEndo`, `Monotone.map_liminf_of_continuousAt`, `ENNReal.mul_iInf'`. Thus the assessment changes `unchecked → available`, and the proof is completed in the same round.

## Statement Design

Blueprint: For fixed K ≥ 0, (1) every isotropic log-concave measure ν on each finite-dimensional Euclidean space satisfies C_P^lit(ν) ≤ K; (2) every finite-dimensional log-concave measure μ satisfies C_P^lit(μ) ≤ K‖Cov_μ‖; (3) every finite-dimensional log-concave measure μ satisfies C_P^aff(μ) ≤ K; the three are equivalent, with the zero-dimensional measure included.

| module | declaration | content |
| --- | --- | --- |
| [Energy/Relaxation/Basic.lean](../../formalization/FunctionalInequalities/Energy/Relaxation/Basic.lean) | `PreEnergy.sequentialRelaxation_comp_le_mul` | Relaxation comparison along continuous maps, testing energy allows a constant factor κ; under the assumption that the relaxation of P is finite (ruling out the problematic combination of κ = 0 and an empty approximation class) |
| [Energy/Euclidean/CovarianceGradient/LinearEquiv.lean](../../formalization/FunctionalInequalities/Energy/Euclidean/CovarianceGradient/LinearEquiv.lean) | `gradient_comp_continuousLinearEquiv`, `Covariance.operator_map_continuousLinearEquiv`, `mapEquivLaw ν T`, `mapEquivL2`, `L2.variance_mapEquivL2`, `integral_id_mapEquivLaw`, `memLp_id_two_mapEquivLaw`, `CovarianceGradientTest.compContinuousLinearEquiv`, `covarianceRelaxation_mapEquivLaw`, `Poincare.L2Energy.constant_covarianceRelaxation_mapEquivLaw`, `Probability.affineSupport_mapEquivLaw(_eq_top)` | Under continuous linear equivalence T: ∇(g∘T) = T†∇g∘T; Σ_{T#ν} = TΣT†; L² pullback isometric preserving variance; centroid and second-moment transport; test correspondence, energy equality; relaxation and optimal constant invariant; affine support is the image |
| [Probability/CovarianceWhitening.lean](../../formalization/FunctionalInequalities/Probability/CovarianceWhitening.lean) | `exists_whitening_of_isSymmetric`, `Covariance.exists_whitening` | For a positive definite symmetric operator T, there exists a self-adjoint continuous linear equivalence W such that ⟪T(Wu),Wv⟫ = ⟪u,v⟫ (eigenbasis term-wise λ^{-1/2}, `ofInjectiveEndo`) |
| [Poincare/Euclidean/LipschitzComparison.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/LipschitzComparison.lean) | `lipschitzGradientRelaxation ν m hac`, `KLS.literatureEnergy_eq_ofReal_integral_sq_norm_gradient`, `L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds`, `Poincare.constant_eq_lipschitzGradientRelaxation`, `covarianceRelaxation_eq_lipschitzGradientRelaxation`, `covarianceRelaxation_le_opNorm_mul_lipschitzGradientRelaxation` | Weighted gradient operator relaxation for B = 1; its finite constant is exactly the constant in the literature, and the optimal constant equals the legacy smooth constant; when Σ = 1, the covariance relaxation is this relaxation; in general, the covariance relaxation ≤ ‖Σ‖ × this relaxation (on its finite domain) |
| [KLS/LogConcave/IsotropicReduction.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/IsotropicReduction.lean) | `LogConcave.of_continuousLinearEquiv_map`, `hν.mapEquivLaw T`, `memLp_id_two_translateLaw`, `interior_support_nonempty_of_affineSupport_eq_top` | Log-concave transport under continuous linear equivalence; translation preserves second moments; full affine support gives non-empty interior of the support |
| | `KLS.IsotropicBound K`, `KLS.CovarianceBound K`, `KLS.AffineBound K` | Three statements, each quantifying over all finite-dimensional Euclidean spaces for a fixed universe u |
| | `hμ.exists_isotropic_literatureConstant_eq`, `hμ.literatureConstant_le_opNorm_mul_affine_constant` | There exists an isotropic log-concave law ν' on the direction space such that C_P^aff(μ) = C_P^lit(ν'); C_P^aff(μ) ≤ K ⇒ C_P^lit(μ) ≤ K·ofReal‖Cov_μ‖ |
| | `affineBound_of_isotropicBound`, `covarianceBound_of_affineBound`, `isotropicBound_of_covarianceBound`, `affine_isotropic_reduction K`, `conjecture_of_affineBound` | (1)⇒(3), (3)⇒(2), (2)⇒(1); pairwise equivalences; `AffineBound.{0} K → KLS.Conjecture` |

Certificate `Solutions.ThmAffineIsotropicReduction.certificate K`: three equivalences ((1)↔(2) , (2)↔(3) , (1)↔(3)) and
`AffineBound.{0} K → Conjecture`. Two `example`s: normalization of covariance bounds from (3) on `Fin n`; both constants are zero on `Fin 0`.

**What is claimed.** The table above lists all statements and certifications. **What is not claimed.** No claim is made that any statement holds for a given K, nor that KLS holds; no claim is made regarding the reverse transitivity from the `Fin n` family to any space (`Conjecture → CovarianceBound.{0}` requires isometric `E ≃ₗᵢ EuclideanSpace` transport of literature constants and covariance norms, which was not performed); no claim is made that whitened W is unique or positive; no Cheeger, Dirichlet, or spectral gap identification is performed.
**Finiteness scope and dimension zero.** The three statements are quantified within the same universe u; the space is of finite dimension; the zero-dimensional law is included in each statement (the positive definiteness premise is vacuously true, W is arbitrary, the two constants are zero, and `‖id‖ ≤ 1` also covers `‖0‖ = 0`).

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| "Each finite-dimensional Euclidean space" | All `V : Type u` and standard instances within a fixed universe u; three statements share the same u | Consistent; fixing the universe is a restriction in Lean expressions, recorded |
| (1) Isotropic log-concave ν: C_P^lit(ν) ≤ K | `IsotropicBound K`, `Isotropic` are realizations of `def:isotropic-law` | Consistent |
| (2) C_P^lit(μ) ≤ K‖Cov_μ‖ | `literatureConstant μ ≤ K * ENNReal.ofReal ‖Covariance.operator μ‖`, same form as `KLS.Conjecture` | Consistent |
| (3) C_P^aff(μ) ≤ K | `Poincare.Affine.constant μ ≤ K` | Consistent |
| ‖Cov_μ‖ = ‖Cov_{μ,V}‖ by `lem:ambient-intrinsic-covariance` | `Covariance.opNorm_operator_intrinsic μ hμ.memLp_id_two`, second moments by `hμ.memLp_id_two` | Consistent |
| Proof sentence "By translation invariance lemma, centering does not change constants" | Centering performed in the direction space of intrinsic laws (`translateLaw ν c`, `constant_covarianceRelaxation_translateLaw`, part of `thm:affine-covariance-relaxation-closed` certification content); `lem:affine-poincare-translation-invariance` retained as `\uses` dependent but not invoked in Lean proof | Same conclusion, different route, recorded |
| "In positive dimension, whiten with Cov^{-1/2}, existence by ambient-intrinsic lemma" | `Covariance.exists_whitening` uses positive definiteness of `intrinsic_operator_inner_self_pos`; no case distinction for zero dimension | Consistent (Lean uniformly handles zero dimension) |
| "Isotropic inequalities pull back to covariance form inequalities, first raw test then relaxation" | `covarianceRelaxation_mapEquivLaw` directly transported at the relaxation level (test corresponds to + `sequentialRelaxation_comp_le` bidirectional), then via `covarianceRelaxation_eq_lipschitzGradientRelaxation` (Σ = 1) and bridge `constant_eq_lipschitzGradientRelaxation` to legacy constants, `legacy_eq_literature` to C_P^lit | Consistent |
| "(3) ⇒ (2) by ⟪Σv,v⟫ ≤ ‖Σ‖‖v‖² with truncation and tailing (local → global Lipschitz)" | Pointwise comparison + `sequentialRelaxation_comp_le_mul`; transition between local/global Lipschitz uses already certified smooth compact support approximations (`exists_smooth_weighted_L2_approximation`, `lem:covariance-test-core-density`) | Same conclusion, different method, recorded |
| "(2) specializes to (1) when covariance is identity" | `isotropicBound_of_covarianceBound`: `hiso.covariance_identity`, `norm_id_le`, `ofReal_le_one` | Consistent |
| Zero-dimensional "zero variance, directly holds" | Included in unified proof; certificate `Fin 0` example | Consistent |
| Blueprint proof tag "Open." | Changed to leanok, with additional Lean route explanation | — |

No weakening of Lean statements relative to Blueprint was found. Among the eight premises of `\uses`, `thm:borell-logconcave-density` (via intrinsic second-moment, absolute continuity, and zero-measure support boundary), `def:isotropic-law`, `def:literature-poincare-constant`, `lem:ambient-intrinsic-covariance`, `def:affine-poincare-constant`, `thm:affine-covariance-relaxation-closed` (Translation module), and `def:log-concave-law` are actually used in Lean; `lem:affine-poincare-translation-invariance` is not directly invoked as described above. Lean additionally provides `conjecture_of_affineBound`, which is not listed in Blueprint.

## Proof path

- **Linear transport.** `comp_right_fderiv` gives fderiv (g∘T) = fderiv g ∘ T, `adjoint_inner_left` gives ∇(g∘T) = T†∇g;
  `covarianceBilin_map` Given Σ_{T#ν} = TΣT† (both sides are zero when second moments are absent); L² pullback along T, T⁻¹ inverse; test composite Lipschitz constant K‖T‖;
  Relaxation bidirectional `sequentialRelaxation_comp_le`; constant `constant_eq_of_linearIsometryEquiv`.
- **Whitening.** e is an orthonormal basis, λᵢ > 0 (positive definiteness on eᵢ); W₀ v = ∑ λᵢ^{-1/2}⟪eᵢ,v⟫eᵢ is injective (coefficient elimination) ⇒
  `ofInjectiveEndo` equivalent; symmetry is expressed by the coefficient expressions; ⟪T(Wu),Wv⟫ = ∑ λᵢλᵢ^{-1}⟪eᵢ,u⟫⟪eᵢ,v⟫ = ⟪u,v⟫ (`sum_inner_mul_inner`).
- **Lipschitz bridge.** ⇐: The literature constant holds directly under the Lipschitz test (Lipschitz ⇒ local Lipschitz, `literatureEnergy` = ofReal∫‖∇g‖²),
  `holds_ofPreEnergy_iff` Pass to relaxation; ⇒: the test function f is approximated by smooth compactly supported fs (B = 1), fs is a Lipschitz test function,
  Var(fs) ≤ C·relaxation ≤ C‖∇fs‖², variance and energy converge along L² limit; the constant equality holds bidirectionally via `Poincare.constant_le`/`le_constant`,
  No need for the infimum to be attained.
- **Factorized comparison.** For each B-test class x = [g] (∇g ∈ L²): ‖B∇g‖² = ⟪Σ∇g,∇g⟫ ≤ ‖Σ‖‖∇g‖² pointwise, integral monotonic;
  `sequentialRelaxation_comp_le_mul` Use `ENNReal.mul_iInf'` with `Monotone.map_liminf_of_continuousAt`.
- **(1)⇒(3) assembly.** ν intrinsic law; c = −∫x dν; νc = translateLaw ν c (mean zero, Σ invariant); νt = mapEquivLaw νc W
  (Average W 0 = 0, Σ_t = WΣW = 1, second moments, log-concave, affine support ⊤ are all transported);
  C_P^aff(μ) = const(ν,cov) = const(νc,cov) = const(νt,cov) = const(νt,Lip) = Poincare.constant νt = C_P^lit(νt) ≤ K.
- **(3)⇒(2) Assembly.** C_P^lit(μ) = Poincare.constant ν = const(ν,Lip); `Poincare.Affine.Holds μ K` ⇒
  `constant_le_mul_of_energy_le_mul` ⇒ const(ν,Lip) ≤ ‖Σ_ν‖₊·K; `opNorm_operator_intrinsic` changed to ‖Cov_μ‖.

Pit: `theorem LogConcave.xxx` inside `translateLaw`, `integral_id_translateLaw_neg_integral` will parse to `KLS.LogConcave.*`
The named theorem must write `Energy.Euclidean.` full name; leaving `(x : Measure _)`'s forced conversion target to `_` will cause the elaborator to timeout on whnf.
Must write full `Measure (affineSupport μ).direction`; for CLM values in subtype use `ext u` which will continue to apply `Subtype.ext`, switch to
`ContinuousLinearMap.ext`; `PreEnergy.ofLinearPMap (...)` Stuck at the universe metavariable when no expected type, needs to be annotated `: PreEnergy (Lp ℝ 2 ν)`;
`hcov_t` has different syntax from `↑W` (CLM forced conversion) and `W` (equivalent forced conversion), with `rw` preceding `← hWadj`.

## Metadata Synchronization

- ledger adds `thm:affine-isotropic-reduction` (proved/lean, `kind: lemma` according to repository legacy rules), seventeen proved nodes;
  `check_blueprint.CERTIFICATES` adds a mapping; lakefile `Solutions` root adds a certificate module.
- Blueprint theorem block anchors twenty-six statements and certificates, with statement and proof tags `leanok`; tail supplements three expressions with Lean names, (2) notation, and
  `Conjecture` inference; in the proof, "Open." is removed and replaced with a Lean path; `\uses` remains unchanged.
  route-composition.yaml updates the claim of this node from `open` to `proved` and includes Lean evidence (`check_blueprint` requires leanok nodes to have explicit local Lean evidence).
- Root aggregation module imports `KLS.LogConcave.IsotropicReduction`; `Poincare/Foundation.lean` imports `LinearEquiv`, `LipschitzComparison`, `CovarianceWhitening` and updates document highlights.
- tasks.json: `thm:affine-isotropic-reduction` changed to `available`, registers four new modules, `Energy/Relaxation/Basic.lean`, `Operator.lean`, `LiteratureComparison.lean`, `LogConcaveComparison.lean`, `CovarianceClosure.lean`, `IntrinsicCovariance.lean`, `Isotropic.lean`, and Mathlib `FiniteDimensional/Basic`, `Module/FiniteDimension`, `Spectrum`, `Adjoint`, `Order/LiminfLimsup`, `ENNReal/Inv`; `thm:cmh-recovery-affine-poincare-bound` changed to `missing` and lists four form gaps; evidence files for other tasks remain untouched (`Energy/Relaxation/Basic.lean` is not in existing evidence).
- Current guide: HANDOFF, README, `verification.md`, `solutions/README.md`, `formalization/README.md`, `blueprint/README.md`, `Energy/README.md`, `KLS/README.md`, `KLS/LogConcave/README.md`, `Poincare/README.md`, `Poincare/Euclidean/README.md`, `naming.md` (three new lines added). The document for `KLS/Statement.lean` states "does not assert equivalence to anisotropic expressions" remains unchanged (this file is part of statement golden closure; equivalence is established by this record and module `IsotropicReduction`). Statement golden, `STATEMENT_CHECKS`, and route configuration logical structure remain unchanged.

## Evidence Boundary

`lake build` passed (3349 jobs), the certificate is guarded by standard axioms of fifteen library-level declarations; `check_ledger`, `check_blueprint`, `atlas check`, and 100 Python test cases passed. The final verification receipt was generated by `python3 research/verify.py` after this record and all guideline edits, with its source code SHA recorded within the receipt itself, not written back to this file. Local kernel replay trusts third-party compiled imports; no isolated rebuild, remote CI, or release was performed.
