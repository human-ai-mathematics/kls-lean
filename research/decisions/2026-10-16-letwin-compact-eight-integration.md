# Exact compact Letwin constant 8: canonical integration

Date: 2026-10-16. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## Result and scope

`KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound` (`KLS/Letwin/CompactBound.lean`): for every n > 0,
every compactly supported isotropic log-concave probability measure μ on `EuclideanSpace ℝ (Fin n)` and every self-adjoint
continuous linear M (singular and indefinite included),
∫ (⟨Mx, x⟩ − ∫ ⟨My, y⟩ dμ)² dμ ≤ 8 ∑ᵢⱼ ⟨M eᵢ, eⱼ⟩² in the standard orthonormal basis. The type is the unchanged existing
predicate; no premise was added.

Certificate `thm:letwin-compact-quadratic-bound` (`solutions/ThmLetwinCompactQuadraticBound.lean`): `certificate` states the
expanded source form above and `bound` the named predicate; both are the canonical endpoint. Source: Letwin,
arXiv:2607.24164v1 (PDF SHA-256 `5dd9194cf36d91e2e4929a48564fe99d8d163a0a5ec7b31d80dc1f58a41778f1`), Theorem 1.2, compact
counterpart, as consumed by Bizeul–Klartag–Lehec arXiv:2610.05474v1, Lemma 4.2. This is a supporting certificate: the
paper's Theorem 1.2 is stated for every isotropic log-concave law and Lemma A.1's noncompact approximation is not
formalized, so Letwin's paper is not covered.

**Not claimed:** the noncompact Theorem 1.2; Theorem 1.1; the smooth source Lemma 2.2 and Theorem 2.5 (their weak C^{1,1}
actual-source counterparts are what the proof uses); the target Stein kernel of Lemma 2.7 (not constructed); stochastic
localization, BKL Theorem 4.1, BKL Theorem 1.1 and KLS. `conjecture_of_letwinCompact letwinCompactBound` would type-check;
it is not added, because the conditional downstream chain is queued for source re-review. `KLS.kls` stays open.

## Proof chain

`regularClass_matrix_variance_le_eight` (`KLS/Letwin/RegularClass.lean`) assumes exactly the original R0 hypotheses
(n > 0, isotropic `1_K e^{-W} dx`, K compact convex with nonempty interior, W smooth and κ-uniformly convex):
1. One weak Stein witness u from `exists_regular_moment_weak_stein_coupling` supplies normalization, the gradient
   pushforward, C¹ regularity, the Lipschitz bounds, a.e. Hessian data, the mean Hessian Id and the exact-2 trace bound for
   every symmetric B.
2. The original regular input law μ is log-concave (`logConcave_of_eq_regularClass`), has full affine support
   (`affineSupport μ = ⊤`, from isotropy) and a finite fourth moment (the bounded gradient ∇u pushes the normalized witness
   law ρ = e^{−u} dx to μ).
3. `symmetric_matrix_variance_bound_of_isUnit` (Lemma A.2, stronger form) reduces to invertible symmetric M.
4. With B = √(M²), S = √B and Q = sign M (`symmetric_matrix_spectral_geometry`), the variance of the quadratic form equals that
   of ⟨Q x, x⟩ under η = S_#μ, the image of μ by S (`variance_quadratic_map_sandwich`).
5. Gaussian smoothing of η does not decrease it (`variance_quadratic_le_smoothedLaw`); the smoothed variance is at most 4 times the
   latent product energy (`gaussian_smoothed_quadratic_variance_le_latent_energy`: smooth convex potential of the smoothed
   image, Gaussian product source Stein identity, compact dual bound, H⁻¹ inequality).
6. The energy is at most 2 tr(M²) + 2(2s)⁻¹ tr B + n(2s)⁻² (`sum_integral_spectral_noise_energy_le`, with
   `latent_field_eq_action_conjugation`), and `le_of_forall_inverse_noise_quadratic_error` removes the noise.

`letwinQuadraticBound_of_matrix_variance_bound` converts the matrix form to `LetwinQuadraticBound`,
`regularClass_letwinQuadraticBound` gives it for the regular class, and the existing `letwinCompactBound_of_regularClass`
gives `letwinCompactBound`.

## Placement

The v3 layout (independently accepted) places generic results in their object families and the per-paper assembly in a
new `KLS/Letwin/` folder:

| File | Change |
| --- | --- |
| `Analysis/Matrix/{Trace,Sign,Integral}.lean`, `Analysis/Operator/HilbertSchmidt.lean`, `Analysis/BakryEmery/Calculus.lean` | trace, spectral geometry, invertible approximation, mean-trace, Hilbert–Schmidt and affine-gradient identities appended |
| `Probability/Stein/{Kernel,HessianKernel}.lean`, new `Probability/Stein/QuadraticAction.lean` | matrix-action algebra; Hessian action in L²; quadratic action identities, spectral sign/noise identity and integrated energy |
| `Probability/Moments.lean`, `L2/MeanVariance.lean`, new `Probability/QuadraticVariance.lean` | quadratic forms in L²; finite-combination variance continuity; quadratic-form continuity, singular extension, centered-noise convolution |
| `KLS/LogConcave/Density/GaussianSmoothing/Moments.lean`, new `…/{LinearImage,ProductCoupling,QuadraticVariance}.lean` | fourth moments and translated identity; latent map and smooth convex potential; product source Stein and compact dual; noise limit, smoothing comparison, quadratic H⁻¹ bound |
| `KLS/LogConcave/{HessianStein,Density/Tilted}.lean` | directional/affine source Stein; restricted-exponential log-concavity |
| new `KLS/Letwin/{RegularClass,CompactBound}.lean` | regular-class bound and compact endpoint |
| `formalization/FunctionalInequalities.lean` | seven imports |
| new `research/audits/BKL/LetwinCompactBoundAudit.lean` | source-form compact client and BKL compact base client |

All accepted names, namespaces and proof bodies are unchanged; the only name migration moves the two audit clients into
the `LetwinCompactBoundAudit` namespace. Existing declarations of the extended files are unchanged; in
`GaussianSmoothing/Moments.lean` the old body is enclosed in an anonymous section so that its file-level `ContDiff`
notation does not reach the appended blocks.

## Validation and evidence boundary

- Production candidate (independently accepted): strict compilation of 262 modules (250 unchanged prior passes and 12
  fresh), 137 affected research audits, all 4468 old physical declarations RAW-unchanged, all 4522 new physical entries
  matching the actual environment and accounted for, the 53 new declarations in their frozen owners (20 RAW-identical to
  scratch, 31 differing only in precisely reviewed module binder-name components, 2 explicit audit name migrations), all
  53 unmodified original types equal by kernel `Eq.refl`, 383 relevant targets with standard axioms only, and kernel replay
  of 262 modules.
- Two additional files named `… 2.olean` held byte-exact old 905-part seed content; they were retained, excluded and
  directly shown not loaded, and a separate 912-part registered view had identical loaded module names and normal paths
  and all 4522 physical core entries.
- Canonical: the 21 files were copied byte for byte and the resulting source snapshot was independently accepted.
- Certificate and metadata: written through a new private index copied from the last reviewed one; the generated
  progress views come from `update.py`.
- The milestone is accepted only with a passed full local verification report for the exact tracked source/meta
  snapshot and its independent acceptance, recorded under `build/` without a further tracked edit; the ignored Goal
  checkpoint records the current report and acceptance state, and each earlier report applies only to its recorded
  snapshot.

The sealed S3 and S4 API runs remain failures; their mathematics was supplied by independently accepted closed assemblies.
