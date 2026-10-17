# Weak trace contraction, Theorem 2.5 (weak C^{1,1}) and source Stein: canonical integration

Date: 2026-10-16. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## Provenance

- **API runs.** The weak trace contraction tasks A5 (4 rounds, 6 queries) and A5a (4 rounds, 2 queries) exhausted
  without an accepted proof; both runs are sealed (944 and 934 files) and failure-reviewed. The S1 task (integrable weak
  derivatives have zero integral) was accepted by the existing gpt-6-astra/high loop in round 2 of 4 and then
  independently accepted; its proof body is used verbatim.
- **Closed assemblies.** The weak trace energy package (compact flux tests, trace contraction, positivity, trace-Gram
  comparison, A.5 conservativity and half energy, weighted-Laplacian pairing, C^{1,1} coercivity and weak
  Brascamp–Lieb) and the Theorem 2.5/source Stein package (matrix trace and variance identities, the given-potential
  weak Theorem 2.5 bound, the a.e. symmetric extension, tilted integration by parts, the C¹ chain, source Stein, the
  compact dual bound and the Gaussian directional identity) were assembled from independently accepted closed reuse
  prototypes.
- **Placement and prototypes.** Codex fixed the placement. Claude built production-shaped prototypes with recorded
  declaration, import, visibility and provenance maps (`weak-trace-energy-integration/phase1-delta` proto03 and
  `weak-trace-theorem25-stein-integration/phase1` proto01). Codex accepted them independently (acceptances `cc90ad12…`
  and `8d2df682…`: strict production 98 and audits 62 with warnings as errors, complete ModuleData semantics, 392 axiom
  reports all standard, kernel replay 98).
- **Integration.** Claude, the sole canonical writer, copied the 25 accepted files byte for byte (source snapshot
  `3af79a97…`). Codex accepted the canonical source copy (`canonical-phase1/CODEX-CANONICAL-SOURCE-ACCEPTANCE.json`)
  and reviewed metadata proposal v3 before this metadata phase.
- **Coordination.** No commit, push, tag, remote CI or release is authorized.

## Exact scope

Generic results (every finite dimension unless stated; owners in the table below):
- `integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`: a compactly supported flux, L² on compact sets,
  with locally integrable forcing tested by compactly supported C¹ functions extends to every globally bounded, locally
  integrable test with compact-local L² weak derivatives. The shared compact-local tools are public in the same owner.
- `bounded_trace_quadratic_weak_derivative_data`, `bounded_weak_matrix_product_entry`: for bounded measurable matrix
  fields with compact-local L² weak derivatives, tr(BABA) and the entries of SHS are bounded with weak derivatives
  2 tr(BAB DA_k) and (S DH S)_ij; arbitrary real B and S.
- `integral_rough_mul_generator_eq_neg_energy_of_contDiff_one`: rough bounded weak tests against the inverse-Hessian
  generator of a compactly supported C¹ cutoff with Lipschitz gradient, under the C¹ Monge–Ampère hypotheses.
- `integral_trace_quadratic_flux_eq_neg_density`: the weak trace contraction (2.8)/(2.10) for arbitrary rough fields H,
  R, E, T and a continuous weight with the stated compact-local integrability and tested identities, every real B.
- `trace_forcing_add_twice_energy_nonneg`, `letwin_tensor_comparison_trace_gram`,
  `four_tensor_trace_le_density_add_twice_energy`: pointwise positivity, (2.12) in trace-Gram coordinates, and
  0 ≤ D, 4D ≤ g + 2 tr(BHBH).
- `integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one`, `compact_ordinary_diffusion_coercivity_of_lipschitz_gradient`
  and `scalar_brascamp_lieb_weak_finite_energy`: Lemma A.6 at C^{1,1} regularity for a given log-concave e^{−U} dx with U
  C¹, globally Lipschitz, with Lipschitz gradient and a.e. positive definite Hessian, for bounded weak tests with
  compact-local L² derivatives and integrable inverse-Hessian energy.
- `sum_matrix_product_entry_mul_eq_trace`, `sum_matrix_product_entry_quadratic_eq_trace`,
  `sum_variance_entries_eq_integral_trace_sub_trace_mean`: finite trace identities and the random-matrix variance
  identity.
- `integral_trace_quadratic_le_two_mul_trace_sq`: the weak C^{1,1} Theorem 2.5 bound for a given convex potential and
  PSD B. The mean Hessian Id, integrable D and the half energy ∫ D dν ≤ ½ ∫ tr(BHBH) dν remain hypotheses.
- `symmetric_trace_integral_extension_of_ae_posSemidef`: the a.e. PSD extension from PSD to every symmetric B.
- `integral_eq_zero_of_integrable_weak_derivative` (S1 body), `integral_fderiv_tilted_eq_integral_mul_fderiv_of_bounded_lipschitz`,
  `chain_coordinate_of_differentiableAt_gradient` and `source_stein_identity_of_bounded_lipschitz_test`: the latent source
  Stein identity ∫ ∂_i u f(∇u) dν = ∫ Σ_j (∇²u)_ij ∂_j f(∇u) dν for C¹, globally Lipschitz u with Lipschitz gradient and
  ∫ e^{−u} = 1, and every C¹, bounded, globally Lipschitz f. No Stein kernel and no target inverse.
- `compact_linear_pairing_sq_le_of_source_identity`: the compact dual Cauchy–Schwarz bound from a latent source identity
  and an L² latent field through a measurable pushforward; the identity and the field are inputs.
- `GaussianSmoothing.gaussianLaw_directional_identity_of_bounded_lipschitz_test`: ∫ ⟨x, v⟩ f = (2s)⁻¹ ∫ D_v f under
  `gaussianLaw s`, s > 0, for C¹ bounded Lipschitz f; no product coupling.

Actual source in `KLS/CEK/MomentRegularity.lean`, exactly the original R0 hypotheses (n > 0):
- `exists_regular_moment_bounded_weak_cutoff_testing`: the same u, L, LF, T and cutoff family as
  `exists_regular_moment_weak_cutoffs`, with the rough cutoff-generator identity for every bounded weak test and r ≥ 1.
- `exists_regular_moment_weak_stein_coupling`: ONE u, L, LF and T with the whole earlier payload, A.5 conservativity
  ∫ g dν = 0 and the half energy for every PSD B, and ∫ tr(BHBH) dν ≤ 2 tr(B²) for every real symmetric B (exact
  constant 2), the weighted integration by parts for bounded Lipschitz tests and the coordinate source Stein identity.
  The intermediate trace-energy producer is private; its exact type is retained by the audit.

Audit `research/audits/BKL/WeakHessianTraceAudit.lean`: a seven-step retention chain from
`weak_stein_coupling_retains_weighted_pairing_contract` to `weak_trace_contraction_retains_trace_cutoff_contract` projects
every earlier public contract from the one witness.

Relation to the paper: this is the weak C^{1,1} counterpart of the proof of Theorem 2.5 at the actual regular source
witness. It is not the smooth moment map of Lemma 2.2 and not Theorem 2.5 as stated; T25, LA5, LA6, L27, L29 and T12
stay partial, and no paper coverage or certificate is added.

**Not claimed:** a Stein kernel, the Gaussian product coupling, the H⁻¹ step on the smoothed law, the spectral constant-8
assembly, Lemma A.2, Theorem 1.2, BKL or KLS. The 30 ledger certificates, paper coverage and the four active routes are
unchanged; the 21 new local-result nodes stay outside the active implication chain.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities.lean` | five imports for the new modules |
| `Analysis/WeakDerivative.lean` | compact flux identity, shared compact-local tools (public), S1 lemma; one import |
| `Analysis/Matrix/WeakDerivative.lean` | bounded trace-quadratic data and matrix-product entries; trace helpers moved to Trace |
| `Analysis/Matrix/Trace.lean` | matrix-product entry/trace identities and shared finite-sum helpers |
| `Analysis/Matrix/WeakTrace.lean` | new: weak trace contraction |
| `Analysis/Matrix/Positivity.lean` | trace-density positivity |
| `Analysis/Matrix/TraceGram.lean` | new: (2.12) trace-Gram comparison and 4D bound |
| `Analysis/Matrix/Integral.lean` | a.e. PSD symmetric extension |
| `Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean` | private helpers replaced by the shared public tools |
| `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessianCutoff.lean` | rough cutoff-generator identity |
| `Analysis/BakryEmery/IntegrationByParts/WeakLaplacian.lean` | new: weighted-Laplacian pairing |
| `Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean` | tilted integration by parts for bounded Lipschitz tests |
| `Analysis/BakryEmery/Bochner/Lipschitz.lean` | C^{1,1} ordinary-diffusion coercivity |
| `KLS/LogConcave/BrascampLieb.lean` | three Hilbert-closure helpers made public |
| `KLS/LogConcave/HminusOne.lean` | duplicate private helpers removed in favour of BrascampLieb |
| `KLS/LogConcave/WeakBrascampLieb.lean` | new: weak finite-energy Brascamp–Lieb |
| `KLS/LogConcave/HessianTrace.lean` | new: given-potential weak Theorem 2.5 bound |
| `KLS/LogConcave/HessianStein.lean` | source Stein identity; one import |
| `KLS/LogConcave/Density/GaussianSmoothing/Moments.lean` | Gaussian directional identity; one import |
| `Probability/Moments.lean` | random-matrix variance identity; one import |
| `Probability/Stein/HessianKernel.lean` | C¹ gradient chain |
| `Probability/Stein/Kernel.lean` | compact source dual bound |
| `KLS/CEK/MomentRegularity.lean` | rough cutoff testing and the weak Stein coupling producer, private intermediates; five imports |
| `research/audits/BKL/WeakHessianProductAudit.lean` | shared tool instead of a private copy |
| `research/audits/BKL/WeakHessianTraceAudit.lean` | new: seven-step retention chain |

The declaration, import, visibility and provenance maps are in the ignored Goal control directory
(`weak-trace-theorem25-stein-integration/phase1/maps-v2`, `weak-trace-energy-integration/phase1-delta`).

## Validation and evidence boundary

- Prototype: strict compilation with warnings as errors, complete ModuleData semantic comparison (every physical entry
  accounted for; the precisely reviewed module-hygiene name mappings were checked with unmodified full-type kernel
  equality, and the one foreign innerSL.eq_1 serialization relocation was checked separately), standard axioms and kernel
  replay, independently accepted.
- Canonical: the 25 files are byte-identical to the accepted prototype sources; Codex accepted the copy.
- Metadata: written through a private index copy; `update.py` regenerated the views, with the documented progress,
  Blueprint, ledger, atlas and diff checks.
- The earlier full receipts do not cover snapshot `3af79a97…` or this metadata. A fresh full local verification is
  pending; no current-full claim is made before an exact report.

## API status and next steps

The S3 Gaussian product source-pairing task ran once and exhausted (4 rounds, 1 query, no accepted proof); the 939-file
run is sealed and failure-reviewed. The fixed loop executes a query block only when a response contains no Lean block,
so rounds 1–3 compiled the unchanged frozen statement. No resend or repair is authorized; the API is idle. S2/Lemma A.2,
the directional/affine helpers, the Gaussian L4 prototype and the S3 Expected preflight are scratch build evidence only.

Next: the Gaussian product coupling of the actual source law (product integrability, translated Gaussian, Fubini); the
compact dual Cauchy–Schwarz bound from the latent source identity; the H⁻¹ inequality on the actual C² convex
Gaussian-smoothed law; the spectral/invertible constant-8 assembly with noise removal; Lemma A.2; the regular-class/A.1
compact constant-8 bound. A target Stein kernel or inverse transport is optional, not a required prerequisite.
