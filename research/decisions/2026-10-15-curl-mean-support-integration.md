# Rough curl, C¹ generator testing and actual mean Hessian: canonical integration

Date: 2026-10-15. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## Provenance

- **H1a, H1b and H1c.**
  - H1a, the original compact rough curl contract, exhausted its four rounds and six queries naturally. Its failures are preserved,
    and it was not retried.
  - H1b, a genuinely smaller common-support smooth approximation contract, was accepted by the existing gpt-6-astra/high loop and then
    independently accepted (`independent/H1b`).
  - H1c returned to the original H1a statement with H1b as its only dependency. It was accepted by the loop and then independently
    accepted (`independent/H1c`). Its complete type equals the original H1a type.
- **C¹ generator and mean Hessian.** The C¹ unprimed generator identity and the actual-source mean Hessian are checked compositions of
  existing canonical proofs: the closed N10b generator proof, and the existing C¹,¹ mean-Hessian identity with isotropy.
- **Prototype and placement.** Codex reviewed the production prototype (`curl-mean-support-package-prototype/SEMANTIC-RESULT.json`,
  CODEX_PRODUCTION_PROTOTYPE_ACCEPT) and the placement (`curl-mean-support-integration/PLACEMENT-ACCEPTANCE.json`).
- **Integration.** Claude, as the sole canonical writer, copied the exact four prototype files (`SOURCE-MANIFEST.json`). Codex then
  accepted the canonical sources (`curl-mean-support-integration/CODEX-SOURCE-ACCEPTANCE.json`).
- **Coordination.** The Goal is coordinated by the current Codex chat and the original Claude session. No commit, push, tag, remote
  CI or release is authorized.

## Exact scope

Generic tools (`Analysis/WeakDerivative.lean`):
- **`Analysis.exists_contDiff_compact_weak_deriv_approximation`** (H1b).
  - Hypotheses: η is compactly supported; its given weak derivatives a, b along directions v, w are compactly supported and globally L².
  - Conclusion: there are one compact set S containing the supports of η, a and b, and smooth compactly supported θ_m. Each θ_m, and
    both of its directional derivatives along v and w, are supported in S; both derivatives are globally L² and converge to a and b in
    global L².
  - Scope: every finite dimension and both directions, zero included. η is not assumed C¹ or globally L².
- **`Analysis.integral_weakDeriv_mul_eq_swap`** (H1c, exactly the original H1a statement).
  - Hypotheses: p and q are weak derivatives of the same f along v and w, each L² on compact sets; η, a, b are as above.
  - Conclusion: ∫ p·b = ∫ q·a.
  - Not assumed: the curl identity itself, a C¹/C² η, global L² of p or q, finite whole-space volume, positive dimension or nonzero
    directions, and any fourth derivative of a rough function.

Generator (`Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`):
- **`Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one`.**
  - Hypotheses: the N10b hypotheses (u ∈ C¹ with Lipschitz gradient, V ∈ C¹, Lipschitz exponent, det H = exp(−u + V(∇u)) a.e.,
    w ∈ C¹ with Lipschitz gradient), with the multiplier η only C¹ and compactly supported.
  - Conclusion: the unprimed identity ∫ η (Lw) e^{−u} = −∫ ⟨H⁻¹∇η, ∇w⟩ e^{−u}.
  - The two original N10b theorems are unchanged, and the primed form still requires C² η. This is readiness support for the actual
    height cutoffs, not a construction of them.

Actual source (`KLS/CEK/MomentRegularity.lean`):
- **`Analysis.exists_regular_moment_weak_inverse_mean_hessian`.**
  - Hypotheses: exactly the original R0 regular-source hypotheses.
  - Retained output: the same u, L, LF and T, with every R0, first-weak-Monge–Ampère and weak-inverse field.
  - New output: for all i, j, the Hessian entry H_ij is integrable for ν = e^{−u} dx, and ∫ H_ij dν = δ_ij.
  - Proof route: integrability follows from the Lipschitz-gradient entry bound. The mean is the existing C¹,¹ identity
    `BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul` combined with isotropy of the actual gradient pushforward
    (`KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map`). One private one-use helper, `mean_hessian_basis_entry`, handles the
    canonical-basis calculation.
  - Not added: no analytic premise, C², given mean or trace estimate.
  - Scope: Lemma 2.3 for the actual R0 source potential, proved under its C¹/Lipschitz-gradient hypotheses. The result does not assert
    the full smoothness or the diffeomorphism properties of the paper's Lemma 2.2.

Audit (`research/audits/BKL/WeakHessianInverseAudit.lean`): `whole_source_interface` is unchanged. Three clients are appended:
- `actual_source_inverse_coefficient_curl`: the curl pairing for η = ψ·(H⁻¹)_ab, whose explicit derivatives
  ψ·(−H⁻¹T_kH⁻¹)_ab + D_kψ·(H⁻¹)_ab have literal compact support and global L² produced from the accepted inverse data;
- `actual_source_c1_generator_test`;
- `whole_source_mean_interface`, the full original-source expectation including the mean Hessian.

**Not claimed:**
- the weak second evolution identity (2.6), bounded H¹ testing with locally L¹ forcing, and the actual A.4/A.5 height cutoffs;
- the energy comparison (2.14), weak Brascamp–Lieb (A.6) and the Theorem 2.5 upper bound;
- Stein/H⁻¹, compact constant 8, BKL and KLS.

L23, L24 and T25 stay partial, and LA4 keeps its earlier reviewed scope. The 30 ledger certificates, paper coverage and the four active
routes are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/WeakDerivative.lean` | H1b and H1c appended; the existing private L² pairing lemma is reused, not duplicated |
| `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean` | C¹ unprimed generator appended |
| `formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean` | one import (`Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`); private helper and mean-Hessian producer appended |
| `research/audits/BKL/WeakHessianInverseAudit.lean` | three clients and a private cutoff helper appended |

- There is no new directory, module, aggregate import or alias. No existing canonical namespace or API is migrated; scratch names are
  mapped as listed below.

Scratch-to-canonical name map (`curl-mean-support-package-prototype/DECLARATION-MAP.json`):

| Scratch name | Canonical name |
| --- | --- |
| `IndependentH1c` private `tendsto_integral_mul_of_l2` | the existing private `Analysis.WeakDerivative` `tendsto_integral_mul_of_l2` (reused) |
| `ActualClientH1c` private `client_cutoff_memLp` | private `WeakHessianInverseAudit.client_cutoff_memLp` |
| `FunctionalInequalities.Analysis.actual_source_inverse_coefficient_curl` | `WeakHessianInverseAudit.actual_source_inverse_coefficient_curl` |
| `FunctionalInequalities.Analysis.actual_source_c1_generator_test` | `WeakHessianInverseAudit.actual_source_c1_generator_test` |
| `ActualMeanHessianSource` private `mean_client_basis_entry` | private `KLS.CEK.MomentRegularity` `mean_hessian_basis_entry` |
| `FunctionalInequalities.Analysis.actual_source_mean_hessian_test` | `FunctionalInequalities.Analysis.exists_regular_moment_weak_inverse_mean_hessian` |

The public H1b and H1c names are the accepted names.

Semantic comparison:
- All 77 old complete type/value/level/owner records are unchanged.
- 9 accepted or checked records are identical under the explicit declaration map above. The map covers the H1c pairing and client
  helpers, the audit names and the mean helper.
- One synthetic anonymous-instance binder label in the reused private pairing lemma moved from the `IndependentH1c` module prefix to
  the `Analysis.WeakDerivative` prefix. Its proof value and levels are unchanged, and no other field changed.

## Validation

Local canonical checks (`curl-mean-support-integration/canonical-local/RESULT.json`):
- The current Lean scope was rebuilt in a fresh filtered view.
- Strict `-DwarningAsError=true` compilation of the three owners, the aggregate and the actual-source audit produced empty logs.
- All 86 complete records are equal to the accepted production prototype.
- The 86 structured axiom reports use only standard axioms.
- `leanchecker` replayed four modules: the three owners and the audit.

Codex independently accepted the canonical sources.

Metadata changes:
- The Blueprint gains five appended lemmas: H1b, H1c, the C¹ generator, the existing C¹,¹ mean identity and the actual mean Hessian.
- `nodes.json`, `tasks.json`, `literature.json` (L23, L24 and T25 stay partial; LA4/LA5 scope preserved), the proof path, `HANDOFF.md`,
  the Goal queue and the root summary are synchronized.
- The pinned portfolio inventory is unchanged.

Evidence boundary: the full receipt `20261015T085050.186417Z` covers only the snapshot `d99c763b…`. Final acceptance requires a passing
full receipt matching the current source/meta snapshot, bound in the ignored `curl-mean-support-integration/` final
acceptance/completion records; inspect `build/verification/latest.json` and the exact report.

## Next

In dependency order (no task is dispatched here):
1. The actual weak second Monge–Ampère identity (2.6): the weak derivative of the right-hand side q_i, the Piola divergence of
   R = H⁻¹, and consumption of the proved rough curl.
2. Bounded H¹ testing with locally L¹ forcing, and the actual C¹/Lipschitz-gradient A.4/A.5 with locally L² flux, leading to (2.14).
3. The actual weak Brascamp–Lieb (A.6) consumer and the Theorem 2.5 upper bound; the actual mean Hessian Id is already available.
4. Stein/H⁻¹ and the spectral/regular-class/compact constant-8 assembly.
