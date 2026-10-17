# Weak inverse-Hessian derivative (Letwin (2.5)): canonical integration

Date: 2026-10-15. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## Provenance

- **E3, E4 and E5.** Codex froze three small contracts. Each candidate was accepted by the existing gpt-6-astra/high loop and then
  accepted independently, with an actual-source client (`independent/E3`, `independent/E4`, `independent/E5` in
  `build/reviews/2026-10-14-letwin-constant-eight-goal/`):
  - E3, `hasWeakDerivAlong_exp_neg_of_lipschitz`, candidate `a794166e…`;
  - E4, `HasWeakDerivAlong.mul_of_locally_bounded`, candidate `1b8eb01e…`;
  - E5, `ae_weak_matrix_inverse_derivative`, candidate `1ea78ad3…`.
- **Cofactor consumers.** The two adjugate consumers reuse the existing certified Piola cofactor measurability and bound bodies and the
  weak-cofactor proof core of the polynomial audit. They were checked as client support before E4 (`E4-preflight/`).
- **Prototype and placement.** The coherent package passed Codex's isolated prototype (`weak-inverse-package-prototype/RESULT.json`,
  CODEX_COHERENT_WEAK_INVERSE_PACKAGE_PROTOTYPE_ACCEPT) and placement acceptance (`weak-inverse-integration/PLACEMENT-ACCEPTANCE.json`).
- **Integration.** Claude, as the sole canonical writer, copied the exact six prototype files
  (`weak-inverse-package-prototype/SOURCE-MANIFEST.json`). Codex then accepted the canonical sources
  (`weak-inverse-integration/CODEX-SOURCE-ACCEPTANCE.json`).
- **Coordination.** The Goal is coordinated by the current Codex chat `01a13ea4-f340-73b1-bbe8-af9381f33679` and the original Claude
  session. The earlier publication checkpoint (HEAD `2c3e369`) is complete; no further commit, push, tag, remote CI or release is
  authorized.

## Exact scope

Generic tools:
- **`Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz`** (E3; `Analysis/WeakDerivative.lean`).
  - Statement: for globally Lipschitz F, exp(−F) has the weak directional derivative −exp(−F)·DF[v], L² on every compact set.
  - Scope: every finite-dimensional real inner-product space and every direction, zero included. There is no lower bound on F, no
    global bound on exp(−F) and no C¹ hypothesis.
- **`Analysis.HasWeakDerivAlong.mul_of_locally_bounded`** (E4; same owner).
  - Statement: factors essentially bounded on each compact set, with compact-local L² weak derivatives, give the explicit derivative
    df·g + f·dg of f·g, L² on compact sets.
  - Scope: one fixed direction, every Euclidean dimension, zero included. The proof reduces to the existing globally bounded rule by
    compact cutoffs.
- **`Analysis.ae_weak_matrix_inverse_derivative`** (E5; `Analysis/Matrix/WeakDerivative.lean`).
  - Statement: if R·A = Id a.e. and the entries of A and R have compact-local L∞ bounds and weak derivatives with compact-local L²
    densities, then DR = −R·DA·R a.e.
  - Scope: independent ambient dimension and matrix size, both possibly zero. There is no symmetry, positivity, C¹ or global bound.

Piola adjugate consumers (`Analysis/Matrix/Piola.lean`). They reuse the existing private Piola cofactor proof core; neither assumes a
log-det exponent or Monge–Ampère equation, and they do not depend on the inverse-integrability theorem of that owner:
- `Analysis.memLp_hessian_adjugate_top`: the Hessian adjugate entries are globally essentially bounded when ∇u is Lipschitz. Each
  entry is a continuous function of the total derivative of ∇u, which lies in a closed ball.
- `Analysis.exists_weak_hessian_adjugate_derivative`: separately, if the Hessian entries are globally essentially bounded and a
  SUPPLIED weak Hessian tensor T has compact-local L² entries, each adjugate entry has some weak coordinate derivative, L² on compact
  sets (row-updated determinants). This statement has no Lipschitz-gradient premise.

New assemblies (two separately frozen complete types; manually reviewed compositions of the accepted tools above):
- **`Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet`** (`Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`).
  - Hypotheses: ∇u is Lipschitz, F is Lipschitz, a.e. the Hessian is positive definite with log det H = F, and a supplied weak Hessian
    tensor T has compact-local L² entries.
  - Conclusion: for all k, i, j, (H⁻¹)_ij has the weak derivative −(H⁻¹ T_k H⁻¹)_ij, L² on compact sets, and (H⁻¹)_ij is essentially
    bounded on compact sets.
  - Proof route: H⁻¹ = exp(−F)·adj(H) a.e.; E3, the adjugate consumers and E4 give a weak derivative of that product, E2 transfers it
    to H⁻¹, and E5 identifies the density.
- **`Analysis.exists_regular_moment_weak_inverse`** (`KLS/CEK/MomentRegularity.lean`).
  - Hypotheses: exactly the original R0 regular-source hypotheses.
  - Retained output: the same u, L, LF and T as `exists_regular_moment_weak_first_derivative`, with every R0 field and every
    first-weak-Monge–Ampère field.
  - New output: the weak (2.5) formula for every (H⁻¹)_ij above, its compact-local L² density and compact-local essential inverse
    bounds.
  - No inverse formula/derivative, C² regularity, global inverse bound, weighted T² or trace estimate is assumed as an input; the
    output is still the explicit weak (2.5). The cofactor-choice implementation fields are not exposed.
- **Audit.** `research/audits/BKL/WeakHessianInverseAudit.lean` consumes the whole source interface.

**Not claimed.** The following are not supplied:
- the second evolution identity (2.6) of Lemma 2.4, bounded H¹ testing and A.4/A.5;
- the energy comparison (2.14), the actual weak Brascamp–Lieb and mean-Hessian consumers, and the Theorem 2.5 upper bound;
- Stein/H⁻¹, the spectral assembly, compact constant 8, BKL and KLS.

L24 and T25 stay partial. The 30 ledger certificates, paper coverage and the four active routes are unchanged. The compact counterpart
remains distinct from the full noncompact paper statement.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/WeakDerivative.lean` | E3 and E4 appended; four private E3 helpers renamed into the owner's `weak_*` names; E4 reuses the existing `cutoff_memLp` |
| `formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean` | E5 appended; one Mathlib import (`LinearAlgebra.Matrix.NonsingularInverse`) |
| `formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean` | two adjugate consumers appended; one import (`Analysis.Matrix.WeakDerivative`) |
| `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean` | intrinsic weak (2.5) appended; one import (`Analysis.Matrix.WeakDerivative`) |
| `formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean` | actual-source weak inverse producer appended |
| `research/audits/BKL/WeakHessianInverseAudit.lean` | new audit; imports `KLS.CEK.MomentRegularity` |

- There is no new library module, aggregate import, alias or namespace migration.
- No generic owner imports KLS/CEK.

Semantic comparison (prototype, then the canonical runner):
- All 112 old complete type/value/level records are unchanged.
- 23 accepted candidate and reused proof records are identical under 20 explicit constant-prefix maps and 8 private binder-label scope
  maps. The constant maps cover private-helper renames, the two cofactor promotions and six elaborator-generated proof constants. The
  binder maps change only labels of anonymous binders, never terms, binder kinds, levels or de Bruijn indices.
- The public E3/E4/E5 frozen types are raw-identical.
- The two new assemblies have their own separately frozen complete types. They are not claimed identical to any E3/E4/E5 candidate.

## Validation

Local canonical checks (`weak-inverse-integration/canonical-local/RESULT.json`):
- The full current Lean scope was built, and a fresh filtered view was made.
- Strict `-DwarningAsError=true` compilation of the five owners, the aggregate and the actual-source audit produced empty logs.
- All 124 canonical complete records are equal to the prototype.
- The 124 structured axiom reports use only standard axioms.
- `leanchecker` replayed 6 modules: the five owners and the audit.

Codex independently accepted the canonical sources.

Metadata changes:
- The Blueprint gains six appended lemmas: E3, E4, E5, the two adjugate consumers (one lemma), the intrinsic weak (2.5) and the
  actual-source weak (2.5). Existing lemmas are unchanged.
- `nodes.json`, `tasks.json`, `literature.json` (L24 and T25 stay partial), the proof path, `HANDOFF.md`, the Goal queue and the root
  summary are synchronized.

Evidence boundary: the previous full receipt `20261015T015709.906783Z` covers only the published snapshot `a3805d3d…`. Final
acceptance requires a passing full receipt matching the current source/meta snapshot, bound in the ignored `weak-inverse-integration/`
final acceptance/completion records; inspect `build/verification/latest.json` and the exact report.

## Next

In dependency order (no task is dispatched here):
1. The genuinely missing weak coefficient and curl testing interfaces, and bounded H¹ testing. A read-only gap review proposes a
   commutation identity tested against a compact rough H¹ coefficient; it is not frozen, proved or dispatched.
2. The actual C¹/Lipschitz-gradient source-height A.4/A.5, with locally L² flux and locally L¹ right-hand sides.
3. The weak second evolution identity (2.6) and the integrated energy comparison (2.14), E tr(BHBH) ≥ 2 E G₁.
4. The actual weak Brascamp–Lieb (A.6) and mean-Hessian (Lemma 2.3) consumers, then the Theorem 2.5 upper bound
   E tr(BHBH) ≤ 2 tr(B²).
5. Stein/H⁻¹ and the spectral/regular-class/compact constant-8 assembly.

Local L² of T gives only local L¹ of T². No C² upgrade, global inverse bound, global weighted tensor square or assumed energy is
available.
