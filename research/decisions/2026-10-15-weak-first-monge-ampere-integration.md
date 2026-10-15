# Actual-source first weak Monge–Ampère derivative (Letwin (2.4)): canonical integration

Date: 2026-10-15. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## Provenance

- **E1 and E2.** Codex froze two small contracts. Each candidate was accepted in its first round and then accepted independently
  (`independent/E1`, `independent/E2` in `build/reviews/2026-10-14-letwin-constant-eight-goal/`):
  - E1, `lipschitzOnWith_exp_Iic`, candidate `725a0da4…`;
  - E2, `HasWeakDerivAlong.congr_ae`, candidate `362ecd80…`.
- **Assembly.** The actual-source assembly reuses the accepted E1/E2 bodies, the existing exponent derivative formula and the J1
  determinant identification. No new API task was dispatched for it.
- **Prototype and placement.** The coherent package passed Codex's isolated prototype
  (`EX-first-MA-package-prototype/RESULT.json`, CODEX_COHERENT_WEAK_FIRST_MA_PACKAGE_PROTOTYPE_ACCEPT) and placement acceptance
  (`EX-first-MA-integration/PLACEMENT-ACCEPTANCE.json`, CODEX_PLACEMENT_ACCEPT). The prototype's three failed MomentRegularity attempts
  are kept in the prototype directory.
- **Integration.** Claude integrated the exact prototype bytes (`EX-first-MA-integration/SOURCE-MANIFEST.json`) as sole canonical
  writer.
- No commit, push, tag, remote CI or release is authorized.

## Exact scope

- **`Analysis.lipschitzOnWith_exp_Iic`** (E1, generic; type hash 845252842).
  - Statement: `Real.exp` is `Real.toNNReal (Real.exp C)`-Lipschitz on `(-∞, C]`.
  - Scope: every real C, negative values included; no lower bound is assumed.
- **`Analysis.HasWeakDerivAlong.congr_ae`** (E2, generic; type hash 1261692643, universe u).
  - Statement: a weak directional derivative is invariant under a.e. changes of both the function and its derivative, and the local
    integrability of the new representatives is produced.
  - Scope: every finite-dimensional real inner-product space and every direction.
- **`Analysis.ae_fderiv_mongeAmpere_exponent`** (existing formula, now public).
  - Statement: for `u ∈ C¹` with Lipschitz gradient and `V ∈ C¹`, almost everywhere the derivative of −u + V(∇u) along `e_j` equals
    −∂_j u + Σ_k H_jk ∂_kV(∇u).
  - Status: it was already proved as a compiler-private theorem in `WeakInverseHessian.lean`. Only its visibility changed; its body
    and imports are unchanged, and its private gradient helper stays private.
- **`Analysis.exists_regular_moment_weak_first_derivative`** (actual source).
  - Hypotheses: exactly the original R0 regular-source hypotheses.
  - Retained output: the same u, L, LF and T as `exists_regular_moment_weak_tensor`, with EVERY original R0 field (normalization and
    actual gradient pushforward are produced, not assumed).
  - New output, for every coordinate k:
    - exp(−u + W(∇u)) is globally Lipschitz;
    - det H has the weak derivative det(H) tr(H⁻¹ T_k), with compact-local L2 density;
    - log det H has the weak derivative tr(H⁻¹ T_k);
    - a.e., tr(H⁻¹ T_k) = ∂_k(−u + W(∇u)) = −∂_k u + Σ_a H_ka ∂_aW(∇u). This is the first weak Monge-Ampère identity, the
      actual-source weak form of Letwin (2.4).
  - Proof route: the exponent upper bound comes from coercivity of the normalized convex u (private one-use helper); E1 gives the
    Lipschitz exponential; E2 transports between a.e. representatives.
  - Not used: no C1-to-C2 step, given tensor, desired equation or trace estimate.

**Not claimed.** The log-det identification is for this ACTUAL source; it is not unrestricted rough-matrix log-det calculus. The
twice-differentiated Lemma 2.4 is not obtained: its second evolution identity (2.6) and positivity/trace integration are not supplied,
so L24 stays partial. Also not claimed: source smooth Lemma 2.2, Theorem 2.5, Theorem 1.2, compact constant 8, BKL and KLS. The 30
ledger certificates, paper coverage and the four active routes are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/Lipschitz/Exponential.lean` | new leaf in the existing `Analysis/Lipschitz` family; exact E1 bytes (two Mathlib imports) |
| `formalization/FunctionalInequalities/Analysis/WeakDerivative.lean` | appended E2 (named instances, `universe u`); old file an exact prefix |
| `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean` | `private` removed from `ae_fderiv_mongeAmpere_exponent`; module docstring updated; body and imports unchanged |
| `formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean` | five imports added (Coercivity, Lipschitz.Exponential, Matrix.DeterminantDerivative, Matrix.WeakDerivative, WeakInverseHessian); private `exponent_upper_of_normalized_convex` and public `exists_regular_moment_weak_first_derivative` appended |
| `formalization/FunctionalInequalities.lean` | one import (`Analysis.Lipschitz.Exponential`) |
| `research/audits/BKL/WeakMongeAmpereFirstAudit.lean` | new audit with five clients (full interface, forgetful projection, singular singleton, empty matrix, negative unbounded exponent) |

The only constant map is
`_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakInverseHessian.0.FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent`
→ `FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent`. There is no alias.

## Validation

Local canonical checks:
- `lake build` completed.
- Strict `-DwarningAsError=true` compilation of the four owners, the new leaf, the aggregate and the audit produced empty logs.
- The prototype's semantic probe gives the same complete types, value ASTs and levels for every old owner declaration under only the
  constant map, and identical records for the new ones.
- The E1 and E2 complete frozen types equal their independent records.
- The structured standard-axiom audit (`verify.axiom_audit_code` with `parse_axioms(structured=True)`) over 74 declarations reports
  only standard axioms.
- `leanchecker` replay of the five modules (four owners and the audit) passed.

Metadata changes:
- The Blueprint gains four appended lemmas (E1, E2, the a.e. exponent formula and the actual-source first weak (2.4)). The existing
  nonclaim of `lem:determinant-permutation-differential` now reads "by itself"; this is a documentation qualifier, not a proof,
  statement or source change.
- `nodes.json`, `tasks.json`, `literature.json` (L24 and T25 stay partial), the proof path, `HANDOFF.md` and the root summary are
  synchronized.

Evidence boundary: the ignored `EX-first-MA-integration/` directory is where this package's final full-verification report and Codex
canonical acceptance are to be recorded. The parent receipt `20261014T210925.376591Z` covers only `88b3ca90…`; a passing full report
for the post-integration snapshot is required before final acceptance.

## Next

In dependency order (no further task is dispatched here):
1. Weak inverse and weighted coefficient calculus, and bounded H1 testing.
2. The actual C1/Lipschitz-gradient source-height A.4/A.5 consumption: locally L1 right-hand sides and locally L2 flux, with T² only
   locally L1. The smooth A.4 and the old N13c locally-L2 right-hand side do not apply to the current weak source.
3. The second Hessian evolution identity and the integrated PSD energy comparison (2.14), E tr(BHBH) >= 2 E G1. This is not yet the
   trace-square upper bound.
4. The actual weak Brascamp-Lieb (A.6) and mean-Hessian (Lemma 2.3) consumers, then the final Theorem 2.5 trace-square upper bound
   E tr(BHBH) <= 2 tr(B^2), then Stein/H^-1 and the spectral/regular-class/compact constant-8 assembly. The existing smooth
   given-potential supports do not by themselves close the actual weak-source hypotheses of Lemma 2.3 or A.6.
