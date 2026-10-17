# Weak Hessian evolution (2.6) and bounded H¹ testing: canonical integration

Date: 2026-10-16. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## Provenance

Twelve independently accepted scratch sources were ported into production-shaped owners:
- CP1, Q2, CF1a, IA1 with the full CF1 package, CF2 and B1 (each CODEX_ACCEPT, `independent/<task>` in
  `build/reviews/2026-10-14-letwin-constant-eight-goal/`);
- the closed-reuse GenericRow;
- the H2 bounded-testing assembly (generic, intrinsic and actual-source parts; `H2-bounded-weak-testing-assembly-draft/`,
  attempt05 accepted);
- the actual weighted R0 client of CF2.

Each API task ran once in the existing gpt-6-astra/high loop (max_rounds 4, max_queries 6). Exhausted or failed attempts are
preserved and were not repaired; only the accepted real bodies were used.

- **Placement:** Codex fixed the placement in `weak-evolution-H1-integration/PLACEMENT.md`.
- **Prototype:** Claude recorded the declaration and dedup maps before building the scratch prototype
  (`weak-evolution-H1-integration/DECLARATION-MAP.json`, `PRIVATE-DEDUP-DECISIONS.json`, `SOURCE-MANIFEST.json`). Codex
  accepted the prototype independently (`codex-independent/ACCEPTANCE.json`).
- **Integration:** Claude, the sole canonical writer, copied the six accepted files byte for byte. Codex accepted the
  canonical sources (`canonical-phase1/CODEX-CANONICAL-SOURCE-ACCEPTANCE.json`).
- **Coordination:** the current Codex chat and the original Claude session. No commit, push, tag, remote CI or release is
  authorized.

## Exact scope

Generic tools in `Analysis/WeakDerivative.lean`. Every finite dimension is included, zero included:
- **`Analysis.exists_contDiff_compact_bounded_all_weak_deriv_approximation`** (B1).
  - Hypotheses: η is locally integrable, bounded by C and compactly supported; for every coordinate i, a_i is a weak
    derivative of η along e_i, compactly supported and globally L².
  - Conclusion: there are one compact set S containing the supports of η and every a_i, and one sequence θ_m of smooth
    compactly supported functions such that:
    - θ_m is supported in S and bounded by 3C;
    - every coordinate derivative of θ_m is supported in S and globally L², and converges to a_i in L²;
    - θ_m → η almost everywhere along the full sequence.
  - Not assumed: continuity or C¹ regularity of η, or a positive dimension. The two-direction theorem
    `exists_contDiff_compact_weak_deriv_approximation` is unchanged.
- **`Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test`** (H2, generic part).
  - Hypotheses: J_i is L² on compact sets, F is locally integrable, and ∫ Σᵢ Jᵢ ∂ᵢψ = −∫ F ψ for every compactly supported
    C¹ ψ.
  - Conclusion: for every η as in B1, each Jᵢ aᵢ and F η are integrable and ∫ Σᵢ Jᵢ aᵢ = −∫ F η.

Fixed-object row divergence in `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`:
- **`Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative`** (GenericRow).
  - Hypotheses: u is C¹ with Lipschitz gradient, F is Lipschitz and det H = exp F a.e.; the given inverse-derivative data
    are the weak derivatives −(H⁻¹T_kH⁻¹)_ij of (H⁻¹)_ij, L² on compact sets, with compact-local essential bounds of H⁻¹.
  - Conclusion: for every row b, Σₐ (H⁻¹)_ba ∂ₐF is L² on compact sets, and a.e.
    Σₐ −(H⁻¹T_aH⁻¹)_ba = −Σₐ (H⁻¹)_ba ∂ₐF (the weak Piola row divergence).

New leaf `Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean`. It imports only WeakDerivative,
Lipschitz/Gradient and WeakInverseHessian, and every finite dimension is included:
- **`Analysis.exists_lipschitzWith_weak_fderiv_comp_gradient`** (CP1): for u C¹, Lipschitz, with Lipschitz gradient, and
  W C², each ∂ₐW(∇u) is Lipschitz with the weak derivative Σ_b H_jb ∂_baW(∇u) along e_j, L² on compact sets.
- **`Analysis.hasWeakDerivAlong_mongeAmpere_first_rhs`** (Q2): with a given weak Hessian tensor T (L² on compact sets),
  the first Monge–Ampère right-hand side −∂ᵢu + Σₐ H_ia ∂ₐW(∇u) has the weak derivative
  −H_ji + Σₐ (T_jia ∂ₐW(∇u) + H_ia Σ_b H_jb ∂_baW(∇u)) along e_j, L² on compact sets.
- **`Analysis.localLp_hessian_flux_trace_forcing`** (CF1a): the flux J_ija = Σ_b (H⁻¹)_ba T_bij is L² on compact sets, and
  the forcing C_ij = Q_ij − Σ T_iab D_jba + Σ_b T_bij Σₐ D_aba is locally integrable.
- **`Analysis.integral_weak_hessian_flux_eq_trace_derivative`** (full CF1).
  - Hypotheses: the weak tensor T, the weak inverse data, and a weak derivative Q of tr(H⁻¹T_i) along e_j that is L² on
    compact sets.
  - Conclusion: ∫ Σₐ J_ija ∂ₐψ = −∫ C_ij ψ for every compactly supported C¹ ψ.
  - Proof route: the rough curl identity `integral_weakDeriv_mul_eq_swap` with η = ψ (H⁻¹)_ba, the weak third-derivative
    symmetry and a finite integral balance.
- **`Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram`** (CF2, weighted weak (2.6)).
  - Hypotheses: those above, plus W C², a Lipschitz exponent −u + W(∇u), det H = exp(−u + W(∇u)) a.e. and the first weak
    identity tr(H⁻¹T_i) = −∂ᵢu + Σₐ H_ia ∂ₐW(∇u) a.e.
  - Conclusion: J is L² on compact sets; E_ij = −H_ij + (H ∇²W(∇u) H)_ij + tr(H⁻¹T_iH⁻¹T_j) and e^{−u}E_ij are locally
    integrable; and ∫ e^{−u} Σₐ J_ija ∂ₐψ = −∫ e^{−u} E_ij ψ for every compactly supported C¹ ψ.
- **`Analysis.integral_exp_neg_hessian_flux_eq_curvature_gram_of_bounded_weak_test`** (H2, intrinsic part): the weighted
  identity, with both sides integrable, for every η as in B1.

Not assumed as an input: C² regularity of u, a global inverse bound, global L² of T, or an energy estimate.

Actual source in `KLS/CEK/MomentRegularity.lean`. Both producers take exactly the original R0 regular-source hypotheses
(n > 0) and add no analytic premise:
- **`Analysis.exists_regular_moment_weak_hessian_evolution`.**
  - Retained output: the same u, L, LF and T as `exists_regular_moment_weak_inverse_mean_hessian`, with every R0,
    weak-tensor, first-weak-Monge–Ampère, inverse and mean-Hessian field.
  - New output: the weak derivative of tr(H⁻¹T_i) along every e_j, the unweighted flux identity and the weighted weak (2.6)
    above.
- **`Analysis.exists_regular_moment_bounded_weak_hessian_testing`.**
  - Retained output: the weighted producer at the same witness, with every field.
  - New output: for every compactly supported C¹ ψ and all l, k, i, j, both sides are integrable and
    ∫ e^{−u} Σ_b J_ijb (ψ T_blk + ∂_bψ H_lk) = −∫ e^{−u} E_ij ψ H_lk. These are the bounded H¹ tests ψ·H_lk.
  - The bounded test data of ψ·H_lk come from a private helper (bounded, compactly supported, L², with compact global-L²
    coordinate weak derivatives). The chosen B1 sequence is not a production definition.

Audit `research/audits/BKL/WeakHessianEvolutionAudit.lean`:
- `weighted_evolution_retains_flux_source_contract`: the original full unweighted source contract;
- `bounded_testing_retains_weighted_source_contract`: the original full weighted contract;
- `actual_source_hessian_entry_weak_test`: ψ·H_lk testing with the same u and T;
- `bounded_approximation_zero_dimension`: a client of B1 for n = 0.

**Not claimed:**
- the pointwise smooth Lemma 2.4 and the positivity of its right-hand matrices in the weak setting;
- the weak trace evolution (2.8)/(2.10);
- the actual C¹ source-height cutoffs A.4 with their generator defect, and A.5 consumption;
- the energy comparison (2.14), weak Brascamp–Lieb (A.6) and Theorem 2.5;
- Stein/H⁻¹, compact constant 8, BKL and KLS.

Reviewed supports for the actual C¹ height family exist only as scratch prototypes; they are not canonical. L24 and T25 stay
partial (a reviewed weak route), LA4 keeps its reviewed scope and LA5 stays partial. The 30 ledger certificates, paper
coverage and the four active routes are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/WeakDerivative.lean` | sections `BoundedWeakDerivativeApproximation` (B1) and `BoundedWeakDerivativeTesting` (H2 generic) appended; one module-doc sentence |
| `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean` | section `WeakInverseRowDivergence` appended; last module-doc sentence updated |
| `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean` | new leaf, one section per accepted source in dependency order |
| `formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean` | one import; section `RegularMomentWeakHessianEvolution` (four private helpers, two producers); module-doc (2.6) sentence updated |
| `formalization/FunctionalInequalities.lean` | one import |
| `research/audits/BKL/WeakHessianEvolutionAudit.lean` | new audit |

- No file move, existing namespace change, alias, wrapper or conclusion-bearing structure.
- No generic leaf imports KLS, CEK or audit modules.
- Every existing declaration of the changed owners is unchanged.

Scratch-to-canonical name map (`weak-evolution-H1-integration/DECLARATION-MAP.json`). 42 of 51 scratch declarations keep
their name and visibility; the others are:

| Scratch | Canonical |
| --- | --- |
| public `integral_array_pair_balance` (IA1) | private in `WeakHessianEvolution` (one use) |
| `actual_source_weighted_weak_hessian_evolution` (two byte-identical accepted copies) | `Analysis.exists_regular_moment_weak_hessian_evolution` |
| `actual_source_bounded_weak_hessian_testing` | `Analysis.exists_regular_moment_bounded_weak_hessian_testing` |
| `retains_original_CF1_source_contract` | `WeakHessianEvolutionAudit.weighted_evolution_retains_flux_source_contract` |
| `retains_original_weighted_source_contract_for_bounded_testing` | `WeakHessianEvolutionAudit.bounded_testing_retains_weighted_source_contract` |
| `GenericBoundedTesting` private `tendsto_integral_mul_of_l2` | the existing private `WeakDerivative` helper of identical text (reused) |
| `IntrinsicFluxIA1` private `locallyIntegrable_mul_of_compact_L2` | the identical CF1a copy in the same module |
| `ActualBoundedHessianTesting` private `locallyIntegrable_mul_of_compact_L2` | omitted (no reference) |

- **Private copies:** identical private helpers in different modules (`cutoff_memLp`, `compact_mul_weak_derivative_data`,
  `memLp_top_hessianMatrix_entry_of_isCompact` and two Hessian-coordinate lemmas) remain module-local copies. Sharing them
  would add public API.
- **Binder labels:** six compiler records differ from their scratch origin only by the module component of hygienic binder
  labels.

## Validation

- **Prototype** (Claude, `weak-evolution-H1-integration/`; independently confirmed by Codex):
  - strict compilation of the four owners, the nine downstream modules of their reverse import closure, the aggregate and
    the new audit;
  - the 14 dependent audits;
  - 81 old records identical, and 54 accepted records equal under the explicit map;
  - 134 standard-axiom closures, compiler helpers included;
  - kernel replay.
- **Codex independent acceptance:** strict 15 modules, 134 fresh complete types and data values, seven complete definition
  values and 540 kernel-replayed modules.
- **Canonical source-only check** (`canonical-phase1/attempt01`):
  - strict compilation of the actual canonical sources;
  - all 900 compiled artifact parts are byte-identical to the accepted prototype view;
  - source/meta snapshot `4417517b…`.

Metadata changes:
- The Blueprint gains eleven appended lemmas; existing lemmas are unchanged.
- `nodes.json`, `tasks.json` and `literature.json` are synchronized. L24, T25 and LA5 stay partial, and LA4 keeps its scope.
- The proof path, `HANDOFF.md`, the Goal queue and the root summary are synchronized.
- Evidence pins of the changed owners and the chapter were refreshed after their old values were checked against the saved
  baselines.

Evidence boundary: the full receipt `20261015T121010.942278Z` covers only the snapshot `464d989a…`. Final acceptance requires
a passing full receipt matching the current source/meta snapshot, bound in the ignored `weak-evolution-H1-integration/` final
acceptance/completion records; inspect `build/verification/latest.json` and the exact report.

## Next

In dependency order (no task is dispatched here):
1. The actual C¹/Lipschitz-gradient source-height cutoffs (A.4), with an integrable generator defect bounded by C/R, and
   their A.5 consumption.
2. The integrated energy comparison (2.14), E tr(BHBH) ≥ 2 E G₁.
3. The actual weak Brascamp–Lieb (A.6) consumer and the Theorem 2.5 upper bound E tr(BHBH) ≤ 2 tr(B²).
4. Stein/H⁻¹ and the spectral/regular-class/compact constant-8 assembly.
