# Weak inverse-Hessian height cutoffs (C¹ Lemma A.4 counterpart): canonical integration

Date: 2026-10-16. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## Provenance

- **API core.** `exists_C1_height_generator_defect_bound` (frozen task A4-C1-height-generator-defect) was accepted by the
  existing gpt-6-astra/high loop (round 2 of 4, 1 of 6 queries; the round-1 failure is preserved in the sealed 937-file run)
  and then independently accepted (`independent/A4`). The integration uses only that accepted core, made private.
- **Closed assemblies.** The full real/natural cutoff families (`A4-full-C1-cutoff-family-assembly-draft`, attempt02) and the
  actual-source producer with the χ_R·H_lk client (`actual-source`, attempt02) were independently accepted as closed
  assemblies. The root `BODY.lean.txt` draft was not used.
- **Placement and prototype.**
  - Codex fixed the placement in `weak-cutoff-integration/PLACEMENT.md`.
  - Claude built the production-shaped prototype with recorded maps (`DECLARATION-MAP.json`, `PRIVATE-DEDUP-DECISIONS.json`,
    `SOURCE-MANIFEST.json`).
  - Codex accepted the prototype independently (`codex-independent/ACCEPTANCE.json`).
- **Integration.** Claude, the sole canonical writer, copied the four accepted files byte for byte. Codex accepted the canonical
  sources (`canonical-phase1/CODEX-CANONICAL-SOURCE-ACCEPTANCE.json`) after rebuilding a clean view (`codex-independent-attempt02`).
- **Coordination.** No commit, push, tag, remote CI or release is authorized.

## Exact scope

Generic leaf `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessianCutoff.lean`. Every finite dimension is included, zero
included:
- **`Analysis.exists_scaled_weak_inverse_hessian_cutoffs`.**
  - Hypotheses: u is C¹, Lipschitz, with Lipschitz gradient, convex and normalized (∫ e^{−u} = 1); V is C¹; the exponent
    −u + V(∇u) is Lipschitz; det ∇²u = exp(−u + V(∇u)) and ∇²u is positive definite almost everywhere.
  - Conclusion: there are one shift c and one constant C ≥ 0 with u − c ≥ 1 such that, for χ_R = smoothTransition(2 − (u − c)/R),
    every real R ≥ 1 gives:
    - χ_R is C¹, compactly supported, has Lipschitz gradient and takes values in [0, 1];
    - χ_R is monotone in R and tends to 1 pointwise;
    - the literal generator L χ_R = tr((∇²u)⁻¹ ∇²χ_R) − DV(∇u)(∇χ_R) is integrable for ν = e^{−u} dx;
    - ∫ |L χ_R| dν ≤ C/R, and this defect tends to 0.
- **`Analysis.exists_weak_inverse_hessian_cutoffs`:** the same family at R = m + 1, with the bound C/(m + 1).
- **Derived, not assumed:** the drift bound, sublevel compactness/coercivity, the majorant and the defect bound.
- **Private:** the 19 one-use supports, including the accepted API core.

Actual source in `KLS/CEK/MomentRegularity.lean`:
- **`Analysis.exists_regular_moment_weak_cutoffs`.**
  - Hypotheses: exactly the original R0 regular-source hypotheses (n > 0).
  - Retained output: the same u, L, LF and T, with the WHOLE payload of `exists_regular_moment_bounded_weak_hessian_testing`
    (R0, tensor, inverse, mean, first Monge–Ampère, trace derivative, unweighted and weighted (2.6), bounded ψ·H tests).
  - New output: one common c and C with the full real-parameter cutoff family above for this u and W.
  - Not added: any source premise or D/Γ bookkeeping.

Audit `research/audits/BKL/WeakInverseHessianCutoffAudit.lean`:
- `weak_cutoffs_retain_bounded_testing_source_contract`: the whole bounded-testing contract is retained.
- `actual_source_cutoff_hessian_entry_test`: at one u/L/LF/T/c/C, for every R ≥ 1 and all l, k, i, j, both pairing
  integrabilities and the weighted weak (2.6) identity hold for the bounded tests χ_R·H_lk.

Relation to the paper:
- The classical Lemma A.4 for smooth source-class potentials (`exists_scaled_cutoffs_hessianInverseOperator`, reviewed
  stronger) is unchanged.
- The new family is its C¹/Lipschitz-gradient counterpart for the actual weak source. It is not a C^∞ cutoff family, does not
  give the smooth moment map of Lemma 2.2, and adds no paper coverage.

**Not claimed:**
- A.5 consumption;
- the finite contraction of the χ·H weak (2.6) tests to the trace-quadratic density (2.8)/(2.10) and its positivity;
- the energy comparison (2.14), weak Brascamp–Lieb (A.6) and Theorem 2.5;
- Stein/H⁻¹, compact constant 8, BKL and KLS.

Reviewed scratch packets (global bounded weak cutoff testing, bounded weak trace data, an actual same-source trace cutoff
client) are research evidence only and are not canonical. L24, T25 and LA5 stay partial, and LA4 keeps its reviewed stronger
relation. The 30 ledger certificates, paper coverage and the four active routes are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakInverseHessianCutoff.lean` | new leaf: the accepted family text byte for byte after a module docstring; six imports, no CEK/KLS/audit import |
| `formalization/FunctionalInequalities/KLS/CEK/MomentRegularity.lean` | one import; section `RegularMomentWeakCutoffs` with the accepted producer; producer docstring and one module-doc sentence |
| `formalization/FunctionalInequalities.lean` | one import |
| `research/audits/BKL/WeakInverseHessianCutoffAudit.lean` | new audit (retention theorem and χ_R·H_lk client) |

Scratch-to-canonical map (`weak-cutoff-integration/DECLARATION-MAP.json`):
- The 22 production declarations retain their mathematical namespace, short names and visibility. The two audit
  declarations move to the audit namespace; the retention theorem is renamed. The API core is private in the leaf, a
  visibility change already reviewed.
- `retains_original_bounded_source_contract_for_weak_cutoffs` →
  `WeakInverseHessianCutoffAudit.weak_cutoffs_retain_bounded_testing_source_contract`.
- `actual_source_cutoff_hessian_entry_test` → `WeakInverseHessianCutoffAudit.actual_source_cutoff_hessian_entry_test`.
- The 19 private names are unique in the leaf. Two helpers keep module-local copies of identical private helpers in other
  modules, and none was promoted.
- Two private records differ from their scratch origin only by the module component of hygienic binder labels.

## Validation

- **Prototype** (Claude; independently confirmed):
  - strict compilation of the four modules and the eight dependent audits;
  - 14 old MomentRegularity records identical and 28 accepted records equal under the map;
  - 42 standard-axiom closures and three direct kernel replays.
- **Codex:** 42 complete types/levels compared structurally, one data value, and 541 kernel-replayed modules.
- **Canonical source-only check:**
  - strict compilation of the canonical sources, 42 standard-axiom closures and three direct kernel replays;
  - all 900 production parts and the audit part are byte-identical to the accepted prototype view;
  - source/meta snapshot `cf69081a…`;
  - Codex's clean rebuild (`canonical-phase1/codex-independent-attempt02/compiled`) is the authoritative proof cache.
- **Extra artifact:** an extra file `FunctionalInequalities 2.olean`, byte-identical to the old registered root, appeared in the
  native check directory after its report. It is preserved, is not used on any proof path, and its producer was not determined.

Metadata changes:
- The Blueprint gains three appended lemmas.
- `nodes.json`, `tasks.json` and `literature.json` are synchronized; L24, T25 and LA5 stay partial, and LA4 keeps its relation.
- The proof path, `HANDOFF.md`, the Goal queue and the root summary are synchronized.
- Evidence pins of the changed owner and chapter were refreshed after their old values were checked against the saved baselines.

Evidence boundary: the full receipt `20261016T033139.894094Z` covers only the snapshot `3a87e101…`. Final acceptance requires a
passing full receipt matching the current source/meta snapshot, bound in the ignored `weak-cutoff-integration/` final
acceptance/completion records; inspect `build/verification/latest.json` and the exact report.

## Next

In dependency order (no task is dispatched here):
1. The finite contraction of the actual χ·H weak (2.6) tests to the distributional trace-quadratic density (2.8)/(2.10), its
   positivity, and the actual A.5 consumption.
2. The integrated energy comparison (2.14), E tr(BHBH) ≥ 2 E G₁.
3. The actual weak Brascamp–Lieb (A.6) consumer with the mean Hessian Id, giving Theorem 2.5's upper bound.
4. Stein/H⁻¹ and the spectral/regular-class/compact constant-8 assembly.
