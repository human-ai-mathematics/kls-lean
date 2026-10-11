# Letwin Lemmas A.4/A.5: source integration (Stage 2A)

Date: 2026-10-11. Controller: Codex chat `01a128eb-e254-7d63-bd15-05abfcb7aaec`; integrator: the sole reviewed Claude
conversation. This record documents the canonical integration of the Stage 2A goal
([goal record](../handoffs/2026-10-11-bkl-a4-goal.md)) and preserves, verbatim, the HANDOFF passages it supersedes.

## Source and statements

Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17) and Lemma A.5 (p. 18).

| Result | Lean | Scope |
| --- | --- | --- |
| Lemma A.4, real parameter | `Analysis.BakryEmery.exists_scaled_cutoffs_hessianInverseOperator` | every potential in the source class (smooth convex `φ`, bounded gradient image `K`, `V` smooth on an open `U ⊇ closure K`, Monge–Ampère, positive definite Hessian, `∫ e^{−φ} dm = 1`), any finite dimension, any additive Haar `m`; every real `R ≥ 1`; one constructed `C` with `∫ |Lχ_R| dν ≤ C/R` |
| Lemma A.4, natural index | `Analysis.BakryEmery.exists_cutoffs_hessianInverseOperator` | `χ_n = χ_{n+1}`, bound `C/(n+1)`; its proof calls the real-parameter construction |
| Lemma A.5 for given cutoffs | `Analysis.BakryEmery.integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs` | cutoff premise explicit; generic core `Analysis.integrable_and_integral_eq_zero_of_cutoff_defect` |
| Source law and test function | `Analysis.BakryEmery.uniformInterval_momentPotential_source_hypotheses`, `uniformInterval_tanhSq_nonconstant_facts` | `φ(y) = 2 log cosh(√3y/2) + log(4/√3)`, `V ≡ log(2√3)`, `K = (−√3, √3)`; `f = tanh²(√3y/2)`, `L f = 1 − 3 tanh²`, `L f + 2f ≥ 0`, `f 0 ≠ f 1`; gradient range inclusion only |
| Nonconstant source-law client | `Analysis.BakryEmery.uniformInterval_tanhSq_integrable_and_integral_hessianInverseOperator_eq_zero` | `L f ∈ L¹(ν)`, `∫ L f dν = 0`, by the source package, the natural-index cutoffs and A.5 (`C = 1`, `c = 2`); no integral-zero premise |

The source-class properties are hypotheses: the moment map of a regular law (Letwin Lemmas 2.1–2.2) is not
constructed. Letwin LA4 is `⇑` (stronger: every real `R ≥ 1`, any potential with those properties), LA5 is partial
(cutoff-given operator form plus one concrete client); Letwin's main Theorem 1.1 is not covered.

## Placement

| Module | Role |
| --- | --- |
| `Analysis/Convex/Coercivity.lean` (new) | minimum and compact sublevels of a convex potential with integrable `e^{−φ}` |
| `Analysis/CutoffConservativity.lean` (new) | generic conservativity from cutoffs with a vanishing defect |
| `Analysis/BakryEmery/HessianOperator.lean` (extended) | self-generator, its bound, composition, coefficient extraction, defect domination, operator continuity |
| `Analysis/BakryEmery/IntegrationByParts/InverseHessian.lean` (extended) | energy identity and bound; A.5 for given cutoffs |
| `Analysis/BakryEmery/IntegrationByParts/InverseHessianCutoff.lean` (new) | Lemma A.4, real parameter and natural index |
| `Analysis/BakryEmery/UniformIntervalPotential.lean` (new) | concrete potential and test-function facts at the MongeAmpere level (no integration-by-parts import) |
| `Analysis/BakryEmery/IntegrationByParts/UniformIntervalClient.lean` (new) | the final client |

The goal record's provisional audit placement of the client was reviewed: the client is a concrete specialization
theorem in the library, and `research/audits/BKL/LetwinUniformIntervalAudit.lean` is its audit (axiom reports and the
used-constant chain). One-use helpers are private; no aliases or wrappers.

## Evidence

Isolated candidates, Codex/Root acceptances and their exact hashes are in
`build/reviews/2026-10-11-bkl-a4-goal-setup/` (support tree v3, `claude-r-actual-client-readiness-v1/` R3,
`claude-t-closed-source-final-freeze-v1/` T, the Root final-client acceptance `ROOT-FINAL-SOURCE-CLIENT-ACCEPTANCE.json`
with the accepted source `final-client-existing-interface-normalizer-v3/candidate.lean`, SHA-256 `6f70011e…`, and the
integration bundles `claude-u-final-integration-readiness-v1/` (doc-only edit map and object comparisons),
`claude-v-current-handoff-correction-v1/` and `claude-w-final-integration-candidate-v1/` (the filled client, identical to
Root's accepted canonical object)). Documentation-only
differences from the accepted sources are listed there; every compiled constant is identical to the accepted objects.
Verification of the integrated snapshot: `python3 research/verify.py`; its result `build/verification/latest.json` counts
only while its status is `passed` and its snapshot hash matches the working tree.

## Superseded HANDOFF passages (verbatim)

The passages are quoted in code blocks, so their repository-root links are inert here; their claims are unchanged.

`HANDOFF.md`, State (latest full local verification, before this integration):

```text
- Latest full local verification: `build/verification/20261010T093056.948739Z/report.json` (scope full, status passed; report
  sha256 `7b258cf3708a0b85b55554db003166fd1ded33bed12cdb30ce952e011b75abe2`, snapshot sha256
  `7e50d2bc4a44d07196d047691ef3d10b544d3c3aa55fc13ea5fd96892317f308`, 1264 snapshot files, 252 gates, 241 strict research
  audits, 835 standard declaration axiom reports, local kernel replay of the 496 owned modules; upstream compiled
  dependencies are trusted, not replayed). It covers everything above, including the adopted Stage 1 integration
  (below). Post-receipt changes: documentation/metadata (this handoff, the staged-goal plan, the rank-1 literature
  next step, regenerated progress views, the Stage 1 receipt history) and, on 2026-10-11, the adopted Letwin
  Lemma A.4 scalar profile (new `Analysis/CutoffProfile.lean`, one aggregate import, the audit
  `BKL/LetwinCutoffProfileAudit.lean` and metadata) and its tail primitive (appended to the same module, with the audit
  `BKL/LetwinCutoffPrimitiveAudit.lean` and metadata), then its affine rescaling and the inverse-Hessian quadratic
  positivity (appended to `CutoffProfile.lean` and `Analysis/BakryEmery/MongeAmpere.lean`, with the audit
  `BKL/LetwinRescalingPositivityAudit.lean` and metadata), and its real-parameter exhaustion (appended to
  `CutoffProfile.lean`, with the audit `BKL/LetwinRealExhaustionAudit.lean` and metadata). These Lean changes are NOT
  covered by this receipt: the current
  Lean snapshot differs from the receipt snapshot, and the new proof delta awaits a new full local receipt. Still open: the SDE/Itô dynamics,
  CEK essential continuity, Euler–Lagrange identification and Theorem 2, the regularity bridge (H2), Letwin's
  quadratic-form bound with constant 8, BKL Theorem 1.1 and `KLS.kls`. Earlier receipts apply to their own snapshots
  only; the previous paragraph is preserved in
  [the 2026-10-10 Stage 1 receipt history](research/decisions/2026-10-10-stage1-receipt-history.md).
```

`HANDOFF.md`, Next (Stage 2A execution notes, before this integration):

```text
The source target is the real-parameter family for every `R >= 1`: smooth compact support, `[0,1]`
bounds, monotone exhaustion, integrable `L chi_R`, and a constructed uniform `C/R` generator-defect
bound. Derive the existing natural-index `C/(n+1)` interface, then apply it with the reviewed A.5
operator argument to an actual nonconstant source-law client. The minimum, compact sublevels,
bounded self-generator and weighted energy estimate must follow from source hypotheses. Independent
semantic/kernel acceptance, canonical integration and a matching full local receipt are completion gates.

The scalar profile/majorant/exhaustion, the Q3 tail primitive, the Q5 rescaling and the Q4R real-parameter exhaustion
are adopted in
`Analysis/CutoffProfile.lean`, and the B1 quadratic positivity in `Analysis/BakryEmery/MongeAmpere.lean`; source A.4
and exact Letwin Theorem 1.2 remain open. The combined A4/A5 supporting candidate is technically
reviewed but not adopted; it was revalidated against the current tree (identical objects, only the aggregate import
list re-merged; `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-a4-a5-joint-refresh-v1/`). Q3 is adopted in source (the original Q3 v6 packet keeps its terminal candidate failure).
The original Q5 and B1 API packets are terminal rejected; their separate explicit-specialization candidates were
independently accepted and are now adopted in source
([rescaling/positivity record](research/decisions/2026-10-11-bkl-a4-rescaling-positivity-supports.md)). Earlier E1
packets keep their own terminal classifications and are not replayed (history in the
[protocol/scheduling record](research/decisions/2026-10-11-bkl-a4-protocol-scheduling-correction.md)); the full original E1 identity is now independently accepted (below). Reconcile authoritative packet records before dispatch, preserve failed histories, and reuse
accepted supports after checking their exact evidence. The latest full receipt still predates scalar adoption.

New Stage 2A progress: the Q3 tail primitive is independently accepted in a separate lint-cleaned
candidate (the original API packet remains failed). Its frozen full type/universes agree without
normalization, all eight actual proof values are standard, and the new scalar module was freshly
kernel-replayed. It is canonically adopted (2026-10-11) from the exact Codex-accepted candidate. Evidence and current
handles are in
[the primitive-support record](research/decisions/2026-10-11-bkl-a4-primitive-support.md) and
`build/reviews/2026-10-11-bkl-a4-goal-setup/STATE.json`. The sole Claude conversation delivered the real-parameter
A.4 interface readiness (`claude-a4-real-scale-readiness-v1/`), now under root review; Q5 and B1 are adopted in source
(original packets terminal rejected); Q4R, the real-parameter exhaustion, is adopted in source after exact copy
verification ([real-exhaustion adoption](research/decisions/2026-10-11-real-exhaustion-adoption.md)).

Connection: the same original authorized connection, key and provider continue, and individual proof units deliberately
pin authorized strong models. The current transport diagnostic (same Astra model) reproduced a chat/completions
incompatibility ("The 'metadata' parameter is only allowed when 'store' is enabled") while `/models` and stateless
`/responses` (`store=false`) return HTTP 200; new requests use that stateless protocol. This does not reclassify earlier
packets: each keeps its own recorded classification or unknown outcome. User-key invalidity or balance exhaustion is not
established, and no owner credential restoration is required
(`build/reviews/2026-10-11-bkl-a4-goal-setup/root-current-controller-20261011/PROTOCOL-DIAGNOSIS.json`). Current units
(authoritative handles in `STATE.json`; consumed requests are never replayed, failed packets preserved):
- E1: the pointwise coefficient extraction (Responses-v2, `root-e1-pointwise-independent-v2`) and the full ORIGINAL
  weighted identity (Responses-v6 over that exact prefix, `root-e1-integral-independent-v6`, two standard values and a
  fresh kernel replay; the original v4 frozen type and universes are raw equal, `e1-original-type-compat`) are
  independently accepted and not in source. The unsent v5 packet (its prefix after the global variables changed the
  universe parameters) is preserved; earlier E1 packets keep their terminal classifications.
- E3: the pointwise defect domination (Responses-v2) is independently accepted after deleting one compiler-reported
  unused tactic; not in source.
- B2: earlier packets keep their own classifications: v1 HTTP429 labelled `invalid_api_key` (not established as a key
  fault), Responses-v2 without a text proof (cause not established), the separately selected strong Sol Responses-v3
  upstream `rate_limit_error` (not a confirmed key or balance fault), and medium Astra Responses-v4, an actual Lean
  proof with basis/API errors (FAILED, retained). The v5 feedback preflight failed only two outside-namespace
  qualification probes (unsent, retained); root owns the v6 feedback preflight
  (`api-b2-operator-continuity-astra-feedback-v6`), no duplicate.
- E2, compact-support assembly, the real-R A4 producer, its natural corollary and the actual nonconstant source-law A5
  client remain open; the client must apply the constructed A4 producer and the A5 operator form, never an assumed
  integral-zero statement (`build/reviews/2026-10-11-bkl-a4-goal-setup/claude-task-h-20261011/dossier/`).

Authoritative handles override old scheduling labels; no source A.4/A.5 or paper-status upgrade is made.
```

`HANDOFF.md`, Uncommitted (the four scalar/support adoption entries, before this integration):

```text
- **Letwin Lemma A.4 real-parameter exhaustion (adopted 2026-10-11; new full local receipt pending):** Codex-accepted
  exact candidate `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-q4r-canonical-candidate-v1/` (patch a33947d2…;
  acceptance `ROOT-Q4R-CANONICAL-ACCEPTANCE.json`, release `root-current-controller-20261011/Q4R-ADOPTION-RELEASE.json`):
  `monotoneOn_and_tendsto_smoothTransition_two_sub_div` appended verbatim to `Analysis/CutoffProfile.lean` (the
  Astra proof with obsolete guessed API names replaced by the exact existing lemmas): for every real `a`,
  `R ↦ η(a/R)` is monotone on `(0, ∞)` and tends to `1`. Blueprint `lem:letwin-cutoff-profile` extended; Letwin LA4
  still partial; audit `research/audits/BKL/LetwinRealExhaustionAudit.lean`. Open: the real-`R` Lemma A.4 producer,
  Lemma A.5 and its nonconstant source-law client, Theorems 2.5 and 1.2. Record:
  [real-exhaustion adoption](research/decisions/2026-10-11-real-exhaustion-adoption.md).
- **Letwin Lemma A.4 rescaling and quadratic positivity (adopted 2026-10-11; new full local receipt pending):**
  Codex-accepted exact candidate `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-q5-b1-canonical-candidate-v1/`
  (patch 94aa6ba8…; acceptance `ROOT-Q5-B1-CANONICAL-ACCEPTANCE.json`): `deriv_comp_sub_div_and_deriv_deriv` appended
  verbatim to `Analysis/CutoffProfile.lean` and `sum_inverseHessianEntry_mul_mul_nonneg` appended verbatim to
  `Analysis/BakryEmery/MongeAmpere.lean` (API proofs with the intended existing lemmas explicitly instantiated).
  Blueprint `lem:letwin-cutoff-profile` extended and new `lem:letwin-inverse-hessian-quadratic`; Letwin LA4 still
  partial; audit `research/audits/BKL/LetwinRescalingPositivityAudit.lean`. Open: the real-`R` Lemma A.4 producer,
  Lemma A.5 and its bounded-gradient source-law client, Theorems 2.5 and 1.2. Record:
  [rescaling/positivity adoption](research/decisions/2026-10-11-rescaling-positivity-adoption.md).
- **Letwin Lemma A.4 tail primitive (adopted 2026-10-11; new full local receipt pending):** Codex-accepted exact
  candidate `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-cutoff-profile-q3-candidate-v1/` (patch 1c8bae61…;
  acceptance `ROOT-Q3-CANONICAL-ACCEPTANCE.json`): `inv_mul_intervalIntegral_div_three_cutoff` appended verbatim to
  `Analysis/CutoffProfile.lean` (the API proof of Q3 v6 with exactly three compiler-reported unused tactics removed):
  `q_R(t) = R⁻¹∫_{t/R}^3 w` is smooth, `q_R′ = −R⁻² w(t/R)`, `0 ≤ q_R ≤ R⁻¹∫_0^3 w`, `q_R = 0` for `t ≥ 3R`. Blueprint
  `lem:letwin-cutoff-profile` and Letwin LA4 (still partial) extended; audit
  `research/audits/BKL/LetwinCutoffPrimitiveAudit.lean`. Open: the real-`R` Lemma A.4 producer, Lemma A.5 and its
  nonconstant source-law client, Theorems 2.5 and 1.2. Record:
  [tail-primitive adoption](research/decisions/2026-10-11-cutoff-primitive-adoption.md).
- **Letwin Lemma A.4 scalar profile (adopted 2026-10-11; new full local receipt pending):** Codex-accepted exact
  candidate `build/reviews/2026-10-10-bkl-stage2-orchestration/claude-cutoff-profile-candidate-takeover-v1/` (patch
  c5dc2f31…): new generic leaf `Analysis/CutoffProfile.lean` (three Mathlib imports) with the independently verified
  API proofs, verbatim: `smoothTransition_two_sub_cutoff` (η(t) = smoothTransition(2 − t), support and derivative
  bound), `exists_majorant_abs_deriv_deriv_smoothTransition_two_sub` (smooth majorant w ≥ |η″|) and
  `monotone_and_tendsto_smoothTransition_two_sub_div_succ` (η(a/(n+1)) ↑ 1). Blueprint `lem:letwin-cutoff-profile`;
  `literature.json` Letwin LA4 partial; audit `research/audits/BKL/LetwinCutoffProfileAudit.lean`. Open: Lemma A.4
  itself (energy estimate, compact support, C/(n+1) defect), Lemma A.5, the moment map, Theorems 2.5 and 1.2; no
  certificate. Record: [cutoff-profile adoption](research/decisions/2026-10-11-cutoff-profile-adoption.md).
```

`HANDOFF.md`, Uncommitted (the metadata entry, before this integration):

```text
- **Metadata:** Blueprint nodes `lem:bkl-*`, `lem:letwin-*`, `prop:bkl-suspension`; `literature.json`
  (BKL2026 P71 `same`, E7274 `⇑`, T11/T41/L42/L43/E67 partial; Letwin2026 CZ14 `⇑`,
  L23/LA3/LA4/T25/D26/L27/L29/LA7/E23/T12 partial); audits
  `research/audits/BKL/*Audit.lean`; progress views regenerated from a temporary index.
```
