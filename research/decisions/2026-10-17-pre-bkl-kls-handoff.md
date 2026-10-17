# Current KLS handoff

Updated 2026-10-17 at the canonical integration of the stage-3 BKL Theorem 4.1 certificate. The previous handoff is
preserved byte for byte in [the dated archive](research/decisions/2026-10-17-pre-bkl-cumulant-bound-handoff.md).
Use the [proof path](research/progress/PROOF-PATH.md) for source-to-Lean navigation and the
[paper register](research/progress/LITERATURE.md) for exact scope and coverage.

## Target and current boundary

The four-stage main line is **Letwin constant 8 → stochastic localization → BKL Theorem 4.1 → KLS**.

**Stage 1 (accepted).** `KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound`
(`formalization/FunctionalInequalities/KLS/Letwin/CompactBound.lean`) is Letwin's Theorem 1.2 for compactly supported
isotropic log-concave laws with the exact constant 8, certified as `thm:letwin-compact-quadratic-bound`. Full report
`8e21b1f6…` for snapshot `d90cec22…`, independently accepted (`8927d8b9…`). The noncompact Theorem 1.2 is not formalized;
Letwin's paper is not covered ([stage-1 record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

**Stage 2 (accepted).** On 2026-10-17 the owner explicitly chose the BKL-sufficient cutoff route
([stage-2 record](research/handoffs/2026-10-17-bkl-step2-stochastic-localization.md)).
- **Certified.** The finite-horizon cutoff form of BKL (95) for every order is certified as `lem:bkl-cutoff-energy`
  (`solutions/LemBklCutoffEnergy.lean`).
- **Accepted.** Full report `build/verification/20261016T191359.457574Z/report.json` (`6644d8bd…`) covers snapshot
  `57478318…`, and Codex independently accepted it (`bbe501c0…`).
- **Open.** The uncut Eldan process (strong solution, uniqueness, non-explosion) and the literal stochastic identities
  (68)–(73) remain open and are not claimed.

**Stage 3: BKL Theorem 4.1 in source form** ([Goal record](research/handoffs/2026-10-17-bkl-step3-theorem41.md)). The
Goal's live status is recorded in the ignored control files `STATE.json` and `NEXT-CHECKPOINT.json` of
`build/reviews/2026-10-17-bkl-step3-theorem41/`.
- **Certificate.** `Solutions.ThmBklCumulantBound.certificate` (`solutions/ThmBklCumulantBound.lean`, registered as
  `thm:bkl-cumulant-bound`, client `research/audits/BKL/CumulantBoundAudit.lean`) states BKL arXiv:2610.05474v1,
  Theorem 4.1, (65)–(66).
- **Statement.** There is one universal K ≥ 1 (witness 153) such that, for every order m = d + 1 ≥ 2 (the base m = 2
  included), every dimension, every isotropic log-concave probability measure (no compactness, Letwin, moment, energy
  or induction premise) and every u, Σ κ_m(u, e_{i₂}, …, e_{i_m})² ≤ K^{m−1}((m−1)!)² ‖u‖².
- **Proof.** It uses the accepted stage-2 cutoff route and the compact-to-general passage `cumulantBound_of_compact`
  ([integration record](research/decisions/2026-10-17-bkl-cumulant-bound-integration.md)): the same conclusion through
  a different route, plus a harmless extension to dimension 0.
- **Acceptance rule.** Milestone acceptance requires a passed full local report for the exact integrated source/meta
  snapshot and its independent acceptance, both recorded in the control checkpoint.

**Stage 4: KLS.** BKL Theorem 1.1 and the KLS composition come after stage-3 acceptance and are not added.
`theorem41`, `theorem41Compact` and `conjecture_of_letwinCompact` keep `LetwinCompactBound` as an explicit hypothesis.
`KLS.kls` remains the intentional hole outside certificate closures; dimension-free KLS is open.

## Evidence

- **Stages 1–2.** The reports above apply only to their recorded snapshots and do not cover later changes.
- **Stage 3.**
  - **Source review.** Codex's independent review of the final certificate and client bytes (strict compilation, the
    literal m ≥ 2 specification, standard axioms, kernel replay) is in the ignored Goal control directory
    (`codex-source-review/ACCEPTANCE-v2.json`). It covers the module-header correction that names the ledger id, a
    documentation-only change. The earlier run03 acceptance and the metadata-prototype v1/v2 failures are preserved.
  - **Current snapshot.** The certificate and client are registered. The full report and independent acceptance for
    the integrated snapshot belong to the control checkpoint.
- **Acceptance rule.** A milestone is accepted only with a passed full local verification report
  (`python3 research/verify.py`) for its exact source/meta snapshot and its independent acceptance; see
  [receipt scope](research/verification.md#receipts-and-trust-scope).

## API status

The API is idle. The certificate reuses accepted closed proofs, so no new proof construction is needed. The sealed
stage-1 S3 and S4 runs remain failures; no resend or failed-body repair is authorized.

## Next obligations and coordination

1. Stage 3 milestone acceptance: a passed full local verification report for the exact integrated source/meta snapshot
   on the real index, and its independent acceptance, recorded in the control checkpoint.
2. Stage 4, after that acceptance: BKL Theorem 1.1 and the KLS composition through `conjecture_of_letwinCompact`.
   `KLS.kls` stays open until that exact statement is proved and verified.

The full uncut Eldan construction and Letwin's noncompact Theorem 1.2 stay separate; neither is on the selected BKL
critical path.

- **Control.** The Goal is coordinated by the current Codex chat (`01a145d7-889a-7102-b0e9-023428bc2584`), which freezes
  sources, statements, dependencies and placement, then independently accepts.
- **Integration and API.** The original Claude session is the sole canonical integrator. It runs one unchanged
  gpt-6-astra/high API loop at a time (max_rounds 4, max_queries 6), one candidate at a time, only for a genuinely
  missing proof.
- **Not authorized.** No commit, push, tag, remote CI or publication. The old large loops stay stopped.

The [Goal record](research/handoffs/2026-10-17-bkl-step3-theorem41.md) holds the completion gates and roles;
historical queues do not override this handoff.
