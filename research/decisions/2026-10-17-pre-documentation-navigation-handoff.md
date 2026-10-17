# Archived KLS handoff before documentation organization

Archived from `HANDOFF.md` on 2026-10-17. This record preserves the original wording and its dated mathematical scope. Relative Markdown link destinations are rebased to this directory.

Use the [current design](../../LEAN_DESIGN.md) and [current handoff](../../HANDOFF.md) for present interfaces and work.

## Original content

# Current KLS handoff

Updated 2026-10-17 at the integration of BKL Theorem 1.1 and the proof of `KLS.kls`. The previous handoff is preserved
byte for byte in [the dated archive](2026-10-17-pre-bkl-kls-handoff.md). Use the
[proof path](../progress/PROOF-PATH.md) for source-to-Lean navigation and the
[paper register](../progress/LITERATURE.md) for exact scope and coverage.

## Target and current boundary

The four-stage main line is **Letwin constant 8 → stochastic localization → BKL Theorem 4.1 → KLS**. All four stages have
local Lean proofs on the owner-selected route.

**Stage 1 (accepted): Letwin's compact bound.**
- `KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound` is Letwin's Theorem 1.2 for compactly supported
  isotropic log-concave laws with the exact constant 8, certified as `thm:letwin-compact-quadratic-bound`.
- Full report `8e21b1f6…` (snapshot `d90cec22…`), independently accepted (`8927d8b9…`).
- The noncompact Theorem 1.2 is not formalized, and Letwin's paper is not covered
  ([stage-1 record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

**Stage 2 (accepted): stochastic localization.**
- On 2026-10-17 the owner chose the BKL-sufficient cutoff route
  ([stage-2 record](../handoffs/2026-10-17-bkl-step2-stochastic-localization.md)).
- The finite-horizon cutoff form of BKL (95) is certified as `lem:bkl-cutoff-energy`.
- Full report `6644d8bd…` (snapshot `57478318…`), independently accepted (`bbe501c0…`).
- The uncut Eldan process and the literal identities (68)–(73) are not claimed.

**Stage 3 (accepted): BKL Theorem 4.1 in source form.**
- `Solutions.ThmBklCumulantBound.certificate`, registered as `thm:bkl-cumulant-bound`, gives one universal K ≥ 1 for
  every m ≥ 2, every dimension and every isotropic log-concave law
  ([stage-3 record](../handoffs/2026-10-17-bkl-step3-theorem41.md)).
- Full report `build/verification/20261016T203531.078057Z/report.json` (`5d796b69…`) covers snapshot `f245f1fb…`
  (1754 files). Codex independently accepted it (`016c0845…`).

**Stage 4: BKL Theorem 1.1 and KLS** ([stage-4 record](../handoffs/2026-10-17-bkl-step4-kls.md),
[integration and scope review](2026-10-17-bkl-theorem11-kls-integration.md)).
- **Certificate.** `Solutions.ThmBklPoincare.certificate` (`solutions/ThmBklPoincare.lean`, `thm:bkl-poincare`) is BKL
  arXiv:2610.05474v1, Theorem 1.1, in source form: one C > 0 for every n ≥ 1 and every isotropic log-concave law,
  C_P(μ) ≤ C. The client is `research/audits/BKL/KlsAudit.lean`.
- **KLS.** `FunctionalInequalities.KLS.kls : KLS.Conjecture` (`KLS/Target.lean`) is proved through the closed producer
  `KLS.BKL.Localization.conjecture` and the affine/isotropic bridge.
  - The statement of `KLS.Conjecture` is unchanged: one constant, every dimension (0 included), every log-concave law with
    finite second moment, singular supports included.
  - The BKL paper is covered in the exact sense of its main theorem.
- **Source acceptance.** Codex independently accepted the proof sources and the verifier migration (strict compilation,
  standard axioms, kernel replay and literal clients) in the ignored Goal control directory
  `build/reviews/2026-10-17-bkl-step4-kls-goal/` (`codex-source-review/ACCEPTANCE.json`).
- **Verifier.** The declaration audit now covers every project-local declaration, `KLS.kls` included, with no exclusion.
  The exact vendored upstream holes stay isolated.
- **Separate.** The uncut Eldan process, the literal (68)–(73), the uncut forms of Lemmas 4.3, 5.1 and 5.2, Letwin's
  noncompact Theorem 1.2 and the four exploratory routes are separate open results. They are not needed by the selected
  route, and the main theorem does not complete them.

## Evidence

- **Stages 1–3.** The reports above apply only to their recorded snapshots and do not cover later changes.
- **Stage 4.** The integrated stage-4 snapshot is accepted only with a passed full local verification report
  (`python3 research/verify.py`) for that exact source/meta snapshot and its independent acceptance. The Goal checkpoint
  (`build/reviews/2026-10-17-bkl-step4-kls-goal/STATE.json`) records the result. No report hash is written into
  canonical sources; see [receipt scope](../verification.md#receipts-and-trust-scope).

## API status

The API is idle. The integration reuses accepted closed proofs, so no proof construction is outstanding on the selected
route. The sealed stage-1 S3 and S4 runs remain failures; no resend or failed-body repair is authorized.

## Coordination

- **Control.** The Goal is coordinated by the current Codex chat (`01a145d7-889a-7102-b0e9-023428bc2584`), which freezes
  sources, statements, dependencies and placement, then independently accepts.
- **Integration and API.** The original Claude session is the sole canonical integrator. It runs one unchanged
  gpt-6-astra/high API loop at a time (max_rounds 4, max_queries 6), one candidate at a time, only for a genuinely
  missing proof.
- **Not authorized.** No commit, push, tag, remote CI or publication. The old large loops stay stopped.

The [stage-4 record](../handoffs/2026-10-17-bkl-step4-kls.md) holds the completion gates and roles; historical
queues do not override this handoff.
