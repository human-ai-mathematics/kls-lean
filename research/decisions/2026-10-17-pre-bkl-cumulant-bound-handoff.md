# Current KLS handoff

Updated 2026-10-17 at the canonical integration of the stage-2 cutoff energy certificate. The previous handoff is preserved
byte for byte in [the dated archive](research/decisions/2026-10-17-pre-bkl-cutoff-energy-handoff.md).
Use the [proof path](research/progress/PROOF-PATH.md) for source-to-Lean navigation and the
[paper register](research/progress/LITERATURE.md) for exact scope and coverage.

## Target and current boundary

The four-stage main line is **Letwin constant 8 → stochastic localization → BKL Theorem 4.1 → KLS**.

**Stage 1 is sealed in its exact compact form.** `KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound`
(`formalization/FunctionalInequalities/KLS/Letwin/CompactBound.lean`) gives, for every n > 0, every compactly supported
isotropic log-concave probability law on `EuclideanSpace ℝ (Fin n)` and every self-adjoint real operator (singular and
indefinite included), `Var_μ ⟨M X, X⟩ ≤ 8 ∑ᵢⱼ ⟨M eᵢ, eⱼ⟩²` in the standard orthonormal basis. It is certified in source
form as `thm:letwin-compact-quadratic-bound` (`solutions/ThmLetwinCompactQuadraticBound.lean`; Letwin arXiv:2607.24164v1,
Theorem 1.2, compact counterpart; the input of BKL arXiv:2610.05474v1, Lemma 4.2). The noncompact Theorem 1.2, Letwin's
Theorem 1.1, the smooth source Lemma 2.2/Theorem 2.5 and the target Stein kernel of Lemma 2.7 are not formalized;
Letwin's paper is not covered. The [stage-1 Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)
and the [integration record](research/decisions/2026-10-16-letwin-compact-eight-integration.md) give the proof chain.

**Stage 2 is the active Goal** ([Goal record](research/handoffs/2026-10-17-bkl-step2-stochastic-localization.md)); its live status is recorded in the
ignored Goal control files `STATE.json` and `NEXT-CHECKPOINT.json`. Its source is BKL arXiv:2610.05474v1 **Sections 4–6**: Eldan
localization and the cumulant and energy equations (67)–(79), Lemmas 5.1–5.2, and their use in the induction (95) of
Section 6. Section 5 alone is not the source.
- **Existing route.** The development in `KLS/BKL/Localization/` and `Probability/Diffusion/` is a cutoff-only route.
  It solves (67) with ball-cutoff coefficients and uses the dynamics only through Dynkin identities for generator
  formulas.
- **Accepted so far.** Codex independently accepted this route against the source ([`ACCEPTANCE-v3.json`](build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/independent-current/ACCEPTANCE-v3.json): all 41 mapped declarations
  probed at full elaboration with standard axioms, and the 913 filtered compiled parts exact).
- **Formalized and registered endpoint.** The endpoint is frozen in [`FROZEN-ENDPOINT.json`](build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/FROZEN-ENDPOINT.json): `SourceCutoffEstimate d` for every d ≥ 1. This is the expanded
  finite-horizon cutoff form of (95), with the exact factor ½, the universal constant 153 and the (d!)² normalization.
  It holds for every compactly supported isotropic log-concave prior, unit direction, ε > 0 and horizon T, every
  sufficiently large cutoff radius R, and every actual cutoff process.
  - It is registered as the supporting certificate `lem:bkl-cutoff-energy`: `solutions/LemBklCutoffEnergy.lean`, with
    the independent client `research/audits/BKL/CutoffEnergyAudit.lean`
    ([integration record](research/decisions/2026-10-17-bkl-cutoff-energy-integration.md)).
  - It uses the actual compact constant-8 theorem and does not import `Theorem41`.
  - It is a restricted, different-route counterpart of (95), not the source's infinite-horizon uncut statement.
  - Milestone acceptance requires a passed full local report for the exact integrated source/meta snapshot and its
    independent acceptance, both recorded in the Goal control checkpoint.
- **Scope (chosen by the owner).** On 2026-10-17 the owner explicitly chose to accept the BKL-sufficient cutoff route
  and then continue to stage 3 ([`USER-SCOPE-CHOICE-20261017.md`](build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/USER-SCOPE-CHOICE-20261017.md)). The full
  uncut construction remains open and is not claimed.
- **Not proved, kept open.** The uncut Eldan process (strong solution, uniqueness, non-explosion) and the literal
  stochastic identities (68)–(73). No completion is claimed.

**Stages 3–4 are queued.** BKL `theorem41`/`theorem41Compact` and `conjecture_of_letwinCompact` keep
`LetwinCompactBound` as an explicit hypothesis. No composition with `letwinCompactBound` is added or claimed.
`KLS.kls` remains the intentional hole outside certificate closures; dimension-free KLS is open.

## Evidence

- **Stage 1.** The fresh full local report `build/verification/20261016T163852.065444Z/report.json` (SHA-256
  `8e21b1f6…`) covers source/meta snapshot `d90cec22…` (1741 entries, HEAD `2c3e369`), and Codex's independent full
  acceptance (`8927d8b9…`) seals the milestone. That report applies only to that snapshot. It does not cover this
  documentation update or any later change.
- **Stage 2.** Claude's source audit and Codex's independent acceptance are in the ignored Goal control directory
  `build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/` (`claude-audit/`, [`ACCEPTANCE-v3.json`](build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/independent-current/ACCEPTANCE-v3.json)). The corrected source map has
  standard axioms for all 41 mapped declarations, and the frozen endpoint is [`FROZEN-ENDPOINT.json`](build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/FROZEN-ENDPOINT.json). The certificate and its client are registered;
  the full report and independent acceptance for the integrated snapshot belong to the control checkpoint.
- **Acceptance rule.** A later milestone is accepted only with a passed full local verification report
  (`python3 research/verify.py`) for its exact source/meta snapshot and its independent acceptance; see
  [receipt scope](research/verification.md#receipts-and-trust-scope).

## API status

The API is idle. The frozen endpoint's closed assembly is already accepted, so no new proof construction is needed, and
no task is sent merely to reproduce accepted work.
The sealed S3 and S4 runs of stage 1 remain failures; no resend or failed-body repair is authorized.

## Next obligations and coordination

1. Stage 2 milestone acceptance: a passed full local verification report for the exact integrated source/meta snapshot
   on the real index, and its independent acceptance, recorded in the control checkpoint. The full uncut construction
   stays open and separate.
2. Stage 3, after that acceptance: a source-form review of BKL Theorem 4.1 (`theorem41`, `theorem41Compact`) and its statement.
3. Stage 4: only after stages 2–3 are accepted, review the composition with `conjecture_of_letwinCompact`; `KLS.kls` stays
   open until that exact statement is proved and verified.

The noncompact Letwin Theorem 1.2 is not on the BKL critical path, which consumes only the compact bound.

- **Control.** The Goal is coordinated by the current Codex chat (`01a145d7-889a-7102-b0e9-023428bc2584`), which freezes
  sources, statements, dependencies and placement, then independently accepts.
- **Integration and API.** The original Claude session is the sole canonical integrator. It runs one unchanged
  gpt-6-astra/high API loop at a time (max_rounds 4, max_queries 6), one candidate at a time.
- **Not authorized.** No commit, push, tag, remote CI or publication. The old large loops stay stopped.

The [Goal record](research/handoffs/2026-10-17-bkl-step2-stochastic-localization.md) holds the completion gates and
roles; historical queues do not override this handoff.
