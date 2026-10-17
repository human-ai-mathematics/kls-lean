# BKL roadmap step 4: Theorem 1.1 and the KLS target

Created on 2026-10-17 at the owner's request in Codex chat `01a145d7-889a-7102-b0e9-023428bc2584`, after the
stage-3 acceptance. The owner authorized continuing the main line to the final KLS target. The Goal's live status is in
the ignored [`STATE.json`](../../build/reviews/2026-10-17-bkl-step4-kls-goal/STATE.json) of
`build/reviews/2026-10-17-bkl-step4-kls-goal/`. This record sets no completion marker.

## Source and target

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Theorem 1.1, p. 2, with its proof on p. 30; pinned PDF SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
- **Paper target.** One universal C > 0 such that every n ≥ 1 and every isotropic log-concave probability law on ℝⁿ have
  C_P(μ) ≤ C, with no added conclusion-bearing hypothesis.
- **Project target.** The unchanged `FunctionalInequalities.KLS.kls : KLS.Conjecture`: one `C : NNReal` before every
  dimension (0 included) and every log-concave law with finite second moment, the intrinsic literature local-slope
  constant, at most `C · ‖Cov‖_op`, with singular affine supports included.
- **Contract.** The source and placement contract is in the control files
  [`SOURCE-INSTRUCTIONS.md`](../../build/reviews/2026-10-17-bkl-step4-kls-goal/SOURCE-INSTRUCTIONS.md) and
  [`SOURCE-CONTRACT.md`](../../build/reviews/2026-10-17-bkl-step4-kls-goal/codex-source-review/SOURCE-CONTRACT.md).

## Integrated state (2026-10-17)

- **Certificate.** `Solutions.ThmBklPoincare.certificate` (`solutions/ThmBklPoincare.lean`) states Theorem 1.1 in source
  form and is registered as `thm:bkl-poincare`
  ([integration and scope review](../decisions/2026-10-17-bkl-theorem11-kls-integration.md)).
- **Proof.** The closed producers `theorem11` and `conjecture` (`KLS/BKL/Theorem41.lean`) apply the existing conditional
  chain to the proved compact Letwin bound:
  - Theorem 4.1 through the accepted cutoff route;
  - Proposition 7.1 and Theorem 3.1;
  - the Section 2 regular approximation;
  - the affine/isotropic reduction.
- **KLS.** `KLS.kls` is `KLS.BKL.Localization.conjecture`. The client `research/audits/BKL/KlsAudit.lean` checks the
  literal statements and consumes the actual target.
- **Verifier.** No local declaration is excluded from the declaration audit; the exact vendored upstream holes stay
  isolated.
- **Acceptance rule.** The milestone requires the exact full receipt and its independent acceptance, recorded in the
  control checkpoint.
- **Separate.** The uncut Eldan process, the literal (68)–(73) and Letwin's noncompact Theorem 1.2 are separate. They
  are not on the selected route.

## Completion gates and roles

**Completion requires:**
- the exact source statement and the unchanged target;
- independently handwritten literal clients;
- standard axioms and local kernel replay, with no excluded local declaration;
- strengthened negative verifier regressions;
- accepted manifest-limited integration and registration;
- progress views synchronized through a new private index;
- a normal build;
- one fresh full real-index local verifier receipt for the exact final source/meta snapshot, followed by Codex's
  independent acceptance.

**Roles.** Codex freezes the source, contract and placement and independently accepts. The original Claude session
`local_4904933f-a611-430d-b4fe-36e2a7f677a2` is the sole sequential canonical writer and integrator. The existing
gpt-6-astra/high API (max_rounds 4, max_queries 6, one candidate at a time) is used only for missing proof obligations;
none remained.

**Not authorized.** No new worker, controller, provider or credential change, and no restart of exhausted runs. No
commit, push, tag, remote CI or publication.

**Preserved.** The real index, the dirty baseline and all historical and failed evidence.
