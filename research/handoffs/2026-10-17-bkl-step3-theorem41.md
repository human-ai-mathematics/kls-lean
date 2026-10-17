# BKL roadmap step 3: Theorem 4.1 in source form

Created on 2026-10-17 at the owner's request in Codex chat `01a145d7-889a-7102-b0e9-023428bc2584`, after the
stage-2 acceptance. The Goal's live status is in the ignored
[`STATE.json`](../../build/reviews/2026-10-17-bkl-step3-theorem41/STATE.json) of
`build/reviews/2026-10-17-bkl-step3-theorem41/`. This record sets no completion marker.

## Source and target

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Theorem 4.1, p. 18, (65)–(66); pinned PDF SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
- **Exact target.** One universal K ≥ 1 for all dimensions, every isotropic log-concave probability law (no
  compactness or extra moment premise), every m ≥ 2 including the base, and every real direction u: the sum in (65) is
  at most K^(m−1)·((m−1)!)²·‖u‖².
- **Contract.** The source and placement contract is in the control files
  [`SOURCE-CONTRACT.json`](../../build/reviews/2026-10-17-bkl-step3-theorem41/SOURCE-CONTRACT.json) and
  [`TASK.md`](../../build/reviews/2026-10-17-bkl-step3-theorem41/TASK.md).

## Current state (2026-10-17)

- **Certificate.** `Solutions.ThmBklCumulantBound.certificate` (`solutions/ThmBklCumulantBound.lean`) states the
  target with K = 153, for every order m = d + 1 ≥ 2 and every dimension (n = 0 included). It is registered as
  `thm:bkl-cumulant-bound` ([integration record](../decisions/2026-10-17-bkl-cumulant-bound-integration.md)).
- **Proof.** It uses the stage-2 cutoff route (`lem:bkl-cutoff-energy`, with the actual compact constant-8 theorem) and
  the compact-to-general passage `cumulantBound_of_compact`. It does not import `Theorem41`.
- **Client.** `research/audits/BKL/CumulantBoundAudit.lean` handwrites the source-index specification and consumes
  the closed certificate for an arbitrary law.
- **Acceptance rule.** Milestone acceptance requires the exact full receipt and its independent acceptance in the
  control checkpoint.
- **Next.** Stage 4 (Theorem 1.1 and the KLS composition) follows that acceptance. The uncut Eldan process and the
  literal (68)–(73) remain open.

## Completion gates and roles

**Completion requires:**
- the exact source statement;
- independently handwritten strict full-specification and substantive clients;
- standard axioms and local kernel replay;
- accepted manifest-limited integration and registration;
- progress views synchronized through a new private index;
- one fresh full real-index local verifier receipt for the exact final source/meta snapshot, followed by Codex's
  independent acceptance.

**Roles.** Codex freezes the source, contract and placement and independently accepts. The original Claude session
`local_4904933f-a611-430d-b4fe-36e2a7f677a2` is the sole sequential canonical writer and integrator. The existing
gpt-6-astra/high API (max_rounds 4, max_queries 6, one candidate at a time) is used only for missing proof obligations.

**Not authorized.** No new worker, controller, provider or credential change, and no restart of exhausted runs. No
commit, push, tag, remote CI or publication.

**Preserved.** The real index, the dirty baseline and all historical and failed evidence.
