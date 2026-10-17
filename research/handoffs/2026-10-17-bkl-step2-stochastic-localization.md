# BKL roadmap step 2: stochastic localization

Created 2026-10-17 by the human in Codex chat `01a145d7-889a-7102-b0e9-023428bc2584`. The Goal tool is ACTIVE without an invented token budget or deadline. Stage 1 is sealed in its exact compact form; stages 3 (BKL Theorem 4.1) and 4 (KLS) remain separate.

## Current state (2026-10-17)

The Goal's live status is in the ignored [`STATE.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/STATE.json) and
[`NEXT-CHECKPOINT.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/NEXT-CHECKPOINT.json). Source: BKL arXiv:2610.05474v1 Sections 4–6.
- **Scope (chosen by the owner).** On 2026-10-17 the owner explicitly chose to accept the BKL-sufficient cutoff route
  and then continue to stage 3 ([`USER-SCOPE-CHOICE-20261017.md`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/USER-SCOPE-CHOICE-20261017.md)).
  The full uncut construction remains open and is not claimed.
- **Accepted.** The existing cutoff-only route (`KLS/BKL/Localization/`, `Probability/Diffusion/`) is independently
  accepted against the source ([`independent-current/ACCEPTANCE-v3.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/independent-current/ACCEPTANCE-v3.json)).
- **Frozen endpoint.** `SourceCutoffEstimate d` for every d ≥ 1
  ([`FROZEN-ENDPOINT.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/FROZEN-ENDPOINT.json)). It is the expanded finite-horizon cutoff (95), with the exact ½,
  153 and (d!)² normalization, every ε, T, every sufficiently large R and every actual cutoff process.
  - It is formalized and registered as the supporting certificate `lem:bkl-cutoff-energy`
    (`solutions/LemBklCutoffEnergy.lean`; record
    [`2026-10-17-bkl-cutoff-energy-integration`](../decisions/2026-10-17-bkl-cutoff-energy-integration.md)).
  - Milestone acceptance requires the exact full receipt and its independent acceptance in the control checkpoint.
- **Not proved.** The uncut Eldan process (strong solution, uniqueness, non-explosion) and the literal stochastic
  identities (68)–(73).
- **Next.** Stage 3, the source-form BKL Theorem 4.1, follows the stage-2 milestone acceptance. This record sets no
  completion marker.
- **Idle.** The API is idle: the accepted closed assembly needs no new proof construction.
- **Queued.** Stages 3 (BKL Theorem 4.1) and 4 (KLS).

## Source and endpoint

Pinned source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, PDF SHA256 `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`. Section 4 introduces Eldan localization (67), the posterior/moment equations (68)–(71), cumulants (72)–(73) and energy normalization (75)–(79); Section 5 supplies Lemmas 5.1–5.2; Section 6 consumes them in (95). The preceding handoff's shorthand “Section 5 stochastic localization” is broadened to the actual Sections 4–6, without changing historical records.

The target is the stochastic-localization machinery for this exact BKL main line, retaining compact isotropic log-concave laws, all finite dimensions n>0, inverse-covariance quadratic variation, the factor one half, the exact constant8 input and the original cumulant/order normalization. No desired variance, covariance-decay, energy bound, process existence or non-explosion may be inserted as an assumed premise. The final source/Lean interface is frozen after auditing the existing implementation. Source-required stochastic statements and an accepted alternative proof sufficient for the same downstream theorem are recorded separately. Existing cutoff-only results cannot be relabelled as construction of the global uncut process, uniqueness, or the literal (68)–(73).

Completion requires: a reviewed source-to-Lean obligation table; exact frozen endpoint(s), without a weaker replacement; independently accepted proof(s) and substantive clients; no sorry or nonstandard axiom in their closures; local kernel replay; accepted placement and canonical integration; correct source provenance and coverage; synchronized English handoff/progress views; a fresh full `python3 research/verify.py` receipt for the final source/meta snapshot, with source and compiled-input drift checks. A proof inventory, an API dispatch, or a conditional interface alone does not close this Goal. Full uncut process claims require actual construction and non-explosion/uniqueness evidence; a cutoff route is labelled explicitly as such and must prove every consumer obligation.

## Existing evidence and initial frontier

The exact compact Letwin endpoint and certificate passed Codex full acceptance at snapshot `d90cec225de9e49bf8e5a2b3c43923e7c6aede516db0e07d7f0cf4ed62330e39`, HEAD `2c3e36926eb63f77750f19f9608c6d84c4d056b9`. Full report [`build/verification/20261016T163852.065444Z/report.json`](../../build/verification/20261016T163852.065444Z/report.json) SHA256 `8e21b1f6d58d723d37132a4972f4f327cd2c22f2875481231475789186e99328`: 292 gates, 161 Python tests, 278 strict audit clients, 9824 audited project declarations, 827 kernel-replayed modules, 913 registered compiled parts. Codex confirmed all 1741 source/meta hashes still match at this Goal's baseline. The old receipt will not certify later documentation or proof changes.

The existing `KLS/BKL/Localization/` family and `Probability/Diffusion/` provide a substantial cutoff route. Initial Codex strict checks confirmed standard axioms for existence, Dynkin, Q PSD, Lyapunov moments/tails, cumulant/energy generators and cutoff induction. A scratch assembly `Stage2Independent.all_cutoff_orders` discharges the actual compact8 input and proves all-order `CutoffEnergyClaim 153 d` without importing Theorem41; strict compilation and local kernel replay passed. This is reuse/diagnostic evidence, not a canonical theorem, new certificate or completion claim. The uncut process and literal stochastic equations require a separate audit.

## Roles and dispatch protocol

Codex freezes the source, exact contracts, dependency order and placement and independently accepts. The original Claude Code session `local_4904933f-a611-430d-b4fe-36e2a7f677a2` (LevyStochCalc source-lock validation) operates the existing API loop and is the sole canonical integrator after Codex acceptance and placement review. No new worker or sub-controller is introduced. Use the existing provider/configuration and `gpt-6-astra/high`, max_rounds=4 and max_queries=6, one candidate at a time. Preserve failures; exhausted tasks require diagnosis and a genuinely reviewed smaller contract. No equivalent resend to evade limits. Do not call an API merely to repeat a proof that is already accepted. The old heartbeat and old large loops remain stopped.

Preserve the dirty tree, real index entries/flags and all historical evidence. Temporary indexes are for progress generation only, never full verification. No commit, push, tag, remote CI, publication, provider/model/credential changes or credit purchase is authorized. Generic supports stay in their owning mathematical families; BKL-specific constructions remain in `KLS/BKL/Localization/`, independent clients in `research/audits/BKL/`. Every new/split module or public API receives a placement plan under the current workflow/naming rules before canonical editing.

## Control records

This record was placed by Claude on 2026-10-17 from the control copy [`GOAL.md`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/GOAL.md) in the ignored Goal control directory [`build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/). [`baseline/BASELINE.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/baseline/BASELINE.json) and the full source manifest [`baseline/SOURCE-MANIFEST.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/baseline/SOURCE-MANIFEST.json) preserve the starting snapshot and actual index. [`STATE.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/STATE.json) tracks this Goal; the old stage1 STATE/NEXT and acceptance files remain untouched. Claude writes only to the areas authorized by the current dispatch (initially [`claude-audit/`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/claude-audit/)). The API is idle until a genuine missing contract, frozen packet and independent validator are ready.

## Initial source audit checkpoint (2026-10-17)

Claude's audit and Codex's independent source review find no missing mathematical input for the existing cutoff-only BKL route. Codex separately compiled the full expanded finite-horizon cutoff (95) specification and a closed all-order proof, using the actual compact8 producer and no Theorem41 import; both scratch modules passed strict compilation and kernel replay with standard axioms. The corrected 41-declaration source map is recorded in [`independent-current/ACCEPTANCE-v3.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/independent-current/ACCEPTANCE-v3.json) (superseding the initial acceptance) and [`independent-current/CORRECTED-AUDIT-MAP.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/independent-current/CORRECTED-AUDIT-MAP.json); Claude's audit is in [`claude-audit/`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/claude-audit/). This is not a canonical certificate or a fresh final full receipt.

A scope clarification has been offered to the human: accept the BKL-sufficient cutoff route and move to stage3, or require the full uncut process and stochastic identities. Codex then stated the working assumption that the BKL-sufficient cutoff route continues, with the full uncut construction kept open; the owner then explicitly chose this scope ([`USER-SCOPE-CHOICE-20261017.md`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/USER-SCOPE-CHOICE-20261017.md)). The exact endpoint is frozen in [`FROZEN-ENDPOINT.json`](../../build/reviews/2026-10-17-bkl-step2-stochastic-localization-goal/FROZEN-ENDPOINT.json). The Goal remains ACTIVE. Source/mathematical acceptance of the cutoff route is independent of that preference; no literal uncut result is claimed. No proof task is sent merely to reproduce accepted work.
