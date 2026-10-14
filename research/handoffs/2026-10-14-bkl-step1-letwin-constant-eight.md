# BKL roadmap step 1: the compact Letwin constant-eight theorem

Created 2026-10-14 by explicit human instruction in Codex chat 01a1349a-c7f3-7a91-b1e0-9f662aca3a19. The owner clarified that the four steps mean the mathematical main line: (1) Letwin constant 8, (2) stochastic localization, (3) BKL Theorem 4.1, (4) the KLS main theorem. Only step 1 is installed as the active Goal. No token budget was requested or imposed.

## Exact completion target

Prove the original frozen `FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound`, with the actual regular-class producer `letwinQuadraticBound_of_regularClass` rather than a supplied regular-class inequality. Letwin arXiv:2607.24164v1 Theorem 1.2 supplies the source constant 8; the immediate consumer is BKL arXiv:2610.05474v1 Lemma 4.2 and the compact localization argument. `LetwinCompactBound` means: for every n>0 and every compactly supported isotropic log-concave probability measure on EuclideanSpace R (Fin n), every self-adjoint quadratic form has centered variance at most 8 times its squared Hilbert-Schmidt norm. Singular and indefinite symmetric matrices are included. Mean/covariance normalization and the exact constant are preserved.

This is the compact source counterpart needed by BKL. It is not full general noncompact Letwin paper coverage, not merely the PSD trace lemma, and not completion of BKL/KLS. The original final statement source is archived beside this record; its imports are historical scratch names, not current canonical dependencies. The actual proposition is canonical in KLS/BKL/CompactReduction.lean. The already proved T10f canonical compact reduction is in KLS/BKL/LetwinApproximation.lean.

## Four-step roadmap and evidence boundaries

1. **Active Goal: compact Letwin constant 8.** Complete its source-law inputs, weak-route analysis, regular-class result and compact approximation. No desired final variance bound, trace estimate, regularity producer or downstream theorem may become an assumed premise.
2. **Queued: stochastic localization.** Before assigning work, audit actual source-specific SDE/non-explosion/Ito/martingale inputs and the current cutoff-localization route. Reuse independently certified work; do not infer completion from posterior calculus alone or blindly recreate existing modules.
3. **Queued: BKL Theorem 4.1.** A canonical conditional result already exists with LetwinCompactBound as its only external premise. Reassess source hypotheses, all-order constants and stochastic provenance before a completion claim; do not repeat its accepted algebraic assembly.
4. **Queued: BKL Theorem 1.1 and KLS.** Reuse the certified Taylor/suspension reductions and exact main interfaces once all inputs are discharged. This Goal does not write KLS.kls, register a main KLS certificate or publish anything.

## Current base and immediate sequence

(State at Goal setup; the current queue is in the section *Current queue* at the end of this record.)

Canonical base: HEAD 8ec28f68c8bf72f60ec195b6fbb0f0f48ea04a22, full snapshot 6e7d5285ab6cf71f63ddabee4683387583242c24a672a57629395825be98661e, passed full receipt 20261013T181656.119706Z (280 gates,266 strict clients,806 replayed local modules). R0 regular moment-potential producer, T10f compact approximation and both N10b generator identities are canonical; no repetition is needed.

N11b.1 is independently CODEX_ACCEPT but remains in scratch: the centered second difference is C1 with 4G-Lipschitz gradient, for every finite n including zero. Its exact hash/type, actual N10b consumer, standard axioms and kernel replay are recorded under build/reviews/2026-10-14-codex-claude-n11-controller/independent/N11b1. Do not rerun it if its source/hash is unchanged.

Immediate dependency-ready work is the original N11b integrated Hessian-increment inequality. Freeze only missing consumer interfaces: first nonnegative/bounded centered difference (0<=w<=D*norm(h)^2 and the needed scalar nonnegativity), then precise compact weighted-integrability consumption, then the unchanged original N11b assembly. Do not add integrability or the desired energy estimate as a premise merely to finish assembly. Preserve the original coefficient 2*K^2*D*norm(h)^2, C1,1/a.e. hypotheses and all original dimensions.

After N11b is independently accepted, proceed sequentially through the actual missing N11d weak third-derivative producer, local H1/chain-rule adapters, weak inverse-Hessian evolution and trace estimate, weak Brascamp-Lieb/variance input, Stein/H^-1 transport and spectral delta-factorization/constant-eight assembly. N11e symmetry assumes an actual weak third tensor and cannot produce it. W3b2a only gives convex-range mollification. Ordinary weighted Laplacian and the inverse-Hessian generator are different interfaces. Every next contract is frozen only after reading the current exact dependencies and published source consumer.

## Roles, limits and progress

Codex owns mathematical source/version, full contract, dependency choice, placement, independent acceptance and stage transitions. The existing Claude session LevyStochCalc source-lock validation (local_4904933f-a611-430d-b4fe-36e2a7f677a2) operates the existing API loop and is the sole reviewed canonical integrator after Codex ACCEPT plus placement review. API supplies scratch proof bodies only. No new Codex/Claude worker or autonomous sub-controller is introduced.

Use existing gpt-6-astra/high, existing provider/credentials/script, max_rounds=4 and max_queries=6 per fresh minimal contract, one mathematical candidate at a time. Retain failed attempts; do not restart/expand the old eight large loops. A consumed exhausted packet requires an explicit diagnostic and a genuinely reviewed smaller contract; do not silently resend an equivalent task to evade its limit. Unsupported repeated mathematics is recorded and the affected branch stops until the gap/contract is resolved. Keep other roadmap stages queued. The old claude-kls heartbeat remains paused while this active Goal is the controller, avoiding duplicate dispatch.

Before canonical changes, review current AGENTS.md/workflow/naming and record owner/scope/destination/imports/extend-split-create/API/client plans. Preserve the dirty tree and real index entries/flags; temporary indexes are only for progress generation and must not enter full verify. English canonical HANDOFF, literature priorities, Blueprint/complete diagram/date/root summary must reflect actual proof status. N11b or another support unit never completes this Goal. Documentation setup alone is not a proof-status upgrade.

## Completion gates

Exact final Lean statements and full elaborated types, semantic source matching (constant, hypotheses, normalization, dimension and arbitrary symmetric matrix scope), strictly compiled substantive clients, all relevant proof values with only propext/Classical.choice/Quot.sound, local kernel replay, independent accepted canonical placement/integration, exact local certificate for the restricted compact target, synchronized English documentation/progress, and a fresh full python3 research/verify.py receipt for the final source/meta snapshot with no drift. Record trust/hole scopes separately. Full noncompact paper coverage and KLS remain separate claims.

No commit,push,tag,remote CI,publication,provider/model/credential change or credit purchase is authorized. No deadline or token budget is invented. The Goal remains active until the actual compact endpoint is achieved; setup, dispatch, support proofs or conditional assembly alone cannot close it.

## Repository record

This file is the repository copy of the active Goal record (control directory
`build/reviews/2026-10-14-letwin-constant-eight-goal/`, files `GOAL.md`, `STATE.json`, `QUEUE.json`, `baseline/`), saved on
2026-10-14 as a documentation-only setup step. Only roadmap step 1 is installed; steps 2-4 are queued and receive no proof dispatch
from this Goal. The existing conditional results (`theorem41` and `conjecture_of_letwinCompact` in `KLS/BKL/Theorem41.lean`, with
`LetwinCompactBound` as the only external premise) are reused for steps 3-4 and will be re-reviewed against the exact source
statements, hypotheses and axiom evidence before any completion claim; their accepted assembly is not re-proved.

The original final statement is archived in the control directory as `ORIGINAL-FINAL-Statement.lean.txt`; its imports are historical
scratch names. Saving this record changes no proof, coverage, certificate or node status; the full receipt `20261013T181656.119706Z`
covers the snapshot `6e7d5285…` taken before this documentation setup.

## Work queue at setup

| Item | Status | Scope |
| --- | --- | --- |
| `N11b1` | independently accepted scratch | C1 and exact 4G-Lipschitz centered-difference adapter |
| `N11b2` | next contract to freeze | derive nonnegative and bounded centered difference from original convexity/upper-bound assumptions |
| `N11b-integrability` | requires API gap review | precise finite weighted-integrability consumption from canonical Hessian/cofactor bounds |
| `N11b-original` | awaits independent supports | original integral_mul_hessian_increment_le with unchanged full type |
| `N11d` | awaits N11b | produce actual local L2 weak third derivatives; reuse N11c1/c2 and then N11e |
| `local-H1-chain-rule` | review small contracts when ready |  |
| `N13-evolution-trace` | awaits actual weak derivatives and testing |  |
| `N14-weak-Brascamp-Lieb` | review small contracts when needed |  |
| `LR2-Stein-HminusOne` | awaits actual trace and weak pairing |  |
| `LRF-original-compact-constant-eight` | exact Goal endpoint not proved |  |

At setup, the immediate next contract was N11b.2: from the original convexity and upper-bound assumptions, the centered second
difference satisfies `0 ≤ w ≤ D‖h‖²` together with the needed scalar nonnegativity. It has since been accepted and integrated (see below).

## Current queue (updated 2026-10-14 at the documentation checkpoint)

The six N11b contracts (N11b.1-N11b.6) each have independent Codex acceptance (`independent/N11b1..6` in the control directory)
and are canonically integrated under the Codex-accepted placement: centered-difference regularity and bounds in
`Analysis/Convex/SecondDifference.lean`, total Hessian-entry measurability and the Lipschitz-gradient bound in
`Probability/Stein/HessianKernel.lean` (namespace `Probability.Stein`), weak generator integrability in
`Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`, and the weighted increment integrability with the unchanged original
`Analysis.integral_mul_hessian_increment_le` in the new `Analysis/Convex/HessianIncrement.lean`; audit
`research/audits/BKL/HessianIncrementAudit.lean`. The full receipt `build/verification/20261014T080831.534453Z/report.json` passed for
snapshot `6465861a…`, and Codex recorded `CODEX_CANONICAL_ACCEPT` for that snapshot (`canonical-independent/ACCEPTANCE.json`). This is a
supporting result; the Goal endpoint `LetwinCompactBound` is not reached.

Next actual producer: N11d, actual local L2 weak third derivatives of the Hessian entries under the original N11 hypotheses (the N11b
uniform difference-quotient bound and the canonical weak-derivative interfaces as inputs; N11e symmetry only consumes such a tensor).
Its first contract, N11d.1 (`tasks/N11d1-uniform-translated-cutoff`), is frozen but undispatched; a frozen interface is not a proof
acceptance. Then local H1/chain-rule bridges, weak Hessian evolution and the trace estimate, weak Brascamp-Lieb, Stein/H^-1 transport
and the spectral constant-8 assembly.

## Authorization update (2026-10-14 documentation checkpoint)

The setup rule above (no commit, push, tag, remote CI or publication) is unchanged as the Goal's default and is kept as history. For
the documentation checkpoint of 2026-10-14 only, the owner explicitly authorized one commit and an ordinary push to `origin/main`
containing the documentation cleanup together with the independently accepted proof changes; Codex reviews, validates, stages,
commits and pushes. No tag, remote CI run, separate release beyond that ordinary push, or new proof dispatch is authorized by it, and the Goal's success criteria are
unchanged.
