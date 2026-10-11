# Continuous BKL formalization goal

Owner instruction, 2026-10-07: use the established Claude/API/Codex workflow,
create a persistent goal and continue until it is complete. This replaces the
four/eight-hour window for this new goal; the previous bounded blocks remain
closed historical records. There is no artificial time, token or request budget.

## Objective and acceptance

Formalize Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits
conjecture*, arXiv:2610.05474v1, Theorem 1.1, with its exact hypotheses,
normalization and universal dimensional scope. Pinned PDF SHA-256:
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
The source files and manifest are in
`/Users/lyuyuwei/Documents/ChatGPT/KLS-paper-sources/2026-10-07/`.

Completion requires the whole proof closure, including the required Letwin
input, Eldan localization, Theorem 4.1, Proposition 7.1 and regular approximation,
then the connection to the already proved Theorem 3.1 and exact KLS target.
Every dependency must be proved or imported from a verified, source-faithful
Lean theorem. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
A conditional counterpart or a sketch is not completion. Register the exact
main-theorem certificate and synchronize the English paper map, Blueprint,
progress views and handoff; obtain a successful full local verification receipt
matching the final source. Do not claim the preprint is covered before this.

## Fresh baseline

Local HEAD `7c0145c`: Theorem 3.1 is certified, Proposition 7.1's convexity
(109)–(110) is proved, and BKL-specific modules/audits have been moved to
`KLS/BKL/` and `research/audits/BKL/` without namespace changes.
The full local receipt
`build/verification/20261007T125302.861460Z/report.json` passed 204 gates,
193 strict audits and 405 module replays. Codex rehashed the recorded source
inputs and archived compiled artifacts before this goal's launch.
The untracked `.clinerules/`, `.cursor/` and
`research/decisions/2026-10-07-three-paper-formalization-comparison.md` are unrelated.
Preserve them and the actual index. Git publication and remote verification are
separate authorizations; the remote baseline is `ca59365` as last checked.

## First milestone: Proposition 7.1

Continue the source proof on pp. 28–30, equations (108)–(113). Do not re-prove
Theorem 3.1 or the completed convexity step.

1. Construct the finite independent product and Laplace noise, retain
   `sigma² = 1 + 2/beta²`, and identify the joint law with the convex
   suspension potential (109).
2. Derive mean and covariance from (108), independence and the exact noise
   variance. Supply the finite-dimensional Euclidean coordinate adapter.
3. Prove the local logarithmic-Laplace derivative identity (111), then
   (112), including vanishing entries involving different copy blocks.
4. Prove the disjoint-block Hilbert–Schmidt bound, the limit as `beta → ∞`,
   affine-orthogonal density and decomposition, with the source's exact
   `2b/(d!)²` estimate. The cumulant premise in Proposition 7.1 is a genuine
   source hypothesis; Theorem 4.1 must later discharge it.

The Laplace noise has exponential moments near zero, not every exponential
moment. Do not apply a global-moment interface to it. Extend the generic
logarithmic-Laplace tools with a proved local-differentiability interface,
then use it for the mixed cumulants.

## Source-faithful decomposition to accelerate the goal

The owner additionally requested analysis of the whole pinned BKL paper to
extract independently formalizable pieces. Build a source-numbered dependency
table and a ready queue alongside the main proof work. For each candidate,
record the exact statement/equation locator, assumptions, constants,
normalization, current Lean prerequisites, missing interface and consumer in
the main proof chain. Prefer substantive deterministic algebra, tensor,
moment and summation results whose dependencies are ready. Keep stochastic
process existence and Itô statements attached to their genuine prerequisites.
Do not manufacture arbitrary conditional packages or count them as complete
source theorems. A small lemma should provide a reusable interface or close
an actual source obligation, rather than restate its desired conclusion.

Codex is independently reading Sections 4–6 for extractable deterministic
pieces while Claude plans the Proposition 7.1 batches. Results go to
`build/reviews/2026-10-07-bkl-continuous/queue/`; freeze full contexts only
after checking the proposed statement and its connection to the source.
Use ready, nonoverlapping batches to feed the Luna proof worker; keep one
production integrator and independent acceptance review.

## Roles and model provenance

- **Claude, existing native Code session:** owns source statements, decomposition,
  mathematical placement plans, frozen full contexts, acceptance and production
  integration. One editor per production file. It may delegate independent
  proof-body tasks, but must use the existing Luna API for substantive proof
  attempts and repairs rather than replacing that role with only Claude workers.
- **Existing Luna API, `gpt-5.6-luna`:** the principal proof-body/helper worker.
  Reuse `/Users/lyuyuwei/.config/kls/gpt.env`; its reuse was already authorized
  in the previous workflow and renewed by the owner. Never log or copy credentials,
  change providers/models/authentication, or write credentials into task artifacts.
  The proof context, hypotheses, imports and statement are frozen by Claude;
  workers only return proof bodies and private helpers. Record requested and
  returned model identifiers, context hashes, actual Lean diagnostics and provenance.
- **Codex, this authenticated desktop goal and the official ChatGPT-authenticated
  CLI:** independent strategy and acceptance review. The confirmed official CLI is
  `/Applications/ChatGPT.app/Contents/Resources/codex-cli/CodexCLI.app/Contents/MacOS/codex`.
  Prior designated CLI review model: `gpt-6.1-sol`, reasoning `xhigh`.
  Use read-only review requests. A response through the Luna relay is not a
  Codex review. Queue review requests and completed candidates in the artifact
  directory so this goal can independently inspect and accept them.

Use the new artifact directory
`build/reviews/2026-10-07-bkl-continuous/`. Existing proof blocks are historical
and must not be overwritten. Adapt their driver into this directory; compile
each one-target scratch batch strictly and check the actual transitive axiom
closure. Earlier unproved placeholders are not accepted dependencies.

## Persistent execution and checkpoints

Keep an execution record, concrete task queue, worker identities, accepted
statement CSV, reviews, diagnostics, work log and verification pointers. The
Codex goal is the continuation owner across turns and compaction. Claude should
continue the next ready BKL milestone after each accepted batch. Make checkpoints
after accepted results and before compaction; do not report the goal complete
because a turn or model context ended.

Use bounded individual HTTP/Lean/CLI timeouts and sensible host/service
concurrency. If a failure repeats unchanged three times, replan the lemma,
context or proof strategy rather than repeat the same prompt. Record outages and
resume useful independent work. Technical retry limits are not a spending quota.
Only control processes positively identified as children of this goal.

Follow `AGENTS.md`, `research/workflow.md` and `research/naming.md`. New BKL-specific
modules belong in `KLS/BKL/`; generic tools remain with their owning objects.
For every accepted endpoint: strict compilation, a real client, elaborated-type
and definition review, and transitive axiom checks. Freeze the intended source
before the full verifier; use a temporary index for progress regeneration.
Track real gaps and exact source mappings throughout.

No commit, push, tag, remote CI, reset/clean, credential change, memory update or
Prove2me operation is authorized by this continuous goal.

## Owner-authorized Claude model selection, 2026-10-08

The owner explicitly authorized reasonable use of Claude Fable 5.1 and adjustment of Claude
reasoning strength based on live usage. Codex may set the existing native session accordingly.
Batch routine integration, compiler-interface repair, existing-proof clients and documentation
with Fable 5.1 at Medium; increase effort for source-statement freezing and mathematical strategy,
and use Opus when that harder phase warrants it. Avoid repeated model toggles because the native
switch rereads the cached session on the next message. Record actual model/effort provenance by
phase, without retroactively attributing earlier responses to a newly selected model.

This authorization concerns Claude model/effort selection. The existing gpt-5.6-luna proof-body
API configuration, credential/provider boundary, independent Codex review, original mathematical
objective and full acceptance criteria are unchanged. Model selection never lowers proof fidelity,
strict compilation or the actual transitive-axiom gate. Current settings and observed usage are
recorded in the private build artifact queue/CLAUDE-MODEL-POLICY-20261008.json.

## Takeover and planning state, 2026-10-08 16:05 CST

The owner moved the continuous goal to Codex thread `01a11a7a-a955-7340-96ca-5eb3d0b8d465`; the
native Claude chat remains the only production editor (Fable 5.1 / Medium, Luna configuration
unchanged). Baseline: `build/reviews/2026-10-07-bkl-continuous/takeover-20261008-01a11a7a/TAKEOVER.json`
(HEAD `7c0145c`, index tree `7e518dba`). While REQUEST-INT-19 is under root capture, production sources
are held and only planning was done: `reviews/COEFFICIENT-SDE-MOMENTMAP-PROPOSALS-20261008.md` records
the placement plan for the (67) coefficient regularity (two existing scratch bundles, no new unit), the
strong-solution / non-explosion decomposition (scratch-only until the external-closure decision; the pinned
closure has no SDE theorem; the non-explosion argument must be extracted from the cited Chen text before any
freeze), and the assessment that the Letwin moment-map producer (Lemmas 2.1–2.2) is out of reach at the pin,
with a generic `IsMomentMap` bundle proposed instead. `LetwinQuadraticBound` remains the explicit hypothesis.
The 339-module external-closure migration artifact waits for the root's license/NOTICE metadata.

## Accepted integrations and rename, 2026-10-08 evening

All five takeover gates were independently accepted and the INT-19 hold released. Integrated into production
(strict, aggregate build 3863 jobs, audits standard): the coefficient regularity of (67)
(`Probability/Posterior/JointRegularity.lean`, `Analysis/MatrixPositivity.lean` floors/Sylvester,
`Analysis/OperatorCoordinates.lean` charts, `Analysis/PrincipalInverseSqrt.lean` local Lipschitz,
`KLS/BKL/PosteriorDomain.lean` `Isotropic.locallyLipschitz_coefficients67`) and Letwin (2.2) for a given potential
(`Analysis/BakryEmery/MongeAmpere.lean` divergence, `IntegrationByParts/InverseHessian.lean`). REQUEST-INT-20 is
the review request. The R1 minimal-closure migration record exists in scratch only
(`reviews/StochLean-Minimal-Closure-Migration-20261008/`); adoption waits for an accepted migration and a verifier
extension that discovers a vendored package. Issue 9 live links were rewritten (record and patch under
`naming-20261008-issue9/`); nothing is committed or pushed, and the issue stays open for the owner.

## Noise and non-explosion supports, 2026-10-08 night

After the independent acceptances of TE1 (trace energy) and NB1/NB3 (covariance Cauchy–Schwarz, whitened-statistic
variance under an actual sandwich), the three generic supports were integrated into their owners
(`Analysis/MatrixTrace.lean` section `TraceEnergy`, new `Probability/Covariance/CauchySchwarz.lean`,
`Probability/Covariance/Whitening.lean` section `WhitenedStatistic`), with the reviewer consumers as audits
(`TraceEnergyAudit`, `CovarianceSupportAudit`) and the Blueprint node `lem:bkl-localization-supports`. Aggregate build
green (3866 jobs). REQUEST-INT-22 is the review request. No new full verifier: the batch is grouped for the next accepted
proof milestone. The scratch checked-context driver revision was independently rejected and is preserved unchanged; a
second revision with staged-layout tests is prepared separately in scratch.

TW1 (canonical standardisation: the principal root transports the centred posterior to an isotropic law) was independently
accepted as a documented repair and integrated into `KLS/BKL/PosteriorDomain.lean` (section `CanonicalStandardisation`,
Blueprint `lem:bkl-canonical-standardisation`, audit namespace `IndependentCanonicalStandardisation`); it is part of the
INT-22 batch. TU1b closed by a recorded linter-only repair (scratch, gate pending); TM1b driver-accepted (gate pending).

## Full receipt for the (67)–(68) supports, 2026-10-08 night

The single full local `research/verify.py` run (root-executed, root-accepted) for the INT-22 batch is
`build/verification/20261008T123842.661988Z/report.json` (report sha256 55b4109f…, snapshot sha256 5c1b55b3…, 233 gates).
It verifies supporting proofs only: no BKL main theorem, Letwin producer, SDE existence or StochLean adoption claim.
The receipt metadata update (the HANDOFF pointer paragraph and this note) is the only post-snapshot change; no Lean source changed.

## Ball conditioning, sixth moment and singleton allocation, 2026-10-08 late night

Root-accepted raw bodies integrated verbatim (Claude Opus 5.5 placement; Luna gpt-5.6-luna bodies under the rev3 checked
context): CB5 half mass (`Probability/Moments.lean` section `MomentTails`), CB1/CB4 `conditionOnBall` and its error
bound (new owner `Probability/Conditioning.lean`), SM1 canonical sixth moment (`KLS/BKL/PosteriorDomain.lean` section
`SixthMoment`) and D74s singleton allocation (`Analysis/BakryEmery/LocalCumulant.lean` section `SingletonAllocation`;
the production docstring reads `κ_{|hs|+1}`, the frozen file's `+2` stays in history). Audits `ConditioningAudit`,
`SixthMomentAudit`, `SingletonAllocationAudit` merge the independent reviewers' clients; Blueprint
`lem:ball-conditioning`, `lem:bkl-posterior-sixth-moment`, `lem:bkl-singleton-allocation`, extended
`lem:moment-tails-eighth`. Gate request INT-25; no new full receipt is claimed. Open: the full (74) expansion
(scratch, awaiting gates), grouping (72)–(73), the (69) entry identity, INTERFACE C energies, parameter jets,
SDE/Itô, the Letwin producer and the main theorem.

## Raw (74) expansion and the (69) entry identity, 2026-10-09

Root-accepted raw chains integrated (Claude Opus 5.5 placement; Luna gpt-5.6-luna bodies under the rev3 checked context,
verbatim except the mapped namespace): D74 — `selected_eq_nil_iff` (IteratedDerivative/Bilinear), `iteratedFDeriv_inner_clm`
(new IteratedDerivative/InnerProduct), the centred-gradient jets and the raw (74) expansion for any `M` (new
BakryEmery/CumulantLeibniz); B69 — Euclidean coordinate algebra in OperatorCoordinates (section EuclideanCoordinates),
cubic-monomial integrability and the finite-sum/integral exchange in Probability/Moments (section CoordinateMonomials),
the generic entry identity in new Probability/CoordinateThirdMoment, the posterior ball bound in Posterior/CompactDomain and
the original (69) entry identity in PosteriorDomain section NoiseEntries (namespace map Analysis → Probability for the four
moved probability lemmas). Audits `RawCumulantExpansionAudit`, `NoiseEntryAudit`; Blueprint `lem:bkl-raw-drift-expansion`,
`lem:bkl-noise-entries`; gate request INT-26. Open: grouping (72)–(73), INTERFACE C energies, parameter jets, SDE/Itô, the
Letwin producer and the main theorem.

## Grouping and energy supports, 2026-10-09 (INT-27)

Root-accepted Ready3 bodies integrated verbatim as additions only: `cumulant_comp_perm_of_compact` (LocalCumulant section
CumulantSymmetry), `sum_filter_eq_two_mul_sum_filter_of_compl_invariant` (IteratedDerivative/Bilinear) and
`sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six` (Probability/Moments section ThirdMomentContraction). Audits
`GroupingSupportAudit`, `SixthContractionMapAudit`; gate request INT-27. The grouping (72)–(73) and the INTERFACE C energy
bounds themselves remain held drafts.

## Full receipt for INT-23 to INT-27, 2026-10-09

The single full local `research/verify.py` run (root-executed, root-accepted) after INT-23 to INT-27 is
`build/verification/20261008T200352.046614Z/report.json` (report sha256 66a32bed…, snapshot sha256 99a62a21…, 1215 files,
242 gates, 231 strict research audits, 799 standard declaration axiom reports, local kernel replay of 477 owned objects;
upstream compiled dependencies trusted, not replayed). It includes the twelve-line duplicate-print repair of
SingletonAllocationAudit and SixthMomentAudit; the first attempt 999a9ff7… failed closed on those duplicates and is
preserved. It verifies supporting proofs only: no BKL main theorem, moment-potential producer, Letwin quadratic-form
bound with constant 8, SDE existence or StochLean adoption claim; the CEK (54) units are scratch. The receipt documentation update (the HANDOFF pointer paragraph, the receipt history
file and this note) is the only post-snapshot change; no Lean source changed. The 2026-10-08 receipt note above stays as
the record of its own snapshot.

## Uniform halfspace mass (CEK (54)), 2026-10-09 (INT-28)

Root-accepted raw chain integrated verbatim into the new owner `Probability/ConvexSupport.lean` (Mathlib-only imports;
distinct object and dependency level from AffineSupport's intrinsic coordinates): the support-point and joint
positive-neighborhood helpers and the uniform open-halfspace mass bound, with the three private product lemmas of the
accepted final proof (finite product of ball masses over a cover of the unit sphere). Audit `ConvexSupportAudit`; Blueprint
`lem:uniform-halfspace-mass`; CorderoKlartag2015 L16 marked partial (probability (54) support only); gate request INT-28.
Open: CEK Lemma 16 (finite measures, extended-real point control), moment-potential existence, Letwin's constant-8 bound.
