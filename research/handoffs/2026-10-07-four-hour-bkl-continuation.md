# Four-hour goal: continue the BKL proof dependencies

Owner renewal on 2026-10-07: verify the completed block and have Claude execute another four-hour
task under the same resource and role arrangement. The previous eight-hour plan and evidence
remain unchanged. This instruction authorizes local proof implementation, integration, model
collaboration and verification; begin the work rather than returning only a proposal.

## Baseline and precheck

Read `AGENTS.md`, `HANDOFF.md`, `research/workflow.md`, `research/naming.md`, the prior goal
`research/handoffs/2026-10-07-eight-hour-bkl-foundations.md`, and:

- `build/reviews/2026-10-07-bkl-eight-hour/FINAL.md`, `WORKLOG.md`, `execution.json`, and the
  accepted-statement provenance and Codex reviews;
- `build/reviews/2026-10-07-bkl-four-hour/PRECHECK.md` (Codex's independent current check).

Verified before this dispatch: HEAD `36e7c781edab9875ca0bfe35d26992f005db7ced`, real index tree
`e3969ca17d5e71e7e4fced490b6821b0478e5f92`. The existing dirty BKL source matches the final local
receipt snapshot `93a27f0355516a53b8b4c04014a6b58f5c53591ac117ddd2adb98de40fb25c6f` (1053 files),
with 186 passed gates, 175 strict audits and 384 replayed modules. Codex rechecked artifact hashes,
reran `BKLFoundationsAudit.lean` strictly, and checked the decisive source interfaces.

This new goal file is a later documentation addition outside that receipt. Preserve all earlier
dirty/untracked BKL modules, documents, audits and model configuration. Save a fresh recoverable
baseline at actual start; do not reset, clean, discard, stage over or rewrite the previous work.
Remote success for `36e7c78` certifies the committed BGL baseline, not the dirty BKL additions.

Pinned source: Bizeul-Klartag-Lehec, arXiv:2610.05474v1, local PDF
`/Users/lyuyuwei/Documents/ChatGPT/KLS-paper-sources/2026-10-07/2610.05474v1.pdf`, SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
Keep the hypotheses, constants, probability normalization, tensor slots and Hilbert-Schmidt norms.

## Targets in priority order

### 1. Repair and integrate the conditional third-cumulant result

Start from `build/reviews/2026-10-07-bkl-eight-hour/assembled/N.lean` and its frozen contexts,
Luna candidates and Codex strategy 12. Codex's fresh strict run found two unused-section-instance
errors at lines 41 and 106 (`[CompleteSpace E]`). Repair by explicit scope organization / `omit`,
not by disabling a linter. Review and re-freeze full elaborated signatures after the repair.

Recompile and axiom-audit the four public results: the first log-Laplace derivative at zero, the
second Taylor tensor of a centered linear function, third cumulant = third centered moment, and
`sum_sq_cumulant_three_le_of_letwin`. Check centering, isotropy, the factor 8, the `1/2` Taylor
normalization and the Hilbert-Schmidt contraction.

Integrate only after a placement plan and independent Codex acceptance. `LetwinQuadraticBound`
remains an explicit premise, with no axiom or assertion that it holds. The all-exponential-moment
scope remains explicit. Label the source relation conditional/partial, not an unconditional proof
of BKL Lemma 4.2. Include a nonzero example where the remaining premises are actually discharged
when possible; at minimum use a real consumer connecting the cumulant and Taylor formulations.

This is a useful first checkpoint, not a reason to end the four-hour task early.

### 2. Connect the proved general identities to source regular laws

The previous work proved the scalar/tensor Lemma 3.6 identities and temperate IBP/Bochner under
explicit growth and exponential-moment premises. Mathematical source matching was reviewed;
there is not yet a bundled Lean proof deriving those premises from the paper's regular-law class.

Build that adapter using the actual probability law `volume.tilted (-V)` and the source's smooth
potential, polynomial bounds on derivatives, and positive lower / finite upper Hessian bounds.
Use `HasTemperateGrowth` and existing finite-dimensional calculus where they faithfully encode
the source class. Derive, rather than assume anew:

- integrability and nonzero normalization of `exp(-V)`, and the probability interpretation;
- Gaussian tail domination from the positive lower Hessian bound;
- all `exp(r * norm x)` moments, the required gradient-growth bound, and polynomial/moment
  integrability for source tests;
- applications of the existing scalar/tensor tilt, IBP and Bochner identities with these
  extra analytic premises discharged.

Also prove the compact-support exponential-moment adapter if it gives an immediate genuine
consumer of the conditional third-cumulant result. Do not hide the missing moment estimates in
a new conclusion-bearing structure, or count the total zero-measure branch as source nonvacuity.
The full regularization/approximation theorem and smoothness of Poisson solutions remain separate.

### 3. Advance BKL Lemma 3.4 and Corollary 3.5

Use the existing tensor Bochner/IBP statements to prove the energy-defect identity and energy
decrease for a pair of smooth temperate tensor fields satisfying the source's defining Poisson
relation (30) and its actual normalization (33). Derive the orthogonality and Pythagorean identity
(39)/(47); do not add them as assumptions merely to make (45) trivial. Handle the zero-scale case.
State all derivative energies in the source Hilbert-Schmidt/direct-sum norm, with all derivative
and trailing tensor indices, not the multilinear/operator norm of `fderiv`.

For a correctly scoped sequence of such pairs, prove the telescoping estimate, summability of
the nonnegative energies and the limit in Corollary 3.5, retaining positive curvature `a`.

Construct the finite componentwise/tensor lift of the already proved centered operator inverse
if it is a needed prerequisite and can be completed coherently. Reuse the actual scalar closed
generator; distinguish form domain, operator domain, L2 classes and pointwise representatives.
Full Lemma 2.1 on class A and the first-eigenfunction construction are still missing. A theorem
for a supplied valid pair/sequence does not construct the paper's iterates; record that remaining
instantiation explicitly and choose a faithful partial/stronger relation after review.

If a target requires a large unresolved PDE theorem, split off a named useful dependency and
continue a parallel ready target. Do not spend this short block only surveying spectral theory,
or claim compact resolvent/eigenfunction existence without a proof.

## Same roles, models and resource authorization

- **Claude:** exact statements and source contracts, decomposition, placement, acceptance,
  production edits and integration. One editor per production file.
- **Existing Luna API (`gpt-5.6-luna`):** the principal proof-body and helper-lemma worker,
  using the already owner-authorized configuration in `/Users/lyuyuwei/.config/kls/gpt.env`.
  Freeze full contexts; send real Lean diagnostics; use independent scratch batches and adjust
  concurrency to the host/service. Most calls should attempt proofs or proof repairs.
- **Owner's real signed-in Codex (`gpt-6.1-sol`, xhigh):** hard proof strategy and independent
  semantic/axiom review. Reuse the actual native integration or official local CLI with ChatGPT
  authentication and bounded read-only review requests. A relay response is not a Codex review.
- The owner's no-artificial-spending/token/request-quota instruction remains in force. Technical
  context, service and time limits still require sensible task splitting and supervision.
- Do not change credentials, global providers, model identity or authentication. Never log secrets.
  Revalidate connectivity safely; a failed request is not a proof result.
- Preserve context/signature hashes, source locator, candidate diff, actual diagnostics, reviewer
  result and model provenance for accepted statements. Split or change approach after repeated
  unchanged failures; do not repeat the same failing prompt indefinitely.

## Four-hour window and failure handling

Record actual `T0` and deadlines in Asia/Shanghai in
`build/reviews/2026-10-07-bkl-four-hour/execution.json`:

| Elapsed time | Action |
| --- | --- |
| 0:00-0:20 | Fresh baseline; repair/check Batch N; freeze placements and the next proof batches. |
| 0:20-2:15 | Integrate the conditional result; prove the regular-law adapter; dispatch independent energy/tensor prerequisites. |
| 2:15-2:45 | Finish the strongest coherent endpoint; obtain real independent Codex acceptance. |
| 2:45 | Stop opening new targets and bound outstanding proof searches. |
| 3:00 | Freeze intended source/metadata and start the final full local verifier. |
| 4:00 | Hard stop, end this block's remaining child workers, preserve evidence and hand off. |

Use an actual local deadline supervisor independent of model/API responses, with recorded child
process identities and bounded request/subprocess timeouts. The previous block lost roughly four
hours to an outage; do not depend on a model returning to enforce the freeze or hard stop. Control
only this task's children; never kill unrelated user, Lean or other-session processes.
Checkpoint accepted proofs and the queue so compaction resumes this same goal. Continue useful
ready work if one model is unavailable; record unreceived independent review honestly. Do not
silently restart the clock, compensate outages by adding hours, or extend beyond four hours.

## Verification and delivery

Follow `research/workflow.md` and `research/naming.md`: record owner/scope/destination/imports/API
and checks before edits; reuse owners and preserve old interfaces. No wrappers, placeholders,
empty future modules, nonstandard axioms, suppressed warnings or weakened source targets.

Every accepted endpoint needs strict compilation, a real consumer, full elaborated-type and
definition review, and transitive `#print axioms` checks. Only `propext`, `Classical.choice`,
`Quot.sound` are permitted. Explicitly conditional reductions remain conditional. No source
paper is covered until its exact main theorem, proof, certificate and evidence are complete.

Update the affected numbered source map, Blueprint, hashes and live progress only for actual
accepted results. Use ✓ / ⇑ / ◐ / ○ faithfully; include the whole pinned source's numbered map.
Regenerate views from an isolated temporary Git index holding only the intended state, keeping
the user's real index and existing dirty baseline. Run `python3 research/verify.py` on the final
frozen tree; report its exact receipt/snapshot and any outstanding failure or unfinished check.
Keep the previous eight-hour evidence unchanged; create new artifacts and a current handoff.

The owner has separately told Claude to leave Prove2Me aside. Do not inspect, retry, modify or
troubleshoot that operation. This proof continuation adds no publication authorization: no
commit, push, tag, remote CI, Slack message, reset/clean, memory update or credential change.

Save `WORKLOG.md`, `accepted-statements.csv`, candidate/worker provenance, Codex review(s), a final
receipt pointer and `FINAL.md` under `build/reviews/2026-10-07-bkl-four-hour/`. End with a concise
Chinese account of new proved statements, exact conditional/restricted scope, unchanged gaps,
Luna/Codex use, actual execution/outage times, verification and baseline preservation, and the
next three proof tasks. Distinguish the new four-hour progress from the previous BKL foundations.
