# Eight-hour goal: formalize the first BKL proof dependencies

Prepared on 2026-10-07 for Claude, on the owner's explicit authorization to run for eight hours,
use the existing ChatGPT-compatible API and the owner's Codex, and impose no artificial spending,
token or request quota. The configured Luna API should do substantially more proof work than
statement design. This is an execution instruction: begin and carry the work through the window,
with actual Lean proofs, integration, review and verification as the deliverables.

## Goal and scope

Advance the faithful formalization of Bizeul–Klartag–Lehec (BKL), *Presenting a proof of the
Kannan–Lovász–Simonovits conjecture*, arXiv:2610.05474v1, by proving the first concrete dependencies
of Theorem 3.1 and, ultimately, Theorem 1.1. Prioritize:

1. **Lemma 2.2, complete:** the tensor partial-symmetrization inequality with the exact `4^d`
   constant, symmetries, block positions, dimension range and trailing indices of the source.
2. **Lemma 2.1, L2/operator-domain part:** construct the unique centered inverse of the closed
   weighted generator and prove the source's norm and energy bounds. Keep this restricted
   counterpart explicitly partial until the full smooth polynomial-growth class is established.
3. **Lemma 3.6, initially on compactly supported smooth tests:** build the exponential-tilt average
   interface and prove its generator/gradient identity, with the precise derivative tensors and
   factorial normalization. Extend the test class if the necessary estimates can be proved.

The desired result is the strongest coherent, source-faithful subset of these targets that is
proved and verified within the window. A completed numbered lemma is real progress; a definition,
conditional endpoint, or compilation with a missing proof is not a completed paper theorem.
Do not promise a complete KLS proof in this window. Do not use a remaining theorem as an axiom
or as an extra premise of a purported unconditional theorem.

## Start and hard boundary

The existing Claude session is currently executing a separately owner-authorized publication /
Prove2Me operation. Finish or record the outcome of that operation first, preserving its existing
authorization and scope. Do not interrupt an upload or overwrite its files with proof workers.
Then record actual `T0`, `T0 + 6h`, `T0 + 6h30m`, and `T0 + 8h` in Asia/Shanghai in a machine-readable
execution record. The eight-hour clock starts when this proof block actually begins, not when
this document is prepared or queued.

- `T0 + 6h`: stop opening new theorem targets; end or bound outstanding proof searches.
- `T0 + 6h30m`: freeze the intended source/metadata tree and start the final full verifier.
- `T0 + 8h`: hard stop. End this block's remaining workers, preserve candidates, and give the
  final handoff. Do not roll silently into another eight-hour block.
- Before `T0 + 6h`, continue meaningful proof work when a first target finishes. Select the next
  named dependency below; do not stop after producing a plan or a literature summary.
- These are elapsed wall-clock boundaries, not a claim of eight hours of CPU time. Record outages,
  execution pauses, service limits and unfinished validation honestly.

## Read and pin the evidence

- Repository: `/Users/lyuyuwei/Documents/ChatGPT/KLS`.
- Read `AGENTS.md`, `HANDOFF.md`, `research/workflow.md`, `research/naming.md`, and the exact existing
  declarations before editing. Preserve historical decisions and earlier review artifacts.
- The completed comparison is
  `build/reviews/2026-10-07-new-kls-papers/REPORT.md`, with `statement-map.csv`,
  `missing-obligations.csv`, `DEPENDENCIES.mmd` and the strict `MainTheoremBridges.lean` client.
- BKL PDF:
  `/Users/lyuyuwei/Documents/ChatGPT/KLS-paper-sources/2026-10-07/2610.05474v1.pdf`.
  SHA-256: `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
- Song–Zhang alternative route: arXiv:2610.01447v2, PDF
  `/Users/lyuyuwei/Documents/ChatGPT/KLS-paper-sources/2026-10-07/2610.01447v2.pdf`.
  SHA-256: `fad3f750a121cd99f09213ea237fc71b66e97ad1699ecca1d07f74c2fd69d771`.
  BKL re-proves its needed criterion in Section 3; its first targets do not require formalizing
  the whole Song–Zhang paper. Do not reuse v1's main conclusion or v2's extraction-damaged constants.

At dispatch, HEAD was `36e7c781edab9875ca0bfe35d26992f005db7ced`, after the other publication task
committed the previously staged BGL work. Remote run 37516844384 was observed in progress, not
confirmed successful here. Recheck all of this at `T0`; do not assume the October 4 staged baseline
or a passed remote run. Save HEAD, real index tree, tracked and untracked status, relevant file
hashes, existing receipts, and a recoverable copy of any dirty work. Preserve `.cursor/`,
`.clinerules/`, credentials, unrelated files, and the actual index state.

## Roles and resource use

### Claude: source, statements, acceptance and integration

You own the literature contracts, proof decomposition, placement, full elaborated statement
review, dependency ordering and integration. You are the single editor of production files.
Spend your effort on the mathematical design and on unblocking workers; use the API actively
for proof bodies rather than writing every routine proof yourself.

Before dispatching a statement, freeze its full Lean context and inspect imports, namespaces,
universes, variables, instances, `include` / `omit`, notation, options and elaborated type. Compare
it with the PDF. Correct a defective statement yourself and re-freeze it; record the correction.

### Existing Luna API: the principal proof worker

The owner explicitly authorizes reuse of the existing Luna configuration and credential for
this run. Safe metadata checked at preparation: `/Users/lyuyuwei/.config/kls/gpt.env` exists,
with `GPT_BASE_URL`, `GPT_API_KEY`, `GPT_MODEL`; the model is `gpt-5.6-luna`.

- Reuse the existing authorized configuration and compatible proof driver; revalidate actual
  connectivity at start. Do not expose credential values in prompts, files or logs.
- Most Luna calls should request a proof body, private supporting lemma, repair of a proof
  against Lean diagnostics, or a competing proof strategy for an already reviewed statement.
  Mathematical statement ownership remains with Claude.
- Give the complete frozen context, exact goal, accepted dependency signatures, and actual Lean
  diagnostics. Do not send just a theorem header or an entire irrelevant repository dump.
- Use separate scratch candidates. Workers may return proof replacements and explicitly listed
  private helpers. They may flag a statement issue, but may not silently edit assumptions,
  definitions, public names, instances, imports or section context.
- Run independent proof batches concurrently when their dependencies are already accepted.
  Start with 2–4 manageable proof workers and adjust to the actual host and service limits.
  Serialize production edits and final builds. Concurrency is a coordination choice, not a
  spending quota; there is no user-imposed token, dollar or total-call cap.
- After repeated failed attempts on the same decomposition, inspect the errors, split the
  lemma or change strategy. Do not spend the window repeating an unchanged failing prompt.
- Keep provenance: prompt/context hash, model, request timing, candidate patch, diagnostics,
  acceptance result and parent dependency versions. Usage metadata may be recorded without
  imposing a quota. Keep all rejected attempts outside production imports.

### Owner's Codex: independent reasoning and review

Use the owner's actual signed-in Codex for difficult proof strategy, semantic review, dependency
and axiom audits, and acceptance of a frozen batch. It is a distinct resource from the Luna
relay. Do not label a Luna/API response a Codex review.

Preparation confirmed a local Codex executable, ChatGPT authentication, the default OpenAI
provider, and configured `gpt-6.1-sol` with `xhigh` reasoning. Recheck safe metadata at dispatch
without reading credential values. Prefer the owner's native Codex integration when available.
The installed official CLI is an acceptable way to use that same signed-in Codex account for
bounded read-only reviews; it must not be redirected to `GPT_BASE_URL` or charged through the
Luna credential. Preserve global authentication and provider settings.

- Give Codex the exact source version, frozen signatures, relevant source/PDF text, candidate
  diff, strict diagnostics and axiom closure. Have it check vacuity, edge cases, constant and
  tensor-block normalization, and hidden section hypotheses.
- Use a read-only reviewer, for example the installed `codex exec --sandbox read-only` with
  prompt via stdin and `--output-last-message` to an ignored review artifact. Use the configured
  model/settings; do not create unrelated desktop chats or alter another active session.
- Record the process/session identity and output path. A launched or stalled review is pending,
  not accepted. Bound each request by the remaining window and leave time for an actual result.
- Obtain an independent review of the primary tensor lemma and the strongest integrated analytic
  endpoint. If Codex is unavailable, continue useful proof work, record the missing review,
  and do not manufacture acceptance or silently substitute Luna.

## Proof batches and placement

Create a short placement plan before adding modules or changing public interfaces: mathematical
object, exact scope, existing owner, destination, imports, extend/split/create choice, API impact,
consumers and validation. Inspect existing owners again. The following are scope directions,
not permission to invent a catch-all directory or move unrelated modules.

**Batch A — BKL Lemma 2.2.** Define only the finite tensor, Hilbert–Schmidt norm, block permutation
and partial-symmetrization interfaces the proof consumes. Generic finite tensor/combinatorial
results belong in the lowest appropriate existing family, without KLS hypotheses. Avoid a new
one-file family, empty future modules, wrappers or duplicate tensor definitions. Freeze the
source's subset-sum identity (25), Vandermonde/binomial estimates and the resulting `4^d` bound.
Give Luna the supporting identities as separate proof tasks; Claude checks block indexing and
the endpoint; Codex reviews the exact source match.

**Batch B — BKL Lemma 2.1, restricted inverse.** Reuse the closed gradient form, the self-adjoint
closed generator, kernel = constants, centered form-domain Poincare estimate, and existing
Lax–Milgram machinery. Prove existence, uniqueness, mean-zero normalization, the norm bound and
the energy identity/bound, for the actual closed operator and domain. Generic inverse tools may
extend `Analysis/Semigroup`; concrete results belong with the owning heat/weighted-gradient family.
Do not conflate form domain with operator domain, or replace regularity/existence by hypotheses
that assume the required solution. Source Lemma 2.1 stays partial until the full class A and
polynomial-growth regularity are established.

**Batch C — BKL Lemma 3.6, tilt calculus.** Reuse `Measure.tilted`, the tilted-density and integration
by parts APIs. Build the normalized exponential tilt, tilt average and derivative identities with
the exact `1/d!` convention. Initially compactly supported smooth tests are an explicit restricted
target. Prove integrability, positivity of the normalizer, differentiation under the integral and
centering identities where needed. Pin tensor conventions from Batch A before dispatching higher
derivative tasks. Do not infer a multivariate/all-orders statement from a scalar mgf lemma.

**Next dependencies, if time remains.** Extend accepted batches toward the full Lemma 3.6,
Lemma 3.4 on a genuinely justified test class, or the compact-resolvent/first-eigenfunction
prerequisites of Theorem 3.1. Read the relevant pinned source before choosing a target. The Letwin
quadratic-form result and Eldan localization remain explicit unproved dependencies; they cannot
be bypassed by postulating their conclusion. It is acceptable to prepare a narrowly scoped audited
client for an existing stochastic library if this unblocks a named target, but do not replace the
main proof window with a broad library survey or adopt an entire unaudited dependency stack.

## Schedule and continuation

| Elapsed time | Work and required outcome |
| --- | --- |
| 0:00–0:30 | Fresh baseline and timing record; source contract and placement; freeze the first batch; start real Luna proof calls and a bounded Codex design review. |
| 0:30–3:00 | Primary tensor lemma and independent analytic/tilt prerequisites. Compile accepted helpers, dispatch consumers only after dependency acceptance. |
| 3:00–5:30 | Integrate the strongest completed endpoints; advance the inverse and tilt targets; independent Codex review of a frozen accepted batch. |
| 5:30–6:00 | Finish the current coherent batch and repair issues; select no speculative new large target. |
| 6:00–6:30 | Stop expansion; close workers, strict clients and semantic review; update only justified progress records and freeze. |
| 6:30–8:00 | Full local verifier, repair and appropriately rerun failed checks; final evidence and remaining-work handoff. |

Persist the queue, accepted dependency hashes, timing boundaries and next actions so compaction
or a session interruption can resume the same goal. Any supervisor/watchdog must enforce this
block's deadline and control only its own recorded child processes. Do not rely on a future
unbounded conversation turn to stop workers, and do not kill unrelated Lean or upload processes.

## Acceptance, progress records and delivery

- Every accepted proof must compile under the pinned toolchain with warnings as errors, retain
  the reviewed full elaborated type and definition dependencies, and have an actual consumer
  client. Audit its exact public declaration and downstream endpoint with `#print axioms`.
  Only `propext`, `Classical.choice`, `Quot.sound` are acceptable in the certified closure.
- Check nonvacuity and source edge cases. For Batch A include nonzero tensors and boundary
  dimensions/block sizes; for Batch B instantiate the actual weighted generator and applicable
  Gaussian/model data rather than a theorem with an impossible premise.
- Follow the project gates and run `python3 research/verify.py` on the final frozen tree.
  Do not claim a receipt covers edits made afterward. If verification is incomplete at the
  deadline, preserve the exact snapshot and report it as incomplete.
- Review `literature.json`, the relevant numbered lemma maps, Blueprint evidence, nodes, priorities,
  diagrams and current summary when proof status changes. Add the pinned BKL entry if needed,
  retain all numbered statements, and use ✓ / ⇑ / ◐ / ○ faithfully. Supporting lemmas do not
  mark the paper covered. Keep local KLS open until that exact theorem is proved and verified.
- Regenerate progress through `python3 research/progress/update.py` using an isolated temporary
  Git index populated with the intended proof/metadata state, preserving the user's real staging.
  Synchronize corresponding hashes and consumers; never edit generated blocks by hand.
- Keep repository-facing prose English. Use a dated current execution log and a compact current
  `HANDOFF.md`; preserve old records and the October 7 comparison as historical evidence.
- This new eight-hour proof authorization permits local proof/API/module/documentation edits,
  local checks, scratch workers and the explicitly described model collaboration. It does not
  extend the earlier publication operation to these new results: no new commit, push, tag,
  remote CI, Prove2Me upload, Slack message, reset, clean, memory update or credential change
  for this proof block without a subsequent owner instruction.

Save new evidence under `build/reviews/2026-10-07-bkl-eight-hour/`: `execution.json`, `WORKLOG.md`,
`accepted-statements.csv`, worker logs/candidate provenance, Codex review(s), verification receipt
pointer and `FINAL.md`. The final Chinese explanation must give the actual elapsed window,
exact new proved statements and source locators, partial results and unresolved dependencies,
Luna versus Codex usage, verification boundaries, baseline/index preservation, and the next
three concrete proof tasks. Report new work separately from the already completed BGL baseline.

Official local Codex references checked when preparing this handoff:
[non-interactive mode](https://learn.chatgpt.com/docs/non-interactive-mode) and
[authentication](https://learn.chatgpt.com/docs/auth). These document invocation and account
separation; actual runtime success still requires the observed session result.
