# Eight-hour plan: upper Minkowski recovery and BV identification

Status: execution authorized by the user and started on 2026-09-30 at 01:07:29
Asia/Shanghai (2026-09-29T17:07:29Z). Expansion cutoff: 07:22:29; wrap-up:
08:37:29; hard stop: 09:07:29 Asia/Shanghai. Previous deadlines do not apply.
Stage A was delivered as message 9 in the existing Claude BV phase-22 session;
the UI visibly showed Running. Stage A is independently accepted. After a
locked-host pause at 01:47, the user restored access and authorized continuation
at 02:17 Asia/Shanghai. Stage B was delivered as message 11 and visibly Running;
heartbeat `kls-claude` is ACTIVE again. A temporary task-owned `caffeinate -di`
assertion prevents idle system/display sleep until the original deadline; it
does not change authentication or persistent lock settings. Details and PID are
in `build/audit/upper-recovery-overnight/keep-awake.json`. The coordinator chat is
`01a0ee14-65a8-7f80-91a8-77dc57eb0aaf`.

## Baseline and objective

At planning time HEAD is `443f352`, with uncommitted phase-23 proofs, acceptance
records, CI-policy changes and other local edits. Preserve all of them and the
real Git index. Phase 23 is recorded as independently accepted in
`codex-bv-overnight-review.md`; planning has inspected the current declarations
but has not rerun its verifier. Recheck source/receipt correspondence at startup.

Primary objective: turn the integrated upper-content bound into genuine
lower-to-upper recovery. Stretch objective: identify the relaxation of upper
Minkowski content with the existing metric BV perimeter, in the existing
probability-law / Borel normed-group scope. This is not a general metric-space
theorem, an RCD identification, or a dimension-free KLS proof.

Read the current sections of `HANDOFF.md`, `claude-bv-overnight.md`,
`codex-bv-overnight-review.md`, `AGENTS.md`, `research/workflow.md`, and
`research/naming.md`. Dated historical next steps do not override current source.

## Roles and schedule

Claude is the sole implementation writer. Codex (the API coordinator) selects
bounded stages, reviews mathematics, writes separate independent audit clients,
and accepts or rejects frozen deliveries. Codex does not edit a production file
while Claude owns it. Shared documentation has one writer at a time. At each
handoff Claude stops writing and signals `READY_FOR_CODEX_REVIEW`; Codex finishes
review before releasing the next stage. No additional agents are required.

| Elapsed time | Claude | Codex |
| --- | --- | --- |
| 0:00–0:30 | Inspect baseline; record placement and exact theorem targets | Save dirty baseline/index fingerprint; inspect receipt and available Claude session |
| 0:30–2:30 | Stage A: quantitative small-radius selection and one-set recovery | Review hypotheses and edge cases; prepare independent clients without importing unfinished additions |
| 2:30–3:15 | Freeze; address concrete review findings after permission to resume writing | Strict independent review of Stage A; accept or return exact counter-obligation |
| 3:15–5:15 | Stage B after acceptance: diagonal upper-content recovery from BV | Review diagonal estimates, finite costs and infinite-value branches |
| 5:15–6:15 | Stage C if B is accepted: relaxed-upper equality and useful direct corollaries | Check both inequalities and definition/test-class fidelity |
| 6:15–7:30 | Stop expansion; resolve failures, synchronize documentation, freeze source | Run/review the final full verifier and independent clients on the same snapshot |
| 7:30–8:00 | Deliver exact achieved scope and remaining obligations | Final evidence report; stop at the deadline |

These are time budgets, not predicted proof durations. If A takes longer, drop C
first, then B; preserve a verified A rather than weaken its statement. Reserve
the final 105 minutes for verification and handoff. If checks exceed the deadline,
report them as running or incomplete, never passed. Finish early if all scoped
deliverables and checks are complete; do not invent filler work.

## Stage A: lower-to-upper recovery

Starting API, in `formalization/FunctionalInequalities/KLS/Geometry/Cheeger/`:

- `UpperMinkowskiContent.lean`: `upperMinkowskiContent`,
  `minkowskiContent_le_upperMinkowskiContent`,
  `setLIntegral_upperMinkowskiContent_thickening_le`.
- Reuse the existing positive-slack selection argument where appropriate;
  do not assume the radius-content function is measurable.

First prove the quantitative selection consequence: for `r > 0` and real
`epsilon > 0`, select `0 < s < r` with upper content of `B^s` at most
`(nu(B^r) - nu(B)) / ofReal(r) + ofReal(epsilon)`, with precise Lean
coercions and `ENNReal` arithmetic. Keep the integrated theorem's legitimate
generality where possible.

Then, for measurable `B` with finite lower Minkowski content, construct positive
radii tending to zero and measurable thickenings `A_n` such that their indicators
converge to `1_B` in actual `L1(nu)` and
`limsup upperMinkowskiContent(nu, A_n) <= minkowskiContent(nu, B)`.
Use radii realizing the lower-content liminf and prove the vanishing mass
increments. Do not assume `nu(closure B) = nu(B)`; derive the needed consequence
from finite lower content. Do not claim equality with the original lower content.

Audit empty/full sets, zero content, boundary atoms, radius endpoints, and a
uniform-interval example. Separate finite-content recovery from the infinite
case; never use `toReal` to silently discard infinity.

## Stage B: actual upper-content recovery of BV perimeter

Use `Perimeter/MetricBVMinkowski.lean` and its existing
`exists_minkowskiRecovery`, indicator convergence and content convergence.
For `perimeter(nu, B) < top`, choose one sufficiently accurate Stage-A
approximation for each lower-content recovery set. Prove explicit diagonal
indicator-error and upper-content bounds, then obtain measurable `U_n` with
`1_(U_n) -> 1_B` in `L1` and
`upperMinkowskiContent(nu, U_n) -> perimeter(nu, B)` in `ENNReal`.

The lower bound must follow from the existing BV lower semicontinuity,
`perimeter <= lower content`, and `lower content <= upper content`.
Do not assume the recovery sequence or the desired limsup bound.
Retain the existing target-set generality if supported by the source proofs;
state any necessary measurability restrictions explicitly.

## Stage C: relaxation identity

Inspect `Perimeter/RelaxedMinkowski.lean`. Reuse its actual measurable-set
sequence class and actual indicator `L1` convergence. Define the upper analogue
by the infimum of sequence liminfs of the genuine upper content. Prove
`relaxedUpperMinkowskiContent(nu, B) = perimeter(nu, B)` and hence equality with
the existing relaxed lower content. The easy inequality is termwise domination
plus lower semicontinuity; the reverse uses Stage B at finite perimeter and the
trivial order bound at infinite perimeter. Cover empty approximation classes.

Do not replace either content definition, redefine perimeter, or assert
pointwise upper/lower content equals perimeter. Additional Cheeger quotient
identifications, general metric extensions and spectral work are outside this run.

## Placement, verification and delivery

Before editing, record owner, scope, destination, imports, extend/split decision,
API impact and validation. Stage-A content estimates belong with the existing
upper-content owner; BV recovery and relaxation comparison belong at the
perimeter integration boundary. Avoid a dependency cycle and preserve existing
public declarations. New modules require actual responsibility separation.

No `sorry`, `admit`, new axioms, hidden conclusion hypotheses, weaker substitute
targets, compatibility aliases or unrelated migrations. Independent clients must
exercise the full signatures and inspect transitive axioms. Use strict compilation
and the workflow's filtered current-source dependency view; cached compilation
alone is insufficient. Run change-appropriate checks during development and one
final frozen `python3 research/verify.py` after source/documentation stabilization.
Run an earlier full verifier if a material dependency concern justifies it.

Synchronize current HANDOFF/root summary, Blueprint and the complete four-route
English progress views only to accepted proof scope. Use canonical records and
an isolated index for `research/progress/update.py`, then its `--check` and view
tests. Refresh only justified evidence hashes; do not weaken any checker or
rewrite historical records to obtain a pass. Keep the real index unchanged.

Place final receipt/log pointers under ignored
`build/audit/upper-recovery-overnight/`; record theorem signatures, source hashes,
commands, exit codes, snapshot match, independent review and remaining gaps.
Acceptance notes written after a receipt must be distinguished from its snapshot.
No commit, push, remote CI, reset, clean or changes to the moment-map workstream.

## Coordination and failure handling

At actual start record timezone, start, start+6h15 expansion cutoff,
start+7h30 wrap-up and start+8h stop. Observe the intended Claude session before
sending; avoid duplicate prompts. Read a completed checkpoint before scheduling
the next stage. A ready signal is not acceptance. Prefer durable checkpoint
messages and bounded checks over tight polling. If a recurring wakeup is used,
notify only on completion, material failure or required user action; stop it when
the window closes. A scheduled wakeup alone is not evidence of productive work.

If computer control reports a locked host, do not bypass it or attempt unlock.
Continue available local read-only review, save the undelivered assignment and
report the block. Never count blocked intervals as work or extend the deadline
automatically. If quota/session limits prevent continuation, preserve progress
and do not buy quota or silently switch accounts. Within a stage, after 45–60
minutes without progress on one obstacle, isolate the exact lemma, try a different
valid proof route, then fall back to the last accepted bounded deliverable.

## Copyable launch instructions

For the API/Codex coordinator:

> Execute this plan for an eight-hour window starting now. Direct Claude through
> the available authorized session, independently review frozen stages, and advance
> only accepted stages. First read this entire file and inspect the live baseline.
> Preserve unrelated work and the real index. Do not commit or push. Stop expansion
> at 6h15 and stop the run at 8h. Deliver exact verified results and remaining gaps.

For Claude, sent by the coordinator after inspecting the current session:

> Read research/handoffs/2026-09-30-eight-hour-upper-recovery-plan.md and the
> current repository instructions. You own implementation; Codex owns independent
> acceptance. Start with Stage A only, record the placement plan, prove and strictly
> test the exact statements, then freeze at READY_FOR_CODEX_REVIEW with source
> hashes and logs. Preserve the dirty baseline and real index. Do not commit or
> push. Do not start Stage B until Codex accepts A and releases the next assignment.
