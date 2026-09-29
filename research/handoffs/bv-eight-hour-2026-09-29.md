# Eight-hour BV test-class continuation (2026-09-29)

User authorized eight hours of continued work, with Fable for hard tasks. Window:
2026-09-29 00:54:27 to 08:54:27 Asia/Shanghai (2026-09-28 16:54:27 to
2026-09-29 00:54:27 UTC). Begin wrap-up at 08:24; do not start new segments then.
At deadline request a safe checkpoint, record verified/unfinished work and pause
kls-claude. Eight hours is a work window, not a guarantee of theorem completion.

Phases 1–16 accepted; see codex-bv-overnight-review.md for exact frozen evidence.
Existing Claude chat: KLS BV phase5 perimeter recovery,
https://claude.ai/epitaxy/local_95418acf-4709-4736-abdf-9fd25c8d7780.
Observed Idle, context67%, model switched to Fable 5.1 for this hard extension.
No second implementation session is running or authorized concurrently.

## Source comparison and scope

Primary reference inspected: Ambrosio–Di Marino–Gigli, arXiv:1603.08412,
https://arxiv.org/html/1603.08412, Definition 3.3, Remarks 3.4–3.5, Theorem 3.6.
Definition 3.3 uses globally Lipschitz approximants and global L1 convergence;
Remark 3.5 distinguishes the locally Lipschitz and L1_loc variants. Do not
conflate these or keep claiming that a locally Lipschitz bridge is necessary
for the globally Lipschitz definition. Existing phase3 already supplies a
finite-measure global-Lipschitz sequence bridge; an exact named infimum equality
may still need to be packaged. Check the actual source before literature claims.

## Phase 17 — first assignment; stop for Codex review after this segment

For a proper metric space with Borel structure and a finite Borel measure nu,
prove that any sequence f_n of genuinely locally Lipschitz real functions
converging to an indicator in global L1 admits an actual existing
MetricBV.ApproximatingSequence with no larger liminf of integrated actual local
slopes. In particular prove perimeter <= that liminf. Use Mathlib's genuine
LocallyLipschitz notion, not an input global Lipschitz constant or an assumed
approximation/energy comparison. Retain current perimeter/Test definitions.
Handle the empty carrier, zero measure, infinite slope costs and empty classes.
No conclusion-bearing premise, sorry or new axiom.

Suggested proof: clamp to [0,1], multiply by radial cutoffs; on a proper space,
compactness upgrades a locally Lipschitz compactly supported function to globally
Lipschitz (prove the needed global bound including pairs crossing the support).
Prove actual pointwise slope/error estimates using locality/product control,
then finite-measure tail control. Do not assume a uniform Lipschitz constant for
the original sequence. If this proof needs another valid hypothesis, report the
precise obstruction before silently strengthening the assignment. A proved
proper-space scope is not the general metric-space literature theorem.

Placement plan before editing: generic compact-support Lipschitz helper in an
existing owning analytic family if reused; test-class bridge in the metric
perimeter family, preferably a focused TestClass/approximation module if this
separates properness/local-Lipschitz imports from the existing basic object.
Inspect research/workflow.md and research/naming.md, existing owners and imports;
record final destination, scope, dependencies, extend/create decision, API impact
and validation. No old-signature changes or compatibility aliases. Keep generic
owners free of log-concave/spectral dependencies.

Strictly compile affected modules and a genuine audit including a non-globally
Lipschitz input example (for example x squared on a compactly supported law),
and empty/zero/degenerate cases. Inspect transitive axioms. Update precise English
handoff/root/four-route progress through canonical records and isolated-index
generation; preserve the real index. Freeze then run research/verify.py workflow
gates. Receipt build/audit/metric-bv-local-lipschitz/receipt.md must state exact
snapshot identity, report, scope, gaps, READY_FOR_CODEX_REVIEW and writing paused.
Do not edit Codex's review record. Do not start the next segment before acceptance.

## Bounded follow-on roadmap (not concurrently assigned)

After phase17 acceptance, next prove/define the precise relaxation infimum over
local Lipschitz global-L1 sequences and equality with existing perimeter in the
proved proper/finite setting, then actual closed intrinsic support specialization.
If useful, treat bounded-ball L1 convergence separately, with an explicit exact
notion and a proved diagonal/clamping/tail argument; do not call it arbitrary
L1_loc without checking conventions. Package global-Lipschitz Definition3.3
comparison and correct documentation distinctions. Next possible bounded segment:
actual relaxed Minkowski set-infimum equality from existing recovery and lower
semicontinuity, including infinite cases; extend metric scope only after inspecting
which normed-space dependencies are essential. Do not declare the whole ADMG
paper, general RCD/Buser or dimension-free KLS finished. Codex chooses one exact
next assignment after each acceptance. No unrelated research workstream.

## Coordination and preservation

Claude/Fable implements; Codex independently reviews exact signatures, arguments,
quantifiers, all edge cases, genuine own strict clients, transitive standard-only
axioms and frozen workflow gates. No competing proof edits or builds while Claude
runs. Preserve all existing dirty work, real index, moment-map-spectral.md and
/private/tmp/kls-affine-w2-liminf. No commit/push/reset/clean or approval/security
bypass. Fable authorization does not authorize purchases or quota upgrades.
Safe chat rollover near context limit is authorized: save exact checkpoint and
receipt/source identities, ensure old session paused, create same-project session,
verify delivery and update exact title/URL. Never two implementation sessions.
Control timeout: at most one reconnect per scheduled run; inspect prompt/messages
before resend; after three consecutive failed checks pause and report. Stay quiet
on unchanged state; notify milestones, failure or required user action only.

Dispatch confirmed: phase17 is message25 in the existing active Claude session;
UI shows Running and Stop, model Fable5.1 High, context67%. No duplicate dispatch.
