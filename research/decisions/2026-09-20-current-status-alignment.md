# Current status alignment and next analytic task

2026-09-20. This is a **status-report correction**, not a new mathematical result or a
reassessment of the correctness of the existing proofs. The inspected source baseline is
`f8e4ca8b63a53b2de070f02d93a3d3f7674a4648`. No Lean source, theorem statement, certificate,
Blueprint proof marker, or pinned upstream portfolio is changed by this update.

## Corrections to the current queue

The root README, progress views and task gaps had retained older pending-work descriptions
after the corresponding proofs were integrated. In particular, they still mentioned sharp
scalar Sard, the Cheeger superlevel bound and reverse infimum comparison, and the Markov
construction as missing. The progress generator checked consistency with those records;
it did not detect that the records were stale.

| Component | Current evidence | Status and scope |
| --- | --- | --- |
| Sharp scalar Sard | `Analysis/Sard/Sharp.lean`, `Analysis.sard` | Proved at `C^(finrank)` regularity; not a general vector-valued sharp Sard theorem |
| Vector coarea | `Analysis/Lipschitz/VectorCoarea.lean`, `Analysis/Lipschitz/Local.lean` | Proved for Lipschitz and locally Lipschitz maps |
| Cheeger superlevel integral | `KLS/Geometry/Cheeger/Equality.lean`, `smoothConstant_mul_lintegral_min_superlevel_le` | Proved under its stated density and test assumptions |
| Cheeger infimum equality | Same module, `smoothConstant_le_minkowskiConstant`, `minkowskiConstant_eq_smoothConstant`; `Solutions.LemRelativePerimeterCheegerInfimum` | Both directions proved, with certified intrinsic transport |
| Canonical energy / Cheeger energy | `Energy/Cheeger/Identification.lean` | `E^can = 2 Ch` for every Borel probability law in the local-slope convention |
| Literature gradient characterization | `Poincare/LocalSlope/Gradient.lean` | Proved; the three local clauses of the density frontend identification are complete |
| Semigroup generation and specialisation | `Analysis/Semigroup/Generated/`, `KLS/LogConcave/HeatSemigroup/Basic.lean` | S1–S8 and the concrete weighted-gradient semigroup are proved |
| Markov properties | `Analysis/Semigroup/Generated/Markov.lean`, `KLS/LogConcave/HeatSemigroup/Markov.lean` | Positivity, preservation of one and integrals, sub-Markov bounds, absolute-value domination and contraction of finite essential bounds on `L²` are proved |
| Full Cheeger–Buser comparison | `KLS/Geometry/Cheeger/Inequality.lean`, `KLS/LogConcave/Line/Buser.lean` | Cheeger half proved; Buser with 12 in affine dimension at most one proved; full π target still pending |

The concrete Markov results assume nonempty interior of the support. They apply to the intrinsic
law of an arbitrary log-concave law using the already-proved intrinsic-support premise. They
are not a separate construction of a semigroup on all `L¹` functions. No gradient estimate,
small-time heat estimate, or complete Buser comparison is inferred from Markovianity alone.

There are **26 registered certificates and one explicit target hole**, `KLS.kls` in
`KLS/Target.lean`. The former WIP modules are removed. The intentional target is outside every
certificate closure; the dimension-free KLS bound remains open. Historical zero-hole counts
describe the period before the target theorem was added, not the current whole-library count.

## Remaining work and handoff (initial scope; superseded below)

The next task is [generator identification and Bochner route exploration](2026-09-20-bakry-emery-handoff-prompt.md)
for smooth convex potentials and identity gradient weight. It must distinguish a local
differential identity from a domain-correct statement about the existing heat semigroup.

The remaining program consists of the generator/Γ/gradient-estimate interfaces, the passage to
general log-concave laws, and the small-time heat, perimeter and spectral-gap estimates needed
for the target π comparison. No complete proof route is asserted here. The four active KLS
branches retain their existing open research requirements. The owner's recorded π target is
unchanged; the one-dimensional constant 12 is not substituted for it.

The new diagram nodes for the analytic program are auxiliary records with explicit evidence.
The Cheeger equality node now derives its status from the existing Blueprint mapping. The
full comparison node continues to derive its pending status from Blueprint. Dotted analytic
program edges describe planned work, not proved sufficiency implications. NEXT is written in
the node label as well as highlighted; pending work is red, completed local proofs blue,
partial work orange and excluded work gray. The complete approach table remains on the same page.

## Evidence and validation boundary

The existing local receipt `build/verification/20260919T171810.344913Z/report.json` records
10 passing gates, 262 replayed modules and 367 axiom reports containing only standard axioms.
Before the documentation edits, all 726 recorded file hashes matched the workspace. The
Markov audit client was separately rerun with `-DwarningAsError=true`: it passed and its
19 axiom reports contained no `sorryAx`.

These edits change the full source/documentation snapshot. The previous receipt remains
evidence for the unchanged Lean sources under its stated trust scope; it is **not** a new
full verification receipt for this documentation revision. This update uses structural
ledger/Blueprint/task checks, generated-view checks, existing progress tests, and a review of
diagram links and route coverage. It does not run a new full Lean build or remote CI.

The earlier dated decision records and handoff rounds remain intact. Current summaries point
here and to the new handoff prompt so that historical next-step instructions are not reused
as today's queue.

Validation completed for this update:

- Atlas: 75 mathematical nodes, 26 certificates, no dependency cycles; ledger: 0 errors;
  Blueprint: 88 labels, 4 active routes, 0 errors.
- Progress regenerated and checked from the intended records staged in a temporary Git index;
  all 7 existing progress/literature tests passed. The real index was left unchanged.
- Every diagram/evidence repository link resolves to a current local file. All four active
  route groups remain present; the pinned portfolio is unchanged; the only NEXT focus is BE.
- All 345 Lean files recorded by the previous receipt retain their recorded hashes.
  `git diff --check` passed. No commit or push was performed.

## Owner priority update: complete Buser first (2026-09-20)

The owner subsequently asked to prioritize completion of Buser. The current handoff is now
[the full Buser implementation prompt](2026-09-20-buser-handoff-prompt.md). The target is
`Psi_KLS(mu)^2 <= pi C_P^lit(mu)` for every finite-dimensional log-concave law, with no
unresolved analytic assumptions. The earlier route-only prompt remains a historical technical
outline; its restrictions on implementation no longer define the current task.

Generator identification, Bochner/gradient estimates, the passage to general laws and small-time
heat bounds are internal milestones. The diagram's sole NEXT focus moves from BE to the full
Cheeger–Buser comparison CB, whose Blueprint-derived status remains pending. Neither choosing
this target nor completing a restricted smooth case is evidence of the full theorem. Its eventual
completion still will not discharge the independent open research conditions of the KLS routes.

The root summary, current handoff, verification pointer, task queue and generated views are
synchronized to this priority. No Lean source or completion marker changes in this scheduling
update. The earlier validation paragraph records the initial BE-focused revision; regenerate and
check the views again for this CB-focused revision before delivery.
