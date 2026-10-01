# Eight-hour ADMG continuation: measures finite on bounded sets

User request: design and execute an eight-hour workflow while the user sleeps.
This is a new authorization to continue the current paper-formalization work;
the accepted finite-total-mass run is complete and its receipts stay historical.

Window: 2026-09-30 22:52:18 to 2026-10-01 06:52:18 Asia/Shanghai
(UTC 2026-09-30 14:52:18 to 22:52:18). Stop theorem expansion at 05:07:18
local (UTC 21:07:18), start final handoff by 06:22:18 (UTC 22:22:18).
Never extend automatically. These are time budgets, not proof-duration promises.

## Source and exact objective

Ambrosio--Di Marino--Gigli, *Perimeter as relaxed Minkowski content in metric
measure spaces*, https://arxiv.org/html/1603.08412, sections 2--3, Lemma 2.1,
Lemma 3.2, Remark 3.4 and Theorem 3.6. The paper's measure is finite on bounded
Borel sets; Definition 3.3 and Theorem 3.6 concern Borel targets of finite mass
and actual global indicator L1 convergence. Finiteness on compact sets alone is
insufficient on nonproper spaces. Infinite mass targets are not part of this
published endpoint. Do not infer complement symmetry at infinite total mass.

The current chain already proves both recoveries and both relaxed identities
for finite Borel measures on arbitrary metric spaces. This run removes the
total-mass restriction where the paper supplies a valid argument. It must first
establish the required support and target-mass bounds. Keep the established
perimeter, genuine content definitions and actual approximating classes.

## Execution budgets and gates

1. First 75 minutes: finite test cost from finite mass of its closed support;
   specialize to a measure finite on bounded Borel sets, and check the proper
   locally finite case and Lebesgue measure. Inspect every use of total mass and
   save an exact obligation list. No progress marker for the full endpoint.
2. Through hour 3: Remark 3.4's bounded-support reduction for globally Lipschitz
   approximants to a finite-mass measurable target. Replace the old complement
   mass cutoff error with an integrable-function or target-tail error. Choose
   actual radii diagonally; no hypothesis containing the desired recovery.
   The zero/empty carrier and infinite-cost branches remain explicit.
3. Through hour 4.5: the local-slope coarea estimate for nonnegative Lipschitz
   tests whose positive support has a finite-measure thickening, as in Lemma
   3.2. Use a finite-measure neighborhood or the actual support majorant; do
   not integrate a constant over an infinite measure. Derive the one-sided
   perimeter/content bridge for finite-mass targets.
4. Through hour 6.25: compose actual lower recovery and its relaxed identity
   at the justified measure/target scope. Extend upper recovery and Lemma 2.1
   only after proving finite neighborhood mass and radius-local estimates;
   an accepted lower-only endpoint is a valid bounded deliverable. Do not
   weaken targets to call the full published theorem complete.
5. Final 105 minutes: freeze mathematics, repair regressions, compile strict
   signature/edge clients, audit transitive axioms, synchronize exact English
   scope and progress, and run one frozen full `python3 research/verify.py`.
   Before/after source snapshots must match. Deliver verified declarations,
   command exits, receipt pointers, trust boundary and remaining obligations.

If an obstacle stalls for 45--60 minutes, record its exact statement and try a
different valid proof route. Save every accepted bounded result; continue the
remaining authorized work instead of filling the window with redundant checks.
At the cutoff stop expanding even if the endpoint is not complete. At the hard
deadline save the actual state, stop owned subprocesses and pause the heartbeat.

## Placement plan and API discipline

Owner: metric BV tests/perimeter and their integration with genuine Minkowski
contents. Scope: arbitrary metric Borel spaces, with explicit finite support or
finite target mass premises when needed. First edit extends
`Perimeter/MetricBV.lean`: local slope vanishes outside closed function support,
and test cost is finite when that closed support has finite measure. Existing
`cost_ne_top` retains its finite-measure signature. No new object or family is
needed. Use existing imports and the local-slope owner; private single-use
helpers stay local. A public generic slope-support fact may belong in
`Energy/LocalSlope/Basic.lean` only if real consumers justify it.

Later support reduction stays in `MetricBV.lean`; coarea in
`Cheeger/LocalSlopeCoarea.lean`; content estimates in the existing content owners;
recovery/identification at `Perimeter/MetricBVMinkowski.lean`,
`UpperMinkowskiRecovery.lean` and `RelaxedMinkowski.lean`. Read workflow/naming and
record any revised placement/API map before each later stage. Preserve old
finite/probability instances and compare elaborated interfaces. No path moves,
compatibility aliases, duplicate perimeter/content definitions or empty modules.

Validation: meaningful independent strict clients against a fresh
workflow-filtered current-source dependency view, standard-only declaration
axioms, nonproper metric scope, Lebesgue measure with infinite total mass,
zero measure, finite and unbounded finite-mass targets, atoms, empty sets,
infinite perimeter/cost and old finite/probability clients. Do not equate cached
compilation, local replay, ledger certificates or remote CI.

## Persistence, credentials and preservation

### Stage B placement refinement (23:10 Asia/Shanghai)

Extend the existing LipschitzBridge section of `MetricBV.lean` with pointwise
and integrated cutoff estimates using the original indicator L1 error and
`nu(B minus ball)`; derive convergence and the Lipschitz-sequence bridge for
measurable targets of finite mass under an arbitrary Borel measure. The test
definition and all existing finite-measure signatures remain unchanged.
The fixed radii `n` may suffice after the stronger estimate, so a diagonal
radius choice is unnecessary if the Lean proof confirms it. Extend
`TestClassRelaxation.lean` at its existing identification boundary to compare
the actual Definition 3.3 infimum with the perimeter at this target scope.
No new module/import cycle or measure typeclass is needed. Private single-use
pointwise estimates stay with their consuming test-cost/error proof. Validate
the empty carrier, zero/infinite slope costs, infinite-total-mass Lebesgue
measure, finite and unbounded finite-mass targets, and the old client scope.
This changes no existing declaration name, argument, visibility or universe;
new finite-target-mass declarations record their different hypothesis scope.

### Stage C placement refinement (23:39 Asia/Shanghai)

Extend `Cheeger/MinkowskiContent.lean` with the radius-local restriction identity:
if a positive neighborhood of a set lies in a measurable set, restriction to
that set preserves the small-radius quotients and lower content. Extend
`Cheeger/LocalSlopeCoarea.lean` with positive-level coarea under finite mass of
a support thickening, using the existing finite-measure theorem for the
restricted measure. A nonnegative-function specialization may recover the
all-level statement because nonpositive superlevels are the whole carrier.
No sigma-finiteness or properness is inferred for the original measure.
Extend the existing plateau-ramp bridge in `Perimeter/MetricBVMinkowski.lean`
with explicit measurable finite-target mass and use the proved Stage B bridge.
Old finite-measure signatures remain intact; additive names distinguish the
new scope. No definitions, module moves or import cycles are needed. Validate
actual restricted quotients, finite neighborhood mass, positive levels, empty
support, zero measure, infinite costs, Lebesgue examples and old clients before
composing recovery. Recovery and upper-content scope remain pending until their
radius-local obligations are proved.

### Stage D lower-recovery placement refinement (23:55 Asia/Shanghai)

Extend `Perimeter/MetricBVMinkowski.lean` with quantitative positive-superlevel
selection under finiteness on bounded Borel sets, and an additive existence
form of actual lower-content recovery. Reuse existing recoveryTest and widths;
choose levels and sets locally inside the proof, without defining duplicate
recovery objects. Closed positive superlevels are bounded and have finite mass.
For the lower bound on arbitrary approximating classes, use finite target mass
and global indicator L1 convergence to prove eventual finite mass of the
approximating sets; no termwise finite-mass assumption is hidden in the class.
Keep all old finite-measure recovery names, arguments and objects unchanged.
Extend `Perimeter/RelaxedMinkowski.lean` at the existing infimum identification
boundary with the measurable finite-mass target identity under the explicit
finite-on-bounded-Borel-sets premise. Preserve the actual approximating class,
including its finite prefix, top branch and zero/empty cases. No module/import
changes or ledger promotion are needed. Validate actual global L1 and content
limits, bounded recovery sets, Lebesgue infinite total mass, arbitrary finite
prefixes, finite/probability regressions and standard-only transitive axioms.
Upper recovery and the full radius-liminf coarea chain remain separate pending
obligations and are pursued only within the bounded expansion window.

### Stage D upper-recovery placement refinement (00:14 Asia/Shanghai)

Extend `Cheeger/MinkowskiContent.lean` with existence of a finite-mass positive
thickening from finite target mass and finite lower content. This generic
radius fact needs no boundedness, properness or global finiteness. Extend
`Cheeger/UpperMinkowskiContent.lean` with the upper-content restriction identity
and actual lower-to-upper recovery at measurable finite-mass targets, by
restriction to that proved finite neighborhood and a tail of small radii.
Prove transfer of original global indicator L1 using the actual support of the
indicator difference. Reuse the accepted finite-measure radius/derivative proof
only inside the finite restriction region; establish the small-radius
thickening containment before transferring upper contents. No original-measure
real/toReal mass is silently treated as finite. A one-use indicator-transfer
helper stays private in this owner. Keep the old finite-measure signatures.
After these obligations pass, extend `Perimeter/UpperMinkowskiRecovery.lean` with
existence/diagonal recovery at the finite-on-bounded Borel scope, reusing the
actual lower-recovery sequence and proving finite masses for upper sets. The
lower bound on arbitrary approximating sets uses eventual finite mass and pure
liminf <= limsup order, without changing the existing comparison API or class.
Extend `Perimeter/RelaxedMinkowski.lean` with the published-scope upper relaxed
identity. No new definitions/modules or aliases are planned. Check nonproper
generic clients, unbounded finite-mass targets, finite prefixes, actual radius
containments, zero/empty/top branches, standard axioms and old exact signatures.
The full Lemma 3.2 intervening radius liminf remains a separate next obligation.

### Full coarea radius-chain placement refinement (00:47 Asia/Shanghai)

Extend only `Cheeger/LocalSlopeCoarea.lean`, at its existing majorant/layer-cake
owner. Factor the proved measurable-strip/Tonelli/Fatou argument before reverse
Fatou into an additive sequence-growth liminf theorem; retain the old majorant
limsup signature as a composition with its existing dominated reverse-Fatou
proof. Add the actual right-neighborhood radius liminf chain for finite measures
by choosing a sequence attaining that liminf and discarding its nonpositive
finite prefix. For the original finite-neighborhood scope, prove that nonnegative
open-ball growth vanishes outside the positive-support neighborhood at small
radii; transfer actual growth integrals and the right-radius liminf under
restriction, and preserve genuine contents at positive levels. The slope
integral of the restricted measure bounds by the original integral. No fake
sequence-specific replacement of the radius filter, no integrability of the
function assumed solely for convenience, and no added conclusion premise.
Single-use support-transfer facts stay private unless real consumers justify a
public API. Keep all old coarea types exact. Validate the full displayed chain,
nonproper arbitrary metric space, infinite original mass, zero/empty/constant
functions, and old closed/open-ball clients, then freeze a new strict receipt.
Theorem 3.6 identities are already accepted in the Stage D upper local receipt.
Expose Lemma 2.1's actual relaxed-upper <= lower-content bound in the existing
`RelaxedMinkowski.lean` owner: for a measurable finite-mass target under any
Borel measure, use the proved radius recovery when lower content is finite and
order at infinity. This is an additive theorem over the unchanged infimum,
with no new objects/imports or stronger measure premise. Check its unfolded
infimum and infinite-content branch. Full frozen verification and broader
literature comparisons remain separate.

Evidence/state: ignored `build/audit/admg-locally-finite-eight-hour/`; baseline
snapshot, dirty patch, saved dirty files and index entries were recorded before
this handoff. `state.json` and checkpoint receipts are the durable continuation
record. A heartbeat in this chat continues actual implementation approximately
every ten minutes; it reads the state first and does not restart completed stages.
One production writer and one build at a time. Do not use subagents without a
separate direct request or applicable instruction.

The user allows Claude/GPT APIs. No usable keys were found in the process
environment or the common local env files checked. Credential reuse/new-key
choice and any requested spending cap remain pending. Until resolved, perform
local work using this Codex session; do not build or call an external API client,
write secrets, inspect credential plaintext, change accounts or purchase quota.
External API capability is optional and does not block the local proof work.

Preserve all pre-existing dirty work, the real index, moment-map and issue8 work.
No commit, push, remote CI, reset, clean, checker weakening, new axioms, sorry,
admit, hidden conclusion premises or unverified status promotion. Generate all
progress views through canonical records and an isolated index. Historical
receipts are not refreshed retroactively. Temporary task-owned idle-sleep
prevention may last only to the deadline; no persistent lock/security changes.
If the computer or app is unavailable, checkpoint actual blocked time and do
not claim continuous execution. Pause/report after a persistent blocker; do not
silently extend the window. Notify on completion, material failure or required
user action; otherwise keep routine heartbeat reports quiet.
