# Parallel moment map and Letwin formalization

Updated 2026-10-09. The active goal is to prove CEK Theorem 2 and Letwin Theorem 1.2 in their
pinned source scope, including the separate regularity bridge needed by the Letwin route.
Two independent proof lanes construct the prerequisites; one integration owner maintains the
production interfaces. Compiled construction skeletons are intermediate work, not completed proofs.

## Source targets

| Lane | Pinned source | Target and scope |
| --- | --- | --- |
| A | Cordero-Erausquin–Klartag, *Moment Measures*, [arXiv:1304.0630v1](https://arxiv.org/html/1304.0630v1) | Theorem 2: every finite nonzero Borel measure on R^n with finite first moments, barycenter zero and support not contained in a hyperplane is the moment measure of an essentially continuous convex potential, unique up to translation. Preserve the source dimension and finite-mass normalization. The target measure need not be log-concave. |
| B | Letwin, [arXiv:2607.24164v1](https://arxiv.org/html/2607.24164v1) | Theorem 1.2: the quadratic-form variance bound for an isotropic log-concave law and every symmetric matrix, with the exact constant 8 in the Hilbert–Schmidt formulation. Theorem 2.5 and Proposition 2.8 are source prerequisites. |
| Bridge | Letwin, same pin | Lemma 2.2: produce the smooth, strictly convex moment potential in the bounded smooth-density setting, and the exact Monge–Ampere identity. General CEK existence alone does not supply this regularity. |

The local Letwin PDF is `../KLS-paper-sources/2026-10-07/2607.24164v1.pdf`, sha256
`5dd9194cf36d91e2e4929a48564fe99d8d163a0a5ec7b31d80dc1f58a41778f1`.
The source PDF manifest is in that directory. No paper coverage marker changes in this setup.

## Ownership and placement

The user changed execution on 2026-10-09: Codex is the coordinator; strong API
models perform new proof construction. See the controlling
[goal execution addendum](2026-10-09-api-first-goal.md). Superseded ownership
and scheduling are preserved verbatim in the dated strategy decision.

| Owner | Responsibility | Scope |
| --- | --- | --- |
| Codex | Mathematical dependency planning, pinned statements, placement, task freezing, dispatch, semantic review and final acceptance | Short task-local context; Lean compilation, proof-value/axiom audits and exact kernel evidence |
| API Astra | Difficult proof bodies and mathematically demanding supporting units | One frozen statement and immutable dependency context per task |
| API GPT-6.1 Sol | General module construction and supporting proofs | Independent task directories; no unscheduled production writes |
| API GPT-5.6 Sol | Minimum model for narrow routine tasks | The user prohibits every Luna fallback |
| API Claude Opus 5.5 | Critical independent mathematical review where useful | Actual source/type/proof comparison, followed by local Lean gates |
| Existing Claude integration owner | Reviewed production batches and metadata | Sole production editor; no new broad proof task by default |

Old Codex proof agents are interrupted at saved checkpoints. The separate Codex
continuation is idle with a completed Proposition 12 candidate. Do not resume
proof construction there or duplicate completed candidates. The current batch
uses `build/reviews/2026-10-09-moment-map-letwin-parallel/`; retain exact source
ownership and immutable seals when assigning unfinished units to API workers.
Generic prerequisites retain their mathematical owning families; paper-only
assembly belongs under `KLS/<Paper>/`. Review workflow/naming and record scope,
imports, API impact and validation before each public change.

## Shared interface and regularity bridge

The common mathematical object is the equality
`Measure.map (gradient phi) (expDensityMeasure phi) = mu`, with the actual exponential density
and the almost-everywhere meaning of the convex gradient. Lane A must retain extended-real
potentials, finite nonzero mass, essential continuity and uniqueness up to translation.
This is not a smooth-potential interface.

The bridge starts from `mu = exp(-V) * 1_K dx`, where K is bounded, open and convex and V is
smooth and convex on a neighborhood of its closure, with the source normalization. Its target
is a finite smooth potential phi on R^n, positive-definite Hessian, a gradient diffeomorphism
from R^n onto K, the gradient pushforward, and
`exp(-V(gradient phi x)) * det(Hess phi x) = exp(-phi x)`.
The log-determinant form is `log(det(Hess phi x)) = -phi x + V(gradient phi x)`.
The final contract must state the actual maps and regularity rather than hide them in a
conclusion-bearing assumption package.

The bridge must account separately for source regularity and approximation. BKL's globally
strongly convex regular-potential class is not automatically the bounded-density class of
Letwin Lemma 2.2. Keep growth, integrability, invertibility and approximation obligations visible
until they are proved from the original input.

## First task cards

| Task | Input and consumer | Current disposition and acceptance |
| --- | --- | --- |
| A0 convex-duality definitions | Actual EReal epigraph and Legendre supremum; consumer CEK Proposition 12 convexification | Actual definitions, duality, convexification and admissibility support are independently accepted in scratch. Canonical integration candidate is being prepared; no production main-theorem claim. |
| A1 CEK compactness | Lemmas 16–17; consumer Proposition 12 maximizer | Full same-subsequence Lemma 17 (56a)+(56b) is independently accepted, including actual dual-mass semicontinuity. Preserve the exact source/type pins when integrating. |
| A2 variational existence | Proposition 12 plus CEK's essential-continuity and Euler–Lagrange steps; consumer Theorem 2 existence | Alternative coercivity and actual normalized-sequence integral control are independently accepted. All-competitor normalization is active; attainment, essential continuity and identification remain open. No extra target log-concavity or smoothness premise. |
| A3 uniqueness | Source uniqueness route including its equality-case prerequisites; consumer full Theorem 2 | Keep a separate WIP target; existence does not complete uniqueness. |
| B0 symmetric-matrix comparison | A real symmetric B and positive-semidefinite H; consumer Theorem 2.5 with indefinite B | The actual trace-absolute inequality is independently accepted with meaningful noncommuting/indefinite consumers, including a reviewed stronger symmetry-only scope. The production batch remains separate. |
| B1 analytic inequalities | Genuine Brascamp–Lieb and H^-1 prerequisites; consumer Proposition 2.8 | Pending. Proposition 2.8 does not require isotropy; preserve centered first derivatives and the source L2/local-Lipschitz scope. The first ambient-gradient skeleton is explicitly restricted to full-dimensional laws. Full source scope for singular laws needs intrinsic or suitable AE derivative semantics; the restriction does not complete the proposition. |
| B2 Hessian estimate | Given actual smooth normalized moment potential and source regularity; consumer Theorem 2.5 | Actual Hessian generator and MA second-derivative identities are accepted; the original metric/tensor comparison is closing its transitive proof checks. Full factor 2 integrated estimate and every integrability obligation remain open. |
| B3 quadratic variance | Theorem 2.5, Proposition 2.8, Stein input and approximation; consumer Theorem 1.2 | WIP skeleton. The source constant 8 must survive transport and approximation in all source dimensions. |
| R0 regularity contract | Letwin Lemma 2.2 and its cited regularity result; consumers A-to-B bridge and B2 | The corrected contract, positive smooth extension, normalization, repaired pointwise MA positivity/log-det and actual gradient injectivity are accepted support. H5 open-image/inverse/range work is active; the deep smooth-potential producer and full bridge remain open. |

## Scheduling and acceptance

New proof work is API-first, with Astra for difficult units, GPT-6.1 Sol for
module construction, GPT-5.6 Sol as the minimum routine model, and API Opus for
selected independent reviews. No new Luna dispatch or retry is permitted.
The existing provider and key remain unchanged; the nonsecret default model
is GPT-6.1 Sol, with task-specific upgrades and no Luna fallback. An actual bounded Astra request
returned HTTP 200, the exact requested model, and the expected reply. This
proves transport access, not mathematical proof capability. The earlier Sol
429 epoch remains preserved and is not retried blindly.

Freeze the exact statement, actual dependency signatures, source/object context
and target model before dispatch. Initially run one real proof job; raise to
at most two independent workers after successful access and accepted output.
Each job has at most two proof attempts. Stop rate/quota errors immediately,
preserve the epoch and diagnose before another request. Read only relevant
source excerpts and diagnostics; keep full logs/types in files and use compact
handoffs. Assess actual relay tokens/time per independently accepted proof;
official prices do not establish this relay's billing.

Codex performs final semantic and Lean acceptance without returning to long
proof-writing loops by default. Failed API work leads to prerequisite/task
repair or a reviewed model change. Explicitly preserve current scopes and
claims through every context handoff. The service goal remains active with
unchanged mathematical targets; its current API supports status changes only,
so the user's newer execution instruction governs through the addendum.

Track three distinct states: statement elaborated; local proof completed; transitive proof
closure completed. A theorem that calls an upstream `sorry` belongs to construction work even
if its own body has no placeholder. Every accepted production declaration must have only the
standard axiom closure (`propext`, `Classical.choice`, `Quot.sound`) and pass strict replay from
the reviewed local sources. No construction skeleton imports `KLS/Target.lean`.

Integration batches include an exact source/type map, a placement review, fresh source and
client compilation, transitive axiom checks and meaningful consumers. Update canonical progress
records only when theorem/evidence status actually changes, regenerate all views from an
isolated intended index, and preserve the real index. A paper is covered only after its exact
main theorem is proved, certified and verified. The KLS conjecture remains open.

## Baseline and verification boundary

`BASELINE.json` records the pre-task 1218-file source snapshot
`ce94ff157d4a8c3c7a617c73912624b7f513c8ec6dfa489cab46502a6202fa59`, local HEAD
`7c0145c4028687dccc4837f3d46410477c14ebe6`, the real-index hash and the dirty file inventory.
The latest full local receipt is `build/verification/20261008T200352.046614Z/report.json`,
sha256 `66a32bedc468b91d652bb06f6db457f985294fea5863f0a7a262a7c6e4570106`, for its own 1215-file
snapshot. Its 242 gates, 231 strict audits, 799 standard axiom reports and 477 local object
replays were checked independently. It does not certify later source or documentation edits.

The later production `Probability/ConvexSupport.lean` and its audit have a separate fresh
strict check (77 standard axiom reports), not a new full-tree receipt. The CEK (54) probability
halfspace estimate is support for Lemma 16; it is not full general moment-map existence.
This setup does not change source proof status, ledger certificates or generated completion
markers. Preserve unrelated work and the actual Git index; commit, push and remote CI remain
separate owner actions.


## Current checkpoint and integration placement

Full CEK Lemma 17 now has an independently accepted scratch proof: one subsequence and
one limit satisfy both (56a) and (56b). Twelve source modules passed the three strict Lean
options; five newly authored modules passed a separate kernel replay, with 31 actual new
declaration closures using only standard axioms. The root acceptance is recorded in
`build/reviews/2026-10-09-moment-map-letwin-parallel/independent-lemma17/ACCEPTANCE.json`.
This does not prove Proposition 12, essential continuity, Euler--Lagrange identification
or uniqueness. A separate Codex conversation owns only the next coercivity support unit.

Placement plan for the next candidate batch: extend the existing
`Probability/ConvexSupport.lean` by reviewed additions after complete interface comparison;
place actual extended-real convex/Legendre definitions and properties with pointwise
compactness and radial extension in `Analysis/Convex/`; place exponential-potential measure
definitions, dual-mass semicontinuity and measure compactness in
`Probability/MomentMeasure/`. These are populated mathematical families, with dependencies
from measure properties to generic convex tools. Scratch namespace/name changes require an
explicit declaration map and type comparison; existing production public interfaces are
preserved. Create an isolated integration candidate first, strictly compile it and its real
clients, and report the exact map for root review before applying it to production. Keep
paper targets and source-numbered assembly in the per-paper `KLS/` family when actual assembly
is ready; no empty future modules or compatibility aliases.

Letwin's fifth batch has the actual spectral-frame factorizations and original-coordinate
tensor contractions. The frozen finite-sum Sol request ended with HTTP 429 before a proof response.
A separate local Codex proof preserves the original header and mathematical type and
passes strict source, actual declaration and signed/singular clients; independent
acceptance and the final Letwin consumers are running. Preserve the failed API epoch;
no repeated rate-limit requests or model escalation is scheduled.
Affine normalization and truncation/convexification batches are under independent review.
None of these scratch checkpoints changes paper coverage or the certificate ledger.


Round3 integrability/epsilon convexification and round4 affine/origin normalization
are independently accepted in `independent-a/round3-round4-review/ACCEPTANCE.json`
(SHA256 `249183872f15b69d6de18323534d4e6bb8294d89da0c774302073ea0b8fc1c62`).
The review checks 109 actual declaration closures, including reused accepted parents.
The smooth regularity worker now owns only `bridge/h5-agent/`, deriving the actual
open gradient image and inverse before attempting the full source H5 surjectivity.
The deep smooth-potential producer remains open. The Codex continuation now owns
`codex-continuation/round3-normalized-competitors/`, using actual competitor reduction;
its previous coercivity delivery is independently accepted in
`independent-coercivity/ACCEPTANCE.json` (SHA256
`8b1c1ef7ca069a2505035b0f3cad4a62fe54991bb47ad6d90b7de87b9346030b`): five strict
source modules, 34 actual standard declaration closures and five exact kernel replays.
The measure-dependent polynomial bound supports Proposition 12 through a different
proof route; the original Lemma 15 sharp constant and attainment remain open.
