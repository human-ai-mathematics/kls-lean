# Eight hour plan for BGL ergodicity and the Poincare bound

Prepared on 2026-10-03 for the KLS owner and the Claude and GPT workers. The owner
authorized Claude and Cursor use and continuation while away on 2026-10-03.
Execution window: 2026-10-03 15:45:57 to 23:45:57 Asia/Shanghai. Stop theorem expansion
at 21:45:57 and reserve the final two hours for review and verification. The objective is to remove the assumed ergodicity from the
current Bakry–Emery bound and obtain the selected BGL corollary with its published hypotheses.
Eight hours is a time budget, not a promise that the missing proofs will be completed.

## Source and baseline

The target is Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
Springer 2014, Grundlehren 348, Corollary 4.8.2, printed p. 212 (PDF page 228). Its probability
law on real finite-dimensional Euclidean space has density `exp(-W)` with respect to Lebesgue
measure, with smooth `W` and `Hess W >= rho Id`, `rho > 0`. The conclusion is `P(1/rho)`:
`Var_mu(f) <= rho^-1 * integral |gradient f|^2 dmu`, on the appropriate form domain.
Propositions 4.8.1 and 4.8.3 explain the semigroup argument. This target does not cover the
entire book, weighted manifolds, general Markov triples or dimension-free KLS.

The source PDF was inspected locally at
`/Users/lyuyuwei/Desktop/KLS/2014 Bakry-Gentil-Ledoux - Analysis and Geometry of Markov Diffusion Operators [Grundlehren 348, Springer].pdf`.
Use this edition again at execution time, record its checksum, and check the definition of
`P(C)` and its test class as well as the corollary. The existing Chapter 4 map has all 46
numbered statements; do not spend this block remapping other chapters.

Observed checkout: `89a85e11a5e8b6937aba4840bac73eb030d63b56`. Tracked files were clean;
`.cursor/` and `.clinerules/` were untracked and must be preserved. Recheck the checkout and
staging when execution starts. The receipt
`build/verification/20261003T053747.588423Z/report.json` records 184 passed gates and 364
replayed modules with no errors. All 1025 recorded file hashes matched the current files at
planning time. Its recorded `snapshot.head` is the parent `ed03e426dd308223d613128f8317ea2a6bebb515`;
this file comparison is not a new verifier run or remote certification of the current HEAD.

Current proved interfaces include the curvature estimate on `D(A)`, exponential energy decay,
the finite-time variance bound, and
`FunctionalInequalities.KLS.LogConcave.literatureConstant_le_inv_of_tendsto`. The last theorem
still assumes decay of the centered semigroup norm. `literature.json` correctly marks
Corollary 4.8.2 partial. There are two separate missing obligations: identifying the gradient
kernel with constants, and deriving strong semigroup convergence from that identification.

## Worker responsibilities

| Worker | Responsibility | Accepted output |
| --- | --- | --- |
| Claude | Read the pinned source, design the proof, write exact Lean statements and review mathematical scope | Statements with full section context, placement decisions and source comparisons |
| GPT through the existing Cursor configuration | Prove one frozen statement at a time | Proof bodies and necessary private helpers, accepted only after local checks |
| Codex coordinator | Preserve the baseline, dispatch bounded tasks, check interfaces and proofs, integrate and report | Source diffs, independent clients, axiom results, verification receipt and remaining obligations |

Claude and Cursor applications are installed. This planning turn did not invoke either model
or test API connectivity. At execution start, use the owner's existing configuration; keep
credentials out of prompts, repository files and logs. Inspect safe configuration metadata to
identify the actual configured GPT model rather than silently choosing another one. The
previous run used `gpt-5.6-luna` for proof bodies only; that is historical evidence, not a
current connectivity result. If a service is unavailable, continue useful local work and
report the missing independent model check explicitly.

Give GPT imports, section variables and already accepted dependencies, not just a theorem
header. Compare ordered section directives, instances, namespaces, imports, declarations and
elaborated types before accepting a candidate. Header equality alone missed a changed Haar
measure assumption in the preceding block. A worker may propose a statement correction to
Claude, but must not silently change its hypotheses or assume the desired conclusion.
Use separate scratch candidates and one coordinator writing each production file.

## Proof obligations and proposed routes

1. **Local restriction.** From a graph-approximating sequence for the actual closed unit
   gradient and `Tbar h = 0`, transfer function and gradient convergence to Lebesgue `L2` on
   bounded cubes. Prove the positive lower density bound on each compact cube. Restriction,
   normalization and the coordinate isometry must be explicit.
2. **Kernel identification.** Apply a local cube Poincare estimate obtained from the existing
   one-dimensional bound and finite tensorization to the approximants. Deduce that `h` is
   almost everywhere constant on each cube. Use nested cubes of positive mass to identify the
   constants and exhaust the space. State the result as equality of `L2` classes, not pointwise
   constancy of an arbitrary representative. Identify that constant with the mean. Prove the
   converse using the existing constant-domain API. Handle dimension zero separately.
3. **Abstract convergence.** For `A = T* T`, establish convergence to zero on
   `(ker A).orthogonal`. A proposed route uses self-adjointness to identify this subspace with
   the closure of `range A`. On `A g`, commute `A` through `P_t` and use the existing
   `t * norm (A (P_t g)) <= norm g`; extend convergence from the range by contraction and
   approximation. Prove the range/kernel identity and `ker A = ker T` with all domain
   conditions. These bridges are proposed work, not existing proved APIs.
4. **Concrete ergodicity.** Show that centered data are orthogonal to the kernel, specialize
   the abstract convergence to the heat model, and obtain exactly the `herg` hypothesis of
   `literatureConstant_le_inv_of_tendsto`. The form-domain scope suffices for this endpoint;
   arbitrary-`L2` convergence is optional if it follows without distracting expansion.
5. **Published endpoint.** Add an unconditional theorem for `C_P^lit <= ENNReal.ofReal rho^-1`.
   Derive auxiliary `LogConcave` and nonempty-support-interior facts from the density and
   curvature assumptions rather than leaving additional analytic premises in the published
   wrapper. Instantiate the actual Lebesgue measure on `R^n`, retain normalization and the
   gradient-energy convention, and expose the original Poincare inequality through the
   established constant/test-class comparison. Keep the existing conditional theorem unchanged.

The local-cube route is a candidate. If its transfer API stalls, examine the existing
`Energy/Euclidean/WeakDerivative.lean` and mollification tools as an alternative proof that a
zero distributional gradient is constant. Do not assume differentiability of a general form
element or assume a finite global Poincare constant to prove the same bound.

## Placement plan

Paths below are relative to `formalization/FunctionalInequalities/`.

| Object and role | Owner and destination | Imports and API impact |
| --- | --- | --- |
| Local graph convergence and zero-gradient kernel | `KLS/LogConcave/WeightedGradient/Kernel.lean`, namespace `KLS.LogConcave` | Create a substantive kernel module; import the existing closure/energy owner and actual local Poincare prerequisites. Keep heat-flow imports above this layer. |
| Strong convergence for a generated Hilbert-space semigroup | `Analysis/Semigroup/Generated/Convergence.lean`, namespace `Analysis.Semigroup.Generated` | Create a convergence module using `VonNeumann`, `Generated/Domain`, `Smoothing` and contraction laws; no probability or KLS imports. |
| Heat-model specialization and source corollary | Existing `KLS/LogConcave/HeatSemigroup/Curvature.lean` | Extend it by importing the two proved prerequisites. Add declarations without renaming or weakening the existing conditional interface. |
| Independent statement and edge clients | `research/audits/BakryEmeryErgodicityAudit.lean` | Use the final public interfaces and the actual Lebesgue/Gaussian instances; candidates are not proofs. |

Generic cube tools belong to the existing Poincare or Euclidean energy family only if their
actual statements and consumers justify extraction. Otherwise keep one-use helpers private
with their consumer. Before implementation, inspect existing owners again and refine this
placement if needed under `research/workflow.md` and `research/naming.md`. No module moves,
public renames, compatibility aliases, duplicate energies or empty future modules are planned.

## Eight hour execution budget

Record the actual start `T0` and `T0 + 8h` in Asia/Shanghai when execution begins. The table
uses elapsed time and does not schedule an automatic future run.

| Elapsed time | Work | Gate or deliverable |
| --- | --- | --- |
| 00:00–00:30 | Save baseline; pin source; identify configured workers; freeze statements and placement | Exact corollary contract and dependency list; preserve existing dirty files |
| 00:30–02:30 | Local restriction, cube inequality, constant compatibility and kernel identification | Strictly compiled kernel result, or a precise remaining local-transfer obligation |
| 02:30–04:00 | Abstract range/kernel identities and semigroup convergence | A proved Hilbert-space result independent of log-concavity; list any missing domain bridge |
| 04:00–05:15 | Combine the kernel result with convergence; instantiate the conditional curvature theorem | Ergodicity and `C_P <= 1/rho` without `herg`, if prerequisites passed |
| 05:15–06:00 | Derive source-wrapper assumptions and check its test class; finish edge clients | Faithful Euclidean source instance, or an explicitly partial result |
| 06:00–08:00 | Stop theorem expansion; independent review, metadata synchronization, frozen verification and report | Exact accepted declarations, scope, source snapshot and receipt status |

Within the last block, finish review and metadata by about 06:30 elapsed, then start the full
local verifier. Reserve the remaining 90 minutes for its completion, necessary repair and
reporting. If prior timings show it needs longer, freeze and start it earlier. After any repair
or documentation edit, the old receipt does not certify the new snapshot. At the hard deadline
report unfinished verification as pending and stop owned work; do not extend the window.

For a stalled obligation, after 45 minutes record the precise obstruction and change a helper
decomposition or valid proof route. After three failed proof submissions for the same frozen
statement, Claude should review and split it before further submissions. Use bounded service
timeouts and retries. Do not fill remaining time with repeated unchanged checks or unrelated
paper maps. Save accepted supporting results even if the corollary cannot be finished.

## Acceptance and delivery

Every accepted Lean result needs strict affected-module compilation, a genuine independent
client and standard-only transitive axiom results. Inspect full elaborated assumptions, not
only theorem names. Check arbitrary dimension, dimension zero, nonconstant kernel exclusion,
constant/centered inputs and a scaled Gaussian with Hessian `rho Id`. This Gaussian client
checks the coefficient and normalization; it does not establish sharpness for every law.
Check the unchanged conditional theorem as a regression client.

If proof progress changes, update the source mapping in `research/progress/literature.json`,
the relevant Blueprint/evidence records, `HANDOFF.md`, the diagram date and root summary.
Prepare canonical metadata in a temporary Git index, preserving the owner's staging, then run
`python3 research/progress/update.py` from that index and review the combined diagram, approach
table, links and source scopes. Run `update.py --check` and `git diff --check`. Synchronize
all live metadata before the frozen full `python3 research/verify.py` run.

A proved and independently verified Corollary 4.8.2 may receive its exact-target certificate
through the normal ledger workflow. Kernel or convergence lemmas alone do not certify the
corollary. Even a certified corollary does not cover every chapter or prove Proposition 4.8.1
for general Markov triples. Dimension-free KLS stays open. Preserve existing certificates.

The final report must identify the start/end time, accepted declarations, their exact scopes,
changed files, check exits, axiom results, receipt path and snapshot, and any failed or pending
obligation. Distinguish full corollary, supporting results and conditional results. If only
kernel identification is complete, keep the corollary partial and name the convergence gap.

The current execution authorization permits Claude and Cursor use and local formalization
work. It does not add authorization to commit, push, tag or run remote CI. Preserve the actual
Git index. A bounded heartbeat may coordinate this window and must stop at the deadline;
remote certification remains a separate milestone tied to the exact successful SHA.

## Execution log

- T0 = 2026-10-03 15:45:57 Asia/Shanghai (window as authorized); theorem expansion stops at
  21:45:57; hard deadline 23:45:57. Claude started reading at 15:49.
- Baseline: HEAD `89a85e11a5e8b6937aba4840bac73eb030d63b56`; tracked files clean; nothing staged
  (index tree `ad81e52c7ef81bc6ea4df98e448e5947baf48084`); untracked `.cursor/`, `.clinerules/` and
  this handoff are preserved. Source PDF sha256
  `d424576f509182a6951b427d2673c9ea9a5e8d48fa98bcdb972683776021fd61`.
- Worker: the existing configuration in `~/.config/kls/gpt.env` (model `gpt-5.6-luna`, relay host
  `api.appintheloop.com`); the key is never printed or written.
- Scratch root (outside the repository):
  `/private/tmp/claude-501/-Users-lyuyuwei-Documents-ChatGPT-KLS/6446f6df-60f4-40be-af27-bb623db78bfe/scratchpad/bgl8h/`.
  One subdirectory per batch holds `full.lean` (frozen statements), `progress.lean` (accepted),
  `driver2.py`, `hints.json`, `api.md`, the candidates `c-*.lean` and the worker log `driver2.out`.
- Acceptance check per candidate (driver plus Claude's recheck): identical theorem headers; identical
  *ordered* section directives (`variable`, `omit`, `include`, `namespace`, `section`, `end`,
  `universe`, `open`, `noncomputable section`); imports only extended by Mathlib modules; identical
  elaborated types of every frozen declaration (`#check @name` output compared with the statement
  file); no `sorry`/`axiom`/`native_decide`; standard axioms only; zero Lean messages at integration.
- Obligation batches (statements by Claude; proofs by the GPT worker):
  - **Batch A, abstract convergence** (`Analysis/Semigroup/Generated/Convergence.lean`). The
    kernel of `A = T†T` equals the kernel of `T` on `D(T)`. A vector orthogonal to `range A` lies in
    `ker A`. A vector orthogonal to `ker A` lies in the closure of `range A`. `P_t (A y) → 0`, and
    `P_t g → 0` for `g ⊥ ker A`.
  - **Batch B, kernel identification** (`KLS/LogConcave/WeightedGradient/Kernel.lean`): `T̄ h = 0`
    implies `h = const (mean h)` in `L²(ν)`. The route is chosen after the API audit (local cube
    Poincaré, or the weak-derivative/mollification route).
  - **Batch C, heat specialization** (extend `KLS/LogConcave/HeatSemigroup/Curvature.lean`).
    Centered data are orthogonal to the kernel. This discharges `herg`, giving the model theorem
    `C_P(ν) ≤ 1/ρ` without `herg`.
  - **Batch D, published wrapper.** Derive `LogConcave` and nonempty support interior from the
    density and curvature if feasible. Instantiate Lebesgue measure on `ℝⁿ`. Clients go in
    `research/audits/BakryEmeryErgodicityAudit.lean`.
- 15:52–16:05 route decisions (after a read-only API audit):
  - **Kernel.** No zero-gradient ⇒ constant lemma exists, and no finite Poincaré constant is
    available, so the local-cube Poincaré route was replaced by a distributional route.
    (i) From the smooth graph sequence (`exists_seq_smooth_tendsto_graph`), `T̄ h = 0` gives
    `∫ h ∂_w φ dm = 0`, passing to the limit through `L²(ν)` pairings with `Z e^{U} ∂_w φ`.
    (ii) This lives in a new generic module `Energy/Euclidean/ZeroGradient.lean` (batch B1): zero
    weak gradient ⇒ `h(· + v) = h` a.e. (translation-invariance via differentiation under the
    integral and the fundamental lemma `ae_eq_of_integral_contDiff_smul_eq`) ⇒ a.e. constant (Fubini).
    (iii) The bridge and the identification `T̄ h = 0 ↔ h = const (mean h)` are in
    `KLS/LogConcave/WeightedGradient/Kernel.lean` (batch B2).
  - **Convergence.** `isSelfAdjoint_adjointComp` exists, so batch A uses `range Aᗮ ⊆ ker A`,
    `Kᗮᗮ = closure K`, `P_t (A y) = A (P_t y)`, `t ‖A P_t y‖ ≤ ‖y‖` and contraction.
  - **Wrapper.** `IsBorellDensity.compactLogConcave` (Prékopa–Leindler in `ℝⁿ`) yields `LogConcave`
    from the density `e^{-W}/Z` w.r.t. `volume`; full support gives the nonempty interior. The
    published statement is for `ν = volume.tilted (-W)` on a finite-dimensional real inner product
    space (`ℝⁿ` with Lebesgue measure as the instance), with `W ∈ C²` and `∇∇W ≥ ρ > 0`. Two forms:
    `C_P^lit ≤ 1/ρ` and the smooth-test inequality `Poincare.SmoothTest.Holds ν ρ⁻¹`.
- 16:05 driver change: the worker repeatedly drifted section headers when returning whole files.
  The driver now always splices only the worker's new helper declarations and its proof of the
  target into the frozen file (plus new `import Mathlib…` lines); all checks then run on the result.
- 16:10–16:20 driver fixes:
  - The elaborated-type check rejected a candidate correctly: a two-line `omit … in` stayed attached
    to a worker helper, so the target gained instances. B1 is restructured to avoid `omit` lines,
    with the basic variables first, then pure-calculus helpers, then a measure `variable` block.
  - The driver now carries a preceding `variable` block as part of the target's frozen lead.
  - `accept_patch.py` applies a logged mechanical patch to a worker candidate and accepts it only
    through the same full check. It is used once so far (`integral_eq_integral_mul_exp`: removed a
    trailing `ring` after `field_simp` closed the goal).
- 16:20 status: A accepted `adjointComp_eq_zero_iff` and
  `exists_mem_adjointComp_domain_of_map_eq_zero` (round 1 each). B1 accepted
  `norm_mul_fderiv_comp_sub_smul_le` (round 2). B2 is on `locallyIntegrable_coeFn` (two failed
  rounds). Claude probed a fallback decomposition (`probe/p1.lean`, compiles):
  `integrable_exp_neg_of_eq_tilted` (from `tilted_of_not_integrable` and total mass one) and
  `restrict_le_smul_of_eq_tilted` (`m|_K ≤ c • ν` for compact `K`, as `e^{-U}/Z` is bounded below on
  `K`); then `Integrable.mono_measure`. Batch C's `api.md` and `hints.json` are written and their
  names checked against the library.
- 16:23 A accepted `exists_mem_adjointComp_domain_of_inner_eq_zero` (worker, round 3; the
  Claude-probed recipe written to `A/hints.json` at 16:22 was not yet read by that run).
- 16:25 B2 redesign after 3 failed rounds on `locallyIntegrable_coeFn`: two helper statements
  (`integrable_exp_neg_of_eq_tilted`, `restrict_le_smul_of_eq_tilted`) inserted before it; failed
  attempts archived in `B2/failed-r1/`. Provenance: the hints for these three statements contain
  Claude's probed proof text (`probe/p1.lean`), so their accepted proofs are not independent worker
  proofs. `integrable_exp_neg_of_eq_tilted` was accepted in round 1.
- 16:27 B1 `hasDerivAt_integral_mul_translate`: the worker failed 3 rounds; round 3 had a single
  error, a final `rw` against `-(h a * …)` while the derivative was `h a * -(…)`. Mechanical patch
  `B1/patch1.json` (replace the `hneg` rewrite by `simp only [mul_neg, integral_neg]`), accepted
  through `accept_patch.py` with the full check. Claude's independent probe of the same statement
  (`probe/pB1.lean`) also compiles; it was not used. B1 relaunched for the last four statements.
- Provenance rule from here on: Claude probes full proofs only after a statement has failed three
  rounds; hints otherwise carry lemma names, signatures and proof plans. The final report lists
  each accepted declaration as worker / worker+mechanical patch / Claude-probed recipe.
- 16:29–16:36: A accepted `mem_closure_range_of_inner_eq_zero` (worker, round 3). B2 accepted
  `restrict_le_smul_of_eq_tilted` (round 3) and `locallyIntegrable_coeFn` (round 1; Claude-probed
  recipe). B1 `integral_mul_sub_translate_eq_zero`: worker failed 3 rounds; round 3's only error
  was a `convert` side goal `1 = ContinuousLinearMap.id ℝ V`. Mechanical patch `B1/patch2.json`
  (state the translate's derivative as `ContinuousLinearMap.id` and use `comp_id`), accepted
  through `accept_patch.py`. B1 relaunched for the last three statements.
- 16:39 batch A ALL_PROVED (7 statements; `tendsto_apply_adjointComp` round 2,
  `tendsto_apply_of_mem_closure_range` and `tendsto_apply_of_inner_eq_zero` worker). Integrated as
  `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean`: docstrings
  match the frozen file; two `omit [CompleteSpace H₁] in` lines added (the two kernel lemmas do not
  use it; strictly more general); zero messages from `lake env lean --json`; aggregator import added
  after `Generated.Curvature`; `lake build` of the module succeeds.
- 16:45 B1 redesign after 3 failed rounds on `ae_add_eq_of_integral_mul_fderiv_eq_zero` (the worker
  could not find local integrability of translates): helpers `locallyIntegrable_comp_add_right` and
  `integral_mul_comp_add_right` inserted; hints carry names only (Claude's probe of the first,
  `probe/pB1b.lean`, compiles and is not in the hints). Failed attempts in `B1/failed-r1/`.
- 16:47 B2 accepted `tendsto_integral_mul_of_tendsto` (worker, round 3).
- 16:50 batch D launched (`bgl8h/D`, log `D/driver.out`). Placement plan: owner
  `KLS/LogConcave/Density`; new module `Density/Tilted.lean` (tilted Haar laws: integrable density,
  log-concavity from a continuous convex potential via `IsBorellDensity.compactLogConcave`, full
  support); imports `Density.FromBorell` and Mathlib `Measure.Tilted`; no API change. Statements:
  `integrable_exp_neg_of_eq_tilted` (any measure `m`; moved from Kernel at integration),
  `logConcave_of_eq_tilted`, `interior_support_nonempty_of_eq_tilted`. Batch C then keeps only the
  heat-model statements and the two published-form wrappers, importing `Density.Tilted`.
- 16:57 progress: B1 accepted `locallyIntegrable_comp_add_right` (round 2),
  `integral_mul_comp_add_right` (round 1) and `ae_add_eq_of_integral_mul_fderiv_eq_zero` (round 2),
  all worker proofs. B2 accepted `tendsto_integral_mul_inner_of_tendsto` (round 2). D accepted
  `integrable_exp_neg_of_eq_tilted` (round 1). D redesign after 3 failed rounds on
  `logConcave_of_eq_tilted` (several independent errors): helpers
  `integral_exp_neg_pos_of_eq_tilted` (any base measure; positivity from total mass one),
  `rpow_mul_rpow_le_of_convexOn` (pure real inequality) and `isBorellDensity_of_eq_tilted`
  (any base measure `m`); the target becomes `IsBorellDensity.compactLogConcave` of the last.
  Hints are plans with names only. Failed attempts in `D/failed-r1/`.

## Shutdown record (23:28 CST, hard freeze)

The session lost contact (worker authentication failure and app restart) after about 17:00.
Under Codex's hard-freeze instruction, nothing was relaunched or integrated after that. HEAD is
`89a85e11a5e8b6937aba4840bac73eb030d63b56` and the real index tree is
`ad81e52c7ef81bc6ea4df98e448e5947baf48084`, both unchanged. No commit, push, tag or remote CI.

Working-tree changes owned by this block:
- New `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Convergence.lean`
  (sha256 `80decea8b54c00ed082bd2209ee281e793fdd136184a7f46220de7d0d8b37b2c`): seven
  declarations, strong convergence `P_t g → 0` for `g ⊥ ker T` (abstract, closed densely defined
  `T`). Codex review: strict compile, import client, type match, standard axioms only
  (`build/audit/bgl-eight-hour-coordination/A-production-review-20261003T0845.json`).
- `formalization/FunctionalInequalities.lean`: one aggregator import for that module.
- This handoff file (untracked, owner-prepared, execution log appended).

Not done, and not to be claimed: BGL Corollary 4.8.2 is not proved. There is no concrete
ergodicity in the heat model, `herg` is still a hypothesis of
`literatureConstant_le_inv_of_tendsto`, and there is no final receipt or certificate. No metadata
(`literature.json`, `naming.md`, `tasks.json`, progress views) was synchronized, and no full
`verify.py` was run on this tree.

Exact open obligations (scratch only; worker proofs in each `progress.lean` are unintegrated and
not strictly approved):
- B1 `Energy/Euclidean/ZeroGradient.lean` (zero weak gradient ⇒ a.e. constant): 7/9 proved in
  scratch. Open: `exists_ae_eq_const_of_forall_ae_add_eq` (Fubini/`ae_ae_comm` step: an
  a.e.-translation-invariant function is a.e. constant; two failed rounds, then the API timed out)
  and the one-line wrapper `exists_ae_eq_const_of_integral_mul_fderiv_eq_zero`.
  `hasDerivAt_integral_mul_translate` and `integral_mul_sub_translate_eq_zero` carry logged
  mechanical patches (`B1/patch1.json`, `B1/patch2.json`).
- B2 `KLS/LogConcave/WeightedGradient/Kernel.lean` (distributional bridge): 6/7 proved in scratch.
  Open: `integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero`, which failed 3 rounds on
  API mismatches (`HasCompactSupport.fderiv_apply` argument order, `tendsto_congr'` misuse); it
  needs a helper split. Not yet appended: K3 `eq_const_mean_of_closedWeightedOperator_eq_zero`
  (draft `B2/k3.lean.txt`, hint `B2/k3hint.txt`), which needs B1.
- D `KLS/LogConcave/Density/Tilted.lean` (tilted Haar laws): 5/6 proved in scratch
  (`integrable_exp_neg_of_eq_tilted`, `integral_exp_neg_pos_of_eq_tilted`,
  `rpow_mul_rpow_le_of_convexOn`, `isBorellDensity_of_eq_tilted`, `logConcave_of_eq_tilted`).
  Open: `interior_support_nonempty_of_eq_tilted` (full support; round 1 used an unknown
  identifier). Integration must also move `integrable_exp_neg_of_eq_tilted` out of Kernel.
- C (heat-model ergodicity and the published wrappers in `HeatSemigroup/Curvature.lean`): not
  started. Statements frozen in `C/full.lean`; `C/api.md` and `C/hints.json` written. Before
  launch, remove the two D statements from C and import `Density.Tilted`. Also update the
  `Curvature.lean` module docstring.
- Certificate candidate draft only: `cert/ThmBakryEmeryPoincare.lean` (not registered).

Provenance: accepted declarations are worker proofs except as logged above (mechanical patches;
Claude-probed recipes for `integrable_exp_neg_of_eq_tilted` and `locallyIntegrable_coeFn` in B2).
Scratch root: `/private/tmp/claude-501/-Users-lyuyuwei-Documents-ChatGPT-KLS/6446f6df-60f4-40be-af27-bb623db78bfe/scratchpad/bgl8h/`.
- Frozen verification: `python3 research/verify.py` started 23:28:50 and passed at 23:37:08
  (`build/verification/20261003T152850.524621Z/report.json`, local only). It covers the working
  tree as of 23:28:50: Convergence.lean, the aggregator import, and this handoff up to the shutdown
  record. Any later edit (this line and any metadata sync) is outside that receipt.
- 23:38 documentation-only sync after the receipt: one sentence appended to the BGL C482
  note in `literature.json` (it links Convergence.lean as the abstract step; relation stays partial;
  no declaration mapping or certificate); the HANDOFF "Next" item 2 now names the abstract step and the
  open pieces; `LITERATURE.md` and `STATUS.md` regenerated with `update.py` through a temporary Git
  index (`update.py --check` passes; real index tree still `ad81e52c…`; `git diff --check` clean).
  Root README, Blueprint, `nodes.json`, diagram date, `naming.md` and `tasks.json` are unchanged:
  no node or paper status changed, and the new module has no naming row yet.
  **Pending verification:** the 23:28:50 receipt does not certify this final snapshot (these four
  files plus the handoff changed afterwards). A rerun needs about 8 minutes and could not finish
  before 23:45:57, so it was not started. The next session should add the naming row and the
  `tasks.json` pins for Convergence.lean and rerun `python3 research/verify.py`.
- 23:40 final documentation-only sync, also after the receipt:
  - Root README: the summary line now names the abstract convergence result and says the BGL 4.8.2
    kernel and ergodicity steps remain open.
  - `nodes.json`: one PARTIAL sentence appended to the existing Bakry–Émery/heat node description
    (the node whose sources include `Analysis/BakryEmery/Bochner.lean`). Node status is unchanged.
  - Views regenerated from the same temporary index: `update.py --check` passes, real index tree
    still `ad81e52c…`, `git diff --check` clean.
  - Blueprint TeX: reviewed, not edited. No Blueprint node states ergodicity or the abstract
    convergence lemma, and none was invented.
  - Receipt `20261003T152850.524621Z` (184 gates, 365 replayed modules, all Lean hashes unchanged
    since) is superseded for documentation only: README, HANDOFF, `nodes.json`,
    `literature.json`, `LITERATURE.md`, `STATUS.md` and this handoff changed after it. A full
    rerun is pending for the next session. Edits frozen here.
