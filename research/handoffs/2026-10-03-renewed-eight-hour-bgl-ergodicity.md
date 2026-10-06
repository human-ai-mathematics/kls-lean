# Renewed eight-hour BGL ergodicity block (window 2)

Owner renewal ("再来8小时"), relayed by Codex. The previous window's record is
[2026-10-03-eight-hour-bgl-ergodicity.md](2026-10-03-eight-hour-bgl-ergodicity.md) and is kept
unchanged.

## Times (Asia/Shanghai)

- Window start 2026-10-03 23:46:57. Claude resumed at 2026-10-04 01:23; the 23:47–01:23 interval
  had no Claude execution.
- Theorem expansion stops 05:46:57. Final full `research/verify.py` starts by 06:16:57. Hard
  deadline 07:46:57.

## Baseline

- HEAD `89a85e11a5e8b6937aba4840bac73eb030d63b56`; real index tree
  `ad81e52c7ef81bc6ea4df98e448e5947baf48084` (kept; progress views use a temporary index).
- Dirty snapshot `7bc84ddc…`: `Generated/Convergence.lean` (seven declarations), its aggregator
  import, and the previous window's documentation. This is baseline work, not window-2 progress.
- No commit, push, tag, remote CI, reset or clean. `.cursor/` and `.clinerules/` untouched.

## Roles

Claude: statements, splitting, acceptance, integration, the only production editor and builder.
GPT `gpt-5.6-luna` (via `~/.config/kls/gpt.env`): proof bodies against frozen contexts.
Codex: independent review and coordination.

## Target

Bakry–Gentil–Ledoux (2014), Grundlehren 348, Corollary 4.8.2 (printed p. 212). It stays partial
until the faithful endpoint is proved and verified. Supporting lemmas do not cover it. Order:
concrete kernel, concrete centered convergence, removal of `herg`, source wrapper.

## First batch: bookkeeping (01:25)

- `research/naming.md`: one paragraph for the `Generated/Convergence.lean` responsibility in the
  semigroup layout section. The `naming.md` sha pin in `research/tasks.json` is refreshed.
- Not pinned in the `thm:logconcave-cheeger-poincare-comparison` inventory: as with the two
  2026-10-03 curvature modules, the BGL route is not evidence for that separately proved theorem.
  No new task, node or certificate.

## Scratch and workers

- Scratch root (reused): `/private/tmp/claude-501/-Users-lyuyuwei-Documents-ChatGPT-KLS/6446f6df-60f4-40be-af27-bb623db78bfe/scratchpad/bgl8h`. Driver `driver3.py` and `accept_patch.py` as in window 1.
  Failed attempts are archived per batch in `failed-r*/`.
- Worker launches are logged below with PID, argv and log path.

## Execution log
- 01:24:39–01:33:29 fresh full `python3 research/verify.py` on the frozen first-batch tree: exit 0,
  "Verification passed", receipt `build/verification/20261003T172439.444418Z/report.json`, snapshot
  sha256 `db6cb0e717b24df1d0c2a2db2712e6cfb3a1d19d0685ca64c16bbdc59d9cd461`. The frozen dirty files'
  hashes, recorded at start (`w2-verify1-files.sha` in scratch), are unchanged at the end. Real
  index tree still `ad81e52c…`. This line and every later edit fall outside that receipt, so a final
  full run is still required.
- 01:25 B2 split frozen: integral_mul_fderiv_eq_neg_integral_mul_inner_gradient (smooth pairing),
  integral_mul_fderiv_eq_neg_integral_mul_inner (graph-limit weak-gradient identity for h in D(T̄),
  stronger than the original target), original target unchanged after them. Old attempts in B2/failed-r2.
- 01:26 B1 split frozen: forall_ae_add_eq_mk (transfer to the measurable representative via
  QuasiMeasurePreserving.ae), exists_ae_eq_const_of_measurable_of_forall_ae_add_eq (ae_ae_comm +
  a.e. point + translation pull-back); original target unchanged. Old attempts in B1/failed-r2.
- 01:26 D hint corrected (no measure_nonneg; pos_iff_ne_zero; mem_support_iff_forall; measure_pos_of_mem_nhds).
- 01:26:38 launched: `perl -e 'alarm 3600' python3 driver3.py <batch> 3` from scratch root;
  B1 pid 71139, B2 pid 71140, D pid 71141; logs <batch>/driver.out.
- 01:28–01:44 worker results. B1 ALL_PROVED: `forall_ae_add_eq_mk` (round 1),
  `exists_ae_eq_const_of_measurable_of_forall_ae_add_eq`, `exists_ae_eq_const_of_forall_ae_add_eq`
  and `exists_ae_eq_const_of_integral_mul_fderiv_eq_zero`, all round 1 worker proofs. D ALL_PROVED:
  `interior_support_nonempty_of_eq_tilted` (round 1, worker). B2:
  `integral_mul_fderiv_eq_neg_integral_mul_inner_gradient` (round 1, worker). The graph-limit
  identity `integral_mul_fderiv_eq_neg_integral_mul_inner` failed 3 rounds; round 3's only errors
  were an equality orientation (`.symm`) and `Tendsto.congr` given `Eventually.of_forall heq`
  instead of `heq`. Mechanical patch `B2/patch2.json`, accepted through `accept_patch.py` with the
  full check. B2 relaunched at 01:44:44 (pid 73765); the original target
  `integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero` was accepted in round 1 (worker).
- 01:45–01:48 integration (all modules: docstrings identical to the frozen files, zero messages from
  `lake env lean --json`, aggregator import, `lake build` of the module succeeds):
  - `Energy/Euclidean/ZeroGradient.lean` (11 declarations). Owner context review: `[CompleteSpace V]`
    dropped from the variable blocks (finite dimension supplies it). Per-lemma `omit` lines for the
    unused `[m.IsAddHaarMeasure]`, `[SecondCountableTopology V]`, and for the two translation lemmas
    also `[InnerProductSpace ℝ V]` and `[FiniteDimensional ℝ V]`. Each change only removes
    hypotheses, so the statements become more general.
  - `KLS/LogConcave/Density/Tilted.lean` (6 declarations). `omit` lines for unused structure on the
    generic integrability/positivity lemmas, the pure convexity inequality, the Borell-density
    packaging (`FiniteDimensional`) and full support (`InnerProductSpace`, `FiniteDimensional`,
    `BorelSpace`).
  - `KLS/LogConcave/WeightedGradient/Kernel.lean` (8 declarations). The generic
    `integrable_exp_neg_of_eq_tilted` copy is removed (owner: Density/Tilted, imported; no duplicate
    or alias). Its three call sites drop the explicit `m` (the owner's `m` is implicit). Mechanical
    cleanups: a dead `<;> ring` and an unused `simp` argument. `[CompleteSpace V]` dropped, and
    `omit` lines added for unused structure on three generic helpers.
- 01:48:22 K3 batch launched (`bgl8h/K3`, pid 75033, wall limit 1800 s): the integrated Kernel module
  plus the `ZeroGradient` import, with `eq_const_mean_of_closedWeightedOperator_eq_zero` appended
  (draft from window 1).
- 01:53 K3 `eq_const_mean_of_closedWeightedOperator_eq_zero` accepted (worker, round 3) and
  integrated into Kernel.lean (9 declarations). The module docstring now points to
  HeatSemigroup/Curvature for the converse. Zero messages; module build succeeds.
- 01:53:10 batch C launched (pid 76179, wall limit 3600 s). Statements (window-2 revision; the old
  draft is kept as `C/full-w1.lean`): the D targets were removed and `Density.Tilted` is imported.
  New targets:
  - `closedWeightedOperator_eq_zero_iff` (kernel = constants; the converse uses the existing
    `closedWeightedOperator_one_eq_zero`);
  - `inner_center_eq_zero_of_closedWeightedOperator_eq_zero`;
  - `tendsto_norm_center_apply` (concrete ergodicity for every `u ∈ L²(ν)`);
  - `norm_center_sq_le_inv_mul` (Dirichlet-domain form `Var(u) ≤ ρ⁻¹‖T̄u‖²` on `D(T̄)`);
  - `literatureConstant_le_inv` (no `herg`);
  - the source wrappers `literatureConstant_le_inv_of_eq_tilted` and
    `smoothTest_holds_inv_of_eq_tilted` for `ν = volume.tilted (-W)`.
  The eight existing declarations (including the regression interface
  `literatureConstant_le_inv_of_tendsto`) are baseline and unchanged.
- 01:54:27 batch G launched (pid 76408, wall limit 1800 s): audit-only helpers for the scaled
  Gaussian client (`ρ ‖x‖² / 2` is `C²`, with first derivative `ρ⟪y, w⟫` and Hessian form
  `ρ‖v‖²`), to live in `research/audits/BakryEmeryErgodicityAudit.lean`.
- 01:55–02:12 C: `closedWeightedOperator_eq_zero_iff` (round 1),
  `inner_center_eq_zero_of_closedWeightedOperator_eq_zero` (round 2) and `tendsto_norm_center_apply`
  (round 3) accepted, all worker proofs. `norm_center_sq_le_inv_mul` failed 3 rounds; round 3's only
  errors were a `simpa` around a composed limit and `le_of_tendsto'` used for an eventual bound.
  Mechanical patch `C/patch1.json` (`exact` the composition; `ge_of_tendsto`), accepted through
  `accept_patch.py`. C relaunched for the remaining three statements.
- G: `contDiff_half_mul_norm_sq` (round 1) and `bilinearIteratedFDerivTwo_half_mul_norm_sq` (round 2)
  are worker proofs. `fderiv_half_mul_norm_sq` failed 3 rounds; round 3's only error was a `rw`
  placed before the `simp` that exposes its pattern. Mechanical patch `G/patch1.json`.
- 02:09 statement fix (Claude's design defect, found from the worker's "Unknown identifier `hν`"):
  the frozen `literatureConstant_le_inv` used `include hνU hU in`. Its type does not mention `hν`
  or `hi`, so those model hypotheses were not in its elaborated type. Changed to
  `include hν hi hνU hU in`, the same hypotheses as the regression interface
  `literatureConstant_le_inv_of_tendsto`, minus `herg`. The C run was stopped (pid 78521, identity
  checked), its round-1 attempt archived in `C/failed-r1/`, reference types recomputed, and C
  relaunched (pid 78842).
- 02:10–02:17 C: `literatureConstant_le_inv` (round 1) and `literatureConstant_le_inv_of_eq_tilted`
  (round 1) are worker proofs. `smoothTest_holds_inv_of_eq_tilted` failed 3 rounds; round 3's only
  errors were `holds_iff_ambient` called without its explicit measure argument (my API sheet listed
  it correctly) and a final `simpa` where `exact` closes the goal. Mechanical patch `C/patch2.json`.
  C is complete: 15 declarations (8 baseline + 7 new).
- 02:18 integration of `KLS/LogConcave/HeatSemigroup/Curvature.lean`:
  - Four docstrings that the worker had altered are restored from the frozen file; the module
    docstring now describes ergodicity and the corollary as proved.
  - Zero messages; `lake build` of the module succeeds. The pre-integration file is kept as
    `C/Curvature-baseline.lean`.
- 02:20 new audit client `research/audits/BakryEmeryErgodicityAudit.lean`:
  - `-DwarningAsError=true` exit 0; 22 `#print axioms` reports, all standard (propext,
    Classical.choice, Quot.sound).
  - Clients: the unchanged conditional interface with `herg` discharged; the kernel iff on the
    constant one; the Dirichlet-domain form; the endpoint on `ℝⁿ` for every `n`, and `n = 0`; the
    scaled Gaussian `W = ρ‖x‖²/2`.
  - The G helpers are copied in. One mechanical edit: the deprecated
    `ContinuousLinearMap.smul_apply` becomes `smul_apply`, needed under warnings-as-errors.
- 02:19–02:22 documentation: `literature.json` BGL C482 is now `stronger` with the three endpoint
  declarations, and P481 stays partial with a note.
  - New `research/decisions/2026-10-04-bgl-corollary-4-8-2-candidate.md`: a certificate candidate
    for owner review, not registered. BGL2014 is therefore not covered.
  - Also updated: the `naming.md` paragraph for the new modules (sha pin refreshed), the
    `nodes.json` Bakry–Émery node description (node status unchanged), the root README summary,
    the HANDOFF state, next step and owner decisions, and the BGL plan log.
  - `tasks.json` task inventories are unchanged (the BGL route is not evidence for the Cheeger
    task).
- 02:23 diagram date (`nodes.json` `last_updated`) and the BGL lemma map's `reviewed_on` set to
  2026-10-04. Views regenerated through a temporary index (`update.py --check` passes; real index
  tree `ad81e52c…`; `git diff --check` clean). No worker is running (all launches above ended).
- Final freeze: theorem expansion ended early, with the endpoint complete. The final full
  `research/verify.py` runs on this frozen tree. Its exit status, receipt path and snapshot hash
  are written to the ignored `build/audit/bgl-eight-hour-coordination/claude-final-receipt.md`,
  not to this file, so that the receipt still matches the tree.

## Window-2 summary (accepted and integrated, uncommitted)

- `Energy/Euclidean/ZeroGradient.lean` (11), `KLS/LogConcave/Density/Tilted.lean` (6),
  `KLS/LogConcave/WeightedGradient/Kernel.lean` (9), and seven new declarations in
  `KLS/LogConcave/HeatSemigroup/Curvature.lean`. Baseline from window 1: `Generated/Convergence.lean`
  (7) and Curvature's eight earlier declarations.
- Endpoint: `literatureConstant_le_inv_of_eq_tilted`, `smoothTest_holds_inv_of_eq_tilted`,
  `norm_center_sq_le_inv_mul` and `literatureConstant_le_inv` (no `herg`). Supporting results:
  kernel = constants, ergodicity, weak gradient of `D(T̄)`, zero weak gradient ⇒ constant, and
  log-concavity and full support of tilted laws.
- Provenance: worker proofs throughout, except seven logged mechanical patches. Window 1:
  `B2/patch1`, `B1/patch1`, `B1/patch2`. Window 2: `B2/patch2`, `C/patch1`, `C/patch2`, and
  `G/patch1` (audit only).
  Window-1 B2 helpers used Claude-probed recipes, as recorded in the previous handoff.
- Not done: no registered certificate. BGL2014 coverage awaits the owner's review of the
  candidate. Proposition 4.8.1 for general Markov triples is open, and so is dimension-free KLS.
