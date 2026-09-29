# Sharp Sard proved, Lipschitz and locally Lipschitz vector coarea proved: three parallel paths fulfilled on the same day

2026-09-19, **implementation round**, followed by the three-route probe on the same day. Three proof sessions (each corresponding to one route) work in parallel on entirely disjoint new files,
this session is responsible for integration. Result:

* **Sharp finite regular Sard**: `Analysis.sard` proved (`Analysis/Sard/Sharp.lean`, Morse paths), and the corollary
  `Analysis.ae_forall_fderiv_ne_zero` together with a **byte-for-byte identical `pp.all` signature** from `KLS/WIP/AnalyticPrerequisites.lean`
  On migration, the WIP file is cleared and deleted (originally frozen at `build/audit/sharp-sard-proofs/AnalyticPrerequisites.before.lean`,
  Before and after `pp.all` print one copy each and `diff` is empty).
*Lipschitz vector coarea*: `Analysis.coarea_of_lipschitz` (`L0`) proved, `L0 = V5 ∘ V1`.
* **Local Lipschitz vector coarea**: `Analysis.coarea_of_locallyLipschitz` (`N0`), proved, `N0 = X5 ∘ L0`.
  The vector coarea chain `C¹ → Lipschitz → locally Lipschitz` now matches the scalar side.

Direct proof hole is reduced from **8 (1/2/5)** to **7 (0/2/5)**; certification remains **24** (these are `Analysis/`-layer conclusions, not ledger nodes).
No commit, no push, the real Git index is unchanged.

Origin `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; origin verification receipt passed
`build/verification/20260918T122459.920890Z/report.json` (final verification receipt for local Lipschitz route round):
10 gates, 224 local module kernel replays, 623 entries, snapshot `dc29c5d9cec95e192d4543b47bada4b3bc5bf40bee3d8366f2540e51e1154818`. Origin drift is empty.

## Boundary

log-concave Cheeger–Buser lines (including `KLS/WIP/CheegerInfimum.lean` remaining two holes) credited to author **Haocheng Wang**, untouched
(the file byte count unchanged; `KLS/WIP/` directory now contains only this entry). Five holes in Energy, dimension-free KLS untouched.
No new certification, no expansion of Blueprint `leanok` scope, no new compatible aliases, no restatement of existing theorems, no weakening of already proven conclusions.

## Rules and Outputs of Three Proof Sessions

Rules: Only create new files, do not modify existing files; do not `lake build`, do not `verify.py`, do not change Git state; use only `lake env lean -DwarningAsError=true` to check; do not import WIP; do not use `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; each route statement is to be verbatim restated and discharged in the audit client. All three sessions complied (each item in `git status` was individually verified during integration).

| route | new library module (rows) | audit client (rows) | settlement |
| --- | --- | --- | --- |
| Sharp Sard | `Analysis/Sard/Chart.lean` 220, `Disk.lean` 188, `MorseVanishing.lean` 337, `Sharp.lean` 125 (+13 migration) | `SharpSardAudit.lean` 240 | `M1`, `M1'`, `M3`–`M6`, `D1`; **`M2` literally false**, see below |
| Lipschitz vector coarea | `Analysis/Lipschitz/Componentwise.lean` 88, `Refinement.lean` 77, `VectorPieces.lean` 75, `VectorCoarea.lean` 158 | `LipschitzVectorCoareaAudit.lean` 294 | `L0`, `V1`–`V5`, `V4'`, `V4''`, `M1`; add `route_M2` during integration |
| local Lipschitz vector coarea | `Analysis/Lipschitz/Extension.lean` 61, `Annuli.lean` 63, `Local.lean` 158 (+18 integration of `N0`) | `LocallyLipschitzVectorCoareaAudit.lean` 223 | `X1`–`X5`, `D1`, `C1`, `C2`; added `route_N0` during integration |

**`M2` Literally false.** The sharp Sard route's mean-value step `M2` only controls `fderiv f` on the curve, yet the conclusion refers to chord length;
the proof session provides a manual counterexample (`C¹` spiral `t ↦ (t³cos(1/t), t³sin(1/t))` with `S` infinitely many intersection points at different scales),
the judgment in the route log that "no anti-Lipschitz constant is needed" is incorrect. The version with the anti-Lipschitz bound added to the disk `route_M2_antilipschitz` has been proven, and each disk in the Morse decomposition carries this bound, `M3`–`M6`, thus unaffected.
The counterexample is not formalized; the route statement file remains byte-for-byte unchanged, with corrections noted in the annotations of the route log.

**Other implementation details.** `M1` requires global `C^k` of `θ`, while `ContDiffAt.to_localInverse` only provides local inverses, so a finite-order bump extension `MorseSard.exists_contDiff_eventuallyEq_nat` was added. `V3` uses an injection `(Fin m → ℕ) ↪ ℕ` rather than equivalence (when `m = 0`, `Fin 0 → ℕ` is a single point). A counterexample of `M1` requires a universe-polymorphic witness `EuclideanSpace ℝ (ULift (Fin 1))`. `X1` is coordinate-wise McShane (`LipschitzOnWith.extend_pi` transported via `PiLp`, constant `√m · K`), not Kirszbraun, and no optimality claim is made for the constant. The library form of `X5` omits the unused dimension relations, and the word-for-word version in the audit retains and discards it.

## Integration action

1. Clean up orphan build artifacts of 213 groups in `.lake` that have no corresponding source code (old build residues, previously masked by new modules with the same name).
2. `Sharp.lean` append `ae_forall_fderiv_ne_zero` (verbatim copy); `Local.lean` append `coarea_of_locallyLipschitz`
   (`X5` for `L0`); two coarea audit clients append `route_N0` / `route_M2`.
3. Delete `KLS/WIP/AnalyticPrerequisites.lean`; five former clients that imported it
   (`research/audits`'s `LipschitzCoareaMigrationAudit`, `LevelSetMeasurableAudit`, `IsoperimetryCoareaAudit`;
   Change `build/audit`'s `LevelSetMeasurableAudit`, `AreaFormulaImportReview` to import `Analysis.Sard.Sharp`, with date annotation.
   The latter two are historical clients and are not among the 7 active clients; `build/audit/LevelSetMeasurableAudit.lean` had expired before this round
   (It references the already-moved `T2` original location), this round only modifies its import, not its content.
4. Aggregate import adds `Analysis.Lipschitz.VectorCoarea`, `Analysis.Lipschitz.Local`, `Analysis.Sard.Sharp`,
   And add a note; change the present tense statement "sharp Sard is still a direct proof hole" in the docstrings of the five library modules to point to `Sharp.lean`
    (`Analysis/Sard/Smooth`, `Analysis/Divergence`, `KLS/Geometry/RegularSuperlevel`, `LevelSetMeasurable`, `IsoperimetryCoarea`).
5. Default `lake build` (3492 jobs) passed; `pp.all` before and after `diff` are empty; `check_ledger.py` 24 certificates have 0 errors.

## What remains unproved

* Sard's theorem for vector-valued targets `C^(n−m+1)`, Hausdorff measure of critical values, Whitney's `C^(n−1)` counterexample: unproven.
* Counterexample for `M2`: not formalized. Constant for `X1`: no optimality. Domain: still the entire space.
* Cheeger's two-hole result by Haocheng Wang, Energy five-hole untouched; dimension-free KLS remains open. No migration of other holes, no new certifications.

## Verification

Default `lake build` passes (3492 jobs). All **58** audit clients (51 in `research/audits` and 7 active clients in `build/audit`) were rerun with `-DwarningAsError=true`, with **0 failures**. Of **732 axiom reports, 5 contain `sorryAx`**, all deliberately reporting the two holes in `KLS/WIP/CheegerInfimum.lean` through `IsoperimetryCoareaAudit` and `LipschitzCoareaMigrationAudit`. The two remaining WIP modules compile separately, with `2 + 5 = 7` `sorry` warnings and **7 direct holes (0/2/5)**. The before/after `pp.all` `diff` is empty. `check_ledger.py` reports **24** certificates and 0 errors. Root-level `python3 research/verify.py` is rerun at the end of the round; the final receipt is recorded in `build/audit/coarea-sard-proofs/final-snapshot.json`. Recomputing every snapshot entry against the worktree finds no drift.
See `research/explorations/2026-09-19-coarea-sard-proofs.json` and `build/audit/coarea-sard-proofs/`.
