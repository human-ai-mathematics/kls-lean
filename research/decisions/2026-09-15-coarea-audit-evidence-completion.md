# Completing audit-evidence binding for the regular coarea round

2026-09-15. This round **proves no theorems**, changes no `.lean` library source, makes no commit or push,
and rewrites no historical decisions. It performs only two closeout tasks: place the regular coarea round's (L9) audit client under version control,
and add that round's outputs to infrastructure evidence in `research/tasks.json`.

Starting HEAD was `e7768408766af27e08ba0fe9ded61d602efc4056`; the starting passed receipt was
`build/verification/20260915T112258.149854Z/report.json`, whose snapshot exactly matched the starting workspace:
447 files, SHA256 `fa8697347cab6da1cf30275c0883866c548803c3758ffc3c355894afd42331cd`.

## What is being fixed

`2026-09-15-ci-audit-source-paths.md` copied nine audit clients referenced by `tasks.json` from ignored
`build/audit/` into `research/audits/`, because a clean checkout cannot read `build/`.
**But L9's own client, `RegularCoareaAudit.lean`, was missed**: it remained only in ignored `build/audit/`,
so a clean checkout could not reproduce L9's axiom audit. It was not referenced by `tasks.json` at the time, so CI did not fail,
but the evidence was not reproducible.

Also, unlike preceding rounds, L9 had not added its outputs to `tasks.json` evidence,
so its five new modules and decision record lacked hash binding in that chain.
They were already among the 73 files bound in `research/explorations/2026-09-15-regular-coarea.json`.

## Work done in this round

1. Copied `build/audit/RegularCoareaAudit.lean` **byte-for-byte** to `research/audits/RegularCoareaAudit.lean`
   (`cmp` passed) and reran it from the new path with `-DwarningAsError=true`: 29 `#print axioms` reports,
   all containing only `propext`, `Classical.choice`, and `Quot.sound`, **without `sorryAx`**.
   `research/explorations/2026-09-15-regular-coarea.json` still binds the original local path;
   unchanged bytes mean the two paths have identical hashes.
2. Added the provenance of this entry to `research/audits/README.md`.
3. Added 7 entries to infrastructure evidence for `lem:relative-perimeter-smoothing` in `research/tasks.json`:
   `Analysis/LocalInverse.lean`, `Analysis/RegularChart.lean`,
   `Analysis/FiberIntegral.lean`, `KLS/Geometry/OpenSliceMeasurable.lean`,
   `KLS/Geometry/RegularCoarea.lean`, `research/decisions/2026-09-15-regular-coarea.md`, and
   `research/audits/RegularCoareaAudit.lean`. Additions only; all other entries were preserved.

## Deliberately unchanged

* **No per-round evidence JSON was rewritten.** The `research/tasks.json` hash in
  `research/explorations/2026-09-15-regular-coarea.json` differs from the current file. This is **not a defect**:
  each per-round JSON binds the state at that round's end, and each round changes `tasks.json`. All ten JSON files containing that entry,
  including earlier rounds, therefore have the same situation. Rewriting them would falsify the historical record.
* **No new theorem was proved**, no `.lean` library source or WIP changed,
  and no certificate or Blueprint `leanok` scope expanded. Direct holes remain **2/3/5, totaling 10**; certificates remain **24**;
  perimeter infrastructure remains **missing**.
* **No commit or push.**
* The **global Lipschitz equality** for weighted coarea (`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
  and its `C¹` specialization) remains a direct hole. L11, L12, Whitney extension L6/L6a/L7, sharp `C^(finrank)`
  `Analysis.sard`, sharpness of the Eilenberg constant, `smoothConstant_le_minkowskiConstant`,
  `smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants all remain unproved.

## Concurrent changes

During this round, an unrelated documentation commit arrived externally:
`737abc3 docs: consolidate proof corrections and improvements` (adding
`research/proof-corrections-and-improvements.md` and changing `README.md`). HEAD consequently changed from the starting
`e776840` to `737abc3`. This round neither created nor rewrote that commit. The final receipt binds the final workspace **including that commit**,
so its `head` differs from the starting HEAD above. This round's four changes
(adding `research/audits/RegularCoareaAudit.lean` and this record, and changing `research/audits/README.md`
and `research/tasks.json`) **remain uncommitted and unpushed**.

## Verification

* L9 client from its new path: passed with `-DwarningAsError=true`; all 29 axiom reports are standard, without `sorryAx`.
* All other 16 audit clients (9 in `research/audits/` + 7 in `build/audit/`) were rerun and passed strictly;
  `sorryAx` in `LevelSetMeasurableAudit` and `SuperlevelSardScope` intentionally reports still-open holes.
* Each of the three WIP files was actually compiled: direct holes **2/3/5, totaling 10**.
* `python3 research/atlas.py check` and the default `lake build` passed.
* Root `python3 research/verify.py` passed. The final receipt, `build/verification/latest.json`,
  exactly matches the complete final source snapshot; the check is separately saved in `build/audit/evidence-completion-final-snapshot.json`.
