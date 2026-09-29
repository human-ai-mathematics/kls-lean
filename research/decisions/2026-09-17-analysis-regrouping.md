# Regrouping Analysis/: moving family names from filenames into directories

2026-09-17 (same day, after the file-management round). This round **proves no theorem and changes no declaration**:
**32 of the 50** flat modules under `formalization/FunctionalInequalities/Analysis/` move into mathematical-family
subdirectories, dropping the family word from each basename. The rule comes from the preceding addition to
`research/naming.md`: “Family names belong in directories, not filenames”.

**This is purely a file-layout change.** No declaration is renamed, added, deleted, or reproved; no namespace changes.
No hole migration, commit, or push. Direct holes remain **8 (1/2/5)**; certificates remain **24**.

Starting point: `HEAD = origin/main = e7c4403352011b6c3ed6dc02f0af3eef6cbb300e`;
preceding final passed receipt: `build/verification/20260917T101245.968268Z/report.json`,
10 gates, 224 local modules replayed by the kernel, 611 entries, snapshot
`52d3c1c3f3c115e85b1413681603573777cfe83a587446a703261579eb85095a`, with no drift.
Concurrent sessions neither changed the worktree nor committed during this round.

## Boundary

The log-concave Cheeger–Buser line belongs to collaborator **Haocheng Wang** and is untouched,
as are sharp finite-regularity Sard, the five Energy holes, and dimension-free KLS.
This round **changes no mathematical content**.

## Why declaration names are unaffected

**43 of the 50** modules use the flat `namespace FunctionalInequalities.Analysis`.
The other three nested namespaces (`Analysis.WhitneyCover`, `Analysis.WhitneyJet`, `Analysis.LipschitzJet`)
are **entirely unchanged**. Namespaces are independent of directories, so moving files does not change declaration names.
Ledger nodes, Blueprint declarations, statement-snapshot goldens, and all axiom reports are therefore
**unaffected by regrouping**, directly checked by unchanged axiom-report counts.

In particular, `WhitneyCover` is both a module name and a namespace name:
module `Analysis.WhitneyCover` moves to `Analysis.Whitney.Cover`,
while namespace `FunctionalInequalities.Analysis.WhitneyCover` remains unchanged.
The rewrite script therefore changes **only `import` lines** and `Analysis/<File>.lean` path strings in documentation,
with no global identifier replacement. Of the 148 pre-edit occurrences of `FunctionalInequalities.Analysis.<moved module>`,
126 were import lines; the remaining 22 were the namespace and its declarations, individually checked and preserved.

## Groups

* **`Whitney/`** (5): Bump, Construction, Cover, Extension, Partition
* **`Sard/`** (4): Basic, Planar, Smooth, Equidimensional
* **`Vector/`** (11): CriticalSlice, FiberIntegral, HausdorffSlicing, LocalCoarea,
  RegularChart, RegularCoarea, SliceMeasurable, plus the nested
  `Vector/Graph/{Basic,Area,Integral,Sandwich}`
* **`RankDeficient/`** (8): Stratification, RightInverseBound, TangentialLipschitz,
  RegularFibreFinite, TargetSplitFubini, StratumSlicing, Coarea, ExponentObstruction
* **`Graph/`** (4): Integral, Jacobian, Implicit, OpenIntegral

**`Sard/Equidimensional` is classified by mathematical object, not provenance.** It is route obligation `R10`,
but its subject is the equidimensional Sard lemma, and `naming.md` assigns files by their main mathematical object.
That choice is explicitly recorded here.

**18 remain flat**: AreaFormula, CoareaGraphJacobian, CoareaJacobian, Divergence,
FiberIntegral, FirstOrderJet, HausdorffContent, HausdorffSlicing, LevelSet,
LipschitzC1Pieces, LipschitzJet, LocalInverse, NormDetContinuity, PartitionOfUnity,
QuadraticCover, RegularChart, SubgraphDivergence, TaylorRemainder.
`CoareaGraphJacobian` **deliberately stays outside `Graph/`**: `Graph/CoareaJacobian` would create a second module
with basename `CoareaJacobian`, making reading harder than the duplication it removes.
`Divergence`/`SubgraphDivergence`, `HausdorffContent`/`HausdorffSlicing`, and
`LipschitzC1Pieces`/`LipschitzJet` each have only two modules, below the rule's threshold of three.

## Path mapping

`research/api-migration/2026-09-17-analysis-module-map.json`: 32 module mappings and 32 file-path mappings.
The reason for this map is that **about 434 references in historical decisions and explorations use old paths;
the project does not rewrite historical records**. The map keeps those references resolvable, following the two
2026-09-08 migrations (`2026-09-08-module-map.json`, `2026-09-08-library-naming-module-map.json`).

## Changed files

* Move **32** modules.
* Rewrite **70** `import` lines and **44** documentation path strings across **61** `.lean` files
  (`formalization/`, `research/audits/`, and the **7 active clients rerun every round** under `build/audit/`).
* The 38 `.before.lean` files and historical route reviews under `build/audit/` **remain frozen**, including old imports:
  they are historical snapshots and are not rerun.
* `research/tasks.json`: rewrite 29 evidence paths and refresh 59 hashes.

## Required disclosure: the route statement file is no longer byte-identical

Earlier rounds recorded `research/audits/RankDeficientRouteStatements.lean` as **byte-identical**.
This round changes **5 lines**: one `import` (`Analysis.VectorCriticalSlice` → `Analysis.Vector.CriticalSlice`)
and four documentation path strings. Moving modules inevitably affects **every** consumer.

**All 15 `#check` propositions remain verbatim unchanged**, mechanically compared block by block with `HEAD`
and confirmed byte-identical. The outdated status note at the top of the file is also unchanged and remains its maintainer's responsibility.
Earlier byte-identity claims remain valid **for those rounds**; this record updates the current situation.

## Validation

* Default `lake build` passes (3426 jobs).
* All **52** audit clients were rerun and passed strict `-DwarningAsError=true` checks, with **0 failures**.
* Library-wide axiom reports: **672**, with **12** occurrences of `sorryAx`, **exactly matching** pre-regrouping counts.
  This is the most direct evidence that the mathematics was unchanged.
* The three WIP files compile separately: **1/2/5 direct holes, total 8**; `check_ledger.py` reports **24** certificates.
* Root-level `python3 research/verify.py` passes; local logs: `build/audit/analysis-regrouping/`;
  final snapshot check: `build/audit/analysis-regrouping/final-snapshot.json`.
* **No commit or push**; the real Git index is unchanged.
