# Cheeger's inequality completed and registered: two holes closed, `lem:relative-perimeter-cheeger-infimum` becomes the 25th certificate, Cheeger's inequality proven

2026-09-19, **implementation + registration cycle**. Owner indicates taking over the Cheeger geodesic previously assigned to our senior colleague, Haocheng Wang. On the same day, two routes were initially written.
(the [two-hole route](2026-09-19-cheeger-infimum-route.md) and [Cheeger inequality route](2026-09-19-cheeger-inequality-route.md)),
Intersecting two parallel proof sessions, this session integrates and registers. Result:

* **Two-hole closure**: `smoothConstant_mul_lintegral_min_superlevel_le`, `smoothConstant_le_minkowskiConstant` in
  `KLS/Geometry/CheegerEquality.lean` proved; seven public statements of the WIP module are migrated with **bit-identical `pp.all` signatures**
  (the 2223-line printed `diff` is empty); `KLS/WIP/CheegerInfimum.lean` is deleted, and the `KLS/WIP/` directory disappears with it
  (Original frozen at `build/audit/cheeger-line-proofs/CheegerInfimum.before.lean`).
* **The 25th certificate**: `solutions/LemRelativePerimeterCheegerInfimum.lean` registered `lem:relative-perimeter-cheeger-infimum`
  (`certificate hρ : h_M = h_S`, any law with Borell density; `intrinsic hμ hρ`: `h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν`,
  That is (the two isoperimetric subclauses of) `thm:klartag-density-frontend-identification`, with four axiom checks.
* **Cheeger inequality**: `KLS/Geometry/CheegerInequality.lean` (including `KLS/Geometry/Median.lean`) proved
  `C_P^smooth(ν) ≤ 4/h_M(ν)²` (any Borel law, `Isoperimetry.smoothTest_constant_le`) and
  `C_P^lit(μ) ≤ 4Ψ_KLS(μ)²` (log-concave law, `LogConcave.literatureConstant_le_four_mul_inverseScale_sq`, both sides are 0 for a Dirac law).
  Buser half `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` **unproven**, `thm:logconcave-cheeger-poincare-comparison` plus `\lean{}` with explanation, without `\leanok`.

Direct proof hole reduced from **7 (0/2/5)** to **5 (0/0/5)**, leaving only **`Energy/WIP/Cheeger.lean`**; certification **24 → 25**. No commit, no push.

Start `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; start verification receipt
`build/verification/20260918T132358.171383Z/report.json`: 10 gates, 234 module replays, 638 entries, snapshot `d9cd7067e18cbebc3408d8e772fc539392533db8be44e91419f2bba370a7226a`.

## Boundary

The five holes of energy (`Energy/WIP/Cheeger.lean`, singular measures' `𝓔^can = 2Ch`) remain untouched; dimension-free KLS is still open.
No new compatibility aliases, no rephrasing of existing theorems, no weakening of previously proven conclusions; the literature statement on Poincaré constants in `thm:klartag-density-frontend-identification`
**not certified at this node** (the node does not mark `\leanok`, only adds a note).

## Two proof sessions

Rules as before (only create new files, do not `lake build`, do not modify Git, strict compilation, word-for-word reproduction, do not import WIP, comments do not contain escape words).

| route | new library module (rows) | audit client (rows) | settlement |
| --- | --- | --- | --- |
| two holes | `KLS/Geometry/CheegerEquality.lean` 568 (seven incoming + five new lemmas `K1`, `K2`, `K4`, `K7`, `K8`) | `CheegerEqualityAudit.lean` 354 | `K0`–`K13`; **`K7` literally false**, see below |
| Cheeger inequality | `KLS/Geometry/Median.lean` 167, `CheegerInequality.lean` 784 (+27 integration `P0`) | `CheegerInequalityAudit.lean` 210 (+9 integration `route_P0`) | `P1`–`P6`, `D1`; `P0` integration combined |

**`K7` Literally false**: `B = ∅` when `Metric.infDist x ∅ = 0`, the truncation is always 1 while thickening is empty, and the statement reads as `1 ≤ 0`; in audits,
`route_K7_empty_counterexample` uses a Dirac delta on `EuclideanSpace ℝ (Fin 1)` to falsify the literal form, `route_K7` proves the version with `B.Nonempty`;
`K5` is only applied to positive mass sets, downstream is unaffected. The route statement file maintains byte integrity.

**Synthesis of `P0`**: `Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope` (intrinsic absolute continuity of log-concave laws) identifies the literature constant as a smooth test constant for the intrinsic law, `Isoperimetry.constant_eq_minkowskiConstant_intrinsic` to `h_μ = h_M(ν)`, then using `P1`.
`P6` reuses repository's existing smooth truncation `Energy.Euclidean.LipschitzApproximation.scaled`, and convergence of gradient energy uses `ℝ≥0∞` dominated convergence, while variance uses Fatou.

## Registration and Integration Actions

1. Certificate file, ledger node (`kind: lemma`, `meta.scope` appended), `research/check_blueprint.py`'s `CERTIFICATES`,
   the `Solutions` root in `lakefile.toml`; Blueprint Chapter 60 Lemma plus `\lean{…}`, `\leanok` (statement notes stronger scope within Lean), proof block `\leanok`;
   Chapter 45 Klartag node with annotations (two isoperimetric substatements certified, Poincaré substatement not yet), Cheeger–Buser theorem with `\lean{…}` and annotations, without `\leanok`.
2. The escape word scanning of `check_ledger.py` is a pure text scanning pass-through import source: certificate import closure contains 13 modules' docstring writing «contains no `sorry`»
   phrases such as “admit fewer covers” are rewritten using hole / allow, without changing code.
3. Three previously imported WIP clients (`research/audits`'s `LipschitzCoareaMigrationAudit`, `IsoperimetryCoareaAudit`;
   Historical client `build/audit/PerimeterInterfaceAudit`) reconnected `KLS/Geometry/CheegerEquality.lean`; they previously carried `sorryAx` of 5 reports are now standard.
4. Aggregate import includes `KLS.Geometry.CheegerEquality`, `KLS.Geometry.CheegerInequality` (`Median` accordingly), together with two additional explanations.
5. `research/tasks.json`: infrastructure `lem:relative-perimeter-cheeger-infimum` `missing → available`, evidence replaced with new module, audit, and certification;
   The hash values of all other nodes are fully refreshed; Klartag and Cheeger–Buser node annotations. The progress view is regenerated temporarily via `research/progress/update.py`
   (`STATUS.md`: 25 certificates).
6. Default `lake build` (3507 jobs) passed; `check_ledger.py` 25 node 0 error; `check_blueprint.py` 88 label 0 error.

## What remains unproved

* Buser half `Ψ_KLS(μ)² ≤ π C_P^lit(μ)`: unproven (Bakry–Émery or Lovász–Simonovits localization not in Mathlib); Cheeger–Buser node not labeled `\leanok`.
* `thm:klartag-density-frontend-identification` literature Poincaré constant clause not certified at this node.
* Energy five holes not touched; dimension-free KLS still open. `K7`'s literal form is false has been recorded (and formally falsified).

## Verification

Default `lake build` (3507 jobs, including new certificate `Solutions` library) passes. All **62** audit clients (**`research/audits` 55** + **`build/audit` 7** active clients) rerun with `-DwarningAsError=true` retries, **0 failures**; **791 axiom reports, 0 `sorryAx`**—no client reports a hole for the first time. The remaining WIP module `Energy/WIP/Cheeger.lean` compiles with **5** `sorry` warnings, direct proof hole **5 (0/0/5)**. The `pp.all` before and after of seven migration declarations are both `diff` empty. `check_ledger.py` **25** certificate 0 errors; `check_blueprint.py` 88 label 0 errors; `atlas.py check` 75 node 25 certificate has no cycle; 104 unit tests pass.
`pp.all` Seven statements before and after `diff` are empty. The root directory `python3 research/verify.py` is rerun at the end of this round, and the final verification receipt is recorded at
`build/audit/cheeger-line-proofs/final-snapshot.json`, snapshot and workspace recalculated line by line, drift is empty.
See `research/explorations/2026-09-19-cheeger-line-proofs.json`.
