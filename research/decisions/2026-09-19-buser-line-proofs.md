# Buser direction, stage one proved: dimension one, constant 12

2026-09-19, **implementation round**, following the same day's [Buser route investigation](2026-09-19-buser-route.md). One proof session proved every stage-one obligation,
`Q0`, `Q0'`, `Q1`, `Q1'`, `Q2`–`Q5` (and `D1`); this session integrated the results. Result: for log-concave laws on the line, `Ψ² ≤ 12·C_P^smooth(ν)`
(`KLS.LogConcave.inv_minkowskiConstant_sq_le`), and transport yields **`Ψ_KLS(μ)² ≤ 12·C_P^lit(μ)` for every log-concave law
with affine-support dimension `≤ 1`** (`LogConcave.inverseScale_sq_le_of_finrank_le_one`).
**`B0` (arbitrary dimension, constant `π`) remains unproved**; the Blueprint node `thm:logconcave-cheeger-poincare-comparison` is not marked `\leanok`; only `\lean{}` and explanatory text were added.
Direct holes **0**, certificates **26**, unchanged. No commit or push.

Starting point: `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; the starting passed receipt
`build/verification/20260918T151845.800831Z/report.json` records 10 gates, 241 module replays, 662 entries, and snapshot `1fc50cd6d74a2b42f74600fc30b5b245316a9d58d53e034f05cd56f2a033606d`.

## New modules and delivered results

| Module (lines) | Content |
| --- | --- |
| `KLS/LogConcave/Line/Isoperimetry.lean` (450, 14 public declarations) | `Q1'` `LineDensity.mul_min_le_relativePerimeter`, `Q1` `LineDensity.two_mul_le_minkowskiConstant`, `Q2` `LineDensity.le_two_mul`, `Q3` `LineDensity.one_div_le_evariance`, `LineDensity.interior_support_nonempty` |
| `KLS/LogConcave/Line/Buser.lean` (371, 10 public declarations) | `Q4` `KLS.evariance_le_smoothTest_constant`; isometric transport `Isoperimetry.minkowskiConstant_map`, `nonempty_linearIsometryEquiv_real`; degenerate cases `exists_support_eq_singleton`, `minkowskiConstant_eq_top_of_interior_empty`; `Q0` `LogConcave.inv_minkowskiConstant_sq_le`; `Q0'` `LogConcave.inverseScale_sq_le_of_finrank_le_one` |
| `research/audits/BuserLineAudit.lean` (195) | `route_Q0`…`route_Q5`, `route_D1` delivered verbatim; boundary cases: dimension zero for `Q0'` (inverse scale 0), Dirac laws on `ℝ` (`h_M = ⊤`); all 36 axiom reports are standard |

`Q5` uses the existing `LogConcave.memLp_id_two`; `D1` uses `Real.pi_le_four` and `linarith`.

## Two proofs differ from the route record (statements unchanged verbatim)

* **`Q1'` needs neither a discrete boundary nor component enumeration** (the route budgeted 300 lines for this): `surfaceMeasure ℝ = μH[0]` bounds the boundary integral from below by `ρ` at **one** boundary point.
  For **any** open set `W` containing the median `m`, `a = sSup (Iio m \ W)` and `b = sInf (Ioi m \ W)` are boundary points and `Wᶜ ⊆ Iic a ∪ Ici b`.
  The hazard bound directly gives `2ρ(m)·ν(Wᶜ) ≤ ρ(a) + ρ(b)`. Split into the median lying inside the domain, on its boundary, or outside its closure; the boundary case needs only `ρ(m)`, since `2·min(p, 1−p) ≤ 1`.
  Smoothness and `ν(∂U) = 0` are unused throughout.
* **`Q3` follows from the certified median-variance bound, not a bathtub rearrangement**: the route statement quantifies over `d : LineDensity ν`, which already carries a log-concave Borell density.
  Thus `d.logConcave` + `interior_support_nonempty` + `one_div_le_variance` from `Line/Variance.lean` + `ρ(m) ≤ M` suffice.
  A rearrangement proof covering non-log-concave bounded densities **was not written**.

## Explicitly unproved

`B0`: the Buser direction in arbitrary dimension, with constant `π`—stage two (semigroup + Bakry–Émery, or localization + transfer) has not started. Dimension-free KLS remains open.
The equality case of `Q2` for the exponential law has not been formalized (the repository has no exponential law equipped with `LineDensity`).

## Verification

The default `lake build` (3514 jobs) passed. All **68** audit clients (61 in `research/audits` + 7 active clients in `build/audit`) were rerun with `-DwarningAsError=true`, with **0 failures**; **903 axiom reports, 0 occurrences of `sorryAx`**. `check_ledger.py`: **26** certificates, 0 errors; `check_blueprint.py`: 88 labels, 0 errors; `atlas.py check`: 75 nodes, 26 certificates, acyclic; all 104 unit tests passed.
Root `python3 research/verify.py` was rerun at the end of the round; the final receipt is recorded in `build/audit/buser-line-proofs/final-snapshot.json`.
The snapshot and workspace were recalculated entry by entry, with empty drift. See `research/explorations/2026-09-19-buser-line-proofs.json`.
