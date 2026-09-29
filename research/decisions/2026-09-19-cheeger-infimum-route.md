# Cheeger Infimum Two-Hole Route Exploration: Taking Over the Cheeger Line from Senior

2026-09-19. Owner instruction: **we are taking over the work previously assigned to our senior colleague** —— the log-concave Cheeger geodesic (originally assigned to Haocheng Wang) with two holes, `KLS/WIP/CheegerInfimum.lean`, `lem:relative-perimeter-cheeger-infimum`, `thm:logconcave-cheeger-poincare-comparison`, is now being taken over by this session.
This round is a **route exploration**, **no theorems are proven**, no modifications are made to any existing `.lean`; the deliverable is a route statement file containing only `#check`.
`research/audits/CheegerInfimumRouteStatements.lean` (14 obligations/migration goal propositions + 8 proven assertions referenced).
**Proposition passing type checking is not a proof.** Direct proof holes remain **7 (0/2/5)**, certification remains **24**. No commit, no push.

Start `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; start verification receipt
`build/verification/20260918T132358.171383Z/report.json` (final verification receipt for the same day's round completion): 10 gates, 234 local module kernel replay,
638 entries, snapshot `d9cd7067e18cbebc3408d8e772fc539392533db8be44e91419f2bba370a7226a`. Drift is empty.

## Two holes

`K0` `Isoperimetry.smoothConstant_mul_lintegral_min_superlevel_le`: smooth Lipschitz `[0,1]`-valued `u`, `h_S · ∫₀¹ m(ν{u > t}) dt ≤ ∫ ‖∇u‖ dν`; `K5` `Isoperimetry.smoothConstant_le_minkowskiConstant`: `h_S ≤ h_M`.
Together with the previously proven `h_M ≤ h_S` (`KLS/Geometry/CheegerInfimum.lean`), we obtain `lem:relative-perimeter-cheeger-infimum` (`K10`) and two isoperimetric subclauses for `thm:klartag-density-frontend-identification` (`K12`, `K13`), and thereby decouple the three intrinsic transports from `sorryAx`.

## Route

**`K0`**: Almost every strict superlevel set of a `t` is a smooth domain (`SmoothDomain.ae_exists_superlevel`, smooth Sard, `K3`),
whose boundary is contained in the level set (`frontier_superlevel_subset`), so the relative perimeter ≤ the integral of the density over the level set (`K2`);
the infimum bound in product form `h_S · m(ν U) ≤ P_ρ(U)` holds for each smooth domain, zero and full mass are closed out by `⊤ · 0 = 0` (`K1`);
after integrating over `t`, using the weighted `C¹` coarea formula for the density (`K4`, derived from previously proven `lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
with weights `ofReal ∘ ρ`, `ν = volume.withDensity`) yields `∫ ‖∇u‖ dν`. Measurability of `t ↦ ∫_{u=t} ρ` is not required (`lintegral_mono_ae` does not require it).

**`K5`**: Take intermediate mass, Minkowski content finite Borel sets `B` (hence `ν(closure B) = ν B`). The gradient integral of distance truncation `w_r`
`≤ (ν(B^r) − ν B)/r` (already proved, `K6`), and the `𝟙_B` distance to `L¹` `≤ ν(B^r) − ν B` (`K7`); smoothing substitute (`K9`, WIP already proved)
satisfies `K0`; the balancing quantity is 1-Lipschitz for a set: `m(ν B) ≤ ∫₀¹ m(ν{u > t}) dt + ‖u − 𝟙_B‖₁` (`K8`, by the already proved
`lintegral_measure_symmDiff_superlevel` and `min_measure_le_add_measure_symmDiff`). **Subtract the error from the balancing quantity instead of multiplying it into `h_S`**:
`h_S · (m(ν B) − e_r) ≤ q(r)`, hence `h_S` need not be finite; first let the smoothing index tend to infinity, then take `r → 0⁺` along `liminf`—that is the Minkowski content.

## Obligation List

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `K0` | **Hole 1**: Smooth coarea bound | 60 | Low (synthesis of `K1`–`K4`) |
| `K1` | infimum bound of product form, for all smooth domains | 30 | low |
| `K2` | Relative perimeter of superlevel set ≤ integral over level set | 20 | low |
| `K3` | Almost every superlevel set is a smooth domain | — | **Proved** |
| `K4` | weighted density `C¹` coarea | 20 | low |
| `K5` | **Hole 2**: `h_S ≤ h_M` | 120 | Middle (limit order and handling of `⊤`) |
| `K6` | gradient integral with distance truncation | — | **proven** |
| `K7` | distance truncated to the indicator function of `L¹` distance | 30 | low |
| `K8` | balanced measure 1-Lipschitz | 30 | low |
| `K9` | Polishing Substitute | — | WIP proven, moved with migration |
| `K10`–`K13` | Equation and three intrinsic transports | — | WIP proven (modulo holes), carried in with migration |

A total of approximately **300 lines** of new proofs, plus about 200 lines migrated from WIP. Recommended order: `K1`, `K2`, `K4`, `K0`, `K7`, `K8`, `K5`.
After verification, migrate according to precedent: the new module `KLS/Geometry/CheegerEquality.lean` carries all seven public assertions from WIP (`pp.all` byte-by-byte comparison),
delete WIP, and register `lem:relative-perimeter-cheeger-infimum` as the 25th certificate.

## Boundary

Five holes in energy, dimension-free KLS untouched. Cheeger–Buser comparison `thm:logconcave-cheeger-poincare-comparison` takes a different route.
`research/tasks.json` contains `lem:relative-perimeter-cheeger-infimum`'s `gaps` which is exactly `K0` and `K5`; this round does not alter it.

## Verification

The route file passes `lake env lean -DwarningAsError=true`, 22 `#check`, 0 errors, 0 warnings, no import of WIP;
Log `build/audit/cheeger-infimum-route/route-statements.log`. This round does not rerun `verify.py`: the implementation round of the same day follows immediately,
the verification receipt is bound to that round.

## Note (2026-09-19, after implementation)

* **`K7` is literally false.** `B = ∅` when Mathlib's `Metric.infDist x ∅ = 0` makes `distanceCutoff ∅ r ≡ 1`, and
  `Metric.thickening r ∅ = ∅`, the statement is read as `1 ≤ 0`. The proof session uses the Dirac law on `EuclideanSpace ℝ (Fin 1)` in auditing.
  Proved the literal form to be false (`route_K7_empty_counterexample`), and proved the version with addition of `B.Nonempty` (`route_K7`);
  `K5` Apply it only to sets with positive mass; downstream is unaffected. Route statement files preserve byte-for-byte.
* The remaining `K0`–`K6`, `K8`–`K13` are all proven or migrated into `KLS/Geometry/CheegerEquality.lean`, and the seven public statements `pp.all` are byte-for-byte identical
  (the 2223-line `diff` is empty). See the [implementation record](2026-09-19-cheeger-line-proofs.md).
