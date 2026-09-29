# Exploring the Cheeger inequality route `C_P^lit ≤ 4Ψ²`: the Cheeger half of Cheeger–Buser

2026-09-19. The second route after taking over the Cheeger line (the first is the [two-hole route](2026-09-19-cheeger-infimum-route.md)).
This round is **route exploration**: **no theorem was proved**, and no existing `.lean` file was changed.
The deliverable is `research/audits/CheegerInequalityRouteStatements.lean`, containing only `#check` commands
(9 propositions and references to 5 proved declarations). **Typechecking a proposition is not proving it.**
Direct holes remain **7 (0/2/5)**; certificates remain **24**. No commit or push.

Starting point: `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; the starting passed receipt is
`build/verification/20260918T132358.171383Z/report.json`: 10 gates, 234 replayed modules, 638 entries,
snapshot `d9cd7067e18cbebc3408d8e772fc539392533db8be44e91419f2bba370a7226a`.

## Goal and scope

The **Cheeger half** (`P0`) of `thm:logconcave-cheeger-poincare-comparison`: for every finite-dimensional log-concave law `μ`,
`C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²`, where `C_P^lit` is the intrinsic local-slope Poincaré constant of
`def:literature-poincare-constant` (`Poincare.LocalSlope.Intrinsic.constant`) and
`Ψ_KLS = h_μ⁻¹` (`Isoperimetry.inverseScale`). Both sides are `0` for a Dirac law.
The **Buser half**, `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` (`B1`), is **outside this route**: known proofs for log-concave laws
use either Bakry–Émery gradient estimates for the weighted heat semigroup (Ledoux; De Ponti–Mondino give the constant `π`)
or Lovász–Simonovits localization, neither available in Mathlib or this repository. The node therefore **will not** receive `\leanok`.
The five Energy holes and dimension-free KLS are untouched.

## Route

Work in coordinate space with an arbitrary Borel probability law `ν` and its Minkowski constant `h_M`, then transfer to log-concave laws.
A median exists (`P2`). For bounded `C¹` Lipschitz `g`, use `Var(g) ≤ ∫ (g−m)²` and split into `(g−m)₊²` and `(m−g)₊²`.
Each `v = (g−m)₊²` is `C¹` (since `t ↦ max t 0 ^ 2` is `C¹`), Lipschitz, and supported on `{g > m}`, of mass ≤ 1/2.
Thus the balanced mass of every superlevel set is its mass. The layer-cake formula, `minkowskiConstant_mul_min_le`,
and the Minkowski coarea inequality `lintegral_minkowskiContent_superlevel_le` yield the **`L¹` Cheeger inequality**
`h_M ∫ v ≤ ∫ ‖∇v‖` (`P3`). The chain rule `∇v = 2(g−m)₊∇g` and Cauchy–Schwarz give
`h_M² ∫ (g−m)₊² ≤ 4 ∫_{g>m} ‖∇g‖²` (`P4`); adding the two halves gives `h_M² Var(g) ≤ 4 ∫ ‖∇g‖²` (`P5`).
For general smooth tests, use smooth bump cutoffs: these are bounded and Lipschitz, and their variances and gradient energies
converge to those of the original test (`P6`). Hence `C_P^smooth(ν) ≤ 4/h_M²` (`P1`; the right side is `⊤` when `h_M = 0`).
Finally, identify the literature constant with the smooth-test constant of the intrinsic law using
`Poincare.SmoothTest.constant_eq_intrinsicMeasure_and_localSlope` (log-concave laws have the required absolute continuity),
and use `h_μ = h_M(ν)` (`K11` of the two-hole route) to transfer `P1` to `P0`.

## Obligations

| ID | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `P0` | **Goal**: `C_P^lit(μ) ≤ 4Ψ_KLS(μ)²` | 15 | Low (transfer, requires `K11`) |
| `P1` | `C_P^smooth(ν) ≤ 4/h_M²` for any Borel law | 40 | Low (`Holds` and `toReal` bookkeeping) |
| `P2` | Existence of a median | 60 | Low |
| `P3` | `L¹` Cheeger: nonnegative, supported on at most half the mass | 60 | Medium (layer cake and two Minkowski lemmas) |
| `P4` | Squared positive part: `h_M² ∫(g−m)₊² ≤ 4∫_{g>m}‖∇g‖²` | 120 | Medium (chain rule and Hölder algebra in `ℝ≥0∞`) |
| `P5` | Cheeger inequality for bounded `C¹` Lipschitz functions | 80 | Low–medium |
| `P6` | Extend by cutoff to all admissible smooth tests | 200 | **Medium–high** (dominated convergence, Lipschitz and gradient bounds for `scaled R`) |
| `D1` | `h_M = ⊤ ⟹ C_P^smooth = 0` | 5 | Not a route step |
| `B1` | Buser half, explicitly out of scope | — | Scope boundary |

Approximately **600 lines** in total. Recommended order: `P2`, `P3`, `P4`, `P5`, `P6`, `P1`.
Assemble `P0` after `K11` moves to a hole-free module. `P6` is the only item likely to take substantially longer.
If the cutoff convergence argument is too involved, a fallback statement for bounded Lipschitz tests is possible,
but it is **not** `P1` and must be reported as such.

## Validation

The route file passes `lake env lean -DwarningAsError=true`: 14 `#check` commands, 0 errors, 0 warnings, no WIP imports.
Log: `build/audit/cheeger-inequality-route/route-statements.log`. The receipt is bound in the immediately following implementation round.

## Addendum (2026-09-19, after implementation)

`P1`–`P6` and `D1` are all proved in `KLS/Geometry/Median.lean` and `KLS/Geometry/CheegerInequality.lean`.
`P6` reuses the repository's smooth cutoff `Energy.Euclidean.LipschitzApproximation.scaled`.
`P0` is assembled during integration after `K11` moves to `CheegerEquality.lean`, as
`LogConcave.literatureConstant_le_four_mul_inverseScale_sq`. `B1` remains unproved.
See the [implementation record](2026-09-19-cheeger-line-proofs.md).
