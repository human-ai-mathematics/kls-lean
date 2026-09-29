# Survey of the Buser Half `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` Route: Obstacle Localization and Phased Program Outline

2026-09-19. After the five holes in energy reach zero, the Owner instructs to proceed with the Buser half of Cheeger–Buser. This round is a **route exploration**, with **no theorems proven**, and **no modifications to any existing `.lean`**; the deliverables are precise localization of obstacles, accurate retrieval from Mathlib and this repository, a **phased roadmap**, and a route statement file containing only `#check` `research/audits/BuserRouteStatements.lean`. **Passing type checking is not a proof.**
Direct proof hole **0**, certification **26**, unchanged. No commit, no push.

Start `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; start verification receipt
`build/verification/20260918T151845.800831Z/report.json`: 10 gates, 241 module replays, 662 entries, snapshot `1fc50cd6d74a2b42f74600fc30b5b245316a9d58d53e034f05cd56f2a033606d`.

## One, Conclusion First

**Buser's half in dimension `n ≥ 2` is not something that can be accomplished in one go; it is a programmatic framework.** All known proofs of the log-concave law go through one of two infrastructures, neither of which exists in Mathlib or in this repository.

1. **Weighted heat semigroup + Bakry–Émery gradient bound** (Ledoux's argument; De Ponti–Mondino obtained the sharp constant `π` on `RCD(0,∞)`).
   Requirement: existence of a semigroup (Mathlib does not have Hille–Yosida, does not have spectral theorem for unbounded self-adjoint operators; this repository has the closed quadratic form of Cheeger energy)
   `Energy/ClosedQuadratic.lean`, `FormCore.lean`, but without tools to generate a semigroup from it; `‖∇P_t f‖² ≤ P_t‖∇f‖²`
   (`CD(0,∞)`, either regularity of strictly parabolic PDEs—support of log-concave laws might be convex bodies with boundary with possibly nonsmooth densities—or via characterization through Wasserstein contraction / EVI)
   Then the duality estimate of Ledoux `‖f − P_t f‖₁ ≤ c√t · μ⁺(A)` and spectral decay `‖P_t f − μA‖₂ ≤ e^{−t/C_P}‖f − μA‖₂` are compared, `t` taking the optimal.
2. **Localization / Needle decomposition** (Lovász–Simonovits partitioning, Klartag's needle decomposition). Partitioning and needle limits are elementary measure theory and convex geometry, but lengthy;
   More importantly, a **transfer argument** is required: needles are one-dimensional log-concave laws; estimates such as `Q1`–`Q3` give `h(needle) ≳ 1/σ(needle)`, but relating `σ(needle)` to `C_P(μ)`
   There is no elementary way to connect (the conditional variance along a fixed direction is only controlled in the average sense under `Var⟨x,θ⟩ ≤ ‖Cov‖ ≤ C_P`, while each individual term is uncontrolled);
   And `h ≳ 1/√‖Cov‖` is the KLS conjecture itself). E. Milman's "concentration implies isoperimetry under convexity" requires a semigroup or GMT regularity; Klartag 2017 re-proved it using needle decomposition,
   The one-step transfer still uses one-dimensional comparison under curvature–dimension conditions, translating to Lean as a complete needle decomposition.

**Mathlib Search**: No heat kernel/heat equation, no Ornstein–Uhlenbeck, no Bakry–Émery, no localization lemma, no log-concavity, no Prékopa–Leindler
(`Analysis/Convex/Intrinsic.lean` related to convex geometry but unrelated to isoperimetric inequalities). Present: convolution, `ContDiffBump`, Gaussian distribution, Fourier transform, variance and `evariance`.
**This repository has**: one-dimensional Borell density and hazard bounds for log-concave laws (`KLS/LogConcave/Line/{Density,Hazard}.lean`: `2ρ(m)F(x) ≤ ρ(x)`, `2ρ(m)(1−F(x)) ≤ ρ(x)`, existence of median), one-dimensional Prékopa–Leindler (`Probability/Line/BrunnMinkowski.lean`),
one-dimensional log-concave Poincaré certificate (`C_P^lit ≤ 4 Var`), lower bound under linear tests (`Var ≤ C_P^smooth`), conditional fibers (one-dimensional reduction along a fixed direction, giving Poincaré-type rather than isoperimetric-type conclusions), newly proven `h_M = h_S` (`lem:relative-perimeter-cheeger-infimum`) and Cheeger half.

## Two. Phased Program

**Phase one (current round definition, immediately actionable): one-dimensional, explicit constant 12.** All materials are in place on the line:
* `Q1`: one-dimensional isoperimetry `h_M(ν) ≥ 2ρ(m)`. The certified `h_M = h_S` reduces this to the smooth-domain form `Q1'`: smooth domains in `ℝ` are open sets with discrete boundary,
  The relative perimeter is `ρ` summed over boundary points in the (interior of the) support (`ℋ⁰` counting points); the median-containing branch gives `ρ(a) + ρ(b) ≥ 2ρ(m)(F(a) + 1 − F(b)) ≥ 2ρ(m)(1 − νU)`,
  The other branches give ρ(endpoint) ≥ 2ρ(m)·ν(branch), summed.
* `Q2` `ρ(x) ≤ 2ρ(m)`: Let `κ` denote the slope of `log ρ` in the direction from the median to the mode, assign the distal half mass to `κ ≤ 2ρ(m)`, and assign the proximal half mass to ρ(mode) ≤ ρ(m) + κ/2.
  Exponential law takes equality.
* `Q3` density `≤ M`'s law variance `≥ 1/(12M²)` (without log-concavity): the masses on both sides of the mean `p`, `1−p` respectively, each having second moments not less than those of the uniform distribution over the long `p/M` interval,
  `p³ + (1−p)³ ≥ 1/4`.
* `Q4` linear test `Var(id) ≤ C_P^smooth` (the identity map is a smooth test with unit gradient energy); `Q5` log-concave law has finite second moment.
* `Q0` Assembly: `Ψ² = h_M⁻² ≤ (2ρ(m))⁻² ≤ ρ_max⁻² ≤ 12·Var ≤ 12·C_P^smooth`; `Q0'` via constant identification in literature and `h_μ = h_M(ν)`
  Move to the affine support dimension `≤ 1` of `μ` (both sides are 0 for a Dirac law).

The constant **12 is not π**: Phase one proves the Buser half in one dimension with a worse constant, saying nothing about `n ≥ 2`. The Blueprint node retains `π`; if the blueprint ultimately closes with a non-sharp constant,
it must **explicitly** weaken the Blueprint statement rather than silently replace it.

**Phase 2 (not started)**: (a) Construct a Markov semigroup from Cheeger's closed quadratic form (first complete the Hille–Yosida or at least construct the spectrum of a symmetric contraction semigroup), prove Bakry–Émry gradient bounds, and run the Ledoux argument; or (b) formalize the Lovász–Simonovits partitioning and needle limit, then find a transfer argument. Both estimates involve thousands of lines and carry Mathlib-level prerequisites.

## Three. Obligatory Checklist (Phase One)

Precise Lean statements at `research/audits/BuserRouteStatements.lean` (7 citation of proven lemmas, 10 theorems: `B0`, `Q0`, `Q0'`, `Q1`, `Q1'`, `Q2`–`Q5`, `D1`).

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `B0` | **Guiding Objective**: Buser half, any dimension, constant `π` | — | Stage two, not started |
| `Q0` | line `Ψ² ≤ 12 C_P^smooth` | 40 | low (synthesis of `Q1`–`Q5`) |
| `Q0'` | affine support dimension `≤ 1` of `μ`: `Ψ_KLS² ≤ 12 C_P^lit` | 120 | Medium (one-dimensional direction space and isometric transport to `ℝ`) |
| `Q1'` | one-dimensional isoperimetric problem for smooth domain forms | 300 | **Medium–High** (discrete boundary, branching enumeration, `ℝ` smooth domain boundary, `ℋ⁰` point counting) |
| `Q1` | `2ρ(m) ≤ h_M` | 20 | low (`Q1'` + `h_M = h_S`) |
| `Q2` | `ρ ≤ 2ρ(m)` | 120 | Medium (supporting line + integral estimate of masses on both sides) |
| `Q3` | `Var ≥ 1/(12M²)` | 150 | Medium (bathtub rearrangement) |
| `Q4` | `Var(id) ≤ C_P^smooth` | 30 | low |
| `Q5` | log-concave law `id ∈ L²` | 20 | low (existing moment results) |
| `D1` | `π < 12` | 2 | accounting |

Total of approximately **800 lines**. Recommended order: `Q5`, `Q4`, `Q3`, `Q2`, `Q1'`, `Q1`, `Q0`, `Q0'`.

## Four. Clarify What Hasn't Been Proven

* `B0` unproven, and this round does not claim any `n ≥ 2` Buser-type conclusions. `thm:logconcave-cheeger-poincare-comparison` does not mark `\leanok`.
* The constant in stage one is 12, not π. dimension-free KLS remains open.

## 5. Verification

The route file passes `lake env lean -DwarningAsError=true`, 17 `#check`, 0 errors, 0 warnings; log `build/audit/buser-route/route-statements.log`. Verification receipt is bound to the following implementation round.

## Note (2026-09-19, after the first implementation round)

Phase one obligations `Q0`, `Q0'`, `Q1`, `Q1'`, `Q2`–`Q5` proved (`KLS/LogConcave/Line/{Isoperimetry,Buser}.lean`), statement verbatim unchanged.
Two proofs differ from this record: `Q1'` does not require boundary discretization or branch enumeration (for any open set containing the median, `sSup (Iio m \ W)` and `sInf (Ioi m \ W)` suffice as boundary points); `Q3` is derived from the median variance bound already certified in `Line/Variance.lean`, without the bathtub rearrangement. `B0` remains unchanged from Phase two. See [implementation record](2026-09-19-buser-line-proofs.md).
