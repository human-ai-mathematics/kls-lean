# Energy's Five-Hole Route Investigation: The `𝓔^can = 2Ch` of Singular Laws

2026-09-19. After Cheeger's line is closed, the Owner instructs to proceed with the Energy five-hole—last WIP module `Energy/WIP/Cheeger.lean`.
This round is a **route exploration**, proving no theorems, making no changes to any existing `.lean`; the deliverable is a route statement file containing only `#check`
`research/audits/EnergySlopeRouteStatements.lean` (19 proposition + 5 cited proven statements). **A proposition passing type checking is not a proof.**
Direct proof hole still **5 (0/0/5)**; certification still **25**. No commit, no push.

Start `HEAD = origin/main = f108397aa6eafcde0a8ca99658e40c47b2926db3`; start verification receipt
`build/verification/20260918T141537.829419Z/report.json`: 10 gates, 237 module replays, 650 entries, snapshot `f91b06cac5cf4d62e270ae9ec48c1d6c2459fa53583be0b4f06a51d7baa3aa4c`.

## The True Structure of Five Holes

WIP module states for any Borel probability measure `ν`: `E0a` smooth gradient relaxation = relaxation of squared local slope; `E0b` two Cheeger-type relaxations are identical; `E0c` two Cheeger energies are equal; `E0d` on coordinate space `𝓔 = 2Ch`; `E0e` Blueprint identity `thm:smooth-gradient-relaxation-two-cheeger`.
The certified `cor:absolutely-continuous-relaxation-two-cheeger` proves all five statements on absolutely continuous laws. **The true obligation is only `E0a`**:
`E0b` derived from squeezing `LocalSlope ≤ AsymptoticLipschitz ≤ SmoothGradient` (`A2`) after collapsing the ends in `E0a` yields (`A3`),
`E0c` is `E0b` divided by 2, `E0d` is `Cheeger.two_mul_energy`, `E0e` is `E0a` used for intrinsic law, copying previously certified inferences as transfer.
WIP module incorrectly directs the Ambrosio–Gigli–Savaré direction to `E0b`: in singular cases, what is required is the **density of smooth tests in the local slope energy**, i.e., the reverse inequality without the density assumption `SmoothGradient.relaxation ≤ LocalSlope.relaxation` (`C6`).

## Route

**A squeezing** (`Energy/Euclidean/SlopeComparison.lean`): The pointwise asymptotic Lipschitz constant of a smooth test equals the gradient norm (`A1`), with the lower bound attained by the slope at a moving point and the upper bound given by the mean value inequality on a ball; thus, the smooth test lies in the asymptotic Lipschitz test class with the same energy, and relaxation over a larger class is smaller (`A2`); `A3` records collapse.

**B Smooth Recovery of Global Lipschitz Test** ( `Energy/Euclidean/SlopeRecovery.lean` ): Mollify a globally `K`-Lipschitz function `g` at radius `2R`,
smoothed at a point only within `2R`, hence inherits the Lipschitz constant of `g` on the ball of radius `δ+2R` to the ball of radius `δ`, yielding
`limsup_R ‖∇(g⋆ρ_R)(x)‖ ≤ Lip_a g(x)`; the global constant uniformly controls the integrand, reverse Fatou applies, yielding `B1`.
**Uniform radius is insufficient for general test** ( `D1`: `ν = Σ2⁻ⁿδ_n` plus narrow spikes ). Hence, need a reduction tool: local Lipschitz multiplied by bounded global Lipschitz remains local Lipschitz ( `B2` ), local Lipschitz and zero outside the ball ⟹ global Lipschitz ( `B3` ), a pointwise Leibniz bound for two slopes ( `B4`, `B5` ).

**C Density** (`Energy/Euclidean/SlopeDensity.lean`): `C1` proves that the local slope of a continuous function is Borel: the supremum of secant slopes at radius `1/(m+1)` is lower semicontinuous, and the local slope is their countable infimum. For the `C2` McShane patch, stratify the slope of a globally `L`-Lipschitz function `f` into bands of width `α`, cut each band using balls from a dense sequence, and apply `disjointed` to obtain a Borel partition. On each piece, the Lipschitz constant of `f` differs from its slope by `≤ 2α`. Inner regularity supplies finitely many pairwise disjoint compact cores with remaining mass `≤ δ`. Extend from each core by McShane and glue with linear cutoffs at scales smaller than the distances between cores. The patch `F` has global Lipschitz constant `9L + 8α`, independent of `δ`; it equals `f` on the cores, and its asymptotic Lipschitz constant there differs from the slope of `f` by `≤ 2α`.
`C4`: choose `α = δ = 1/(n+1)`. The patches converge to `g` in `L²(ν)`. `B1` bounds the relaxation at each patch by its asymptotic Lipschitz energy, which is `≤ (1+4α)·LocalSlope.energy g + 4α + 4α² + M²δ` (using measurable majorants, without requiring measurability of the asymptotic constants). Lower semicontinuity of the relaxation finishes the argument.
`C5`: truncate a general admissible test using `scaled (n+1)`. By `B2` and `B3`, the truncations are globally Lipschitz. Dominated convergence gives `L²` convergence; `B5` and Young's inequality `(a+b)² ≤ (1+θ)a² + (1+θ⁻¹)b²` give the energy bound. First let `n → ∞`, then `θ → 0`. `C6` applies `LocalSlope.le_relaxation_of_lowerSemicontinuous` to `C5`.

The closest literature: S. Eriksson-Bique, *Density of Lipschitz functions in energy*, Calc. Var. PDE 62 (2023), Art. 60, Thm 1.1
(general metric measure space), the Euclidean argument here is a simple special case; Ambrosio–Gigli–Savaré, Rev. Mat. Iberoam. 29 (2013) §8.3 reaches the same conclusion via Hopf–Lax.

## Obligation List

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `E0a`–`E0e` | **five holes**, word by word | 60 (migration + synthesis) | low (synthesized from `A`, `C`) |
| `A1` | asymptotic Lipschitz constant of smooth test = gradient norm | 80 | low |
| `A2` | `AsymptoticLipschitz.relaxation ≤ SmoothGradient.relaxation` | 40 | low |
| `A3` | collapse | 15 | low |
| `B1` | Smooth recovery of global Lipschitz test | 250 | Medium |
| `B2`, `B3` | reduction tool (product of locally Lipschitz; zero outside the ball ⟹ global) | 80 | low |
| `B4`, `B5` | a moving point Leibniz bound | 60 | low |
| `C1` | locally measurable slope | 80 | low–medium |
| `C2` | **McShane patch** | 500 | **High** (the sole single-point criterion) |
| `C4` | Density of global Lipschitz tests | 150 | Medium |
| `C5` | all admissible tests | 150 | Medium |
| `C6` | reverse inequality | 20 | low |
| `D1` | Diagnosis (uniform radius insufficient), not obligatory | — | Not a step |

Total of approximately **1500 lines**. Recommended order: `A1`–`A3` and `B` in parallel; `C1`, `C2`, `C4`, `C5`, `C6`; finally, `E0a`–`E0e` are synthesized and migrated for registration
(`thm:smooth-gradient-relaxation-two-cheeger` becomes the 26th certificate).

## Verification

The route file passes `lake env lean -DwarningAsError=true`, 24 `#check`, 0 errors, 0 warnings, no import of WIP; log `build/audit/energy-slope-route/route-statements.log`. Verification receipt is bound to the following implementation cycle.

## Note (2026-09-19, after implementation)

`A1`–`A3`, `B1`–`B5`, and `C1`–`C6` are all proved as stated (`Energy/Euclidean/{SlopeComparison,SlopeRecovery,SlopeDensity}.lean`).
`E0a`–`E0e` are assembled and migrated into `Energy/Cheeger/Identification.lean`. Implementation corrections: the library form of `C2` also carries the uniform bound `|F − f| ≤ 2L + 2α`, needed for the `L²` convergence in `C4` (the patches do not converge pointwise); the piecewise constant is tighter by one `α` than in the route. `B4` needs an `O(r)` correction omitted from the route text, and empty compact cores must be removed (`Metric.infDist x ∅ = 0`). `D1` is not formalized. See the [implementation record](2026-09-19-energy-slope-proofs.md).
