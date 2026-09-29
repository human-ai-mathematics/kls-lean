# Klartag Frontend Recognition Literature: Poincaré Subclauses: Route Exploration

2026-09-19. On day twelve, the first eleven rounds had already commit been `2a882c8` (not pushed). This round is a **route exploration**,
**no theorem is proven**, no modification is made to any existing `.lean`; the deliverable is a route statement file containing only `#check`
`research/audits/KlartagLiteraturePoincareRouteStatements.lean` (4 obligations + 6 proven statement references, totaling 10 `#check`).
**Proposition passing type checking is not a proof.** The direct proof hole remains **0**, the certificate remains **26**, no WIP modules. Not commit, not pushed.

Start `HEAD = 2a882c89f59faaf23eb59d321a211422f5b24e3e`, leads `origin/main = f108397` by one commit;
Start verification receipt `build/verification/20260918T165957.183636Z/report.json`: 10 gates, 243 modules replayed,
26 local declarations, snapshot `4e5cb9cb5ef74a51343cbcf334a7fd5b154555a7e5777567aa62db2da729c8dd`.

## Why this node

`atlas.py ready` After the verification receipt is refreshed, there is only one node in the entire table that is neither `research`, nor `blocked`, and also does not lack Mathlib infrastructure:

```
inspect_infrastructure  thm:klartag-density-frontend-identification
blocked                 thm:logconcave-cheeger-poincare-comparison — depends on it
```


`tasks.json` denote it as `mathematics: local_argument`, `infrastructure.gaps: []`. It is the Cheeger–Buser comparison node
the only listed dependency of current `blocked`.

## Objectives and Boundaries

`thm:klartag-density-frontend-identification` There are three conclusions. Two isoperimetric conclusions `h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν` have been certified by `lem:relative-perimeter-cheeger-infimum`
(`Solutions.LemRelativePerimeterCheegerInfimum.intrinsic`, certificate number 25). **The third one is unverified**, and this is the sole reason the node lacks `\leanok`: `C_P^lit(μ)` equals the one that makes

```
Var_ν(g) ≤ C ∫_V ‖∇g‖² dν
```

The infimum of the locally Lipschitz `g ∈ L²(ν)` (and `∫_V ‖∇g‖² dν < ∞`) over a finite `C ≥ 0`,
`inf ∅ = +∞`, where `ν` is the intrinsic law on `V = (affineSupport μ).direction`.

The content is a verification of the gradient description of energy. `C_P^lit` (`def:literature-poincare-constant`) is defined using the local metric slope `|D f|` (`Energy.LocalSlope.apply`), not using `‖∇g‖`; this clause asserts that the two descriptions yield the same admissible class, the same energy, and thus the same optimal constant.

**Out of scope**: Buser half `Ψ_KLS² ≤ π C_P^lit` (`n ≥ 2` and constant π remain imported mathematics, Mathlib lacks Bakry–Émery weighted heat semigroup, lacks Lovász–Simonovits localization); dimension-free KLS.
Even if `Q0` is proven, `thm:logconcave-cheeger-poincare-comparison` **still will not** mark `\leanok`—
it merely removes the condition "depends on unauthenticated" from `blocked`.

## Key Finding: This is an assembly round, not an analysis round

Four analytical steps have been fully proven, in `Energy/LocalSlope/Gradient.lean`, and have been certified in `thm:smooth-lipschitz-constant-equivalence` (these four are listed in the `#check` certificate).

| Proven | Content |
| --- | --- |
| `apply_eq_norm_gradient` | Pointwise: the slope at a differentiable point equals `‖∇f(x)‖` |
| `apply_ae_eq_norm_gradient` | Rademacher + `ν ≪ m` ⟹ almost everywhere equality of local Lipschitz test |
| `energy_eq_lintegral_gradient` | Two extended energies are equal, containing `⊤` |
| `admissible_iff_memLp_gradient` | The class of admissible functions is exactly `LocallyLipschitz g ∧ MemLp g 2 ν ∧ MemLp (gradient g) 2 ν` |

The missing piece is to transfer these to the optimal constant: `Poincare.LocalSlope.Holds` is written using `Energy.LocalSlope.energy`,
rewritten in gradient form (`Q1`), and then taking the infimum over effective constants (`Q2`), yielding a clause for any absolutely continuous law;
`LogConcave.intrinsic_absolutelyContinuous` serves as a premise for each finite-dimensional log-concave law, namely `Q0`.

The Haar reference measure follows the established notation in `Poincare.SmoothGradient.Intrinsic.constant_eq_localSlope`:
`m` is an explicit parameter of the theorem, equipped with `[m.IsAddHaarMeasure]`, not a defined field, so **no** measure needs to be selected on the direction submodule. This avoids introducing new definitions.

## Obligation List

| Number | Content | Estimated lines | Risk |
| --- | --- | --- | --- |
| `Q1` | `Holds ν C ↔` gradient form, `ν ≪ m` | 25 | low (two previously proven lemmas rewritten) |
| `Q2` | infimums are equal, any absolutely continuous intrinsic law | 20 | low (`iInf` via bijection transport) |
| `Q0` | **Goal**: Poincaré clause of log-concave laws | 10 | Low (substitution of absolute continuity) |
| `Q3` | affine origin independence | 0–15 | low (expected from the definition of `intrinsicMeasure` directly) |

Total of approximately **55–70 rows**. Recommended order: `Q1`, `Q2`, `Q0`, `Q3`.

`Q3` is a ledger entry, not an analytical item: Blueprint's statement "these quantities do not depend on the affine origin `a`" refers to node assertions, while `Probability.intrinsicMeasure` inherently does not involve a choice of origin. The implementation must explicitly record whether it is directly given by definition or actually requires a lemma—both outcomes must be stated truthfully, without defaulting to the former.

## Risk

* **The only substantive risk is `Q1` in the `iff` direction**: `energy_eq_lintegral_gradient` and `admissible_iff_memLp_gradient` both carry the `ν ≪ m` assumption, and the quantifier of `Holds` applies to **all** admissible `f`, so the test classes on both sides must match exactly. If the three fields of `Admissible` do not fully align with the three premises of the gradient form in the `MemLp` `AEStronglyMeasurable` details, then `Q1` will be longer than the estimate.
* This path **does not** introduce any new definitions. If during implementation it is found that a new name such as `GradientHolds` must be introduced, this constitutes a deviation from this path, and the reason must be documented in the implementation record, and the `\lean{}` list in Blueprint must be synchronized ([`lake exe checkdecls` will verify]).
* After `Q0` is deployed, it must be updated: add a `\leanok` and `tasks.json` note, and update the `infrastructure.status` and `atlas.py check` evidence hashes under the Blueprint node, then rerun `research/verify.py`. Whether a new 27 certificate is added is decided by the owner—this clause pertains to an existing node and does not necessarily require a separate certificate.

## Verification

The route file passes `lake env lean -DwarningAsError=true`: **10 `#check` commands, 0 errors, 0 warnings**,
do not import WIP module (repository has no WIP). Log
`build/audit/klartag-literature-poincare-route/route-statements.log`.
Verification receipt is bound in the next implementation round.

## Note (2026-09-19, after implementation)

`Q1`, `Q2`, `Q0` all proved (`Poincare/LocalSlope/Gradient.lean`), no new definitions introduced, route point names specified,
`Q1` `iff` risk did not occur. The conclusion of `Q3` is **directly given by existing definitions**: `Probability.intrinsicMeasure`
without origin selection; furthermore, the statement of `Q0` contains no reference measure (Haar used internally in the proof).
`thm:klartag-density-frontend-identification` has been marked `\leanok`,
`thm:logconcave-cheeger-poincare-comparison` transformed from `blocked` to `inspect_infrastructure`,
but **still not** certified—Buser half unproven. See [implementation record](2026-09-19-klartag-literature-poincare-proofs.md).
