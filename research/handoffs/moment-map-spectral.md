# Moment-map spectral route: collaborator handoff

**Prepared:** 2026-09-27

**Intended owner:** senior collaborator

**Scope:** the `moment-map-spectral-full-damping` branch toward dimension-free KLS.

This is a research and formalization workstream. The route has a precise conditional
endpoint, but its universal-time estimate is open. Ownership of the branch includes
checking the mathematics of that estimate, developing the required stochastic
localization interface, and formalizing valid results. It does not presume that the
open estimate follows from the cited literature.

## Start here

1. Read the [local route statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex)
   (`q:mm-spectral-occupation` and `prop:spectral-sufficiency`) and the
   [route-composition record](../../formalization/blueprint/route-composition.yaml)
   (`moment-map-spectral-full-damping`). They are the current KLS-facing contract.
2. Read the pinned [upstream spectral manuscript](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/modules/kls/30-spectral-route.tex),
   its [conditional sufficiency proof](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/solutions/prop-spectral-sufficiency.tex),
   and the [research portfolio](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/research/program/portfolio.yaml).
   The pinned revision is `34b5fcd57fef17089e781616005fe6d3641bd11e`.
   The [local evidence snapshot](../upstream/2026-09-12-kls-research.json) preserves
   selected ledger records, assumptions, and review paths. Recheck the upstream
   source and proof dossier before relying on any natural-language proof.
3. Read the [research synchronization record](../decisions/2026-09-12-upstream-research-sync.md)
   for the short-window work and the [target-interface decision](../decisions/2026-09-19-kls-target-theorem.md)
   for the reasons no Lean statement of the open gate exists yet.

## Exact target and current evidence

On smooth strongly log-concave isotropic approximants, fix a normalized first
eigenfunction and use the upstream definitions of its localization quantities
`g_t`, `H_t`, and posterior covariance `A_t`. The open question asks for universal
`T₀, C₀, C₁ > 0`, independent of dimension and regularization, such that every
`0 < t ≤ T₀` satisfies

```text
E ∫₀ᵗ ‖Hₛ‖²_HS ds
  ≤ C₀ t + C₁ E ∫₀ᵗ |gₛ|² ds + E ∫₀ᵗ 2 gₛᵀ Aₛ gₛ ds.
```

Preserve the *full* damping term, its coefficient and sign, the fixed initial
eigenfunction, the quantifier order, and uniformity through approximation and
unwhitening. Check measurability, integrability, and any limiting step rather
than treating them as implicit. The exact definitions and normalization belong
to the pinned manuscript; this display alone is not a Lean specification.

The upstream `prop:spectral-sufficiency` is an agent-reviewed **conditional**
argument: assuming that occupation estimate, Itô's formula, Gronwall, and
posterior variance conservation give a dimension-free Poincaré bound, hence
KLS after the certified affine/isotropic adapter. The open premise remains
explicit. Neither node has a local Lean proof or certificate.

The constants in the local conditional statement are
`M_* = (1 + C₀ T₀) exp(C₁ T₀)` and `T_* = min(T₀, 1/(2M_*))`, with the claimed
bound `C_P^lit ≤ 2/T_*`. The algebra is consistent **provided** the pinned
definitions establish the following identities and hypotheses for the fixed
normalized test: `E|g₀|² ≤ 1`; the integrated Itô identity has source
`‖Hₜ‖²_HS` and damping `−2 gₜᵀ Aₜ gₜ`; the posterior-mean martingale gives
`E Var_{μₜ}(f) = 1 − ∫₀ᵗ E|gₛ|² ds`; and the posterior strong-convexity
inequality gives `E Var_{μₜ}(f) ≤ λ/t` for first eigenvalue `λ`. Then
Gronwall gives `E|gₜ|² ≤ M_*`, so at `t = T_*` the expected posterior variance
is at least `1/2`, hence `λ ≥ T_*/2`. The stochastic identities, domains,
posterior inequality, and approximation limit are **proof obligations**, not
verified Lean facts. The pinned upstream proof dossier was not independently
replayed for this handoff.

The upstream stopped-window source and window-occupation results retain
Letwin's quadratic Poincaré inequality as an assumption. Their time window
depends on dimension, and the resulting `C_P ≤ C log² n` is conditional. They
do not establish the universal positive `T₀` above. The route also remains
separate from the deterministic **Moment-map CMH** branch.

## Existing Lean interfaces and semantic audit

- [KLS.Conjecture](../../formalization/FunctionalInequalities/KLS/Statement.lean)
  is a `Prop`: one finite `C : NNReal` is chosen **before** every `n` and
  every compact-set log-concave probability law `μ` with `MemLp id 2`; its
  conclusion bounds the *intrinsic literature local-slope* optimum by
  `C · ‖Cov_μ‖`. It asserts no proof. The theorem `KLS.kls` in
  [Target.lean](../../formalization/FunctionalInequalities/KLS/Target.lean)
  has the project's isolated intentional `sorry`; do not import it into a
  certificate closure.
- [Affine/isotropic reduction](../../formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean)
  proves equivalence of `IsotropicBound K`, `CovarianceBound K`, and
  `AffineBound K` for each *fixed finite* `K : NNReal` over finite-dimensional
  Euclidean spaces of one universe. It does not produce a `K`. At universe
  zero, `conjecture_of_affineBound` maps an `AffineBound K` to the exact
  `KLS.Conjecture` proposition. The independent
  [reduction certificate](../../solutions/ThmAffineIsotropicReduction.lean)
  includes that implication and a zero-dimensional client.
- The [selected/literature Poincaré comparison](../../formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean)
  proves `Poincare.SmoothGradient.Intrinsic.constant μ =
  Poincare.LocalSlope.Intrinsic.constant μ` for every finite-dimensional
  compact-set log-concave probability law, including singular affine support
  and dimension zero. The [certificate](../../solutions/ThmSelectedLiteratureConstantEquivalence.lean)
  proves this equality; it is not an eigenfunction-existence theorem or a
  dimension-free inequality.
- [Probability and covariance](../../formalization/FunctionalInequalities/Probability/)
  and the [log-concave KLS family](../../formalization/FunctionalInequalities/KLS/LogConcave/)
  provide deterministic measure, covariance, and Poincaré foundations. Existing
  weighted-gradient heat semigroup results describe a different process and
  do not supply Eldan's stochastic localization, Itô calculus, or eigenfunction
  evolution.

On 2026-09-27, an independent strict Lean client checked the named reduction,
the selected/literature equality, and `IsotropicBound.{0} K → KLS.Conjecture`.
`#print axioms` for both certificates and the relevant bridge declarations
returned only `propext`, `Classical.choice`, and `Quot.sound`. The target
`KLS.kls` still returned `sorryAx`; no spectral-route declaration was proved
by that check. This audit concerns the current checkout, not a fresh build of
Mathlib or a remote CI result.

The pinned Mathlib has Brownian-motion, filtration, martingale, and stopping
modules, but the required stochastic integral/SDE and Itô framework is not
already an application-ready API here. The route additionally needs a fixed
regular-approximation scheme, a first-eigenfunction existence/normalization
interface, and precise posterior moment dynamics. Check each of these against
the source before creating public definitions.

## First deliverables

1. **Source audit.** Produce an exact map from the upstream definitions and
   equations to the local target: assumptions, first-eigenfunction choice,
   stopping/localization convention, constants, approximation, and tensor
   transformation under unwhitening. Record any unresolved or circular step
   as a named mathematical obligation.
2. **Minimal interface plan.** Following [workflow](../workflow.md) and
   [naming rules](../naming.md), identify the owner, scope, destination,
   imports, API impact, and validation for the stochastic process, its
   posterior quantities, and the spectral consumer. Reuse a generic
   probability owner only when a theorem is genuinely independent of KLS.
3. **Conditional consumer.** Once the underlying objects exist, formalize
   the implication from an explicitly assumed occupation inequality to the
   exact dimension-free target. Verify its normalization and transitive axioms.
   This is a useful milestone, not completion of the route.
4. **Open gate.** Seek a proof or a decisive obstruction for the universal-time
   estimate. Restricted model calculations and the Letwin-dependent window
   should be recorded at their actual scope. Close the branch only after the
   universal statement and its consumer are proved and verified in Lean.

For each progress update, state separately what is established in literature,
what is established only in upstream natural-language work, what is conditional,
and what is certified locally. A local commit, a verifier receipt, and remote CI
are distinct evidence. If proof status changes, stage the intended source and
metadata, then regenerate the progress views with
`python3 research/progress/update.py` as required by [AGENTS.md](../../AGENTS.md).

## Reading list by role

| Role | Source | Use and limit |
| --- | --- | --- |
| Direct route source | [Pinned upstream §30](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/34b5fcd57fef17089e781616005fe6d3641bd11e/modules/kls/30-spectral-route.tex) | Defines the research route; the universal-time gate is open. |
| Stochastic localization | [Eldan, 2013](https://arxiv.org/abs/1203.0893); [Lee–Vempala, 2024](https://annals.math.princeton.edu/2024/199-3/p02) | Foundational method and quantitative KLS work; neither proves this gate. |
| Existing dimension-dependent input | [Klartag, 2023](https://arxiv.org/abs/2303.14938) | Literature isoperimetric/spectral frontier used in the short-window analysis. |
| Explicit short-window assumption | [Letwin, 2026, v1](https://arxiv.org/abs/2607.24164v1) | Quadratic-test inequality and polylogarithmic result; retain its status and the upstream dependency. |
| Related moment-map background | [Klartag, *Moment measures I*](https://arxiv.org/abs/1309.2767); [Fathi, *Stein kernels and moment maps*](https://arxiv.org/abs/1804.04699) | Primarily relevant to the separate deterministic CMH branch; neither is a citation for the occupation estimate. |

## Completion test

The branch is complete only when the universal occupation bound has the stated
quantifiers and normalization, its approximation passage and conditional
consumer are proved in Lean without `sorryAx` or a new unproved axiom, the
exact KLS implication is checked by an independent client, and the appropriate
build, axiom, ledger, Blueprint, and progress checks pass on the same source
snapshot. Until then the progress tree must retain `○` for both branch nodes
and for dimension-free KLS.
