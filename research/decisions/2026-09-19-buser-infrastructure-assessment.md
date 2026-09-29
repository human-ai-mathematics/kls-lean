# Infrastructure assessment for the Cheeger–Buser comparison node

2026-09-19, the fourteenth round of the day. **No theorem was proved and no `.lean` file was changed.**
This round assesses the `infrastructure` of `thm:logconcave-cheeger-poincare-comparison`, changing it from
`unchecked` to `missing` and recording **5 concrete gaps** and **6 evidence items** with sha256,
against pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Direct holes remain **0**; certificates remain **26**.

Starting point: `HEAD = origin/main = 7986adfb07e35e900e80570f495ede4cafd0a672`
(pushed that day, with both CI workflows successful).

## Why this round was needed

After closing the Klartag clause, this node is the sole `inspect_infrastructure` item in `atlas.py ready`
and the last gate on the Cheeger–Buser line. Following the established rule, **do not promise `B0` in one round**.
The accurate next step is to specify the gaps so the scheduler classifies it as `develop_infrastructure`,
using the same treatment as `thm:cmh-recovery-affine-poincare-bound` (missing `W₂`) and
`prop:weighted-spectator-obstruction` (missing stochastic integration).

## What remains

**Only the Buser half for `n ≥ 2`, with constant π.** The node's other two components already have local Lean proofs:

* Cheeger half `C_P^lit ≤ 4Ψ_KLS²`, via `KLS.LogConcave.literatureConstant_le_four_mul_inverseScale_sq`;
* Buser half in affine-support dimension `≤ 1`, with constant **12**, via `KLS.LogConcave.inverseScale_sq_le_of_finrank_le_one`.

## Five gaps (full English entries are in `tasks.json`)

1. **Generate a symmetric Markov semigroup from the Cheeger form.** Pinned Mathlib has **no** strongly continuous
   one-parameter semigroup theory: no `C0Semigroup`/`OneParameterSemigroup` type, Hille–Yosida or Lumer–Phillips generation theorem,
   or spectral/Borel functional calculus for unbounded self-adjoint operators.
   The **module header itself** of `Analysis/InnerProductSpace/Spectrum.lean` assumes a compact operator or finite-dimensional space.
   `ContinuousFunctionalCalculus/` only covers bounded C\*-algebra elements, and operator `exp` exists only for bounded Banach-algebra elements.
   `LinearPMap.lean` supplies adjoints and closedness for unbounded densely defined operators.
   **The repository already has the form side**: `Energy.Cheeger.energy` and the densely defined closable weighted gradient in
   `KLS/LogConcave/WeightedGradient.lean` (`weightedOperator_isClosable`, `dense_domain_weightedOperator`).
   The missing step is passing from the closed form to `P_t = e^{-tL}`.
2. **Dirichlet forms and Markov semigroup theory.** Dirichlet forms in the functional-analytic sense are absent,
   as is Markovianity (sub-Markov contraction on `L¹`/`L^∞`, positivity preservation, mass preservation).
   Mathlib's `Dirichlet` results concern Dirichlet characters and L-functions; its `Markov` results concern
   `MarkovCategory`, Chebyshev–Markov inequalities, and Riesz–Markov–Kakutani.
   Without Markovianity, the pointwise bounds in Ledoux's argument are unavailable.
3. **Bakry–Émery Γ calculus.** No carré du champ `Γ`, `Γ₂`, or `CD(K, ∞)`,
   and in particular no gradient commutation estimate `‖∇P_t f‖ ≤ e^{-Kt} P_t‖∇f‖`.
   This is the analytic input for Ledoux's proof and De Ponti–Mondino's constant π, and is also absent from this repository.
4. **Small-time heat-semigroup estimates.** No heat kernel or heat semigroup on weighted Euclidean spaces;
   consequently, neither inequality combined in Ledoux's proof is available:
   `‖P_t f − f‖₁ ≲ √t · TV(f)` and `‖∇P_t f‖_∞ ≲ t^{-1/2}‖f‖_∞`.
5. **Alternative route (b): Lovász–Simonovits localization.** No needle decomposition/bisection or Prékopa–Leindler,
   and no Brunn–Minkowski in pinned Mathlib (the repository only has its own one-dimensional
   `Probability/Line/BrunnMinkowski.lean`). The transfer lemma from the one-dimensional conclusion to the ambient
   isoperimetric constant is also absent, so the proved stage-one bound `Ψ_KLS² ≤ 12 C_P^lit`
   in dimension ≤ 1 **cannot** be lifted to `n ≥ 2` by localization either.

## Evidence

Six items, each with sha256: two Mathlib files (`Spectrum.lean`, `LinearPMap.lean`) supporting the restricted
spectral-theory scope and the unbounded-operator adjoint interface; three repository modules
(`Energy/Cheeger.lean`, `KLS/LogConcave/WeightedGradient.lean`, `KLS/LogConcave/Line/Buser.lean`)
supporting the existing form theory and proved stage one; and one Blueprint chapter.

## Effect and boundary

In `atlas.py ready`, the node moves from `inspect_infrastructure` to **`develop_infrastructure`**, with each gap visible.
This is **not** a regression in proof progress: “not assessed” becomes “assessed and genuinely missing”.
The node still has no `\leanok`; `cor:tight-window-consumption` remains `blocked`.
**This round does not schedule `B0`.**

The estimates for the two routes, from the [route record](2026-09-19-buser-route.md), are unchanged:
both require thousands of lines and Mathlib-level prerequisites. The smallest reasonable next step is gap 1,
generation of a one-parameter contraction semigroup. It is a prerequisite for gaps 2, 3, and 4,
and is general theory that could be contributed to Mathlib independently of KLS.

## Validation

`check_ledger.py`: 26 nodes, 0 errors; `check_blueprint.py`: 88 labels, 0 errors;
`atlas.py check`: 75 nodes, 26 certificates, acyclic; all 104 `research/tests` pass.
No `.lean` file changed, so `lake build` and `checkdecls` retain the preceding round's results.
The receipt is bound by rerunning `research/verify.py` at the end of this round.
