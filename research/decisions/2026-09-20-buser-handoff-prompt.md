# Next prompt: Complete the Buser comparison for log-concave laws in any dimension

2026-09-20, owner adjusts priority: **first complete the full Buser, then advance the KLS path dependent on it**.
This replaces the scope of the prior-day task to probe the Bakry–Émery path; the current proof status is unchanged.

---

Continue the Lean proof at `/Users/lyuyuwei/Documents/ChatGPT/KLS`, with the main goal being to complete the missing Buser half in Blueprint node `thm:logconcave-cheeger-poincare-comparison`.

**For any log-concave probability measure μ on an arbitrary finite-dimensional Euclidean space, prove**

`Ψ_KLS(μ)² ≤ π C_P^lit(μ)`.

Take the exact statements of B0 in `research/audits/BuserRouteStatements.lean` and the existing Blueprint as authoritative.
Must preserve the constant π, arbitrary dimension, non-smooth potentials, boundaries, or dimension-reduced support, Dirac/zero-dimensional cases, and extended non-negative real number conventions.
No use of one-dimensional constant 12, theorems valid only for smooth strictly convex densities, or conditional theorems with unresolved analytical assumptions.

## Existing Results and Entry Points

First read the current state segment and workspace changes of `AGENTS.md` and `HANDOFF.md`. Protect existing uncommit files, and do not re-apply already completed semigroup generation or Markov property.

- Cheeger half `C_P^lit ≤ 4 Ψ²` has been proven: `KLS/Geometry/Cheeger/Inequality.lean`.
- Upper bound of affine support dimension one's Buser constant 12 has been proven: `KLS/LogConcave/Line/Buser.lean`.
- Cheeger infimum equivalence has been proven: `KLS/Geometry/Cheeger/{Infimum,Equality}.lean`.
- Literature Poincaré gradient characterization has been proven: `Poincare/LocalSlope/Gradient.lean`.
- Generators S1–S8, `-T*T`, and specific heat semigroup have been proven: `Analysis/Semigroup/Generated/`, `KLS/LogConcave/HeatSemigroup/Basic.lean`.
- Positivity, constancy preservation, sub-Markov, integral preservation, absolute value control, and finite essential bound contraction on `L²` have been proven: `Analysis/Semigroup/Generated/Markov.lean`, `KLS/LogConcave/HeatSemigroup/Markov.lean`.

All modules are located under `formalization/FunctionalInequalities/`. An existing audit entry is `research/audits/{HeatSemigroupAudit,HeatSemigroupMarkovAudit}.lean`.
Complete parameters and assumptions are current as per `#check @...`. The full-dimensional theorem can be used for intrinsic law; the existing `L²` result does not automatically equal the one that has constructed the full `L¹` semigroup.

## Implementation approach: internal decomposition, final delivery of complete Buser

First verify the original literature and existing API, write down precise dependencies and normalization, then proceed directly with the proof.
Route records and candidate statements are intermediate products and cannot serve as completion criteria for this task.
Adopt a route with literature support and capable of connecting to the existing API; the following is a suggested semigroup route, which does not require mechanical replication:

1. **Generators, Bochner, and gradient estimates.** In smooth convex potential `V`,
   On the intermediate class of `dμ = Z⁻¹ exp(-V) dx`, `0 < Z < ∞`, `B = I`,
   Verify the domains and symbols of `A = T*T ≥ 0` and `ℒ = Δ - ⟨∇V,∇·⟩ = -A`.
   Prove membership and action consistency for test functions with exactness, handling the required core/closure interface.
   Construct Γ, Γ₂ using the convention of the diffusion generator ℒ, and prove
   `Γ₂(f) = ‖Hess f‖_HS² + Hess V(∇f,∇f) ≥ 0`.
   Continue to complete the domain stability, regularity, differential, and limit interfaces leading to existing `P_t`, obtaining the gradient estimates required by the literature.
   Local Bochner calculations are not semigroup estimates; `L²` representatives from equivalence classes cannot be selected to compute classical gradients without a regularity proof.
2. **General log-concave law.** The approximation or other extension mechanism employed proves appropriate convergence of closed forms, resolvent, or semigroups,
   And the stability of the inequalities and constants used. The support boundary, nonsmooth potentials, dimension reduction, and zero-dimensional cases must be implemented.
   Do not assume Neumann boundary conditions or RCD identity holds, nor hide the validity of approximation in the final theorem assumptions.
3. **Small time estimate.** The proof of Buser's argument actually requires the L¹ approximation bound and gradient smoothing bound for the heat semigroup,
   Handle indicator function/BV tests, the required L¹ interface, and the relationship among metric BV, Minkowski, and relative perimeter.
   Implement only the interfaces needed for the endpoint, avoiding unnecessary generalization of theoretical frameworks.
4. **Assembling π comparison.** Align the spectral gap, Poincaré optimal constant, `‖Tf‖²`, `E^can = 2 Ch`, and time normalization precisely,
   Complete time parameter optimization and handling of degenerate cases, eliminate all intermediate analytical assumptions, and provide a local Lean proof for B0.
   Together with the existing Cheeger semi-combination, complete the full comparison node.

Verify the normalization by De Ponti–Mondino <https://arxiv.org/abs/1902.03835> and Klartag in the Blueprint bibliography; record specific versions, theorem numbers, assumptions, and constants.
Do not omit the formalization bridge based on abstracts or "standard arguments." The technical checks in `research/decisions/2026-09-20-bakry-emery-handoff-prompt.md` can be referenced,
but the scope limitations of "only probing," "no modification of Lean," and "this round does not complete Buser" have been superseded by this prompt.

## Completion Criteria

- Add proof of zero `sorry`, zero custom placeholder axioms, no hidden cyclic dependencies, target assumptions, or scope weakening.
  Retain existing public signatures and mathematical boundaries, conform to current directory and naming conventions.
- Independently audit the client by verbatim restatement and proof of original B0, verify all quantifiers, constants, infinite values, and degenerate cases.
  Key public declarations and final comparisons `#print axioms` contain only standard axioms, not relying on `sorryAx`.
- Affected modules and the audit client pass under `-DwarningAsError=true`; run `lake build`,
  ledger/Blueprint/atlas checks and `python3 research/verify.py`, bind the final workspace snapshot.
  Existing `KLS/Target.lean` isolated KLS target holes are outside the scope of this task and must not be imported into the proof chain.
- Only after complete original comparison is proven and verified, update Blueprint completion mark and corresponding certificate records;
  update task evidence, current summary, and progress view, generated according to `AGENTS.md` from cached canonical records.
  Intermediate auxiliary results may be truthfully recorded, but the full Buser must not be prematurely marked as completed.
- Do not upgrade Lean/Mathlib, do not commit, do not push. Continuously complete internal subtasks without re-requesting permission at each stage.

Completing Buser does not equal proving KLS. If encountering truly insurmountable mathematical or API barriers, honestly report the exact proven statements, unproven obligations, failed paths, and minimal gaps; do not consider degraded results as completion, nor prematurely terminate the implementation simply because the roadmap has been written or individual auxiliary lemmas have been completed.
