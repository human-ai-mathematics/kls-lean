# Next prompt: Bakry–Émery B stage——Γ, convex Hessian, and local Bochner identity

Continue the Bakry–Émery route at `/Users/lyuyuwei/Documents/ChatGPT/KLS`. The current goal is to actually complete B0–B4 in `research/audits/BakryEmeryRouteStatements.lean`, i.e., the local Γ/Γ₂ and Bochner calculations for smooth convex potentials on finite-dimensional Euclidean spaces.

This round does not address semigroup regularity, gradient commutation, general log-concave measure approximation, small-time BV estimates, or final Buser assembly; it is not permissible to mark π comparison or the complete Bakry–Émery pathway as proved merely because local Bochner has been completed.

## 1. First verify the current baseline

First read:

- `AGENTS.md`
- `HANDOFF.md` top `Current operational status (2026-09-20)`
- `research/decisions/2026-09-20-bakry-emery-route.md`
- `research/decisions/2026-09-20-generator-identification.md`
- `research/audits/BakryEmeryRouteStatements.lean`
- `research/audits/BakryEmeryGeneratorAudit.lean`

Focus check existing modules:

- `formalization/FunctionalInequalities/Analysis/BakryEmery/Basic.lean`
- `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts.lean`
- `formalization/FunctionalInequalities/Analysis/Semigroup/AdjointClosure.lean`
- `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Generator.lean`

Currently proven, do not repeat implementation:

- `weightedLaplacian U f = Δf - ⟪∇U,∇f⟫`
- G0: Weighted integration by parts
- G1: For `f ∈ C_c∞`, `[f] ∈ D(T̄†T̄)` and
  `T̄†T̄[f] = [-weightedLaplacian U f]`
- B2: `bilinearIteratedFDerivTwo_symm`
- Bridge between the closed gradient energy of `B = I` and canonical energy, and `2 Ch`'s generator
- Semigroup generation and current `L²` Markov property

Here the diffusion generator is always

```text
ℒf = weightedLaplacian U f = Δf - ⟪∇U,∇f⟫,
```

A non-negative operator is `A = T̄†T̄ = -ℒ` (only on already-recognized smooth test functions for this equivalence).
Maintain symbol consistency and do not mix `A` and `ℒ`.

First check the current dirty worktree, retain all existing modifications; do not reset, clean, overwrite, or delete others' work.
This round does not commit, does not push.

## 2. This round's precise objective

Suggest adding:

- `formalization/FunctionalInequalities/Analysis/BakryEmery/Gamma.lean`
- `formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner.lean`
- `research/audits/BakryEmeryBochnerAudit.lean`
- `research/decisions/2026-09-20-bochner-identification.md`

And add the new module to the necessary aggregate imports. Do not create a new set of Laplacian, gradient, or Hessian definitions for convenience; directly reuse the current `weightedLaplacian`, `gradient`, `bilinearIteratedFDerivTwo`, and `stdOrthonormalBasis`.

### B0: Product identity of Γ

Define the local carré du champ, recommend using its geometric expression:

```lean
def gamma (f g : E → ℝ) (x : E) : ℝ :=
  inner ℝ (gradient f x) (gradient g x)
```

Prove the exact statement of B0 in `BakryEmeryRouteStatements.lean`:

```text
(ℒ(fg) - f ℒg - g ℒf) / 2 = ⟪∇f,∇g⟫.
```

Requirements:

- The current candidate range for `U f g ∈ C²` must be instantiable directly;
- Do not add assumptions of compact support, integrability, convexity, positive dimension, or non-empty base;
- Explicitly verify normalization by dividing out `2`, and ensure no factor `2` bias remains;
- It is permissible to first prove reusable lemmas such as the gradient product rule and Laplacian product rule;
- If an algebraic Γ is defined separately, it must be proven equal to the above `gamma`; equivalence cannot be directly inserted into the definition.

### B1: Convexity Implies Hessian Positive Semi-Definite

Proof of exact candidate:

```lean
ContDiff ℝ 2 U →
ConvexOn ℝ Set.univ U →
∀ x v, 0 ≤ bilinearIteratedFDerivTwo ℝ U x v v
```

First search pinned Mathlib for existing theorems on "second-order differentiable convex functions with positive semidefinite Hessian". If none exists,
recommend the following route:

1. Fix `x v`, and restrict to the line `t ↦ U (x + t • v)`;
2. From `ConvexOn ℝ Set.univ U` obtain the convexity of a univariate function;
3. By the monotonicity of the derivative or non-negativity of the second derivative of a univariate convex function, obtain the conclusion;
4. Precisely connect the second derivative of this univariate function to
   `bilinearIteratedFDerivTwo ℝ U x v v`.

Do not assume the Hessian is non-negative as a new hypothesis, nor prove only along the coordinate axis directions.

### B2: Reuse Existing Hessian Symmetry

Do not reprove another version. Use directly:

```lean
Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm
```

Use it to precisely close route B2 in the new audit.

### B3: Bochner's identity under a fixed standard orthonormal basis

Proof of the exact candidate B3 in `BakryEmeryRouteStatements.lean`:

```text
ℒ(‖∇f‖²)/2 - ⟪∇f, ∇(ℒf)⟫
  =
Σᵢ Σⱼ (D²f(eᵢ,eⱼ))²
  + D²U(∇f,∇f).
```

Among them:

- `eᵢ = stdOrthonormalBasis ℝ E i`;
- Retain the `ContDiff ℝ 3 U`, `ContDiff ℝ 3 f` interfaces among candidates;
- Do not add assumptions on compact support, integration, probability measure, convexity, or positive dimension;
- The theorem must cover zero-dimensional spaces, naturally degenerating when the finite sum is empty;
- Correctly use B2 to handle the exchange of mixed derivatives;
- The third-order derivative terms must genuinely cancel out, not circumvented by strengthening the conclusion or hiding assumptions;
- The sign of the drift term must ultimately yield `+ D²U(∇f,∇f)`.

Suggest splitting the proof into auditable local lemmas, for example:

- relationship between gradient/directional derivative and Hessian;
- coordinate expression of `gradient (fun y ↦ ‖gradient f y‖²)`;
- expansion of `Laplacian.laplacian (fun y ↦ ‖gradient f y‖²)`;
- expansion of `gradient (Laplacian.laplacian f)`;
- expansion of `gradient (fun y ↦ ⟪gradient U y, gradient f y⟫)`;
- exchange and cancellation of third-order derivatives;
- organization of remaining squared terms and potential Hessian terms.

We can define:

```lean
def hessianSqStdBasis (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, ∑ j,
    (bilinearIteratedFDerivTwo ℝ f x
      (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E j)) ^ 2
```

But before proving basis independence, it must not be publicly described as already constructed invariant Hilbert–Schmidt norm. If, by the way, we can prove that the sum is the same in any orthogonal basis, we may introduce an invariant notation; otherwise, clearly retain the name and restrictions `StdBasis`.

### Γ₂ definition

Recommended definition:

```lean
def gammaTwo (U f : E → ℝ) (x : E) : ℝ :=
  weightedLaplacian U (fun y => gamma f f y) x / 2 -
    gamma f (weightedLaplacian U f) x
```

Then it is shown to equal the left end of B3 and the right end of the above coordinates.

Do not arbitrarily increase regularity for the sake of using B0 to `C⁴`. Here
`gamma f (weightedLaplacian U f)` can be directly interpreted according to the geometric definition of gradient;
prove the required differentiability under the `C³` assumption in B3.

### B4: Convex potential under Γ₂ non-negative

By B3, B1, and the non-negativity of the sum of squares, we obtain the exact candidate:

```lean
ContDiff ℝ 3 U →
ConvexOn ℝ Set.univ U →
ContDiff ℝ 3 f →
∀ x, 0 ≤ gammaTwo U f x
```

Also provides a theorem that directly closes the "expanded form" B4 in the route file.

Do not treat `Γ₂ ≥ 0` as an assumption, nor derive conclusions by including it in structure fields.

## 3. Clear non-target and interface boundaries

This round completes the differential identities for pointwise, finite-dimensional, smooth functions. It must not be claimed that we have already obtained:

- `‖∇P_t f‖² ≤ P_t(‖∇f‖²)`;
- `‖∇P_t f‖ ≤ P_t(‖∇f‖)`;
- smooth representatives of `P_t f`;
- `D(A)` or the closed gradient domain is stable under the semigroup;
- interchange of time derivative, integration, and limit;
- general non-smooth log-concave laws, results with boundary or low-dimensional support;
- `C_c∞` is the operator core of `A`;
- complete Buser or constant π.

Especially do not directly call classic `gradient` for any `L²`. Semigroup connections are left for the subsequent S stage.

## 4. Audit requirements

Add `research/audits/BakryEmeryBochnerAudit.lean`, at least containing:

- `route_B0`
- `route_B1`
- `route_B2`
- `route_B3`
- `route_B4`

These statements must literally cover the candidate ranges in `research/audits/BakryEmeryRouteStatements.lean`, not weaker alternatives. Each route theorem should be directly proved from actual library declarations.

The audit should also include a few boundary checks:

- `U = 0` degenerates into the Euclidean Bochner identity;
- Affine `f` implies the Hessian square term vanishes;
- No additional assumptions are needed in zero-dimensional spaces;
- The non-negativity of B4 has no sign reversal.

Run `#print axioms` for all newly added public definitions and theorems. Dependencies allowed are limited to Mathlib's common foundational axioms, and the following are not permitted:

- `sorryAx`
- new `axiom`
- `admit`
- placeholder proof
- Hide the conclusion to be proven inside assumptions, structural fields, or typeclass
- "Prove" a weaker statement by changing the range of route candidates

Synchronize the existing-interface `BakryEmeryRouteStatements.lean` and B0–B4 annotations with `#check`,
But retain the original candidate proposition as precise signature audit.

## 5. Decision record

Add `research/decisions/2026-09-20-bochner-identification.md`, record:

- Final public statements of B0–B4;
- Actual Mathlib differential API used;
- Notation and factor normalization of Γ, Γ₂;
- How third-order derivatives cancel in B3;
- Boundary between fixed standard orthonormal basis and basis-independent Hilbert–Schmidt expressions;
- Zero-dimensional case;
- Axiom certification and reproduction commands;
- Missing semi-group regularity, domain stability, time differentiation, and limit exchange in the next stage.

Provide a three-column table:

| Proved | Type-checked only | Still an informal plan |
| --- | --- | --- |
| G0, G1, B2, E0, and the current round's completed B0, B1, B3, B4 | Not yet proven but precisely written subsequent interfaces | S0, square Γ estimate, `L¹` gradient exchange, general measure approximation and Buser tiling |

After completion, B0–B4 can be placed in "Existing Proofs"; S0, square Γ estimate, `L¹` gradient exchange, general measure approximation, and Buser tiling must remain in the last two columns or the non-formalized column.

Do not label `thm:logconcave-cheeger-poincare-comparison`, Buser nodes, or the entire Bakry–Émery infrastructure as proved. If synchronizing progress documentation, must adhere to `AGENTS.md`:
Run `python3 research/progress/update.py` from the cached canonical records, retaining other uncommit modified entries.

## 6. Acceptance command

Run from `formalization/`:

```bash
lake env lean -DwarningAsError=true \
  FunctionalInequalities/Analysis/BakryEmery/Gamma.lean

lake env lean -DwarningAsError=true \
  FunctionalInequalities/Analysis/BakryEmery/Bochner.lean

lake env lean -DwarningAsError=true \
  ../research/audits/BakryEmeryBochnerAudit.lean

lake env lean -DwarningAsError=true \
  ../research/audits/BakryEmeryRouteStatements.lean
```

And run:

```bash
lake build
```

Run from repository root:

```bash
git diff --check
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests
python3 research/verify.py
```

A strict new file compilation should have zero errors and zero warnings. Complete `lake build`
`KLS/Target.lean`'s existing target hole warnings may be retained, but no new `sorry` or warnings may be added.

## 7. Final Report

Final explanation in Medium:

1. Statements B0–B4 are completed by which declarations;
2. Does the symbol and factor in Bochner's formula agree with the diffusion generator convention `1/2`?;
3. Is the Hessian square currently expressed in a fixed standard basis, or has basis independence been proven;
4. Axiom audit and all verification results;
5. The remaining actual semi-group interface gaps;
6. Recommended next minimal proof task.

Do not commit, do not push.
