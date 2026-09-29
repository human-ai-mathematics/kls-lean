# Bakry–Émery Path: `B0`–`B4` Proved—Local `Γ`/`Γ₂` Computation and Bochner Identity

2026-09-20, followed by the [generator identification record](2026-09-20-generator-identification.md) on the same day, is
[Complete Buser handover](2026-09-20-buser-handoff-prompt.md)'s second internal milestone. This round is a **real Lean proof**:
`research/audits/BakryEmeryRouteStatements.lean`'s `B0`, `B1`, `B3`, `B4` are literally resolved, and `B2` reuses existing ones.
`bilinearIteratedFDerivTwo_symm`. All conclusions are pointwise differential identities for smooth functions on finite-dimensional Euclidean spaces; the following are neither proved nor claimed:
semigroup gradient estimates, approximation of general log-concave laws, or assembly of Buser. No commit or push; all other uncommitted workspace changes are preserved.

## Result

Two new modules, both zero `sorry`, zero custom axioms, `-DwarningAsError=true` under zero warnings.

| module / declaration | content |
| --- | --- |
| `Analysis/BakryEmery/Gamma.lean` | |
| `gamma f g x := ⟪∇f x, ∇g x⟫` | carré du champ, geometric definition |
| `gamma_self`, `gamma_self_fun` | `Γ(f,f) = ‖∇f‖²` (without additional factors) |
| `weightedLaplacian_mul` | `ℒ(fg) = f ℒg + g ℒf + 2 Γ(f,g)`, `f, g ∈ C²`, `U` arbitrarily |
| `gamma_eq_weightedLaplacian` | **`B0`**: `(ℒ(fg) - f ℒg - g ℒf)/2 = Γ(f,g)` |
| `gammaTwo U f x := ℒ(Γ(f,f)) x / 2 - Γ(f, ℒf) x` | `Γ₂` under the diffusion convention; `Γ(f, ℒf)` read geometrically as `⟪∇f, ∇(ℒf)⟫`, without `C⁴` |
| `gammaTwo_eq_expanded` | `Γ₂` expanded to `(Δ‖∇f‖² - ⟪∇U,∇‖∇f‖²⟫)/2 - ⟪∇f, ∇(Δf - ⟪∇U,∇f⟫)⟫`, i.e., the left end of route file `B3` |
| `contDiff_fderiv_apply`, `differentiable_fderiv_apply`, `fderiv_fderiv_apply`, `bilinearIteratedFDerivTwo_eq_fderiv_apply` | Regularity of the directional derivative `y ↦ Df(y)v`; `D²f(x)(v,w) = D(y ↦ Df(y)w)(x)v` |
| `fderiv_apply_comm` | Directional derivative form of `B2`: `∂ᵥ∂_w f = ∂_w∂ᵥ f` (`C²`) |
| `fderiv_fderiv_fderiv_apply_comm` | third-order commutative `∂_w∂ᵥ∂ᵥ f = ∂ᵥ∂ᵥ∂_w f` (`C³`) |
| `fderiv_mul_apply`, `fderiv_const_mul_apply`, `fderiv_sum_apply`, `fderiv_sub_apply`, `fderiv_add_apply` | Product rule, constant multiple, sum, and difference rule for directional derivatives |
| `contDiff_gradient`, `gradient_mul`, `gradient_sub` | Gradient regularity and product, difference rules |
| `gradient_eq_sum_fderiv_smul`, `norm_gradient_sq_eq_sum`, `bilinearIteratedFDerivTwo_gradient_gradient`, `bilinear_sum_smul_sum_smul` | `∇f = Σᵢ ∂ᵢf eᵢ`, `‖∇f‖² = Σᵢ (∂ᵢf)²`, `D²U(∇f,∇f) = Σᵢ Σⱼ ∂ᵢf ∂ⱼf D²U(eᵢ,eⱼ)` |
| `laplacian_eq_sum_fderiv_apply_fderiv_apply`, `laplacian_eq_fun_sum`, `contDiff_laplacian`, `laplacian_mul` | `Δg = Σᵢ ∂ᵢ∂ᵢ g` (pointwise and functionwise), `Δ` regularity, `Δ(fg) = fΔg + gΔf + 2⟪∇f,∇g⟫` |
| `Analysis/BakryEmery/Bochner.lean` | |
| `convexOn_line`, `hasDerivAt_line`, `deriv_line`, `deriv_deriv_line` | restriction to a line `t ↦ U(x + t v)` of convexity, first derivative `DU(x+tv)v`, second derivative at `0` equals `D²U(x)(v,v)` |
| `bilinearIteratedFDerivTwo_nonneg_of_convexOn` | **`B1`**: `C²` convex `U` ⟹ `0 ≤ D²U(x)(v,v)` |
| `hessianSqStdBasis f x := Σᵢ Σⱼ (D²f(x)(eᵢ,eⱼ))²`, `hessianSqStdBasis_nonneg` | Sum of squares of the Hessian under a fixed standard orthonormal basis |
| `fderiv_norm_gradient_sq_apply`, `inner_gradient_gradient_norm_sq`, `laplacian_norm_gradient_sq`, `inner_gradient_gradient_laplacian`, `inner_gradient_gradient_inner` | Coordinate expansion of the four terms `Γ₂` |
| `gammaTwo_eq_hessianSqStdBasis_add` | **`B3` (`Γ₂` form)**: `Γ₂(f) = hessianSqStdBasis f + D²U(∇f,∇f)`, `U ∈ C²`, `f ∈ C³` |
| `bochner_stdBasis` | **`B3` (expanded form, character-by-character candidate)**, `U, f ∈ C³` |
| `gammaTwo_nonneg`, `bochner_nonneg_stdBasis` | **`B4`**: convex `U` ⟹ `0 ≤ Γ₂(f)` (two forms) |
| `gammaTwo_zero_potential`, `bilinearIteratedFDerivTwo_affine`, `hessianSqStdBasis_affine`, `gammaTwo_affine`, `gammaTwo_of_subsingleton` | boundary case: `U = 0` degenerates to Euclidean Bochner; affine `f` has Hessian square zero, `Γ₂ = D²U(∇f,∇f)`; zero-dimensional space `Γ₂ = 0` and no regularity is required |

Audit `research/audits/BakryEmeryBochnerAudit.lean` verbatim restate route file `B0`–`B4` as `route_B0`–`route_B4` (one each `exact`),
also provide `Γ₂` form `route_B3_gammaTwo`, `route_B4_gammaTwo`, and boundary checks `boundary_euclidean` (`U = 0`), `boundary_affine`,
`boundary_zero_dim`, `boundary_affine_nonneg`, `boundary_one_dim_value`, `boundary_one_dim_hessianSq`;
**70 clause `#print axioms` all standard (`propext`, `Classical.choice`, `Quot.sound`), 0 `sorryAx`**.
`BakryEmeryRouteStatements.lean` adds new declaration `#check @…`, and paragraphs `B0`–`B4` note declaration resolution; anonymous candidate propositions retained verbatim, zero errors, zero warnings.

The regularity actually used is weaker than in the candidates: `B0` requires no regularity of `U`; the `Γ₂` forms of `B3` and `B4` require only `U ∈ C²`. The audit restates the candidates verbatim after reducing their `C²`/`C³` assumptions to these orders.

## Symbols and Normalization

- diffusion generator `ℒf = weightedLaplacian U f = Δf - ⟪∇U, ∇f⟫`; the non-negative operator of the semigroup `A = T̄†T̄` equals `-ℒ` only on smooth test functions already identified in `G1`. All statements in this round pertain only to `ℒ`, and do not involve `A`.
- `Γ(f,g) = ⟪∇f, ∇g⟫`; `B0` gives `Γ = (ℒ(fg) - fℒg - gℒf)/2`, the factor `1/2` and `Δ(fg) = fΔg + gΔf + 2⟪∇f,∇g⟫`'s `2` cancel exactly, `Γ(f,f) = ‖∇f‖²`.
- `Γ₂(f) = ℒ(Γ(f,f))/2 - Γ(f, ℒf)`. `B3` Both terms on the right-hand side `Σᵢ Σⱼ (D²f(eᵢ,eⱼ))² + D²U(∇f,∇f)` have positive signs; for convex `U` both terms are non-negative, so the direction of `B4` is `0 ≤ Γ₂`, with no sign reversal.
- Independent numerical verification (`boundary_one_dim_value`): On `ℝ`, take `U = 0` and `f(t) = t²`, **without going through `B3`**, directly compute `Γ₂(f)(0) = 8/2 - 0 = 4` using Mathlib's `laplacian_eq_iteratedDeriv_real` and `gradient_eq_deriv'`, which matches the right-hand side `(f'')² = 4` of `B3`. If the factor `1/2` is missing, we obtain `8`; if the sign is reversed, we obtain `-4`.

## Proof structure

All computations are carried out in a fixed standard orthonormal basis `eᵢ = stdOrthonormalBasis ℝ E i` using directional derivatives `∂ᵢ g := y ↦ Dg(y)eᵢ`:
`∇g = Σᵢ ∂ᵢg eᵢ`, `‖∇f‖² = Σⱼ (∂ⱼf)²`, `Δg = Σᵢ ∂ᵢ∂ᵢg`, `⟪∇U,∇f⟫ = Σᵢ ∂ᵢU ∂ᵢf`, Hessian `D²f(eᵢ,eⱼ) = ∂ᵢ∂ⱼf`
(`bilinearIteratedFDerivTwo` is defined as `fderiv (fderiv f)`, `bilinearIteratedFDerivTwo_eq_fderiv_apply` replaces it with iterated directional derivatives).
At point `x` denote `aⱼ = ∂ⱼf`, `bᵢⱼ = ∂ᵢ∂ⱼf`, `cᵢⱼ = ∂ᵢ∂ᵢ∂ⱼf`, `uᵢ = ∂ᵢU`, `wᵢⱼ = ∂ᵢ∂ⱼU`:

| item | expansion | statement |
| --- | --- | --- |
| `Δ‖∇f‖²` | `2 Σᵢ Σⱼ bᵢⱼ² + 2 Σⱼ aⱼ Σᵢ cᵢⱼ` | `laplacian_norm_gradient_sq` |
| `⟪∇U, ∇‖∇f‖²⟫` | `2 Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ` | `inner_gradient_gradient_norm_sq` |
| `⟪∇f, ∇(Δf)⟫` | `Σⱼ aⱼ Σᵢ ∂ⱼ∂ᵢ∂ᵢf = Σⱼ aⱼ Σᵢ cᵢⱼ` | `inner_gradient_gradient_laplacian` |
| `⟪∇f, ∇⟪∇U,∇f⟫⟫` | `Σⱼ aⱼ Σᵢ (uᵢ bⱼᵢ + aᵢ wⱼᵢ) = D²U(∇f,∇f) + Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ` | `inner_gradient_gradient_inner` |

Thus `Γ₂ = (2S + 2T - 2M)/2 - (T - H - M) = S + H`, where `S = Σᵢ Σⱼ bᵢⱼ²`, `T = Σⱼ aⱼ Σᵢ cᵢⱼ`, `M = Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ`, `H = D²U(∇f,∇f)`, the last step is `ring`.

**Cancellation of third derivatives.** `Δ‖∇f‖²/2` Contribution `Σⱼ aⱼ Σᵢ ∂ᵢ∂ᵢ∂ⱼf`, `⟪∇f, ∇Δf⟫` Contribution `Σⱼ aⱼ Σᵢ ∂ⱼ∂ᵢ∂ᵢf`.
`fderiv_fderiv_fderiv_apply_comm` (`f ∈ C³`) proves `∂ⱼ∂ᵢ∂ᵢf(x) = ∂ᵢ∂ᵢ∂ⱼf(x)`: first apply the directional form of `C²` to the function `g = ∂ᵢf` with `B2`
`fderiv_apply_comm` swapping two outer derivatives, `∂ⱼ∂ᵢg = ∂ᵢ∂ⱼg`; then at each point using `B2` to swap the two inner derivatives of `f`, `∂ⱼ∂ᵢf = ∂ᵢ∂ⱼf`
(function equality via `funext`), thus `∂ᵢ(∂ⱼ∂ᵢf) = ∂ᵢ(∂ᵢ∂ⱼf)`. The two terms are therefore identical word for word and cancel; neither strengthens the conclusion nor hides assumptions.

**Drift term.** `-⟪∇U,∇‖∇f‖²⟫/2 = -Σᵢ Σⱼ uᵢ aⱼ bᵢⱼ`, `+⟪∇f, ∇⟪∇U,∇f⟫⟫ = Σⱼ Σᵢ aⱼ uᵢ bⱼᵢ + Σⱼ Σᵢ aⱼ aᵢ wⱼᵢ`;
canceling the first part of `B2` (`bᵢⱼ = bⱼᵢ`) against the previous one, leaving `Σⱼ Σᵢ aⱼ aᵢ wⱼᵢ = D²U(∇f,∇f)` (`bilinearIteratedFDerivTwo_gradient_gradient`),
sign is `+`.

**`B1`.** Fix `x v`, `φ(t) = U(x + t v)`. `convexOn_line` is directly obtained from the definition of `ConvexOn` and yields `φ` to be convex on `ℝ` (without using `comp_affineMap`, since instance conversion under `convert` produces irrelevant instance goals);
`ConvexOn.monotoneOn_deriv` establishes `φ'` is monotone, `Monotone.deriv_nonneg` establishes `φ''(0) ≥ 0`;
`deriv_deriv_line` is proved using `HasFDerivAt.comp_hasDerivAt` and `HasDerivAt.clm_apply` to establish `φ''(0) = D²U(x)(v,v)`.
The pinned Mathlib does not have an existing theorem stating "Hessian of `C²` convex function is positive semi-definite", so the proof proceeds along this route; the conclusion holds for all directions `v`, not just coordinate directions.

## Practical Mathlib Differential API

`bilinearIteratedFDerivTwo` (`Mathlib.Analysis.InnerProductSpace.Laplacian`, defined as `(fderiv (fderiv f) x).toLinearMap₁₂`) ,
`laplacian_eq_iteratedFDeriv_orthonormalBasis` (by existing `laplacian_eq_sum_fderiv_fderiv`), `laplacian_eq_iteratedDeriv_real` (one-dimensional kernel check only),
`fderiv_fun_mul`, `fderiv_const_mul`, `fderiv_fun_sum`, `fderiv_fun_add`, `fderiv_fun_sub`, `fderiv_fun_const`,
`HasFDerivAt.clm_apply`, `ContDiff.fderiv_right`, `ContDiff.clm_apply`, `ContDiff.sum`, `ContDiff.mul`, `ContDiff.norm_sq`, `ContDiff.inner`,
`inner_gradient_left`, `gradient_fun_const`, `gradient_eq_deriv'`, `OrthonormalBasis.sum_repr'`, `OrthonormalBasis.sum_sq_inner_left`,
`ConvexOn.monotoneOn_deriv`, `Monotone.deriv_nonneg`, `HasFDerivAt.comp_hasDerivAt`, `HasDerivAt.clm_apply`, `monotoneOn_univ`,
and the existing repository has `bilinearIteratedFDerivTwo_symm` (`B2`), `inner_gradient_eq_sum_fderiv_mul_fderiv`, `laplacian_eq_sum_fderiv_fderiv`.

## Boundary: Fixed basis and invariant Hilbert–Schmidt norm

The basis in `hessianSqStdBasis f x = Σᵢ Σⱼ (D²f(x)(eᵢ,eⱼ))²` is `stdOrthonormalBasis ℝ E`. **This round does not prove that the double sum is independent of the choice of an orthogonal basis**,
thus no introduction of invariant notation such as `‖Hess f‖²_HS` is made, and the public name retains `StdBasis`; the public statement of `B3` also follows the fixed standard basis as specified in the route document.
Basis independence (or alternatively using `Hess f` as the Hilbert–Schmidt norm of `E →L E`) is an independent obligation.

## Zero-dimensional case

When `E` is `Subsingleton`, `Fin (finrank ℝ E)` is empty and both double sums are empty; `gammaTwo_of_subsingleton` proves `Γ₂ = 0` for arbitrary `U f`, without regularity assumptions
(Any function is constant). The general proof of `B3` and `B4` does not require positive dimension or non-empty basis.

## What it means, what it does not mean

Proved: pointwise identities for smooth functions on finite-dimensional Euclidean spaces `B0`–`B4`. Unproven and not claimed:

- `‖∇P_t f‖² ≤ P_t(‖∇f‖²)` or `‖∇P_t f‖ ≤ P_t(‖∇f‖)` (two candidates for `S0`);
- smooth representatives of `t > 0` under `P_t[f]`; `D(A)` or closed gradient domain is stable under `P_t`;
- interchange of derivative, integration, and limit with respect to `s ↦ P_s Γ(P_{t-s}f)`;
- general (non-smooth, with boundary, low-dimensional support) log-concave law; `C_c^∞` is the operator core of `A`;
- Buser inequality or constant `π`.

`thm:logconcave-cheeger-poincare-comparison` still has no `\leanok`, 26 certificates and `KLS/Target.lean`'s target hole unchanged.

## State Three-Column

| Proved | Type-checked only | Still an informal plan |
| --- | --- | --- |
| `G0`, `G1`, `B2`, `E0`; this round `B0`, `B1`, `B3` (fixed standard basis), `B4` | `N0` smooth tilted probability model package | `hessianSqStdBasis`'s basis independence |
| Semigroup generation, `L²` Markov property, closed gradient energy `= E^can = 2 Ch` | `S0`: `P_t f` smooth representative; square `Γ` estimation and `L¹` gradient exchange as two candidates | Semigroup regularity, domain stability, time derivative, self-improvement, BGL reverse estimation |
| Cheeger half and one-dimensional constant 12 | — | General measure approximation (Mosco/resolvent/semigroup/BV stability) and Buser argument |

## Friction record

- The second argument of `ContDiff.differentiable` is `n ≠ 0`, not `≤`; write `one_ne_zero`.
- `ContDiff.norm_sq`, `ContDiff.inner`'s domain `𝕜` needs to be explicitly: `hg.norm_sq (𝕜 := ℝ)`, `hgU.inner ℝ hgf`; and needs `import Mathlib.Analysis.InnerProductSpace.Calculus`; `ConvexOn.monotoneOn_deriv` needs `import Mathlib.Analysis.Convex.Deriv`.
- `contDiff_of_subsingleton` requires the range to be trivial; rewrite `f = fun _ => f x` for the domain being trivial case and then use `contDiff_const`.
- On `Fin (finrank ℝ E)`, `rw [finrank_zero_of_subsingleton]` produces a motive error; use `omega` to handle `↑i < finrank ∧ finrank = 0` instead.
- Without an expected type, `DifferentiableAt.mul` produces `f * fun y => …` rather than `fun y => f y * …`, so `rw` cannot find the pattern; use a type-annotated `have`.
- `simp only [map_sum, …]` Will rearrange the double sum on a bilinear form, followed by `Finset.sum_comm`.
- The type of `contDiff_id.pow 2` is `fun x => id x ^ 2`; it requires prior `have hf : ContDiff ℝ 3 (fun t : ℝ => t ^ 2) := contDiff_id.pow 2`.

## Verification and Reproduction

From `formalization/`:

```bash
lake env lean -DwarningAsError=true FunctionalInequalities/Analysis/BakryEmery/Gamma.lean
lake env lean -DwarningAsError=true FunctionalInequalities/Analysis/BakryEmery/Bochner.lean
lake env lean -DwarningAsError=true ../research/audits/BakryEmeryBochnerAudit.lean
lake env lean -DwarningAsError=true ../research/audits/BakryEmeryRouteStatements.lean
lake build
```

Four files, zero errors, zero warnings; audit 70 axiom reports list only standard axioms, 0 `sorryAx`. Default `lake build` **3550 jobs** pass
(aggregation root `FunctionalInequalities.lean` added `BakryEmery/Gamma`, `BakryEmery/Bochner`), where the only `sorry` warning remains the target hole of `KLS/Target.lean`.

From the repository root:

```bash
git diff --check
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests
python3 research/verify.py
```

`check_ledger.py` 26 certificates 0 error; `check_blueprint.py` 88 labels 0 error; `atlas.py check` 75 nodes, 26 certificates, acyclic; 104 unit tests.
`tasks.json` in `thm:logconcave-cheeger-poincare-comparison` the infrastructure evidence is added to the current file's sha256 (`BakryEmeryRouteStatements.lean` hash synchronization refresh), the first gap is rewritten as remaining obligations; the progress diagram `BE` nodes remain partial, description updated, view regenerated from `AGENTS.md` canonical records temporarily stored in the temporary index, the real index unchanged. Root `python3 research/verify.py` is rerun at the end of this round, its receipt recorded in `build/audit/bochner-identification/final-snapshot.json`.

## Next step

The minimal next task on the semigroup side is the route record of section 6, item 1–2: **`t > 0` at `P_t[f]` the regular representative and `P_t` preserving `D(T̄)`**.
Before these two items, the `B4`'s `Γ₂ ≥ 0` cannot connect to `Γ(P_t f) ≤ P_t Γ(f)`: the time derivative of the interpolation quantity `s ↦ P_s Γ(P_{t-s} f)` requires `P_{t-s} f` at least `C³`
And its `Γ`, `ℒ` return to `L²`. An independently provable local fragment is the independence of the basis of `hessianSqStdBasis` (by rewriting the right-hand side of `B3` as an invariant),
But it is not the blocking element of the semigroup interface. The 3, 4 layers (operator core, closure equivalence, etc.) require separate proofs if used.
