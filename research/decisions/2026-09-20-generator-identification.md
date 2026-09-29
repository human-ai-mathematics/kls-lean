# Bakry–Émery Paths: `G0`/`G1` Proven—Generator Identification on Smooth Test Functions

2026-09-20, followed by the [route review](2026-09-20-bakry-emery-route.md) on the same day, is
the first internal milestone of [complete Buser handover](2026-09-20-buser-handoff-prompt.md). This round is a **real Lean proof**,
not a route exploration; it does not prove nor claims to be complete Buser, nor does it regard `C_c^∞` as the operator core of `T̄†T̄`.
No commit, no push; all uncommitted modifications in the workspace are retained.

## Result

Three new modules, all zero `sorry`, zero custom axioms, `-DwarningAsError=true` under zero warnings.

| module / declaration | content |
| --- | --- |
| `Analysis/BakryEmery/IntegrationByParts.lean` | |
| `weightedLaplacian U f x := Δ f x - ⟪∇U x, ∇f x⟫` | diffusion generator convention of `ℒ`; `Δ` is Mathlib's `InnerProductSpace.instLaplacian` |
| `laplacian_eq_sum_fderiv_fderiv`, `inner_gradient_eq_sum_fderiv_mul_fderiv` | `Δf = Σᵢ D²f(eᵢ,eᵢ)`, `⟪∇f,∇g⟫ = Σᵢ ∂ᵢf ∂ᵢg` (`stdOrthonormalBasis`) |
| `continuous_laplacian`, `hasCompactSupport_laplacian`, `continuous_gradient`, `hasCompactSupport_gradient`, `continuous_weightedLaplacian`, `hasCompactSupport_weightedLaplacian`, `memLp_weightedLaplacian` | `ℒf` continuous, with compact support, so for any finite measure in each `L^p` |
| `integral_mul_fderiv_mul_fderiv` | one direction: `∫ w ∂ᵥf ∂ᵥg dm = -∫ (w ∂ᵥ∂ᵥf + ∂ᵥw ∂ᵥf) g dm` |
| `integral_mul_inner_gradient_eq_neg` | **Haar-weighted integration by parts**: `∫ w ⟪∇f,∇g⟫ dm = -∫ (w Δf + ⟪∇w,∇f⟫) g dm` |
| `inner_gradient_tilted_weight`, `integral_inner_gradient_tilted` | **`G0`**: `μ = m.tilted (-U)` when `∫ ⟪∇f,∇g⟫ dμ = ∫ (-ℒf) g dμ` |
| `Analysis/Semigroup/AdjointClosure.lean` | |
| `inner_eq_inner_closure_apply` | `T` closable, `⟪w,x⟫ = ⟪v,Tx⟫` holds for `x ∈ D(T)` ⟹ holds for `x ∈ D(T̄)` and `T̄x` (graph closedness implies contained in a closed set) |
| `mem_adjoint_domain_closure_of_forall`, `adjoint_closure_apply_eq_of_forall` | Derives `v ∈ D(T̄†)` and, when `D(T̄)` is dense `T̄† v = w` |
| `KLS/LogConcave/HeatSemigroup/Generator.lean` | |
| `integral_inner_gradient_eq` | Probability law form of `G0`: premise `(ν : Measure V) = m.tilted (-U)` |
| `integral_weightedLaplacian_eq_zero` | `∫ ℒf dν = 0` (`g = 1`; infinitesimal form of `integral_heatSemigroup`) |
| `memLp_neg_weightedLaplacian` | **`G1` integrability**: `-ℒf ∈ L²(ν)` |
| `toLp_mem_closedWeightedOperator_domain`, `closedWeightedOperator_toLp_eq` | `[f] ∈ D(T̄)`, `T̄[f] = [∇f]` |
| `inner_toLp_neg_weightedLaplacian_eq` | weak identity `⟪[-ℒf], x⟫ = ⟪[∇f], T̄x⟫` for all `x ∈ D(T̄)` |
| `toLp_mem_adjointComp_domain`, `adjointComp_toLp_eq` | **`G1`**: `[f] ∈ D(T̄†T̄)`, `T̄†T̄ [f] = [-ℒf]` |

Here `T̄ = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi`, `A = T̄†T̄ = adjointComp T̄`,
`P_t = exp(-tA)`; by `heatSemigroup_generator`, for `f ∈ C_c^∞`, `(P_t[f] - [f])/t → [ℒf]`,
i.e. `d/dt P_t f |_{t=0} = ℒf`, the symbols and route records are consistent.

Audit `research/audits/BakryEmeryGeneratorAudit.lean` verbatimly reiterates the route file's `G0`, `G1` as
`route_G0`, `route_G1` and each with one `exact` proof, additionally noting three consistency usages (`g = 1` zero mean, `g = f` Dirichlet form `∫ ‖∇f‖²`, `ℒ` symmetric on `C_c^∞`); **32 clauses `#print axioms` all standard, 0 `sorryAx`**.
`research/audits/BakryEmeryRouteStatements.lean` adds a new module's `#check @…`, and annotates the `G0`, `G1` sections indicating
which declarations have resolved it; its anonymous propositions are retained as signed audit, zero errors, zero warnings.

## Proof structure

`G0`: Mathlib has only one-directional `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`. Take
`F = w ∂ᵥf` (`f` compact support thus `F` compact support, `g` need not be compact support), using `HasFDerivAt.mul`, `HasFDerivAt.clm_apply`
Compute `∂ᵥF`, integrability arises entirely from "continuity × compact support". Then sum over `stdOrthonormalBasis`:
`OrthonormalBasis.sum_inner_mul_inner` To `⟪∇f,∇g⟫`,
`laplacian_eq_iteratedFDeriv_orthonormalBasis` + `iteratedFDeriv_two_apply` to `Δf`.
In the tilted case, `integral_tilted` reduces the integral to a Haar integral. The weight `w = exp(-U)/Z` has gradient `-w ∇U`; positivity of `Z` is not needed for this identity, which is linear in the weight.

`G1`: **Do not perform pointwise computations**. From `G0` we obtain `⟪[-ℒf],[g]⟫_{L²} = ⟪[∇f],[∇g]⟫_{L²}` for `g ∈ C_c^∞`;
`closure_domRestrict_eq_of_smoothCore_le` states that the restriction to smooth core has the same closure as `T̄`,
`inner_eq_inner_closure_apply` extends the identity to the entire `D(T̄)`; thus by the adjoint definition
(`LinearPMap.mem_adjoint_domain_of_exists`, `LinearPMap.adjoint_apply_eq`, the latter using
`dense_domain_closedWeightedOperator`) `[∇f] = T̄[f] ∈ D(T̄†)` and `T̄†[∇f] = [-ℒf]`,
this is exactly the domain membership and value (`adjointComp_apply`) of `adjointComp`.

The actual regularity used is weaker than that in the route file: `U ∈ C¹`, `G0` only requires `f ∈ C²`, `g ∈ C¹` (`g` does not require compact support); `G1` retains `f ∈ C_c^∞` because `smoothCore`/[`IsTest.of_contDiff_hasCompactSupport`] uses `ContDiff ℝ ∞` as an interface. The audit client reduces `ContDiff ℝ ∞` to these orders and then rephrases it word by word.

## What it means, what it does not mean

The route record keeps the four-level distinction of section 4 unchanged, **only the first level is proven**:

1. ✓ `C_c^∞` on top of `A[f] = [-ℒf]`, contains `[f] ∈ D(A)`;
2. (Existing) `C_c^∞` is the form core of a first-order closed form (`closure_domRestrict_eq_of_smoothCore_le`);
3. ✗ Not proven that `C_c^∞` is an operator core under the graph norm of `D(A)`;
4. ✗ Not proven that the closure of `-ℒ` on `C_c^∞` equals the full `A`.

The premise `(ν : Measure V) = m.tilted (-U)` is an explicit assumption, and in this round neither the log-concavity nor the convexity of `U` was used to construct it (the `N0` package still passes type checking). There is no `Γ`, no `Γ₂`, no Bochner, no any `t > 0`, regularity or gradient estimates for `P_t f`, no general approximation of the log-concave law, and no step from Buser. `thm:logconcave-cheeger-poincare-comparison`
There is still no `\leanok`; the constant `π` remains untouched, and 26 certificates with the same target hole as `KLS/Target.lean`.

## Friction record

- `HasCompactSupport.fderiv`'s `𝕜` cannot be derived from the conclusion, must write `hfc.fderiv (𝕜 := ℝ)`;
  `HasCompactSupport.fderiv_apply`'s `𝕜` is an explicit parameter: `hfc.fderiv_apply ℝ v`.
- `ContDiff ℝ ∞ f → ContDiff ℝ 2 f`: `mod_cast le_top` failure (target is `2 ≤ ↑⊤`),
  Use `hf.of_le (WithTop.coe_le_coe.mpr le_top)`.
- `ContinuousLinearMap.add_apply`/`smul_apply`/`zero_apply`/`neg_apply` are deprecated, use the root namespace instead
  `add_apply` etc.
- `set S := T₀.domRestrict …` afterwards `rw [LinearPMap.domRestrict_apply …]` can't find a pattern (type annotations of subtype differ),
  Change to not use `set`, explicitly write out the operator and use `erw`; `(LinearPMap.le_closure T).2` must also be provided for both `x` and `y`.
- Aggregate root `FunctionalInequalities.lean` lacked `Generated/Markov`, `HeatSemigroup/Markov`,
  `CanonicalEnergy`, `BakryEmery/Basic` (both are uncommitted modules), this round together with three new modules is added.

## Verification

By default `lake build` **3548 jobs** proceed through (the aggregate root containing the above seven modules).
`BakryEmeryGeneratorAudit.lean` and `BakryEmeryRouteStatements.lean` have zero errors and zero warnings under `-DwarningAsError=true`;
**32 axiom reports list only standard axioms, 0 `sorryAx`**. `check_ledger.py` 26 certificates 0 errors; `check_blueprint.py` 88 labels
0 error; `atlas.py check` 75 nodes, 26 certificates, acyclic; `research/tests` 104 unit tests passed.
The infrastructure evidence for `thm:logconcave-cheeger-poincare-comparison` in `tasks.json` now includes this round's file
sha256, the first form gap is rewritten as remaining obligations; the progress chart `BE` node is changed from pending to partial, view according to `AGENTS.md`
Regenerate canonical records from temporarily indexed ones, keeping the true index unchanged. Root `python3 research/verify.py`
In the final iteration of the rerun, its receipt is recorded in `build/audit/generator-identification/final-snapshot.json`.

## Next step

Along the route recording Section 10: Section `B0` (carré du champ product identity) and Section `B1` (the Hessian is positive semi-definite for `C²` convex functions) are purely local differential module, provable independently; the coordinate Bochner expansion of `B3` and other Hessian/mixed derivative auxiliary lemmas are stable before proceeding. The next obstacle on the semigroup side is
the representative and domain stability of Section 6: the regular representative of `t > 0` at `P_t[f]`, preservation of `D(T̄)` under `P_t`, and the interchange of time derivative and limit.
Sections 3 and 4 (operator core, closure equivalence, etc.) require separate proofs if used, and cannot be derived from the conclusions of this round.
