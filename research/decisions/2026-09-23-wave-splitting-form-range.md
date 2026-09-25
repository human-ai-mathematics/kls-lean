# Finite wave splitting: class-level density of the form range

## Placement and scope

This continues the [error continuation](2026-09-23-wave-splitting-average-error.md). It
implements the first step of the route's
[passage to the two fields](2026-09-22-heat-test-wave-approximation.md#from-this-construction-to-the-requested-two-fields):
density of `J C_c^∞` in the form domain. The placement plan was recorded in `HANDOFF.md`
before editing. The work is split by dependency level:

- [Potential.lean](../../formalization/FunctionalInequalities/Analysis/WaveSplitting/Potential.lean)
  (`Analysis.WaveSplitting`). It imports AverageError, `BakryEmery.Laplacian` and Mathlib
  tilted measures, and no KLS module. It contains the potential weight, the production
  classical density theorem, the orthonormal-basis identities and the tilted normalization.
- [FormRange.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/FormRange.lean)
  (`KLS.LogConcave`). It imports Potential, `HeatSemigroup.Generator`,
  `WeightedGradient.Multiplier` and `Semigroup.Resolvent.Basic`. It contains the class-level
  bridges and the density theorem.

The library root imports both. No existing file, declaration or API changed. The baseline is
`build/audit/heat-test-splitting-form-range/baseline/`.

## Setting

`V` is a finite-dimensional real inner product space and `m` an additive Haar measure. The
law `ν` is log-concave with nonempty interior support and satisfies `ν = m.tilted (-U)`,
where `U` is `C^∞`; convexity enters only through `LogConcave ν`. Let
`T̄ = hν.closedWeightedOperator m (id) hi` be the closed unit-weight gradient, `A = T̄†T̄`
(`adjointComp`) and `J = I + A`. `E = D(T̄)` carries the graph norm
`‖x‖_E = √(‖x‖² + ‖T̄x‖²)` in `L²(ν) × L²(ν; V)`. That is the norm of `graphL2 T̄`, not the
`L²(ν)` subspace topology.

## Formalized in Lean

**Pointwise identities** (orthonormal basis `e`, any finite index type):

- `sum_fderiv_sq_eq_norm_gradient_sq`: `Σ_j (D_(e_j) f)² = ‖∇f‖²`.
- `sum_fderiv_fderiv_eq_laplacian`: `Σ_j D_(e_j) D_(e_j) f = Δf`, where `Δ` is
  `Laplacian.laplacian`. This holds wherever `Df` is differentiable. The proof uses Mathlib's
  orthonormal-basis formula for the Laplacian.
- `sum_fderiv_mul_fderiv_eq_inner_gradient`: `Σ_j (D_(e_j) U)(D_(e_j) f) = ⟪∇U, ∇f⟫`.
- `formOperator_eq_sub_weightedLaplacian`: for `C²` f,
  `formOperator e b f = f - ℒf` with `b_j = D_(e_j) U` and `ℒf = Δf - ⟪∇U, ∇f⟫`
  (`weightedLaplacian`). Hence `contDiff_formOperator` and `hasCompactSupport_formOperator`.
- `weightedFormEnergy_eq_integral_norm_gradient`:
  `FE_w(f) = ∫ w (f² + ‖∇f‖²) dm`.

**Tilted normalization.** Let `μ = m.tilted (-U)` be a probability measure. Then:

- `exp(-U)` is `m`-integrable (`integrable_exp_neg_of_tilted`);
- `Z = ∫ exp(-U) dm > 0` (`integral_exp_neg_pos_of_tilted`);
- `∫ exp(-U) g dm = Z ∫ g dμ` for every `g`, with no integrability assumption
  (`integral_exp_neg_mul_eq_of_tilted`);
- `FE_w(f) = Z ∫ (f² + ‖∇f‖²) dμ` for `w = exp(-U)` (`weightedFormEnergy_eq_mul_integral`).

**Weight and classical density.** `fderiv_exp_neg_apply` proves the weight equation
`D_v exp(-U) = -(D_v U) exp(-U)`. `exists_timeAverage_error_lt` promotes the earlier audit
client to production: for smooth `U`, any directions `a`, `h ∈ C_c^∞` and `ε > 0`, some
actual cellwise time average `q ∈ C_c^∞` has `√FE_w(J_cl q - h) < ε`.

**Norm bridge** (`norm_sq_add_norm_closedWeightedOperator_sq_eq`). Let `e` be any
orthonormal basis, and let `x ∈ D(T̄)` be the class of some `f ∈ C_c^∞`. The only
information used about `x` is `(x : L²) = [f]`. Then

```text
‖x‖² + ‖T̄x‖² = FE_w(f) / Z,   w = exp(-U),  Z = ∫ exp(-U) dm.
```

The proof identifies `T̄x = [∇f]`, computes both squared `L²(ν)` norms as integrals, and
applies the energy normalization.

**Operator bridge.** For `q ∈ C_c^∞`, `[q] ∈ D(A)` holds by the existing G1 theorem. Then:

- `toLp_add_adjointComp_eq_formOperator`: `[q] + A[q] = [formOperator e b q]` in `L²(ν)`;
- `toLp_add_adjointComp_mem_closedWeightedOperator_domain`: `J[q] ∈ D(T̄)`, because
  `formOperator e b q = q - ℒq` is `C_c^∞`.

**Density theorem** (`exists_toLp_add_adjointComp_graph_lt`). Its only premises are the
model hypotheses (`hν`, `hi`, `hνU`) and `hU : ContDiff ℝ ∞ U`. For every `z ∈ D(T̄)` and
`ε > 0` there exist `q ∈ C_c^∞(V)` with `hA : [q] ∈ D(A)` and `hJ : J[q] ∈ D(T̄)`, and

```text
√(‖J[q] - z‖² + ‖T̄ J[q] - T̄ z‖²) < ε.
```

The proof has three steps:

1. The existing graph-norm smooth core `exists_seq_smooth_tendsto_graph` gives
   `h ∈ C_c^∞` with `‖[h] - z‖_E < ε/2`. Both component distances are below `ε/4`.
2. `exists_timeAverage_error_lt`, with the standard orthonormal basis and tolerance
   `(ε/2)√Z`, gives `q`.
3. `J[q] - [h]` is the class of `J_cl q - h ∈ C_c^∞`, and `T̄` is linear on its domain. The
   norm bridge gives `‖J[q] - [h]‖_E = √FE_w(J_cl q - h) / √Z < ε/2`. Minkowski's
   inequality in `WithLp 2 (L² × L²)` then finishes the proof.

`dense_formRange_graphL2` restates the result in the Hilbert space `graphL2 T̄`: the graph
points `(J[q], T̄J[q])`, `q ∈ C_c^∞`, form a `Dense` set.

The statements have no hypothesis of form-range density, operator core, surjectivity of `J`
or a Poincaré inequality. The target `z` is arbitrary, not restricted to `C_c^∞`. Zero
dimension is not excluded: there the basis is indexed by `Fin 0`, `formOperator = id` and
`J = I`.

## Clients

[WaveSplittingFormRangeAudit.lean](../audits/WaveSplittingFormRangeAudit.lean) checks the
following:

- `arbitrary_target`: for an arbitrary `z ∈ D(T̄)` and every `n`, some `qₙ` satisfies
  `‖J[qₙ] - z‖_E² < 1/(n+1)²`.
- `norm_bridge`: `Z > 0` and `‖[f]‖² + ‖T̄[f]‖² = (∫ exp(-U)(f² + ‖∇f‖²) dm)/Z`.
- `pointwise_identities`: all four pointwise identities in an arbitrary orthonormal basis.
- `operator_bridge`: `J[q] = [q - ℒq]` and `[q - ℒq] ∈ D(T̄)`.
- `zero_dimension`: if `finrank V = 0`, then `A[q] = 0`, so `J = I`.
  `zero_dimension_energy` shows that the form energy then has no derivative terms. The
  density theorem has no dimension premise.

Twenty-four transitive axiom reports, covering the clients and every new public theorem, use
only `propext`, `Classical.choice` and `Quot.sound`.

## Not claimed

This record does not prove two-field convergence for `e = [qₙ] - F`, including the
`‖Je‖_E² = ‖e‖² + 3‖Te‖² + 3‖Ae‖² + ‖TAe‖²` step. It does not prove the arbitrary-data
heat-test frontend, the `Γ` interpolation, gradient estimates, the Buser constant π or KLS.
Convexity of `U` is not derived from `LogConcave ν`, and the tilted-law representation
`ν = m.tilted (-U)` remains an explicit premise.

## Verification

Strict source and client checks, the full build and the project verifier are logged under
`build/audit/heat-test-splitting-form-range/`. Its `final-snapshot.json` records the actual
final verifier outcome, report and source snapshot. Pinned dependency artifacts are trusted.
There was no remote CI, commit, push or change to the real Git index.
