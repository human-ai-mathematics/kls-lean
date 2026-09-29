# Semigroup route: specializing `T` to the weighted gradient—the heat semigroup for log-concave laws

2026-09-19, following the [`S7`/`S8` round](2026-09-19-generated-semigroup-route.md). This session completed the work directly (all transfers are one-line `exact` proofs, with no mathematical content); no proof session was needed. No commit or push.

## Results

New module `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup.lean`, namespace `FunctionalInequalities.KLS.LogConcave`:

| Declaration | Content |
| --- | --- |
| `closedWeightedOperator hν m B hi` | `T̄ := (hν.weightedOperator m B hi).closure`, `L²(ν) →ₗ.[ℝ] L²(ν; V)` |
| `closedWeightedOperator_isClosed`, `dense_domain_closedWeightedOperator` | `T̄` is closed (`IsClosable.closure_isClosed`) and densely defined (density transfers via `le_closure`) |
| `heatSemigroup hν m B hi ht` | `P_t = exp(−t T̄†T̄) : L²(ν) →L[ℝ] L²(ν)`, namely `semigroupCLM T̄ … ht` |
| `norm_heatSemigroup_apply_le`, `inner_heatSemigroup_left`, `heatSemigroup_zero_apply`, `heatSemigroup_add_apply`, `continuousOn_heatSemigroup` | Contractivity, symmetry, `P_0 = 1`, the semigroup law, and strong continuity on `[0,∞)` |
| `heatSemigroup_generator` | `f ∈ D(T̄†T̄)` ⟹ `(P_t f − f)/t → −T̄†T̄ f` |
| `inner_adjointComp_self_eq` | `⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²`, which by `weighted_relaxation_of_mem` is the sequential relaxation of `‖B∇g‖²`: **the semigroup's Dirichlet form is the repository's closed energy** |
| `intrinsicHeatSemigroup hμ m B ht` | Heat semigroup on the intrinsic law of any log-concave `μ` (`hμ.intrinsicMeasure` is full-dimensional) |

Audit `research/audits/HeatSemigroupAudit.lean`: all 13 `#print axioms` results are standard, with 0 `sorryAx`. The module is imported by the aggregate root; `lake build` passed with 3533 jobs.

## Meaning and limitations

**Gap one** of `thm:logconcave-cheeger-poincare-comparison` in `tasks.json` (generating a symmetric contraction semigroup from the closed energy form) is now also closed for the concrete operator:
for full-dimensional log-concave `ν` (and the intrinsic law of any log-concave `μ`), `P_t` is a strongly continuous self-adjoint contraction semigroup on `L²(ν)`, with generator `−T̄†T̄` and Dirichlet form the closure of `‖B∇·‖²`.
`infrastructure.status` remains `missing`: gaps two (the Markov property), three (Bakry–Émery Γ), and four (small-time heat estimates) are unchanged. The node has no `\leanok`, and the constant π has not been addressed.

## A minor difficulty

`heatSemigroup` is a `def`, not an `abbrev`, so unification cannot infer `hd` from the underscores in `semigroupApply_le _ _ _` in the transfer lemmas.
One must explicitly write `(hν.closedWeightedOperator m B hi) (hν.closedWeightedOperator_isClosed m B hi) (hν.dense_domain_closedWeightedOperator m B hi)`.

## Next step

Gap two: the Markov property. See the handoff prompt [2026-09-19-markov-handoff-prompt.md](2026-09-19-markov-handoff-prompt.md).
