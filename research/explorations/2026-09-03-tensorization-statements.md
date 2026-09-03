# Tensorization statement skeleton and ledger lifecycle

**Date:** 2026-09-03 (Asia/Shanghai)

**Scope:** statement-agent deliverable. The revised work package reserves freezing to a human
and proofs to a separate agent. This branch supplies candidate signatures, 24 `sorry` stubs,
ledger metadata, and documentation. Tensorization remains **drafted**, not frozen or proved.

## Encoding and statement audit

Use `WithLp 2 (E × F)` with Mathlib's Hilbert product inner product and the product law
`Poincare.prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)`. Ordinary products retain their
standard maximum norm. `MeasurableEquiv.toLp` connects the measure theory on the two types;
`WithLp.prodContinuousLinearEquiv` connects their calculus.

The candidate ambient spaces are real separable Hilbert spaces with Borel sigma algebras,
including all finite-dimensional Euclidean spaces and dimension zero. `Holds` continues to
carry probability normalization, constant nonnegativity, and the original smooth L2
finite-energy test inequality. The optimal-constant statement includes `⊤` and imposes no
finite second moment. Both public signatures are in `FunctionalInequalities/Tensorization.lean`
and are reproduced in `LEAN_DESIGN.md` for human review.

Admissibility of sections is only asserted a.e. Smoothness restricts to every section, but L2
and finite energy do not: with a standard Gaussian first factor, `ν = δ₀`, and
`f(x,y) = y² exp(x²)`, the product test and its gradient vanish on the support while the
section at `y = 1` is not L2. The a.e. contract suffices for the planned iterated-integral bound.
No smoothness of a marginal integral is claimed or added as a hypothesis.

## Mathlib audit and gaps

The audit uses the repository's pinned Mathlib v4.33.0, commit
`db584cd6d46c92f209a44c0f1c829460d327499d`.

- `Analysis/InnerProductSpace/ProdL2` and `Analysis/Normed/Lp/ProdLp` supply the L2 inner product,
  `prod_inner_apply`, and `prod_norm_sq_eq_of_L2`; gradient restriction still needs a bridge
  from the derivative of an affine coordinate inclusion.
- `Analysis/Normed/Lp/MeasurableSpace` supplies the Borel structure and `MeasurableEquiv.toLp`.
  `integral_map_equiv` and `memLp_map_measure_iff` are the intended transport interfaces.
- `MeasureTheory/Integral/Prod` supplies Fubini, `Integrable.prod_left_ae`/
  `prod_right_ae`, and integrability of marginal integrals. The direct L2-section and marginal-L2
  statements needed here are exposed as draft helpers.
- `Probability/Moments/Variance` supplies `variance_eq_sub`, `variance_eq_integral`,
  `variance_nonneg`, and variance of additive independent tests. It does not supply the required
  general nonlinear two-factor bound in the audited module. The generic conditional-variance
  identity in `Probability/CondVar` would require a product conditional-expectation bridge;
  the proposed skeleton instead states the direct Fubini version.

## Independent placeholder targets and intended proof routes

Every item below is a signature with an intact `:= sorry`, including the probability instance.
The routes describe work for the future proof agent; this deliverable provides no proof terms.
Names in the first two tables and the last table are relative to
`FunctionalInequalities.Poincare`.

### ProductGeometry.lean (6 targets)

| Declaration | Intended route after human freeze |
| --- | --- |
| `prodMeasure_isProbabilityMeasure` | Transport the probability instance of `μ.prod ν` by the measurable `WithLp.toLp 2` map. |
| `contDiff_section_left` | Compose smoothness with the affine inclusion of the first coordinate and the continuous linear equivalence. |
| `contDiff_section_right` | Compose smoothness with the affine inclusion of the second coordinate. |
| `gradient_section_left` | Apply the Fréchet chain rule to the first-coordinate inclusion, then Riesz uniqueness and the product inner-product formula. |
| `gradient_section_right` | Apply the same derivative/Riesz bridge to the second-coordinate inclusion. |
| `norm_gradient_sq_prod` | Combine the two gradient projections with `WithLp.prod_norm_sq_eq_of_L2`. |

### ProductAdmissible.lean (6 targets)

| Declaration | Intended route after human freeze |
| --- | --- |
| `Admissible.memLp_uncurry` | Transport `memLp_two` back to the ordinary product via the measurable equivalence. |
| `Admissible.integrable_gradient_fst` | Bound the first squared component by the full squared gradient and use continuity for measurability. |
| `Admissible.integrable_gradient_snd` | Bound the second squared component by the full squared gradient with the same integrability argument. |
| `Admissible.section_left_ae` | Combine smooth restrictions, the a.e. L2-section lemma, and Fubini for the first gradient component. |
| `Admissible.section_right_ae` | Combine smooth restrictions, the a.e. L2-section lemma, and Fubini for the second component. |
| `energy_prod_eq` | Transport the energy integral and integrate the squared-norm decomposition using both explicit component-integrability lemmas. |

### ProductVariance.lean (10 targets)

Names below are relative to `FunctionalInequalities.ProductVariance`; these statements require
only probability spaces and L2 data, independently of Hilbert-space geometry.

| Declaration | Intended route after human freeze |
| --- | --- |
| `memLp_right_ae` | Apply Fubini to the integrable square and combine with a.e. section measurability. |
| `memLp_left_ae` | Use the corresponding Fubini statement in the other order. |
| `sq_integral_le` | Use nonnegative variance and the L2 variance formula to express Jensen's square inequality. |
| `memLp_integral_right` | Dominate the squared marginal integral by the marginal square integral using Jensen a.e. |
| `memLp_integral_left` | Apply the same marginal-L2 argument with the coordinates exchanged. |
| `integrable_variance_right` | Express section variance a.e. as its second moment minus its squared mean, both integrable. |
| `integrable_variance_left` | Use the same variance formula and marginal integrability in the other order. |
| `variance_decomposition` | Expand the L2 variance formulas and use Fubini to obtain the law of total variance. |
| `variance_integral_le` | Center by the first-coordinate mean, apply Jensen in the second coordinate, and integrate using explicit L2 bounds. |
| `variance_le` | Combine total variance with the preceding bound for the variance of a marginal mean. |

### Tensorization.lean (2 targets)

| Declaration | Intended route after human freeze |
| --- | --- |
| `Holds.prod` | Apply the two factor inequalities to a.e. admissible sections, integrate the bounds, and combine variance and energy decompositions with `max C C'`. |
| `constant_prod_le` | Take infima over both finite valid constants in `ENNReal`; lattice distributivity preserves the bound even if one indexing set is empty and an optimal constant is `⊤`. |

## Ledger and build boundary

`lem:linear-test-lower` remains `proved` with `checked_by: lean`. The tensorization node is
`drafted` with `checked_by: null`. Drafted/frozen nodes still require a valid node entry point in
the default Lake target. For proved nodes, the static escape-token guard also checks literal
local imports and includes `native_decide`. A snapshot check cannot authorize human freezing.

`solutions/LemPoincareTensorization.lean` imports the reusable skeleton and names both public
signatures with `#check`; it supplies no proof wrapper or duplicate statement. The default
`Issue2Solutions` target compiles it. The existing Poincaré/covariance definitions and linear-test
proof files are unchanged.

## Local acceptance

All three commands passed after registration of the new node:

```text
python3 research/check_ledger.py
1 ledger(s), 2 nodes. 0 error(s).

python3 -m unittest discover -s research/tests -p 'test_*.py'
Ran 24 tests in 0.079s
OK

cd formalization && lake build
Build completed successfully (2952 jobs).
```

The 24 Lean placeholder warnings are expected. They are not proof certification. Regression
coverage includes both unproved states, invalid statuses, metadata pairings, missing artifacts,
default-target membership, prohibited proved-node tokens, local import traversal, and rejection
of promotion while placeholders remain. Task 0's successful initial remote CI run is recorded
separately in `2026-09-03-issue2-ci.md`; the combined skeleton branch must also pass CI before
delivery. Human statement review and proof implementation remain future phases.
