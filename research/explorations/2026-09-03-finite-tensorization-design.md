# Finite tensorization: candidate design, source correspondence, and proof handoff

Date: 2026-09-03 (Asia/Shanghai). Statement agent: Codex.
Node: `lem:poincare-finite-tensorization`.
Issue: [#7](https://github.com/human-ai-mathematics/kls-lean/issues/7), verified as an actual sub-issue of [#1](https://github.com/human-ai-mathematics/kls-lean/issues/1).
Status: **drafted / checked_by: null**. This is a statement preparation record, not a freeze or proof acceptance.

## Baseline and ownership

The initial checkout was clean on `main` at `4801ca958778ae02cc0d81fc7ec805a4e96a894c`, exactly the supplied accepted baseline. The local Lean toolchain is `v4.33.0`; the manifest pins Mathlib to `db584cd6d46c92f209a44c0f1c829460d327499d`. No AGENTS.md was found in the workspace or applicable ancestor directories. The existing design, next-step context, ledger/schema, freeze/source records, binary product modules, project wrapper, and solution certificate were read before designing the new API.

GitHub was checked through the authenticated local CLI after the connector returned a repository access error. The full issue listing contained only #1 (open), #2 (closed), and #6 (closed); #6 describes finite products/equality as follow-up work and has no existing same-scope issue. The new issue number was obtained from creation, not predicted. Its database ID is `5333351383`; GitHub's sub-issue endpoint confirms #7 under #1. Its body records sources, scope, stage ownership, and final proof acceptance gates.

This phase adds definitions and compilable candidate declarations. Every new mathematical obligation, including norm preservation of the new concrete linear equivalences and probability of the transported finite law, uses `sorry`. The solution file uses `#check @...` only. It is a statement entry point, not a proof certificate. No proof agent was started, no statement was frozen, and no commit or push was made. Human review must precede the independent proof phase.

## Encoding contract

For `[Fintype ι]` and a dependent family `E : ι → Type*`, use `PiLp 2 E`. Each factor is a real complete inner product space, has its Borel measurable structure, and has second-countable norm topology. All factors in a family share a Lean universe; the index universe is independent. No finite-dimensional or nontrivial-space restriction occurs.

```lean
Poincare.piMeasure μ := (Measure.pi μ).map (WithLp.toLp 2)
```

The measurable structure is the existing transported `WithLp` structure. The `PiLp` Hilbert norm satisfies `‖x‖² = ∑ i, ‖x i‖²`. The ordinary function space is only the measure-construction/linear-equivalence carrier; its standard maximum norm is never treated as a Hilbert norm. This follows the existing `prodMeasure` convention on `WithLp 2 (E × F)`.

`piCongrLeft E (e : κ ≃ ι)` maps `PiLp 2 (fun j ↦ E (e j))` to `PiLp 2 E`. Its linear map is assembled from actual Mathlib linear equivalences and is specified by `(piCongrLeft E e x) (e j) = x j`. Its norm proof remains a placeholder. The corresponding pushforward sends `piMeasure (fun j ↦ μ (e j))` to `piMeasure μ`.

`piOptionEquivProd E` maps `PiLp 2 E` for `E : Option ι → Type*` to
`WithLp 2 (E none × PiLp 2 (fun i ↦ E (some i)))`, with value
`WithLp.toLp 2 (x none, WithLp.toLp 2 (fun i ↦ x (some i)))`.
The product-law identity has exactly this order:

```lean
(piMeasure μ).map (piOptionEquivProd E) =
  prodMeasure (μ none) (piMeasure (fun i ↦ μ (some i)))
```

The linear maps of both equivalences are concrete definitions, not arbitrary isometries selected by a placeholder. Their norm proofs and application/measure-compatibility propositions are explicit pending obligations. No second norm instance is installed on ordinary products or functions.

## Pinned Mathlib API audit

All locations below are relative to `formalization/.lake/packages/mathlib/Mathlib/`, at the pinned commit. The accompanying [API probe](2026-09-03-finite-tensorization-mathlib-api.lean) checks the actual types and ambient instances. The probe is an audit script, run with `lake env lean` from `formalization/`; the node's mathematical declarations are compiled in the default build.

| Need | Actual API and location | Remaining repository obligation |
| --- | --- | --- |
| Finite Hilbert product | `PiLp.innerProductSpace`, `PiLp.inner_apply`, `Analysis/InnerProductSpace/PiL2.lean:83`; `PiLp.norm_sq_eq_of_L2` in `Analysis/Normed/Lp/PiLp.lean` | Use the existing norm; no replacement instances |
| Completeness/topology/Borel | `PiLp.uniformEquiv`, `PiLp.homeomorph`; `PiLp.borelSpace` and `MeasurableEquiv.toLp` in `Analysis/Normed/Lp/MeasurableSpace.lean` | `#synth` verifies complete, second-countable, and Borel instances for dependent factors |
| Dependent finite measure | `Measure.pi`, `Measure.pi.instIsProbabilityMeasure`, `Measure.pi_of_empty`, `MeasureTheory/Constructions/Pi.lean:310,340` | Define `piMeasure` and prove its probability instance after transport |
| Coordinate law | `MeasureTheory.measurePreserving_eval` at `Pi.lean:402`; raw `Measure.pi_map_eval` at line 375 includes other factors' total masses | Transport to `PiLp.proj`; retain every factor's probability hypothesis |
| Continuous linear coordinate | `PiLp.proj 2 E i`, `PiLp.single`, `PiLp.norm_single`; `WithLp.fstL`, `WithLp.sndL` | Prove adjoints are the norm-preserving coordinate insertions |
| Reindexing | `LinearIsometryEquiv.piLpCongrLeft` at `PiLp.lean:868` handles only a homogeneous family; `LinearEquiv.piCongrLeft` is dependent | Add the dependent `Poincare.piCongrLeft` norm proof |
| Measure reindexing | `measurePreserving_piCongrLeft`, `Measure.pi_map_piCongrLeft` at `Pi.lean:732,746` | Pushforward compatibility after `toLp` |
| Hilbert decomposition | `PiLp.sumPiLpEquivProdLpPiLp` at `PiLp.lean:993` splits a sum-index dependent family; `LinearIsometryEquiv.piLpCurry` handles dependent nested products | These verify that suitable Hilbert splitting APIs exist; the chosen induction interface is the smaller Option split |
| Option splitting | `LinearEquiv.piOptionEquivProd` in `LinearAlgebra/Pi.lean:531`; `Measure.pi_map_piOptionEquivProd` at `Pi.lean:449` | **Different orders:** the linear equivalence returns `E none × tail`; the measurable equivalence returns `tail × E none`. Reconcile by swapping the measure factors, not by assuming matching names imply matching order |
| Empty/singleton laws | `Measure.pi_of_empty`, `measurePreserving_pi_empty`, `measurePreserving_piUnique` | Prove zero Poincaré constant for a probability on a subsingleton Hilbert space |
| Finite induction | `Fintype.induction_empty_option`, `Data/Fintype/Option.lean:90` | Use a motive quantifying over dependent spaces, measures and constants, and prove equivariance |
| L²/integral transport | `MemLp.comp_measurePreserving`, `memLp_map_measure_iff`; `MeasurePreserving.integrable_comp_of_integrable`; `ProbabilityTheory.variance_map` | Combine actual measure-preserving maps with explicit L²/admissibility hypotheses |
| Gradient transport | `ContinuousLinearMap.adjoint`, `toDual_gradient`, derivative composition APIs | No already-packaged repository theorem for projection/isometry transport of this `Admissible` class was found; state the required chain and energy rules locally |

The exploratory name `MeasurePreserving.memLp_comp` does not exist in this version; the actual name is `MemLp.comp_measurePreserving`. `variance_map` is in `ProbabilityTheory`, not `MeasureTheory`. These corrected names are checked by the retained probe. API existence is not a proof of any new candidate theorem.

## Source correspondence

BGL Proposition 4.3.1 gives a binary upper bound with the larger factor constant in a Markov-triple/Dirichlet-domain setting; its energy adds the two coordinate energies. Finite iteration explains the source correspondence for the proposed finite upper bound. There is no reciprocal, square, or factor-of-two conversion. See [BGL chapter](https://link.springer.com/chapter/10.1007/978-3-319-00227-9_4) and [full text, printed pp. 185–187](https://www.hse.ru/data/2016/11/24/1113029204/bok%253A978-3-319-00227-9.pdf#page=201).

The reverse bounds and optimal equalities are independent coordinate-test deductions in this repository's domain, not an assertion that BGL directly states or certifies every part of this API. For arbitrary Borel measures, a smooth function's gradient energy need not depend only on its L² equivalence class: under `δ₀` on the line, zero and the identity agree almost everywhere but have different energies. Thus a Sobolev/closed-Dirichlet domain identification is a separate theorem.

The pinned upstream [`prop:products`, proof (iii)](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/8185e46ffb040e04fea076953e5bcaeb4157d71a/modules/kls/16-model-geometries.tex#L64) was re-read through GitHub at `8185e46ffb040e04fea076953e5bcaeb4157d71a`. It uses finite-product equality, then a one-dimensional log-concave estimate in terms of variance, and then a Cheeger–Poincaré comparison. This node prepares the finite-product ingredient with explicit local test-domain semantics. The remaining analytic comparisons and localization assertions in parts (i) and (ii) remain separate obligations.

## Proposed proof route and helper boundaries

1. **Projection calculus and probability transport (`PoincareTransport`).** For a continuous linear `q : H →L[ℝ] K`, `f ∘ q` is globally smooth when `f` is. At differentiability points, its gradient is `q.adjoint (gradient f (q x))`. If `q.adjoint` is an isometry, the squared norm is exactly preserved. If `q` also preserves the two explicitly normalized probability laws, L² membership pulls back. For `Admissible μ f`, the lifted squared gradient is integrable; only then use its integral as energy. `variance_comp_projection` retains `MemLp f 2 μ`; `energy_comp_projection` retains the complete admissibility hypothesis. These pieces assemble `Admissible.comp_projection`.
2. **Binary coordinate lift (`ProductReverse`).** Use the actual `WithLp.fstL` and `sndL`; their adjoints insert `(v,0)` and `(0,w)` in the Hilbert product and preserve norms even when a factor is zero-dimensional. Their pushforwards are the factor laws only after the other factor's mass is normalized. For example, `(2 δ₀) ⊗ ((1/2) δ₀)` has total mass one while neither factor does. Therefore both probability instances appear explicitly in every public reverse/equality signature. Apply the product inequality to lifted factor tests to recover the same finite constant.
3. **Binary optimal lower bounds.** For every finite valid product constant, fixed-constant recovery and existing `constant_le` bound the factor's optimal constant by it. Existing `le_constant` then gives each extended lower bound. Combine with the accepted `constant_prod_le`; do not edit that proof.
4. **Isometry transport.** A linear isometry equivalence preserves the smooth domain, L² membership and gradient energy in both directions. State exact admissibility correspondence, variance and energy identities, `holds_map_linearIsometryEquiv_iff`, and `constant_map_linearIsometryEquiv`. These are invertible geometric transports, with no Lipschitz loss and no moment hypothesis.
5. **Finite upper bound.** Use `Fintype.induction_empty_option`, quantifying in its motive over the dependent family and data. The empty Hilbert product is a subsingleton; all variances vanish and constant zero is valid. The Option step transports its law to the binary product of `none` and the tail, applies existing `Holds.prod`, and transports back. The finite `NNReal` supremum splits as the maximum of the head and tail suprema; the empty supremum is zero. The equivalence step uses dependent reindexing and invariance of the finite supremum under that equivalence.
6. **Finite lower bounds.** `PiLp.proj` has the single-coordinate insertion as adjoint; `adjoint_pi_proj` uses `[DecidableEq ι]` only to state `PiLp.single`. The norm/measure interfaces and public conclusions require no `DecidableEq` or nonempty hypothesis. Apply the common projection helper to derive `Holds.of_pi`, then the optimal coordinate lower bound as in the binary case.
7. **Extended optimal upper bound without attainment.** If `⨆ i, constant (μ i)` were strictly smaller than the product constant, each defining infimum supplies a finite valid factor constant strictly below that product constant (`iInf_lt_iff`). Finitely choose them and use `Holds.pi`; their finite supremum is still strictly below the putative product constant. The empty case uses valid constant zero. This contradicts `constant_le`. This route never assumes the infima are attained and never applies `toReal` to infinity. The lower bounds and `iSup_le` then give equality. If any factor constant is `⊤`, its coordinate lower bound directly forces the product to be `⊤`.

The existing binary upper bound restricts smoothness to every section, but L² and finite energy only to almost every section. Its Fubini argument is reused intact. None of the new interfaces assumes every section of an admissible product test is admissible, or differentiates an averaged function.

## Boundary cases and statement surface

- No `Nonempty ι` occurs in `Holds.pi` or `constant_pi_eq`. `holds_pi_empty` and `constant_pi_empty` explicitly give zero for empty products.
- `constant_pi_unique` handles a singleton dependent family, and the concrete Euclidean singleton uses `Fin 1` for every natural dimension, including zero.
- `holds_zero_of_subsingleton` and `constant_eq_zero_of_subsingleton` cover zero-dimensional Hilbert factors. The generic finite formula permits such factors mixed with arbitrary other factors. `constant_pi_of_subsingleton` and the all-zero Euclidean statement cover families consisting entirely of them.
- `constant_pi_eq_top_of_factor` records the infinite-factor boundary without a real conversion. Equality quantifies over all probability laws, including those for which an infimum is not supplied with an attaining witness.
- Euclidean families use `E i = EuclideanSpace ℝ (Fin (d i))`, with arbitrary `d : ι → ℕ`. Typed applications of the generic API check family constants, binary `(0,n)` and `(n,0)`, `Fin 0`, zero-dimensional `Fin 1`, and two zero-dimensional factors. Dedicated empty/singleton/mixed-zero/all-zero declarations are also present. These are type checks, not completed mathematics.

The [candidate review record](../decisions/2026-09-03-finite-tensorization-candidate.md) identifies the complete public surface and the verbatim ledger snapshot. All 53 public declaration types, including implicit parameters, universes, and typeclasses, are printed in the [signature output](2026-09-03-finite-tensorization-signatures.txt). The frozen definition boundary should include the concrete `piMeasure`, `piCongrLeft`, and `piOptionEquivProd` constructions and their direction conventions.

Human review should specifically confirm: separate binary normalization; the `PiLp 2` dependent encoding and Option factor order; the real cast of the finite `NNReal` supremum; the `ENNReal` indexed supremum and empty-zero convention; the projection/isometry helper hypotheses; and agreement of the Euclidean statements and ledger with this scope. After approval, append a new freeze record and let a separate proof agent replace placeholders. Suspected errors in frozen statements must return through a new exploration entry.

## Excluded work

No second moments, densities, positive dimensions, finite optimal constants or attainment witnesses are introduced. Gaussian, LSI, Bakry–Émery, Cheeger comparisons, Sobolev/spectral-gap bridges, and the full KLS conclusion remain outside this node. This local draft has no new remote CI claim; the earlier accepted commit's CI is not evidence for the unpublished skeleton.
