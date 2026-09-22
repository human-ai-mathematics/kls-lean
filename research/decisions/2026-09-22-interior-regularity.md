# Interior regularity of deficiency elements: `hreg` proved, `hcore` discharged

2026-09-22, after the operator-core criterion (`2026-09-22-operator-core-criterion.md`). The
task of this round is to **prove** the local regularity hypothesis `hreg` of
`KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity` in the current smooth
convex-potential model, and thereby deliver the heat-flow weak `Γ₂` theorem without `hcore` or
`hreg`. It preserves all earlier work, makes no commit or push, does not upgrade Lean/Mathlib,
and does **not** complete Bakry–Émery, Buser or KLS.

## 1. Placement plan (recorded before editing)

| Item | Object and role | Destination | Decision |
| --- | --- | --- | --- |
| `M0`–`M4` mollification by a normalised bump against a Haar measure: `L²` contraction, `L²` convergence, self-adjointness (Fubini) identity, commutation of `∇` and `Δ` with the mollifier on smooth compactly supported tests | reusable analytic tool, no probability law, no `ν` | `Analysis/Mollification.lean` | **create** (root-level `Analysis/` file, like `Divergence.lean`, `PartitionOfUnity.lean`); no existing module owns convolution |
| `R0`–`R3` the tilted model: `ν`-integrals as `m`-integrals, the weak equation for the density-weighted class `w = ρ u`, the mollified weak equation, the Caccioppoli-type estimate, the Cauchy argument and the passage back to `D(T̄)` | substantive theorem about `T̄` and `A = T̄†T̄` in the tilted model | `KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean` | **create**: `OperatorCore.lean` owns the global cutoff argument and must not acquire mollifiers; `Generator.lean` is the per-test identification |
| `R4` the unconditional operator-core theorem | consequence of `R3` and the criterion `C3` | `KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean` | same module: it cannot live in `OperatorCore.lean` without an import cycle |
| `R5` the heat-flow weak `Γ₂` theorem without `hcore`/`hreg` | concrete heat-flow frontend | `KLS/LogConcave/HeatSemigroup/GammaTwo.lean` | **extend**: that module owns the heat-flow `Γ₂` frontends; it gains the import of `InteriorRegularity` |

Dependency direction: `GammaTwo → InteriorRegularity → {OperatorCore, Generator, Multiplier,
Mollification}`; `Mollification → BakryEmery/Calculus`. No cycle. No existing statement is
weakened, renamed or removed; the `C¹` theorems of `OperatorCore.lean` and the `_of_core` /
`_of_localRegularity` frontends stay exported unchanged. Validation: strict compilation of the
new and touched modules and of a new audit `research/audits/BakryEmeryInteriorRegularityAudit.lean`,
axiom audit, default `lake build`, and the root `research/verify.py` rerun on the final snapshot.

## 2. Headline

**`hreg` is proved and `hcore` is discharged.** For `ν = m.tilted (-U)` with a `C¹` potential and
unit weight, every `u ∈ L²(ν)` orthogonal to `(A + 1) C_c^∞(V)` has all of its localizations
`[χ u]`, `χ ∈ C_c^∞(V)`, in `D(T̄)` (`KLS.LogConcave.toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`).
Consequently `C_c^∞(V)` **is** an operator core of `A = T̄†T̄` for every `C¹` potential
(`KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp`), i.e. `ℒ` is essentially self-adjoint on
`C_c^∞(V)` in `L²(ν)`, and the heat-flow weak `Γ₂` inequality holds **without** any
operator-core, approximation or regularity hypothesis
(`KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg`): for `C^∞` convex `U`, unit
weight, **arbitrary** `g ∈ L²(ν)`, **every** `t > 0` and **every** nonnegative `φ ∈ C_c^∞(V)`,
with `F = P_t g`,

`0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν`.

The round's stated target is met. The remaining hypotheses are those of the model: the tilted form
of the law, smoothness (`C^∞`) and convexity of the potential for the `Γ₂` frontend, and the
unit weight. Nothing was packaged into a structure, an instance or a definition; the two
conditional frontends `_of_core` and `_of_localRegularity` and every `C¹` theorem of
`OperatorCore.lean` remain exported unchanged.

## 3. The setting, stated in full

As in `2026-09-22-operator-core-criterion.md` §1: `V` a finite-dimensional real inner product
space with its Borel structure, `m` a Haar measure, `ν : ProbabilityMeasure V` full-dimensional
log-concave with `(ν : Measure V) = m.tilted (-U)`, `T̄` the closed unit-weight gradient,
`A = T̄†T̄`, `P_t` the semigroup. Mathlib's `Measure.tilted` is normalised: the density of `ν`
with respect to `m` is `ρ = e^{-U} / Z`, `Z = ∫ e^{-U} dm`, and `Z > 0` because `ν` is a
probability measure (`tilted_of_not_integrable` otherwise makes `ν = 0`).

| Result | weight | `U` | extra |
| --- | --- | --- | --- |
| mollification toolkit `M0`–`M3` | — | — | Haar measure only |
| interior regularity `R1` | `B = I` | `C¹` | none: no convexity, no semigroup |
| operator core `R2` | `B = I` | `C¹` | none |
| deficiency elements vanish `R2'` | `B = I` | `C¹` | none |
| heat-flow weak `Γ₂` `R3` | `B = I` | `C^∞`, `ConvexOn ℝ Set.univ U` | `φ ∈ C_c^∞`, `φ ≥ 0`, `t > 0` |

## 4. Route check, with what Mathlib v4.33.0 actually has

Checked in the pinned Mathlib before choosing the route:

* **Convolution.** `Analysis/Convolution.lean` and `Analysis/Calculus/ContDiff/Convolution.lean`
  give existence, continuity, smoothness (`HasCompactSupport.contDiff_convolution_left`), the
  derivative of a convolution (`HasCompactSupport.hasFDerivAt_convolution_right`,
  `convolution_precompR_apply`), `support_convolution_subset` and `integral_convolution`; the bump
  files give `ContDiffBump.normed`, its integral one, evenness, `dist_normed_convolution_le` and
  pointwise a.e. convergence. **Absent:** any `Lp` bound for a convolution (no Young inequality,
  no `eLpNorm`/`MemLp` statement), `Lp` convergence of mollifications, and the symmetry identity.
  These four are exactly what `Analysis/Mollification.lean` adds.
* **Density.** `MeasureTheory/Function/ContinuousMapDense.lean` gives
  `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` for a regular measure, which a Haar measure on a
  finite-dimensional space is.
* **Fourier/Sobolev.** `Analysis/Distribution/Sobolev.lean` (Bessel-potential spaces on tempered
  distributions) has `MemSobolev`, `besselPotential_neg_two_laplacian_eq`, `MemSobolev.laplacian`
  and `MemSobolev.lineDerivOp`, i.e. the *downward* regularity of derivatives, but no elliptic
  bootstrap, no bridge from an `Lp` class with respect to an abstract Haar measure to `𝓢'`, and
  no approximation of a Sobolev function by `C_c^∞` in the `H¹` norm. The passage back to the
  repository's graph-closure domain `D(T̄)` would still require exactly the mollification facts
  above. Rejected as a longer route to the same lemmas.
* **Integration by parts.** The repository's `integral_mul_inner_gradient_eq_neg` with the
  constant weight is the Haar-measure identity `∫ ⟪∇f, ∇g⟫ dm = -∫ Δf g dm` for `f ∈ C²_c`,
  `g ∈ C¹`; it is the only integration by parts the argument needs.
* **Closed graph.** `Analysis/Semigroup/AdjointClosure.lean`'s
  `exists_mem_domain_apply_eq_of_tendsto` is the bridge from a graph-convergent sequence of tests
  to membership in `D(T̄)`; `Closure.lean` provides the test-class membership and the value of
  `T̄` on tests (`toLp_mem_closedWeightedOperator_domain_of_isTest`,
  `closedWeightedOperator_apply_toLp`). A compactly supported `C¹` function is a test
  (`IsTest`: Lipschitz, `L²`, gradient in `L²`), so the potential needs only `C¹`.

**Why no weak compactness.** The classical proof extracts a weakly convergent subsequence from
the bounded family `χ ∇vₙ`. Here the Caccioppoli estimate is applied to the **differences**
`vₙ - vₖ`, whose data `(vₙ - vₖ, Hₙ - Hₖ)` satisfy the same weak equation by linearity and tend
to zero in `L²(m)`; this makes `χ ∇vₙ` **Cauchy**, and completeness of `L²(ν; V)` plus closedness
of `T̄` finish. No Banach–Alaoglu, no Mazur, no Friedrichs commutator and no Fourier transform.

## 5. `M0`–`M3`: the mollification toolkit (`Analysis/Mollification.lean`)

With `ρ = φ.normed m`, `φ : ContDiffBump (0 : V)`:

* `M0` `eLpNorm_convolution_le`: `‖ρ ⋆ f‖₂ ≤ ‖f‖₂` for a.e. strongly measurable `f : V → E`.
  Pointwise, `‖(ρ ⋆ f) x‖ₑ ≤ ∫⁻ ρ(t) ‖f (x - t)‖ₑ dt` and Hölder with exponents `2, 2` against
  `√ρ` give `‖(ρ ⋆ f) x‖ₑ² ≤ ∫⁻ ρ(t) ‖f (x - t)‖ₑ² dt` since `∫ ρ = 1`; Tonelli and translation
  invariance integrate this to the claim. Everything is done with `lintegral`, so no
  integrability side condition appears.
* `M1` `tendsto_eLpNorm_convolution_sub`: `‖ρₙ ⋆ f - f‖₂ → 0` for every `f ∈ L²(m)` when
  `rOut (φₙ) → 0`. For continuous compactly supported `f` the bound
  `dist_normed_convolution_le` and uniform continuity give uniform convergence on a fixed compact
  thickening of the support; the general case follows by `ε/3` from `M0` and the density of
  that class.
* `M2` `integral_inner_convolution_eq`: `∫ ⟪ρ ⋆ a, b⟫ = ∫ ⟪a, ρ ⋆ b⟫` for integrable `a` and
  continuous compactly supported `b`, by two applications of `integral_integral_swap`, one
  translation, one reflection and the evenness of `ρ`.
* `M3` `gradient_convolution`, `laplacian_convolution`: `∇(ρ ⋆ g) = ρ ⋆ ∇g` and
  `Δ(ρ ⋆ g) = ρ ⋆ Δg` for `g ∈ C_c^∞`, from Mathlib's derivative of a convolution applied to
  `g` and to its directional derivatives.

## 6. `R1`–`R3`: what is proved (`KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean`)

Private steps, in order:

1. `integral_laplacian_mul_tiltedDensity_mul`: from `⟪A [f], u⟫ + ⟪[f], u⟫ = 0`, with
   `A [f] = [-ℒf]` and `∫ · dν = ∫ ρ · dm`, the class `W = ρ u` satisfies
   `∫ Δf W dm = ∫ ⟪∇f, W ∇U⟫ dm + ∫ f W dm` for every `f ∈ C_c^∞(V)`. The integrabilities come
   from `integrable_tilted_iff` and `u ∈ L²(ν) ⊂ L¹(ν)`.
2. `integral_laplacian_mul_convolution_eq`: for a bump `η` equal to one on
   `closedBall 0 (R + 1)`, `w = η W ∈ L¹ ∩ L²(m)`, `G = η W ∇U ∈ L¹ ∩ L²(m)` and a normalised
   bump `ρ` of radius `≤ 1`, the smooth `v = ρ ⋆ w` and continuous `H = ρ ⋆ G` satisfy
   `∫ Δg v = ∫ ⟪∇g, H⟫ + ∫ g v` for every `g ∈ C_c^∞` supported in `closedBall 0 R`: by `M2`
   the mollifier moves onto `g`, by `M3` it commutes with `Δ` and `∇`, and since `ρ ⋆ g` is
   supported in `closedBall 0 (R + 1)` the cutoff `η` is invisible there.
3. `norm_toLp_smul_gradient_le` (Caccioppoli): if `(v, H)` satisfies that equation against every
   smooth test supported in `tsupport χ`, then `‖χ ∇v‖₂ ≤ 3 ‖v ∇χ‖₂ + 2 ‖χ H‖₂` in `L²(m)`, from
   the single test `g = χ² v`, the Haar integration by parts and Cauchy–Schwarz; the term
   `∫ χ² v²` has the good sign and is dropped.
4. **`R1`** `toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`: with the mollifier
   sequence `ρₙ` of radii `1/(n+1)`, `vₙ = ρₙ ⋆ w → w` and `Hₙ = ρₙ ⋆ G → G` in `L²(m)` by
   `M1`; the differences `(vₙ - vₖ, Hₙ - Hₖ)` satisfy the equation of step 2 by linearity, so
   step 3 gives `‖χ ∇(vₙ - vₖ)‖₂ ≤ 3 M₁ ‖vₙ - vₖ‖₂ + 2 M₂ ‖Hₙ - Hₖ‖₂ → 0`. The `C¹` compactly
   supported tests `gₙ = χ vₙ / ρ` (with `1/ρ = Z e^{U}`) satisfy `gₙ - χ u = (χ/ρ)(vₙ - w)` and
   `∇gₙ - ∇gₖ = (χ (vₙ - vₖ)) ∇(1/ρ) + (1/ρ) χ ∇(vₙ - vₖ) + (1/ρ)(vₙ - vₖ) ∇χ`, all supported in
   `tsupport χ`, where `ρ ≤ C₃`; hence `[gₙ] → [χ u]` in `L²(ν)` and `[∇gₙ] = T̄ [gₙ]` is Cauchy
   in `L²(ν; V)`. Closedness of `T̄` gives `[χ u] ∈ D(T̄)`, for the exact class
   `(memLp_mul_of_contDiff_hasCompactSupport hχ hχc u).toLp _` of the criterion theorems.
5. **`R2`** `exists_seq_smooth_tendsto_adjointComp`: `C3` with its hypothesis discharged by `R1`.
6. **`R3`** `HeatSemigroup.integral_mul_weakGamma_apply_nonneg` (in `GammaTwo.lean`): the
   `_of_core` frontend with `hcore := R2`.

The audit `research/audits/BakryEmeryInteriorRegularityAudit.lean` restates and proves `M0`–`M3`,
`R1` with the exact class and the sign of the tested equation (`A + 1`, i.e.
`⟪A [f], u⟫ = -⟪[f], u⟫`), `R1` in the shape of `hreg`, `R2`, the vanishing of every deficiency
element (`R2'`, from `C2` and `R1`), the non-vacuity of `R2` on smooth classes, `R3` with its full
quantifiers, and that the conditional frontend `_of_localRegularity` is now a consequence; it
prints **23 axiom reports, all standard**, and no `sorryAx`.

## 7. Boundaries

The potential is `C¹` for `R1`–`R2'` and `C^∞` convex for `R3`, as in the earlier frontends; no
`C¹` theorem of `OperatorCore.lean` was weakened or replaced. Not proved and not claimed:
`Γ(P_t f) ≤ P_t Γ(f)` in any form; the `Γ` time interpolation
`s ↦ ∫ (P_s φ) Γ(T̄ (P_{t-s} f)) dν` with the outer semigroup on the test function; the extension
of the weak `Γ₂` inequality from `C_c^∞` tests to `{P_s φ}`; the square and first-order gradient
estimates; the passage from smooth potentials to general log-concave laws; the constant `π`;
Buser; KLS. These are separate obligations and are not advanced by this round. Certificates stay
**26**; the deliberate `KLS/Target.lean` hole is untouched. No new axiom, no `sorry`, no
structure, instance or definition carries a hypothesis.

## 8. Validation

New: `FunctionalInequalities/Analysis/Mollification.lean`,
`FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean`,
`research/audits/BakryEmeryInteriorRegularityAudit.lean`.
Extended: `FunctionalInequalities/KLS/LogConcave/HeatSemigroup/GammaTwo.lean` (new import and
frontend, documentation), `FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean`
(documentation only), `FunctionalInequalities.lean` (two new leaves).
All four Lean modules and the new audit compile with `-DwarningAsError=true`, 0 errors, 0
warnings. `#print axioms` on `R1`, `R2`, `R3` and the four `M` lemmas reports only `propext`,
`Classical.choice`, `Quot.sound`. Default `lake build` (3579 jobs) passes with the single
deliberate `KLS/Target.lean` warning. Progress views are regenerated from a temporary Git index
that preserves the real staging area, and the root `python3 research/verify.py` is rerun at the
**end** of the round, after every tracked edit; its receipt is identified in
`build/audit/interior-regularity/final-snapshot.json`.

| Proved | Interface only (hypothesis visible in the type) | Still an informal plan |
| --- | --- | --- |
| `M0`–`M3`; `R1` interior regularity; `R2` operator core; `R2'` deficiency elements vanish; `R3` heat-flow weak `Γ₂` with only the model hypotheses; `C0`–`C5` of the previous round now unconditional in their conclusions | — (the conditional frontends `_of_core`, `_of_localRegularity` are kept as statements, not as gaps) | `Γ(P_t f) ≤ P_t Γ(f)`, the `Γ` time interpolation with the outer semigroup, the `{P_s φ}` test class, BGL/BV, general-law passage, the constant `π`, Buser, KLS |

## 9. Minimal remaining obligations toward the `Γ` time interpolation

1. ~~`hcore`~~ — **proved** (`R2`), for every `C¹` potential.
2. The time interpolation `s ↦ ∫ (P_s φ) Γ(T̄ (P_{t-s} f)) dν` with the **outer semigroup**
   applied to the test function: `P_s φ` is an `L²` class, not a smooth compactly supported
   function; extending the weak `Γ₂` inequality to the test class `{P_s φ}` is a separate
   obligation (boundedness of `P_s φ`, a representative regular enough for `ℒ (P_s φ)` to be
   tested, integrability of `(ℒ P_s φ) Γ(·)`), not a formal product-rule computation.
3. Only after 2 do the differentiability in `s`, the interchange of derivative and integral, and
   the square and first-order gradient estimates become the next objects.
