# Weighted coarea route exploration

2026-09-15. This round only performs route exploration; **no new theorems are proven, and no modifications are made to any `.lean` library source code**.
No commit, no push, no alteration of historical decisions. Starting HEAD is `2965b32bc79bdb24921c633df12102450eaedcc4`;
starting verification receipt is `20260914T181901.237724Z`, and the fully computed snapshot matches the receipt: 408 files,
SHA256 `c65036cc1bc9362b558864d470ec2c7f10c6dd15faba9d3f0a499b637e396adf`.
The byte-by-byte verification refers to identical SHA256 per file (including deleted items) and consistent full snapshot structure, not merely the HEAD.

## Judgment and Next Step

**Mathematical path is feasible; current libraries cannot assemble coarea.** Recommend proving L12: on any finite-dimensional real inner product space,
for globally Lipschitz real-valued `u`, any Borel set `S`, and any measurable `g : V → ℝ≥0∞`, simultaneously provide
the `AEMeasurable` of the cross-sectional integral and the weighted equality. `S` does not require boundedness, finite volume, or finite perimeter; `g` does not require finite values, integrability, or boundedness. `V` does not impose a non-zero dimension restriction, and the gradient preserves Mathlib's `gradient`.
All specific Lean statements are listed below and in `build/audit/WeightedCoareaRouteStatements.lean`.

The first precise obstacle is **L2: the surface measure of the volume zero set of Lipschitz mappings is almost everywhere zero in each section**.
Rademacher only gives volume zero for non-differentiable sets, and cannot directly establish L2.
L1 provides sufficient and stronger foundational infrastructure: an Eilenberg-type upper bound on sections, expressed by a **measurable upper bounding function**, thus avoiding circularity.
The measurability of sections remains unproven. In particular, one cannot treat an arbitrary function's Lean `lintegral = 0` as a.e. zero;
Without established measurability, such arguments lack the necessary premises.

The second precise obstacle is the **C¹ Whitney first-order jet extension of L6** and the **Whitney–Lusin piecewise splitting of L6a/L7**.
Existing results such as Rademacher, measurable derivatives, piecewise linear approximations, and Egorov do not directly yield a global C¹ function where the function and its derivative are simultaneously exactly equal. Convolution approximation in L¹ does not preserve level sets and thus cannot substitute for this statement.
The area formula proven in this repository only applies to **C¹ graphs**, so it cannot bypass these bridging steps to directly apply to arbitrary Lipschitz level sets.

Suggest starting the next round with the proof of the zero set coverage for **L2** (it suffices to prove the zero-measure special case, without first completing the full L1 with constants), followed by L3–L5; this can independently advance the first raw hole. Then complete L1 and C¹ coarea, and finally handle L6/L6a.
This order does not guarantee that any particular hole will be proven in the next round.

## Back from L12 to three original goals

* Goal T1: In L12 (or earlier L5), take `S = Set.univ`, simplify `univ_inter`, and take the measurable component.
* Goal T2: Similarly take `S = univ`, simplify `Measure.restrict_univ` and `univ_inter`, and take the equality component.
* Goal T3: Directly apply T2/L12 to its `hK` and `hg`; the C¹ assumption does not need to be involved in the proof.
  The original `ContDiff ℝ 1 u` and `SecondCountableTopology V` parameters are retained and cannot be modified or removed during this process.

There is no replacement of the Lipschitz objective with a C¹ objective. C¹ serves as an intermediate step, and L7 and L2 elevate it to the originally required Lipschitz range. The source files for T1–T3 have unchanged full file hashes; file inspection only writes unused named proof arguments as `_` to pass the unusedVariables linter, with unchanged types, quantifier order, and conclusion.

## Phased Dependencies and Proof Design (not yet formalized)

1. **0-dimensional L0.** A finite-dimensional `finrank = 0` is converted to `Subsingleton V`. All gradients are zero, and the image of `u`
   At most one real number. The cross-sectional integral may be `⊤` at this point, but zero elsewhere, hence AEMeasurable and the integral is zero.
   Without using `surfaceMeasure = 0`: This repository natural number subtraction from zero-dimensional `ℋ⁰` is not a negative-dimensional Hausdorff measure.
   The `[Nontrivial V]` branch of L1 begins in dimension one; one-dimensional fibers use `ℋ⁰`, so the counting effect must be preserved.
2. **L1 → L2.** For any set, take a countable covering with vanishing scale and intersect each covering set with `S`;
   On the horizontal axis, replace the image itself with a measurable interval containing `u`, and the length of the interval is controlled by `K × diameter`,
   The layer-wise section cost is `diameter^(n-1)`. The measurable covering cost of `liminf` gives an upper bound `F`, Fatou and covering cost.
   Give `∫ F ≤ C K volume S`. Only require a finite positive dimensional constant C, without claiming the sharp constant 1.
   The dimensional Hausdorff and volume normalization equation has been proven in repository. `K = 0`, empty coverings, and `volume S = ⊤`
   Independent branch handling; the zero set special case by `F = 0` a.e. and pointwise domination yields L2, without measurable choice, without Sard.
3. **L3 → L4 → L5.** The sections of compact sets with respect to continuous `u` are compact. First establish a finite open cover bounded by a strict diameter bound.
   Interface for computing Hausdorff content: the content at each scale is on `t` upper semicontinuous, and its zero-limit equals
   There is currently `μH` (must prove compatibility with the definition of `mkMetric'`, cannot directly assert `μH` itself upper semicontinuous).
   Thus we obtain L3. Borel `S` divides the Lebesgue inner regularity into an increasing union of compact sets and adds a set of measure zero; L2 removes the remainder.
   L4 under measure continuity. For simple weights use finite addition, for general ENNReal measurable weights use an increasing sequence of simple functions.
   And from two-layer monotone convergence we obtain L5, including `g = ⊤`. This path does not rely on L6–L12, nor on the coarea equation.
4. **L8 → L9.** Upgrade the already proven weight-free global C¹ graph area identity to non-negative measurable weights (simple functions,
   (Monotone convergence), then by countable local C¹ extension in open domains and disjoint Borel piecewise, obtain L8.
   Here is a local extension inside an open set, localized by a bump, **independent of Whitney L6 for closed sets**.
   For a regular point choose the unit direction `e` satisfying `Du(e) ≠ 0`, using orthogonal decomposition `V ≃ H × ℝ` and the inverse function theorem,
   Let `Φ(y,s) = (y,u(y+s e))`, whose local inverse is `(y,t) ↦ y+ψ(y,t)e`.
   Need a C¹ graph with level parameter t, not just a fixed level-set graph inclusion relation.
   Use L8 for fixed t; use Mathlib's same-dimensional Jacobian change of variables and Tonelli for volume.
   Compute `|det DΦ| = |Du(e)|` and
   `sqrt(1 + ‖D_y ψ‖²) = ‖gradient u‖ / |Du(e)|`, both sides yield the same non-negative integrand function.
   First compute on countable open pieces, then take disjoint Borel piecewise summation. The measurability of each graph domain and Jacobian must be established simultaneously.
   The parameter space must use the Euclidean norm induced by an inner product / orthogonal isomorphism; it cannot use the sup norm of `Fin n → ℝ`
   Treat directly as Euclidean Hausdorff measure. The C∞ interface in current `Analysis/ImplicitGraph.lean` is not directly applicable;
   Add a C¹ layer, or directly use Mathlib's `ContDiffAt` implicit function interface, without modifying the original public signature.
5. **L1 → L10; L9 + L10 → L11.** Restrict the critical set of C¹ functions to a finite volume ball, at each precision ε,
   Divide using Mathlib's `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` into countably disjoint
   Borel slices. The derivative on each slice is identically zero, so the Lipschitz constant on each slice can be taken as ε.
   Apply L1 and sum over each piece to obtain the integral over the cross-section no more than `C ε volume(ball)`; letting ε → 0 yields L10.
   Use the measurable upper bound of L1 directly, or first extend with Lipschitz restriction on the ball and then use L4.
   L10 is the "section zero measure of the critical part," not the zero measure of the critical value set; the latter cannot be assumed in high dimensions.
   Multiply by measurable weights on zero-measure sections, together with the regular part L9 to obtain L11. The auxiliary `v j` does not require global Lipschitz.
   So L11 deliberately does not include this assumption.
6. **L6a + L6 → L7.** Rademacher gives a.e. differentiability; `measurable_fderiv` and a measurable encoding of the first-order difference-quotient remainder
   yield countably many compact jet pieces covering almost everywhere, through simple-function approximation on finite-volume sets, Egorov, and inner regularity,
   On each piece, the derivative is continuous and the remainder is uniformly o(distance), i.e. L6a. Here, Lusin-type compact set extraction needs to be implemented, existing library
   The Lusin–Souslin (analytic set separation/image measurable) is not this theorem. Then L6 on each extension, differentiates compact pieces to make them
   Disjoint, obtain L7. The equality of derivatives is explicitly written in the conclusion, not inferred from the equality of values on an arbitrary sparse set.
7. **L2 + L7 + L11 → L12.** Let `N = (⋃j S j)ᶜ`. Ignore the volume-null N on the left; on the right
   **Use the original Lipschitz u** apply L2 to N. On each piece `u = v j` makes the level sets identical, and equal derivatives make
   Gradients are equal. For measurable weights on each piece use L11, then use countable disjoint addition and Tonelli to obtain the global equality; L5 is independent.
   Given measurability. Throughout, no finite value subtraction is used, avoiding `⊤ - ⊤`, and no requirement for `g` to be integrable.

Route selection refers to Section 3 of Jerrard's lecture notes: there, the integral over cross sections, the measurability of cross sections over compact sets, and the C¹/Lipschitz reduction are separately addressed, and the role of Whitney extension in the subsequent step is pointed out. Here, it is used merely to verify the route at the level of the path. The decomposition of Lean interfaces, the gaps, and the implementation estimates are independent analyses of the current repository, and do not represent the completed formalization in the lecture notes. [Original lecture notes](https://www.math.toronto.edu/rjerrard/1501/notes/week5-6.pdf).

## List of required lemmas

The number of rows in the following table is an approximate number of new Lean proofs, excluding reused existing modules, and does not represent fulfillment of commitments.
"None" means that the current Mathlib pin does not have the complete interface; "existing ingredients" does not imply that the lemma has been proven.
The exact statements for each entry are listed below by number; no implicit finiteness or non-degeneracy conditions are assumed.

| Number | Content and Dependencies | Existing in Mathlib (complete interface) | Estimated Lines | Risk |
|---|---|---|---:|---|
| L0 | zero-dimensional joint conclusion | none; subsingleton, real number singleton has zero measure and a.e. congruence is usable | 30–60 | low; `0 * ⊤` and H⁰ |
| L1 | Eilenberg measurable upper bound; Hausdorff cover, Fatou, normalization | None; `MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum` has cover limit upper bound, but no estimate for integral over level parameter | 400–800 | High; double cover, K=0, n=1, non-measurable S |
| L2 | the a.e of zero measure sets. Zero section; L1 + L0 | none | 20–50 (direct zero set cover approx 200–350) | medium; cannot be achieved solely with Rademacher |
| L3 | Borel measurable section of compact set | none; `MeasureTheory.OuterMeasure.mkMetric'.eq_iSup_nat` has scale limit, missing open cover content parameter upper semicontinuous interface | 200–400 | high; cannot substitute μH/content; n=1 |
| L4 | Borel section a.e. measurable; L2 + L3 + inner regularity | None; `MeasurableSet.exists_isCompact_isClosed_sdiff_lt` as existing material | 80–160 | Medium; infinite volume by countable exhaustion |
| L5 | measurable weight version; L4 + approximation by simple functions | none; `MeasureTheory.lintegral_iSup` available | 80–150 | medium; does not assume inner measure SFinite |
| L6 | C¹ extension of first-order Whitney jet on compact sets | **None** | 800–1600 | High; new Whitney cover/splitting unification and boundary differentiability proof |
| L6a | a.e. extraction of compact jets for differentiable Lipschitz functions | **None**; `LipschitzWith.ae_differentiableAt`, `measurable_fderiv`, `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`, `exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt` are only raw materials | 250–500 | High; Lusin-type precise uniformization and measurable encoding of remainder |
| L7 | countable C¹ piecewise; L6a + L6 | none | 80–160 | medium; must simultaneously preserve derivative equality |
| L8 | weighted area of open domain graphs | none; global unweighted version already exists in repository `FunctionalInequalities.Analysis.hausdorffNormalized_image_graphMap` | 180–350 | medium; open domain and countable localization |
| L9 | C¹ regular open domain coarea; L8 + parametrized implicit function + Jacobian | None; `ContDiffAt.implicitFunction`, `ContDiffAt.contDiffAt_implicitFunction`, `ContDiffAt.eventually_apply_eq_iff_implicitFunction`, `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul` available | 500–1000 | High; family of graphs, determinants and Hausdorff normalization |
| L10 | C¹ critical part transverse section zero measure; L1 + linear approximation piecewise | None; `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` available | 150–300 | High; cannot invoke C∞ Sard as substitute |
| L11 | Weighted coarea for any C¹ function; L9 + L10 | None | 80–160 | Chinese; no global Lipschitz bound |
| L12 | General Lipschitz joint conclusion; L0/L2/L5/L7/L11 | None | 120–240 | Medium; uses antiderivative for N, handles infinite weights |
| T1/T2/T3 | Raw three goals; L12 takes univ (T1 can be derived from L5) | None; all current WIP declarations contain direct proof holes | Each 3–10 | Low; can only be filled after all premises are proven |

The row range applies to this selected route, without claiming it has the minimum cost. A more direct alternative route is to generalize the existing C¹ area formula to an area formula on Lipschitz/differentiable piecewise domains, paired with a double Lipschitz regular piecewise structure; this would avoid L6, but requires separate proof of the "codimension-one area formula for differentiable pieces" and critical cross-section estimates, and one cannot claim that Mathlib's same-dimensional Jacobian change-of-variables already establishes this result. This round does not regard undecomposed alternative routes as implementable shortcuts. The BV route still requires proof of finite perimeter, reduced boundary/level-set identification, and BV coarea; the current choice does not introduce this additional infrastructure.

## Is measurability worth proving separately in this round?

The L2–L5 path shows it is independent of the coarea formula, but is not a cheap parameter integral wrapper on the current library.
The actual signature of `Measurable.lintegral_prod_right'` requires `[SFinite ν]`.
The `(n-1)`-dimensional Hausdorff measure on a positive-dimensional environment V cannot satisfy this requirement: one can take uncountably many pairwise disjoint parallel hyperplane sheets, each with positive finite surface area; the SFinite measure cannot have such a family of disjoint positive measure sets.
At `u = constant`, a certain level or even the entire ambient space, local finiteness cannot be imposed on all fibers.
Thus, this round does not claim to prove T1, nor does it prove a weak version under additional SFinite/regular value assumptions as a "filling of a gap".
Although the global weighted subcases of L0 or L8 are relatively cheap, they fail to close any of the three targets; this round delivers complete statements and obstacle localization, without introducing new auxiliary declarations. The axiomatic audit of new results is empty (no new results), not "proven coarea".

## Placement, Verification, and Boundaries

Subsequent L6/L6a/L7 should be placed in `Analysis/WhitneyExtension.lean`, `Analysis/LipschitzC1Pieces.lean`,
depending only on Mathlib; the underlying coverage of L1/L2/L3 can be expressed in `Analysis/HausdorffSlicing.lean` using raw `μH`
formulation, then normalized packaging followed by dependency on existing `KLS/Geometry/SurfaceMeasure`. L8 extends the responsibilities of existing `Analysis/AreaFormula`,
L9–L12 are placed in independent `Analysis/Coarea.lean`, and C¹ KLS packaging remains at the appropriate Geometry layer.
These are merely future module suggestions; no modules were created, no declarations migrated, no signature modifications, or no certificate/leanok scope changes in this round.

* `WeightedCoareaRouteStatements.lean`: 17 `#check`, only import/open and proposition checking,
  No declarations, no proofs, no placeholder axioms, compiled with `-DwarningAsError=true`.
* `WeightedCoareaInfrastructure.lean`: 20 API with `#check`, equally strictly compiled; actual signature
  Recorded in `build/audit/coarea-infrastructure.log`, including the SFinite condition for parametric integrals.
* Retrace `AreaFormulaAudit`, `CheegerInfimumAudit`, `MinkowskiConstantAudit`,
  `SuperlevelSardScope`, `SmoothSardAudit`, `SmoothSardRouteStatements`, all strictly compiled;
  Three WIP files were actually compiled successfully one by one, with the direct proof holes in the diagnostics respectively **3/3/5**, total **11**.
* Default `lake build` and root directory `python3 research/verify.py` are passed. Final verification receipt is
  `build/verification/latest.json`, must be exactly equal to the final full code snapshot.
  Evidence JSON is `research/explorations/2026-09-15-weighted-coarea-route.json`, recording input snapshot,
  Source/code/statement/log hash; ignore the final verification save in the directory `build/audit/coarea-final-snapshot.json`,
  Avoid creating cyclic hashes for verification receipts. `build/audit` Not present in regular source code snapshots, thus bound separately by evidence JSON.

Clearly incomplete: sharp C^(finrank) `Analysis.sard` (no downstream consumers); two Analysis coarea holes and Isoperimetry's C¹ hole; `smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and two Cheeger constants equal.
C∞ Sard and migrated WIP's `ae_exists_superlevel` remain without `sorryAx`, but the entire chain is not closed.
Certification still 24; perimeter infrastructure still missing.

## Exact Lean statements

The following corresponds line by line to the file check; L0–L12 (including L6a) are all pending, T1–T3 are the original pending goals.
General import/open matches the file check; all instances are explicitly listed, with no new assumptions hidden in sections.

### L0

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Subsingleton V] (u : V → ℝ) {g : V → ℝ≥0∞}, Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) volume ∧
    (∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L1

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [Nontrivial V], ∃ C : ℝ≥0, 0 < C ∧
    ∀ {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzOnWith K u S →
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (∀ t, KLS.surfaceMeasure V (S ∩ {x | u x = t}) ≤ F t) ∧
      (∫⁻ t, F t ∂(volume : Measure ℝ)) ≤ (C : ℝ≥0∞) * (K : ℝ≥0∞) * volume S)
```

### L2

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {N : Set V}, LipschitzOnWith K u N →
    (volume : Measure V) N = 0 →
    ∀ᵐ t ∂(volume : Measure ℝ), KLS.surfaceMeasure V (N ∩ {x | u x = t}) = 0)
```

### L3

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {S : Set V}, Continuous u → IsCompact S →
    Measurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t})))
```

### L4

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V}, LipschitzWith K u → MeasurableSet S →
    AEMeasurable (fun t : ℝ ↦ KLS.surfaceMeasure V (S ∩ {x | u x = t}))
      (volume : Measure ℝ))
```

### L5

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} {S : Set V} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ))
```

### L6

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ Set.EqOn v f S ∧
      ∀ x ∈ S, fderiv ℝ v x = F x)
```

### L7

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ (S : ℕ → Set V) (v : ℕ → V → ℝ),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j ↦ Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x)
```

### L8

```lean
#check (∀ {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (ι : H →ₗᵢ[ℝ] V) {e : V}
    {O S : Set H} {v : H → ℝ} {g : V → ℝ≥0∞},
    ‖e‖ = 1 → (∀ y : H, ⟪ι y, e⟫ = (0 : ℝ)) →
    IsOpen O → ContDiffOn ℝ 1 v O → MeasurableSet S → S ⊆ O → Measurable g →
    (∫⁻ x in Analysis.graphMap ι e v '' S, g x
        ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))) =
      ∫⁻ y in S, ENNReal.ofReal (Analysis.graphJacobian (gradient v y)) *
        g (Analysis.graphMap ι e v y) ∂(volume : Measure H))
```

### L9

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {O S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    IsOpen O → ContDiffOn ℝ 1 u O → (∀ x ∈ O, fderiv ℝ u x ≠ 0) →
    MeasurableSet S → S ⊆ O → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L10

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ}, ContDiff ℝ 1 u →
    ∀ᵐ t ∂(volume : Measure ℝ),
      KLS.surfaceMeasure V ({x | fderiv ℝ u x = 0} ∩ {x | u x = t}) = 0)
```

### L11

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {g : V → ℝ≥0∞},
    ContDiff ℝ 1 u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L12

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞},
    LipschitzWith K u → MeasurableSet S → Measurable g →
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V)) (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### L6a

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u →
    ∃ S : ℕ → Set V, (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧
      ∀ j, IsCompact (S j) ∧ (∀ x ∈ S j, DifferentiableAt ℝ u x) ∧
        ContinuousOn (fderiv ℝ u) (S j) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ x ∈ S j, ∀ y ∈ S j, ‖y - x‖ < δ →
            ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ ε * ‖y - x‖)
```

### T1

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0} (_ : LipschitzWith K u)
    {g : V → ℝ≥0∞} (_ : Measurable g) ,
    AEMeasurable (fun t : ℝ ↦ ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ))
```

### T2

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {u : V → ℝ} {K : ℝ≥0}
    (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ))
```

### T3

```lean
#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    {u : V → ℝ} (_ : ContDiff ℝ 1 u)
    {K : ℝ≥0} (_ : LipschitzWith K u) {g : V → ℝ≥0∞} (_ : Measurable g) ,
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(surfaceMeasure V) ∂(volume : Measure ℝ))
```
