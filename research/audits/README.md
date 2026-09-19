# Versioned infrastructure audit sources

These Lean clients are source evidence referenced by `research/tasks.json`. Keep them in Git:
CI validates their paths and SHA-256 hashes from a clean checkout. Generated logs and local
verification receipts belong under the ignored `build/` directory.

The files were copied byte-for-byte from the local coarea audit sources on 2026-09-15, preserving
the recorded evidence hashes. Their comments describe the corresponding historical audit rounds.
`RegularCoareaAudit.lean`, the client of the regular open-domain coarea round, was copied here in
the same way once the omission was noticed: its round's evidence record
`research/explorations/2026-09-15-regular-coarea.json` still binds the original local path, and
the bytes are unchanged, so both hashes agree.
`WeightedCoareaRouteStatements.lean` checks proposition types only; it does not prove them.
`LevelSetMeasurableAudit.lean` deliberately reports the axioms of still-open WIP results as well as
proved results. These clients are not ledger certificates and are not library-root imports.

After building the relevant library modules, run any client from `formalization/`, for example:

```sh
lake env lean -DwarningAsError=true ../research/audits/OpenGraphAudit.lean
```

`FirstOrderJetAudit.lean` checks the **necessity** of the uniform first-order jet remainder
condition, with a compact closed-ball square example and four standard-only axiom reports.
Its L6 `#check` is a proposition type check, **not an extension proof**.

`WhitneyExtensionAudit.lean` audits the **boundary gluing** part of L6, including the construction
that overwrites an off-set candidate on the compact set. It has 13 standard-only axiom reports
and clients for the empty set, a singleton with arbitrary derivative, a zero-dimensional domain,
and a candidate taking the wrong value on the set. Its final `#check` pins the construction
that was unproved in that historical round; it is now proved by the new client below.

`WhitneyConstructionAudit.lean` proves the **original complete L6 proposition**, including all
its instances and assumptions. It audits the quantitative cover, scaled bumps, normalized
partition, complement construction and full extension, with 13 standard-only axiom reports.
Clients cover empty sets, singleton jets with arbitrary ambient derivative, zero dimension and
a square jet on an infinite compact interval. Earlier clients retain their historical comments.
`LipschitzCoareaAudit.lean` proves the original **L6a, L7, L12 and T2** statements, preserving
their full proposition text. Its 15 standard-only axiom reports include a norm function proved
not differentiable at zero, a constant function with infinite weight, and zero dimension.
It imports the new hole-free coarea module; it does not import the work-in-progress files.

`LipschitzCoareaMigrationAudit.lean` audits the **migration of the original `T2` entry point**
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` out of
`KLS/WIP/AnalyticPrerequisites.lean` into `KLS/Geometry/Coarea/Lipschitz.lean`. It imports the new
module and **both** work-in-progress files, so its sixteen reports come from one environment:
twelve are standard-only — the migrated declaration, its `L12` source `KLS.coarea_of_lipschitz`,
the two previously migrated neighbours, and eight clients including a verbatim restatement
discharged through named arguments, the original `T2` proposition text, a function not
differentiable at zero, an identically infinite weight and a zero-dimensional space — while the
sharp `C^(finrank)` `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero` and the two Cheeger
comparisons still report `sorryAx`. The machine `pp.all` signature comparison for that migration
is in `build/audit/t2-migration/`.

`LevelSetMeasurableAudit.lean` and `IsoperimetryCoareaAudit.lean` gained an import of
`KLS/Geometry/Coarea/Lipschitz.lean` in the same round, so that the migrated name still resolves;
their client statements are unchanged and two reports in each stopped carrying `sorryAx`.

`LocallyLipschitzCoareaAudit.lean` audits **L13**, `KLS.coarea_of_locallyLipschitz`: the weighted
coarea formula under local Lipschitz continuity alone. Its 10 standard-only reports include the
verbatim statement, a re-derivation of the `L12` statement that never names `coarea_of_lipschitz`,
a re-derivation of the `L11` statement that never names `coarea_of_contDiff`, and the witness
`x ↦ x² + ‖x‖`, proved there to be neither globally Lipschitz for any constant nor differentiable
at `0`, so the generalization is strict. It imports no work-in-progress file.

`CoareaJacobianAudit.lean` audits `Analysis.coareaJacobian`, the linear-algebra layer of the
codimension-`m` coarea program. Its 17 standard-only reports cover the defining identity
`J² = det (L ∘ Lᵀ)` on the target, the bridge `coareaJacobian (fderiv ℝ u x) = ‖gradient u x‖`
that makes the proved scalar theory the `m = 1` case, the regular-set characterization
`J ≠ 0 ↔ surjective`, and the identity map, zero map, subsingleton target and a Euclidean
projection. **It proves no coarea formula.**

`LinearAreaFormulaAudit.lean` audits step one of the codimension-`m` program: the linear area
formula in this repository's normalized convention, with the norm determinant as the exact volume
factor, and the fibre statement that a translated isometric slice carries **exactly** Lebesgue
measure on its parameter space. Its 14 standard-only reports include the top-dimensional
consistency check against the already proved `hausdorffNormalized_finrank_eq_volume`, a
zero-dimensional parameter space, a degenerate zero map, and the count
`finrank (ker L) = n - m` for a surjective `L`. **It proves no coarea formula and no `C¹` area
formula.**

`GraphJacobianAudit.lean` audits step two of the codimension-`m` program, its linear layer: the
Gram operator of a graph map is `1 + Aᵀ A` on the parameter space, so the volume factor in
arbitrary codimension is `√det (1 + Aᵀ A)`, independent of the ambient embedding, and the
codimension-one case agrees exactly with the repository's existing `graphJacobian`. Its 11
standard-only reports include a flat graph, a subsingleton target and a zero-dimensional parameter
space. **Its final `#check` is a proposition type-check of the still open nonlinear (Federer) area
formula, not a proof of it.**

`AreaFormulaRouteStatements.lean` checks the **nine route obligations** for the nonlinear
(Federer) area formula as proposition types only; like `WeightedCoareaRouteStatements.lean` it
declares nothing, proves nothing and adds no placeholder axiom. Its round recommends the graph
route and localizes the obstruction of the textbook route.

`NormDetContinuityAudit.lean` discharges route obligation **`A1`**: it reproduces the two `A1`
statements of `AreaFormulaRouteStatements.lean` verbatim and proves them, records that the proved
measurability needs **no** differentiability hypothesis at all, and checks consistency with the
scalar theory by deriving measurability of `‖gradient u x‖`. 13 standard-only reports. The route
statements file itself is left byte-unchanged as the previous round's dated evidence.

`VectorGraphAudit.lean` audits the first part of obligation **`B1`**: the `C¹` infrastructure for
the graph of a vector-valued slope — the explicit left inverse that the general route `A3` lacks,
injectivity with no hypothesis on the slope, the derivative, image measurability, linear
approximation, and the linear case of `B1`, which needs no shear argument. 20 standard-only
reports, including codimension zero, a constant slope and a zero-dimensional parameter space.
**The area formula itself is not proved.**

`VectorGraphSandwichAudit.lean` audits the fourth phase of `B1`: the Pythagorean identity across
the two orthogonal factors, the expansiveness it gives the graph map — the lower-bound input the
general route has to obtain from an inverse it does not have — injectivity of the linear model, the
two sandwich estimates, and the approximating partition that feeds the fifth phase. 15
standard-only reports. Its `exact_at_zero` client is the sandwich degenerating correctly at
`ε = 0`, **not** the area formula.

`VectorGraphAreaAudit.lean` audits the **codimension-`m` area formula for `C¹` graphs**, the
completion of obligation `B1`. It discharges route statement `B2` verbatim, proves the corrected
`B1` (raw Hausdorff measure on both sides), and records that the route's own `B1` mixed the two
normalizations and is false as written for `k ≥ 2`. 10 standard-only reports, including the whole
parameter space and a zero-dimensional one. It is the area formula for a **graph**, not the Federer
area formula `A0`.

`CoareaGraphJacobianAudit.lean` audits the **fibre Jacobian** of the codimension-`m` regular case:
the linear identity `coareaJacobian L = normDet (L ∘ κ) · normDet (graphMapLinear ι κ A)` and its
`C¹` form along a level family, which is the codimension-`m` analogue of
`abs_deriv_mul_norm_gradient` and literally that identity when `m = 1`. Its reports include
a zero-dimensional parameter space, a level family on the whole space (so no finiteness
is available), and the regular-point data showing the hypotheses are automatic where the
differential is surjective. Its `fails_without_codimension` and `necessity` clients **exhibit** the
failure of the identity when `finrank K = finrank W` is dropped, rather than asserting it.
It also records a **second route-statement error**: obligation **`A0`** in
`AreaFormulaRouteStatements.lean` pairs the raw `μH` with Lebesgue measure exactly as `B1` did, and
`route_A0_false` **proves it false** with the identity map of the plane on the closed unit ball,
the two sides differing by `4 / π`; `A5` writes the same mis-pairing on both sides, so it is not
falsified by it. The route statements file stays byte-unchanged.
**No coarea formula is proved**: the codimension-`m` charting, the fibrewise `m`-dimensional change
of variables and the patching are all still missing. 30 standard-only reports.

`VectorRegularChartAudit.lean` audits the **codimension-`m` parametric implicit-function
charting**: the level-graph family, its regular-point form whose only hypothesis is
`coareaJacobian (fderiv ℝ u x₀) ≠ 0`, the identification of each fibre with a graph, and the two
interfaces — the proved `B2` measuring a fibre (weight one only) and the previous round's fibre
Jacobian identity holding on the whole chart. 25 standard-only reports, including a zero-dimensional
parameter space, a **zero-dimensional target** where every point is regular, the whole space as
domain, and the full `m = 1` chain: a scalar `IsGraphSplitting` **is** a vector splitting with
one-dimensional normal factor, and the scalar hypotheses `gradient u x₀ = c • e`, `c ≠ 0` produce
the family `u (ι y + ψ (y, t) • e) = t` that the proved scalar
`Analysis.setLIntegral_coarea_graph_family` consumes. **No coarea formula is proved.**

`VectorFiberIntegralAudit.lean` audits the **fibrewise `m`-dimensional change of variables**: the
missing between-different-spaces change of variables with `LinearMap.normDet` as the volume factor,
the codimension-`m` vertical substitution, its ambient transport, and the ambient side of the local
coarea equality. 16 standard-only reports, including a zero-dimensional fibre, the whole space as
domain, a linear isometry preserving measure as a self-consistency check, the **verbatim**
derivation of the repository's proved `Analysis.setLIntegral_image_verticalMap` as the `m = 1` case,
and `equal_dimension_necessary`, which **exhibits** the failure of the change of variables when the
dimensions differ rather than asserting it. **No coarea formula is proved.**

`VectorLocalCoareaAudit.lean` audits the **weighted codimension-`m` graph area formula** and the
**local coarea equality** it completes. 15 standard-only reports, including the verbatim recovery of
`B2` as the weight-one case, the whole parameter space, an identically infinite weight, a
zero-dimensional parameter space, a zero-dimensional target where every point is regular, and the
`m = 1` recovery of the repository's proved `Analysis.setLIntegral_image_graphMap` together with the
identification of the ambient density as the gradient norm. **This is not the codimension-`m`
regular coarea formula**: codimension-`m` weighted slice measurability and the countable patching
are not proved, and the audit says so.

`VectorRegularCoareaAudit.lean` audits the **codimension-`m` weighted slice measurability** and the
**codimension-`m` regular coarea formula** it assembles. 11 standard-only reports, including the
empty Borel set, the whole space, an identically infinite weight, a zero-dimensional target where
every point is regular, and `scalar_L9`, which reproduces the statement of the proved
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` **verbatim** and discharges it from the
codimension-`m` theorem; the last report is that scalar `L9` itself, for comparison. The audit
records that the slice measurability here needs the differential to be surjective — the
codimension-`m` Eilenberg slicing inequality is not proved — so **the general codimension-`m` coarea
formula, which must treat the critical set, remains open**.

`VectorHausdorffSlicingAudit.lean` audits the **Eilenberg slicing inequality in codimension `m`**.
15 standard-only reports, including `K = 0`, `d = 0`, a zero-dimensional target, null slicing, and
`codimension_one_majorant`, which reproduces the proved `Analysis.exists_measurable_majorant`
**verbatim, constant `2 K` included**, and discharges it from the codimension-`m` theorem; the last
report is that scalar bound itself, for comparison. The audit records that this is **not** slice
measurability: codimension-`m` compact-slice measurability is not generalized here, so the critical
case and the general codimension-`m` coarea formula remain open.

`VectorSliceMeasurableAudit.lean` audits **codimension-`m` compact-slice measurability** and the
**unconditional weighted slice measurability** it completes. 18 standard-only reports, including a
constant map — whose differential is nowhere surjective, so the **critical** case is witnessed — an
identically infinite weight, a zero-dimensional target, and the `m = 1` recovery of the proved
`Analysis.measurable_hausdorffMeasure_inter_levelSet` and
`KLS.aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn`; the last two reports are those scalar
statements themselves, for comparison. The audit records the one honest difference, the extra
`1 ≤ finrank V` in the open-domain recovery, and that **this is not a coarea formula**.

`VectorCriticalSliceAudit.lean` audits the **codimension-`m` vanishing-derivative slicing** and the
coarea formula it extends to the whole space under a no-intermediate-rank hypothesis. 17
standard-only reports, including a constant map, a subsingleton target where every derivative
vanishes, the `m = 1` recovery of the proved `L10` and `L11`, and `rank_deficient_witness`, which
**exhibits** the gap: a rank-one map of the plane whose derivative is nowhere zero and nowhere
surjective, so the vanishing-derivative set is empty while the critical set is everything. The last
two reports are the scalar `L10` and `L11` themselves, for comparison. **No Sard theorem is
claimed**, and the general codimension-`m` coarea formula remains open.

`RankDeficientRouteStatements.lean` checks the route obligations for the rank-deficient part of
the codimension-`m` critical set as proposition types only — **thirteen numbered items `R0`–`R10`,
`N1`, `N2`, written as fifteen `#check`s**, because `R1` and `R3` each have two halves; like
`AreaFormulaRouteStatements.lean` and `WeightedCoareaRouteStatements.lean` it declares nothing,
proves nothing and introduces no placeholder axiom, and **a proposition that type-checks is not a
proof**. `R0` is the target — the rank-deficient part of almost every level is `ℋ^k`-null — and
`R1`–`R10` are the steps of an iterated-slicing route: slice first along the `r` directions where
the differential is already surjective, where the proved regular coarea formula applies, then apply
the Eilenberg bound inside a fibre along the `m − r` surviving directions, where the exponent
finally matches. `N1` and `N2` are diagnostics rather than steps: they state the wrong exponent the
one-step method yields, and that the right-hand side becomes `∞` if the exponent is simply lowered.
**Nothing in this repository proves any of the fifteen.** Its local import closure is 28 modules
with no work-in-progress file.

`RankStratificationAudit.lean` audits the **rank stratification and the kernel lemma**, that is
route obligations **`R1` and `R2` only**. Its 20 standard-only reports include the three
propositions of `RankDeficientRouteStatements.lean` copied **verbatim** and discharged
(`route_R1_measurable`, `route_R1_decomposition`, `route_R2`), the kernel form the route consumes,
a **counterexample showing the dimension hypothesis of `R2` is necessary** — the identity of the
plane composed with the first coordinate functional, where the composite is surjective but the
kernels differ — four boundary cases (zero-dimensional target, zero-dimensional domain, a stratum
index above the target dimension, a zero-dimensional projection target), a strengthening that needs
no finite-dimensional target, and the `m = 1` collapse together with the `m = 1` case of the
still-open `R0` **derived** from the proved vanishing-derivative slicing. **`R0`, `R3`–`R10`, `N1`
and `N2` remain unproved and the rank-deficient part of the codimension-`m` coarea critical set
remains open**; no coarea formula, slicing statement or Sard theorem is proved there. Its local
import closure is 29 modules with no work-in-progress file.

`RightInverseBoundAudit.lean` audits the **approximate right inverse**, that is route obligation
**`R3` only**, in both versions. Its 16 standard-only reports include the two propositions of
`RankDeficientRouteStatements.lean` copied **verbatim** and discharged (`route_R3_pointwise`,
`route_R3_uniform`), strengthenings recording that neither version needs an inner product or a
finite-dimensional domain, the core estimate with **no** surjectivity, and three boundary cases
(zero-dimensional target, linear isomorphism, constant map). Two reports are deliberately careful
about what surjectivity buys: `no_right_inverse` shows the rank-one projection of the plane admits
none, while `pointwise_conclusion_does_not_imply_surjective` shows the **pointwise conclusion does
not characterize surjectivity** — the zero map satisfies it with `C = 0` — and
`uniform_constant_degenerates` shows the **uniform** constant really does blow up as a family
approaches a non-surjective map. **`R0`, `R4`–`R10`, `N1` and `N2` remain unproved** and the
rank-deficient part of the codimension-`m` coarea critical set remains open. Its local import
closure is 2 modules with no work-in-progress file.

`TangentialLipschitzAudit.lean` audits the **tangential small-Lipschitz estimate**, that is route
obligation **`R4` only** — the step the route turns on. Its 10 standard-only reports include the
route proposition copied **verbatim** and discharged (`route_R4`), a strengthening recording that
`R4` needs no inner product, measure, completeness or finite-dimensionality,
`ker_hypothesis_necessary` — which **exhibits** the failure of `R4` when only the `R2` hypothesis is
dropped, with the `R3` hypothesis still holding — `zero_model_recovers_vanishing_derivative`, which
records that on the rank-zero layer `R4` returns the already proved situation and **adds nothing**,
three boundary cases, and the corollary combining `R2`, `R3` and `R4` on a rank stratum, which is
**not `R7`**: no measure, Hausdorff dimension, slice or approximating partition appears in it. The
`R3` hypothesis is **not** claimed necessary; it supplies the constant. **`R0`, `R5`–`R10`, `N1`
and `N2` remain unproved** and the rank-deficient part of the codimension-`m` coarea critical set
remains open. Its local import closure is 3 modules with no work-in-progress file.

`RegularFibreFiniteAudit.lean` audits **route obligation `R5` only**: at almost every level the
fibre of a regular `C¹` map meets a relatively compact piece in a set of finite `ℋ^{n−r}` measure.
Its 8 standard-only reports include the route proposition copied **verbatim** and discharged
(`route_R5`), both directions of the normalized-versus-raw finiteness transfer, the empty piece, and
`relative_compactness_necessary`, which **exhibits** the failure without that hypothesis: the first
coordinate functional of the plane on `S = univ` is a submersion everywhere, yet every fibre is a
full line of infinite `ℋ^1` measure. `R5` is a corollary of the proved regular coarea formula and
**extends its applicability by nothing**; it says nothing about the critical set of `v`.

`TargetSplitFubiniAudit.lean` audits **route obligation `R6` only**: a set whose almost every
first-coordinate slice is null is null. Its 6 standard-only reports include the route proposition
copied **verbatim** and discharged (`route_R6`), an instantiation along
`Submodule.orthogonalDecomposition` confirming that the abstract splitting is directly usable for
the route's intended decomposition, the **converse** direction so that `R6` is not mistaken for the
easy half, and the empty set. **`R0`, `R7`–`R10`, `N1` and `N2` remain unproved** and the
rank-deficient part of the codimension-`m` coarea critical set remains open. The local import
closures are 22 and 1 modules, neither containing a work-in-progress file.

`StratumSlicingRouteStatements.lean` states the two sub-obligations `R7b`, the per-scale bound, and
`R7c`, the limit, as proposition types only, declaring nothing and proving nothing. Both were open
when it was written and **both are now proved** in `Analysis/RankDeficient/StratumSlicing.lean`; a status note at
the top records that, and the two propositions are unchanged.

`StratumSlicingAudit.lean` audits **obligation `R7`, which is proved**: `route_R7` copies it
**verbatim** from `RankDeficientRouteStatements.lean` and discharges it. Its 16 standard-only
reports also cover the pieces — the **local package**, which assembles `R2`, `R3` and `R4` into one
neighbourhood carrying a single tangential Lipschitz constant valid for every stratum point in it
(the uniformity over the points is the difficulty, since `R4`'s constant depends on each piece's
linear model), the **integral form of the target splitting**, and the per-scale bound itself. `R7`
is a statement about **one stratum in one neighbourhood**: **`R0`, `R8`, `R9`, `R10`, `N1` and `N2`
remain unproved**, `R0` still needing `R8` and the finite union over the strata, and the
rank-deficient part of the codimension-`m` coarea critical set remains open.

`RankDeficientCoareaAudit.lean` audits the **last three obligations**, `R8`, **`R0`** and **`R9`**,
copied **verbatim** from `RankDeficientRouteStatements.lean` and discharged. Its 14 standard-only
reports also include `strictly_extends_conditional`, which derives the previously proved conditional
coarea formula from the new unconditional one; `rank_deficient_witness_now_covered`, which shows the
rank-one projection of the plane — the witness that the old hypothesis fails at every point — is
covered by `R0`; `no_sard_claimed`, recording that `R0` is about the critical set **inside a level**
and asserts nothing about the set of critical *values*; a zero-dimensional target; and the `m = 1`
recovery of the proved scalar `L10` and `L11`, each with the extra `1 ≤ finrank V` the
codimension-`m` bookkeeping forces. **The rank-deficient gap of the codimension-`m` coarea program
is closed**; `R10`, `N1` and `N2` remain unproved, and **no Sard theorem is proved**.

`EquidimensionalSardAudit.lean` audits **obligation `R10`, which is proved**: `route_R10` copies it
**verbatim** from `RankDeficientRouteStatements.lean` and discharges it. Its 13 standard-only reports
also record where `R10` sits. It is **not a Sard theorem and not progress on the route**:
`r10_reaches_only_dimension_one` shows the entire overlap with the direct hole `Analysis.sard` is
`finrank ℝ V = 1`, `sard_dimension_one_recovered` carries that recovery out — a case
`Analysis.sard_of_finrank_le_one` already proved unconditionally from the same Mathlib lemma — and
for `n ≥ 2` nothing is claimed; the sharp finite-regularity Sard hole is untouched.
`equidimensional_R0_of_R10` and `equidimensional_R10_of_R0` derive `R10` and the `n = m` reading of
`R0` from each other, which is a genuine cross-check because `Analysis/Sard/Equidimensional.lean`
imports no part of the rank-deficient route. The boundary cases — two zero-dimensional spaces, a
constant map together with `constant_map_critical_everywhere` showing that case is not vacuous, and
`n = m` with an everywhere invertible differential — are all checked.

`ExponentObstructionAudit.lean` audits the route's two diagnostics. **`N1` is proved**: `route_N1`
copies it **verbatim** from `RankDeficientRouteStatements.lean` and discharges it from
`Analysis/RankDeficient/ExponentObstruction.lean`. Proving it is **not progress on the route** — `N1` is the
obstruction itself, whose exponent is `k + r` and not `k` (`N1_exponent_is_k_add_r`), and for
`r ≥ 1` a `μH[k + r]`-null statement implies nothing about `μH[k]`, where a set of positive Lebesgue
measure already has infinite measure (`N1_null_at_higher_exponent_says_nothing_at_k`). Its side
condition `0 < finrank ℝ W₂` is necessary: `N1_needs_positive_codimension` refutes `N1` with that
hypothesis deleted, using a zero-dimensional target where the Eilenberg constant is `1`.
**`N2` is proved false as written**: `N2_counterexample` exhibits the zero-dimensional space, where
the truncated exponent `finrank ℝ V - r` collapses to `0` and `μH[0]` of the one set of nonzero
volume is `1`, not `⊤`, and `route_N2_is_false` derives the contradiction from the `Type` instance of
the route proposition, which its `Type*` version implies. The repair itself lives in the module, as
`Analysis.hausdorffMeasure_finrank_sub_eq_top`: `N2` with `0 < finrank ℝ V` added, necessary by the
counterexample and free wherever the route appeals to `N2`, which is what the client's
`N2_repair_is_free_on_the_route` records. Both side-condition counterexamples share the single
zero-dimensional abbreviation `Pt`. 11 standard-only reports; local import closure 5 modules, no
work-in-progress file.

`SharpSardRouteStatements.lean` checks the route obligations for the **sharp finite-regularity
Sard theorem** `Analysis.sard` — the one direct hole of `KLS/WIP/AnalyticPrerequisites.lean` — as
proposition types only: **eleven `#check`s**, three referencing proved declarations
(`volume_image_eq_zero_of_oscillation_pow`, `exists_local_graph`, `sard_smooth`) and eight stating
the obligations `M1`, `M1'`, `M2`–`M6` and the diagnostic `D1`. Like `RankDeficientRouteStatements.lean`
it declares nothing, proves nothing and introduces no placeholder axiom, and **a proposition that
type-checks is not a proof**. The route is Morse's (1939) decomposition of an arbitrary set rather
than the hypersurface descent of the proved `C^∞` theorem, which loses `j − 1` derivatives on the
`j`-th layer and cannot run at finite regularity (`D1` records the bookkeeping): `M3`, the Morse
vanishing lemma, is the single high-risk item; `M4` forgets the disks, `M5` consumes the proved
covering count and `M6` is the target verbatim. The statements use Mathlib notions only, with no
auxiliary `structure` or `def`, so that an audit client can copy them verbatim once a proof lands.
**Nothing in this repository proves any of `M1`–`M6`.** Its local import closure contains no
work-in-progress file.

`LipschitzVectorCoareaRouteStatements.lean` checks the route obligations for the **codimension-`m`
coarea formula of Lipschitz maps** — `coarea_of_contDiff` with `ContDiff ℝ 1 u` replaced by
`LipschitzWith K u` — as proposition types only: **fifteen `#check`s**, five referencing proved
declarations (`exists_contDiff_pieces`, `coarea_of_contDiff`, `KLS.coarea_of_lipschitz`,
`KLS.coarea_of_locallyLipschitz`, `ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`) and ten
stating `L0`, `V1`–`V5`, `V4'`, `V4''` and the diagnostics `M1`, `M2`. Like the other route files it
declares nothing, proves nothing and introduces no placeholder axiom, and **a proposition that
type-checks is not a proof**. Of the scalar `L12`'s three steps, the `C¹` formula and the null
slicing already exist in codimension `m`; the vector `C¹` pieces `V1` are the only new ingredient,
routed componentwise through a linear isometry (`V3`, `V4`, `V4'`, `V4''`) rather than through a
vector-valued Whitney extension, and `V5` is the `L12` assembly stated as an implication from `V1`.
The locally Lipschitz version `M2` is out of scope. **Nothing in this repository proves any of `L0`,
`V1`, `V3`–`V5`.** Its local import closure contains no work-in-progress file.

`LocallyLipschitzVectorCoareaRouteStatements.lean` checks the route obligations for the
**codimension-`m` coarea formula of locally Lipschitz maps** — `coarea_of_contDiff` with
`LocallyLipschitz u`, the `M2` that the Lipschitz route left out of scope — as proposition types only:
**eleven `#check`s**, two referencing proved declarations (`KLS.coarea_of_locallyLipschitz`,
`coarea_of_contDiff`) and nine stating the target `N0`, the steps `X1`–`X5`, the strictness witness `D1`
and the consistency items `C1`, `C2`. Like the other route files it declares nothing, proves nothing
and introduces no placeholder axiom, and **a proposition that type-checks is not a proof**. The route
is the scalar `L13` reduction by half-open annuli, verbatim except that the scalar McShane extension
becomes a componentwise one (`X1`, some constant, not Kirszbraun); `X5` is stated as the implication
`L0 → N0`. **Nothing in this repository proves any of `N0`, `X1`, `X3`–`X5`.** Its local import
closure contains no work-in-progress file.

`SharpSardAudit.lean` audits the **sharp finite-regularity Sard theorem**. Seven of the eight
propositions of `SharpSardRouteStatements.lean` are copied **verbatim** and discharged
(`route_M1`, `route_M1'`, `route_M3`, `route_M4`, `route_M5`, `route_M6`, `route_D1`); `route_M6` is
`Analysis.sard` itself. **`M2` is false as written** — the mean value step without the disk's
antilipschitz bound; the client states the pen-and-paper spiral counterexample in its header,
declares no `route_M2`, and proves `route_M2_antilipschitz`, the statement with exactly that bound
inserted, which is what the Morse decomposition supplies and `M3`–`M6` consume. Consistency checks
recover the statements of `sard_smooth`, `sard_plane` and `sard_of_finrank_le_one` from the sharp
theorem without naming them, plus dimension-zero and constant-function boundary cases.
14 standard-only axiom reports; local import closure with no work-in-progress file.

`LipschitzVectorCoareaAudit.lean` audits the **codimension-`m` coarea formula for Lipschitz maps**.
All nine in-scope propositions of `LipschitzVectorCoareaRouteStatements.lean` are copied
**verbatim** and discharged (`route_L0`, `route_V1`–`route_V5`, `route_V4'`, `route_V4''`,
`route_M1` — the last with a universe-polymorphic witness), and `route_M2`, the locally Lipschitz
follow-on, is discharged from `Analysis.coarea_of_locallyLipschitz`. Boundary cases: a
zero-dimensional target, the equidimensional case `k = 0`, a constant map, and the `m = 1`
comparison with `KLS.coarea_of_lipschitz`. 24 standard-only axiom reports; no
work-in-progress file in the import closure.

`LocallyLipschitzVectorCoareaAudit.lean` audits the **codimension-`m` coarea formula for locally
Lipschitz maps**. All eight propositions of `LocallyLipschitzVectorCoareaRouteStatements.lean` are
copied **verbatim** and discharged (`route_X1`–`route_X5`, `route_D1`, `route_C1`, `route_C2`),
and `route_N0`, the target, from `Analysis.coarea_of_locallyLipschitz`. The strictness witness
`x ↦ ‖x‖² e₀ + ‖x‖ e₁` on the plane is proved locally Lipschitz, globally Lipschitz for no
constant, and not differentiable at `0`. 22 standard-only axiom reports; no
work-in-progress file in the import closure.

`LipschitzCoareaMigrationAudit.lean`, `LevelSetMeasurableAudit.lean` and
`IsoperimetryCoareaAudit.lean` formerly imported `KLS/WIP/AnalyticPrerequisites.lean`; since
2026-09-19 they import the proved `Analysis/Sard/Sharp.lean`, and their reports on `Analysis.sard`
and `Analysis.ae_forall_fderiv_ne_zero` no longer show `sorryAx`.

`CheegerEqualityAudit.lean` audits the **closed Cheeger-infimum line**. All fourteen propositions of
`CheegerInfimumRouteStatements.lean` are copied **verbatim** and discharged (`route_K0`–`route_K13`),
with one exception recorded honestly: **`K7` is false as written** — for `B = ∅` the distance cutoff
is identically `1` while the thickening is empty — so `route_K7` carries `B.Nonempty` and
`route_K7_empty_counterexample` refutes the verbatim form on a Dirac law. `route_K0` and `route_K5` are
the two former holes, `route_K10` the certified equality. Boundary cases: dimension zero (both infima
`⊤`), `h_M = ⊤ ↔ h_S = ⊤`, and a Dirac-type law on the affine support. 31 standard-only axiom
reports; no work-in-progress file in the import closure.

`CheegerInequalityAudit.lean` audits **Cheeger's inequality**. `P0`–`P6` and `D1` of
`CheegerInequalityRouteStatements.lean` are copied **verbatim** and discharged (`route_P0` added at
integration once the Cheeger-infimum module supplied `h_μ = h_M(ν)`); `B1`, the Buser half, is not
touched. Boundary cases: dimension zero (smooth-test constant `0`), a constant test, a `1`-Lipschitz
admissible test. 28 standard-only axiom reports; no work-in-progress file in the import closure.

`LipschitzCoareaMigrationAudit.lean` and `IsoperimetryCoareaAudit.lean` formerly imported
`KLS/WIP/CheegerInfimum.lean` and deliberately reported its two holes; since 2026-09-19 they import
`KLS/Geometry/Cheeger/Equality.lean` and every report is standard.

`EnergySlopeComparisonAudit.lean` audits the **sandwich of the three relaxations**: `A1`–`A3` of
`EnergySlopeRouteStatements.lean` copied **verbatim** and discharged, the sandwich as one statement,
the pointwise agreement of the two slope conventions on smooth tests, the four consequences
`E0b`–`E0e` derived with `E0a` as an explicit hypothesis, the absolutely continuous scope recovering
that hypothesis, and dimension zero. 18 standard-only axiom reports.

`EnergySlopeRecoveryAudit.lean` audits **smooth recovery of globally Lipschitz tests**: `B1`–`B5`
copied **verbatim** and discharged, the sandwich on Lipschitz tests and boundary cases. 33
standard-only axiom reports.

`EnergySlopeDensityAudit.lean` audits the **density of smooth tests in the local-slope energy**:
`C1`–`C6` copied **verbatim** and discharged (`route_C2` projects the route's conjunction out of the
stronger patch lemma, which also bounds `|F − f|` everywhere), the sandwich
`LocalSlope.relaxation ≤ SmoothGradient.relaxation ≤ LocalSlope.energy ≤ AsymptoticLipschitz.energy`
on Lipschitz tests, and the now law-independent vanishing of every relaxation in dimension zero.
25 standard-only axiom reports. None of the three clients imports a work-in-progress module —
there is none left.

`BuserRouteStatements.lean` checks the route for the **Buser half** `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` as
proposition types only: **seventeen `#check`s**, seven referencing proved declarations, the target
`B0` verbatim as the Blueprint states it (out of reach in dimension `n ≥ 2`: no heat semigroup, no
Bakry–Émery, no localization in Mathlib or here), the Stage-1 items `Q0`, `Q0'`, `Q1`, `Q1'`, `Q2`–`Q5`
(dimension one with the explicit constant `12`: one-dimensional isoperimetry through `h_M = h_S`, a
density-versus-median bound, a bathtub variance bound, the linear test) and the bookkeeping `D1`
(`π < 12`). Like the other route files it declares nothing, proves nothing and introduces no
placeholder axiom, and **a proposition that type-checks is not a proof**.

`BuserLineAudit.lean` audits **Stage 1 of the Buser program**: `Q0`, `Q0'`, `Q1`, `Q1'`, `Q2`–`Q5`
and `D1` of `BuserRouteStatements.lean` copied **verbatim** and discharged — one-dimensional
isoperimetry `h_M ≥ 2ρ(m)`, `ρ ≤ 2ρ(m)`, `Var ≥ 1/(12ρ_max²)`, the linear test, and the assembled
`Ψ² ≤ 12 C_P` on the line and for affine supports of dimension at most one — with the
zero-dimensional and Dirac boundary cases. `B0` is not touched. 36 standard-only axiom reports.

There are now 61 source clients here, plus the 7 previously referenced local clients.
