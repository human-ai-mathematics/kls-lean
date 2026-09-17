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
`KLS/WIP/AnalyticPrerequisites.lean` into `KLS/Geometry/LipschitzCoarea.lean`. It imports the new
module and **both** work-in-progress files, so its sixteen reports come from one environment:
twelve are standard-only — the migrated declaration, its `L12` source `KLS.coarea_of_lipschitz`,
the two previously migrated neighbours, and eight clients including a verbatim restatement
discharged through named arguments, the original `T2` proposition text, a function not
differentiable at zero, an identically infinite weight and a zero-dimensional space — while the
sharp `C^(finrank)` `Analysis.sard`, `Analysis.ae_forall_fderiv_ne_zero` and the two Cheeger
comparisons still report `sorryAx`. The machine `pp.all` signature comparison for that migration
is in `build/audit/t2-migration/`.

`LevelSetMeasurableAudit.lean` and `IsoperimetryCoareaAudit.lean` gained an import of
`KLS/Geometry/LipschitzCoarea.lean` in the same round, so that the migrated name still resolves;
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

There are now 37 source clients here, plus the 7 previously referenced local clients.
