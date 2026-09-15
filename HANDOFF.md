# KLS Lean repository handoff

命名空间已表达的内容不再重复进声明短名；见[短名补充记录](research/decisions/2026-09-08-namespace-short-names.md)。
比较名称也只写一次共有操作，见[比较短名记录](research/decisions/2026-09-08-comparison-short-names.md)。

This is the current operational handoff for `kls-lean`. It records repository identity,
authority boundaries, certified results, exact non-claims, and reproducible checks.

## Regular open-domain coarea round (2026-09-15)

**Current state; older dated rounds below are historical snapshots.**
**L9 is proved in full**, including weighted-slice `AEMeasurable`, as
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` in `KLS/Geometry/RegularCoarea.lean`.
The hypotheses are exactly the requested open-domain C¹ regularity, Borel `S ⊆ O`, and measurable
ENNReal weight. No global regularity, boundedness, integrability, finite measure, nonzero-dimension,
or SFinite hypothesis is added; the client restates the complete target including `CompleteSpace`.

The joint C¹ inverse keeps the level parameter. Orthogonal volume splitting (already proved via
`WithLp 2`) and Mathlib's one-dimensional specialization of the same-dimensional Jacobian theorem
provide a fiberwise substitution, followed by Tonelli. The proved identity
`|∂t ψ| * ‖∇u‖ = sqrt(1 + ‖∇y ψ‖²)` matches the weighted graph-area formula by multiplication
only, so infinite weights and measures remain in scope. Interior C¹ representatives on smaller
balls and countably many disjoint Borel pieces remove all outside-domain regularity. Slice
measurability is proved independently by localizing L5 in `OpenSliceMeasurable.lean`.
`Analysis/LocalInverse.lean` and `Analysis/FiberIntegral.lean` depend only on Mathlib;
`Analysis/RegularChart.lean` supplies the joint chart and differential identity.

Five new modules and `RegularCoareaAudit` compile with `-DwarningAsError=true`. All 29 new/client
axiom reports use only the standard three axioms. Clients cover infinite weight, the empty set,
zero dimension, actual infinite-volume integrals, infinite surface slices at every level, and a
function discontinuous outside its C¹ domain. All 15 previous clients re-pass unedited; the three
WIP files actually compile with **2/3/5** direct holes, total **10**. Existing Lean files and
historical decisions are unchanged. The final acceptance receipt is `build/verification/latest.json`,
with source/evidence equality attested in `build/audit/l9-final-snapshot.json`.

**Still unproved:** L11, L12, L6/L6a/L7 (Whitney extension and exact pieces), both original weighted
coarea equality holes, sharp `C^(finrank)` `Analysis.sard` (no downstream consumer), Eilenberg
constant sharpness, `smoothConstant_le_minkowskiConstant`,
`smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants.
L10 was not used. Certificates stay **24**, perimeter infrastructure **missing**, and no Blueprint
leanok scope was expanded. No commit/push; HEAD remains `2965b32`.
See [the L9 decision](research/decisions/2026-09-15-regular-coarea.md) and `research/explorations/2026-09-15-regular-coarea.json`.

## Open-domain graph area round (2026-09-15)

**Superseded by the regular open-domain coarea round above; retained as a dated snapshot.**
This round **proves obligation `L8`**: the weighted graph-area change of variables, previously
available only for a graph function that is `C¹` on the whole parameter space, now holds for one
that is `C¹` on an **open set** `O`, over any measurable `S ⊆ O`
(`Analysis.setLIntegral_image_graphMap_of_contDiffOn` in the new
`Analysis/OpenGraphIntegral.lean`). The route's statement is matched exactly; the weight may be
unbounded, non-integrable or identically `∞`, `S` need not be bounded or of finite measure, `v` has
no regularity outside `O`, and `O = ∅`, `S = ∅` are covered.

A `ContDiffOn` function on an open set generally does **not** extend to a globally `C¹` function —
`x ↦ x⁻¹` on `(0, ∞)` is the standard counterexample, and the client applies `L8` to exactly that
instance, which the pre-existing global theorem cannot reach. So the localization is genuinely
countable: `exists_contDiff_one_eqOn_ball` gives, around each point of `O`, a ball on which some
globally `C¹` function agrees with `v` (multiply by a `ContDiffBump` supported in `O`; smoothness
is local). Second countability extracts a countable subfamily of such balls covering `O`,
`disjointed` makes countably many pairwise disjoint measurable pieces of `S`, `graphMap` is
injective so the images are disjoint and measurable, both sides are countably additive over the
pieces, and the gradients agree because the functions agree on an **open** ball. This is the
**interior** localization the route prescribes; it is **not** the Whitney extension from a closed
set, which is the separate unproved obligation `L6`. `Analysis/SmoothSard.lean`'s `C^∞` analogue
`exists_contDiff_eventuallyEq` is deliberately left untouched, since generalizing it would change a
published signature.

`build/audit/OpenGraphAudit.lean` compiles strictly: the route's `L8` text `#check` and six
theorems — `target`, `global_case` (recovering the pre-existing global theorem at `O = univ`, so
`L8` is a genuine generalization), an identically-`∞` weight, the empty parameter set, the `x⁻¹`
instance, and a `preserved_*` named-argument signature check — plus 9 `#print axioms` lines that
all report only `propext`, `Classical.choice` and `Quot.sound`. Fourteen earlier strict clients
re-pass unedited, and the three WIP files actually recompile with **2/3/5** direct holes, total
**10** — unchanged, since `L8` fills no hole. Default `lake build` and root `research/verify.py`
pass; the final source-bound receipt is `build/verification/latest.json`, with the final equality
check in `build/audit/opengraph-final-snapshot.json`. Certificates stay **24**, perimeter
infrastructure **missing**. The incoming passed receipt `20260915T040555.802878Z` matched all 427
snapshot entries. HEAD stays `2965b32`; no commit/push. See
[the open-graph decision](research/decisions/2026-09-15-open-graph-area.md) and
`research/explorations/2026-09-15-open-graph-area.json`.

`L8` gives the area of a **graph**, not a coarea formula. Still unproved: `L9` (regular-part `C¹`
coarea, which additionally needs the `t`-**parametrized** `C¹` implicit function family, the
same-dimensional Jacobian change of variables and the cancellation
`|det DΦ| = |Du(e)|`, `√(1 + ‖D_yψ‖²) = ‖∇u‖ / |Du(e)|`), `L11`, `L12`, the weighted coarea
**equality** and its `C¹` specialization, `L6`/`L6a`/`L7`, sharp `C^(finrank)` `Analysis.sard` (no
downstream consumer), sharpness of the Eilenberg constant,
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Critical-slice round (2026-09-15)

**Superseded by the open-domain graph area round above; retained as a dated snapshot.**
This round **proves obligation `L10`**: for a `C¹` real function on a finite-dimensional
inner-product space, almost every level meets the critical set `{x | fderiv ℝ u x = 0}` in a set of
zero `surfaceMeasure` (`KLS.ae_surfaceMeasure_critical_inter_levelSet_eq_zero` in the new
`KLS/Geometry/CriticalSlice.lean`). Only the unused `[CompleteSpace V]` is dropped; `u` is **not**
assumed Lipschitz, bounded or proper, the critical set needs no measurability hypothesis (it is
closed), and `V` may be zero-dimensional.

**This is not Sard's theorem and does not imply it.** Sard concerns the Lebesgue measure of the set
of critical *values*, needs `C^(finrank)` regularity in general, and is still the unproved direct
hole `Analysis.sard`. `L10` concerns the codimension-one measure of the critical *part of each
slice*, for merely `C¹` functions. The client makes the difference concrete: for a constant function
the critical set is everything, so the slice at the attained value is the whole line and has
**nonzero** surface measure — "almost every level" cannot be strengthened to "every level".

`L10` is the first genuine consumer of the Eilenberg bound `L1`. On the critical set the derivative
vanishes, and the approximating linear maps of Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` are *values of the derivative*, so
they are all zero and its approximation becomes a genuine `ε`-Lipschitz estimate on countably many
**pairwise disjoint measurable** pieces. Applying `L1` on each piece inside a ball of radius `R`
and summing gives a measurable majorant of integral at most
`eilenbergConstant V * ε * volume (closedBall 0 R)`; the pointwise infimum over `ε = (k + 1)⁻¹` has
integral zero, and a countable union over the radii removes the ball. Localizing to a ball is
essential — the bound is only useful where the ambient volume is finite.

`build/audit/CriticalSliceAudit.lean` compiles strictly: the route's `L10` text `#check` and seven
theorems — `target`, `target_of_not_completeSpace`, `ae_slice_eq_regular` (the form `L11` will
consume: almost every slice may be computed after discarding the critical set), the singleton
computation, `constant_exceptional_level`, a `C¹` non-Lipschitz application, and a `preserved_*`
named-argument signature check — plus 11 `#print axioms` lines that all report only `propext`,
`Classical.choice` and `Quot.sound`. Thirteen earlier strict clients re-pass unedited, and the
three WIP files actually recompile with **2/3/5** direct holes, total **10** — unchanged, since
`L10` fills no hole. Default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/critical-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260915T035117.865459Z` matched all 424 snapshot
entries. HEAD stays `2965b32`; no commit/push. See
[the critical-slice decision](research/decisions/2026-09-15-critical-slice.md) and
`research/explorations/2026-09-15-critical-slice.json`.

Still unproved: `L8` (weighted graph area on an open domain), `L9` (regular-part `C¹` coarea),
`L11`, `L12`, the weighted coarea **equality** and its `C¹` specialization, sharp `C^(finrank)`
`Analysis.sard` (no downstream consumer), sharpness of the Eilenberg constant,
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Level-set measurability migration round (2026-09-15)

**Superseded by the critical-slice round above; retained as a dated snapshot.**
This round **closes the first original coarea hole**. The direct hole
`Analysis.aemeasurable_lintegral_levelSet` moved out of `KLS/WIP/AnalyticPrerequisites.lean` into
the hole-free `KLS/Geometry/LevelSetMeasurable.lean` with a **byte-identical `pp.all` signature**
and is now proved from last round's `L5` (`KLS.aemeasurable_setLIntegral_inter_levelSet` at
`S = univ`). Direct holes drop **11 (3/3/5) → 10 (2/3/5)** — the first hole-count reduction of
this sequence. Certificates stay **24**, perimeter infrastructure **missing**.

Byte-identity is machine-checked, not asserted: the `pp.all` type was printed before the move in an
environment importing the WIP file and after the move in one importing the new module, and the two
logs `diff` empty (`build/audit/migration-signature-before.log`,
`migration-signature-after.log`). The same universe, the same six instance arguments in the same
order — including the `CompleteSpace V` the proof does not use — the same binders and hypothesis
names, and the same conclusion. The unused section variables are kept and the linter silenced with
`set_option linter.unusedSectionVars false in`, the way the 2026-09-15 superlevel rewire did it,
rather than narrowing the signature with `omit`. The WIP file lost exactly that one declaration;
every other declaration there is unchanged in statement, proof and position.

**This round proves no new theorem** — it is a migration and rewiring only, and it does **not**
close the weighted coarea formula. `build/audit/LevelSetMeasurableAudit.lean` imports **both** the
new module and the WIP file, so its six `#print axioms` reports come from one environment in which
the migrated name resolves to a single declaration: the migrated result reports only `propext`,
`Classical.choice` and `Quot.sound`, while `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
(the **equality**), the sharp `C^(finrank)` `Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero`
all still report `sorryAx`. A client theorem restating the equality compiles **with** `sorryAx`,
which is the point: restating is not proving.

Twelve earlier strict clients re-pass unedited, the three WIP files actually recompile with
**2/3/5** direct holes, and default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/migration-final-snapshot.json`. The incoming passed receipt
`20260915T033803.710026Z` matched all 421 snapshot entries. HEAD stays `2965b32`; no commit/push.
See [the migration decision](research/decisions/2026-09-15-levelset-measurable-migration.md) and
`research/explorations/2026-09-15-levelset-measurable-migration.json`.

Still unproved: the weighted coarea **equality** (`L6`–`L12`, targets `T2`/`T3`, including the
Whitney `C¹` extension), the remaining two original coarea holes, sharpness of the Eilenberg
constant, sharp `C^(finrank)` `Analysis.sard` (no downstream consumer),
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Borel-slice and measurable-weight round (2026-09-15)

**Superseded by the level-set measurability migration round above; retained as a dated snapshot.**
This round **proves obligations `L4` and `L5`** of the weighted coarea route, and with them the
full statement of the first original target **`T1`** — which is verbatim the statement of the
direct hole `Analysis.aemeasurable_lintegral_levelSet`. **No WIP file was touched**: migrating that
declaration out of `KLS/WIP/AnalyticPrerequisites.lean` is a separate decision, so the direct-hole
count is unchanged at **11** (3/3/5) and that hole is still a hole. What is established is that its
statement is now provable from hole-free modules.

`KLS.aemeasurable_surfaceMeasure_inter_levelSet` (`L4`) and
`KLS.aemeasurable_setLIntegral_inter_levelSet` (`L5`) are added to
`KLS/Geometry/SurfaceSlicing.lean`; no new module, and no other Lean file changed. `L4` combines
all three earlier results and needs each: inner regularity
(`exists_isCompact_seq_volume_sdiff_eq_zero`, new here) splits a measurable `S` into an increasing
sequence of compact pieces plus a Lebesgue-null remainder, `L3` makes each compact slice
measurable, continuity from below turns the supremum into the slice measure of the union, and `L2`
kills the remainder for almost every level. `L5` follows by simple-function approximation: each
simple weight turns the slice integral into a **finite sum** of slice measures of the measurable
sets `S ∩ s ⁻¹' {c}`. No parametric-integral theorem is used, so the inner measure is never
assumed `SFinite` — which it is not in positive dimension.

Both drop the recorded `[CompleteSpace V]` and weaken global `LipschitzWith K u` to `Continuous u`
plus Lipschitz **on `S` only**; `S` need not be bounded, nonempty or of finite volume, and `g` may
be unbounded, non-integrable or identically `∞`. `L4` and `L5` give measurability only: **no
equality**, so the weighted coarea identity itself (targets `T2`/`T3`, obligations `L6`–`L12`) is
untouched.

`build/audit/BorelSliceAudit.lean` compiles strictly: three statement `#check`s (the route's `L4`,
`L5` and `T1` texts) and twelve theorems — `target_L4`, `target_L5`, `target_T1`, two
weakened-hypothesis versions, `eilenberg_borel` packaging `L1` with `L4`, `weighted_one`,
an infinite-volume unbounded set, an identically-`∞` weight, and three `preserved_*`
named-argument signature checks — plus 15 `#print axioms` lines that all report only `propext`,
`Classical.choice` and `Quot.sound`. Eleven earlier strict clients re-pass unedited, their own
`preserved_*` theorems re-confirming the previous rounds' statements, and the three WIP files
actually recompile with **3/3/5** direct holes, total **11**. Default `lake build` and root
`research/verify.py` pass; the final source-bound receipt is `build/verification/latest.json`,
with the final equality check in `build/audit/borelslice-final-snapshot.json`. Certificates stay
**24**, perimeter infrastructure **missing**. The incoming passed receipt
`20260915T024959.891644Z` matched all 419 snapshot entries. HEAD stays `2965b32`; no commit/push.
See [the Borel-slice decision](research/decisions/2026-09-15-borel-slice-measurable.md) and
`research/explorations/2026-09-15-borel-slice-measurable.json`.

Still unproved: the weighted coarea **equality** itself (`L6`–`L12`, targets `T2`/`T3`, including
the Whitney `C¹` extension), both remaining original coarea holes, sharpness of the Eilenberg
constant, sharp `C^(finrank)` `Analysis.sard` (no downstream consumer),
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Compact-slice measurability round (2026-09-15)

**Superseded by the Borel-slice and measurable-weight round above; retained as a dated snapshot.**
This round **proves obligation `L3`** of the weighted coarea route: for `S` **compact** and `u`
merely continuous, `t ↦ surfaceMeasure V (S ∩ {u = t})` is Borel measurable
(`KLS.measurable_surfaceMeasure_inter_levelSet` in `KLS/Geometry/SurfaceSlicing.lean`, over the
Mathlib-only `Analysis.measurable_hausdorffMeasure_inter_levelSet` in the new
`Analysis/HausdorffContent.lean`). `L3` is **not** a consequence of `L1`: the majorant bound says
nothing about the slice function's own measurability. Both `[CompleteSpace V]` and
`[FiniteDimensional ℝ V]` of the recorded `L3` are dropped as unused — `surfaceMeasure` only reads
`Module.finrank` — and no Lipschitz, boundedness or finiteness hypothesis is added.

The new module names Mathlib's scalewise cover cost (`coverCost`) and adds the variant restricted
to **open** covers (`openCoverCost`). Two facts carry the proof. At a fixed scale the open-cover
cost of the slices is upper semicontinuous in the level, because an open cover of one slice still
covers all nearby slices: the compact remainder `S \ U` keeps `u` at a positive distance from the
level (`isOpen_setOf_slice_subset`). And the open-cover costs have the same scale limit,
`⨆ n, openCoverCost d (n+1)⁻¹ A = μH[d] A`, proved by thickening a near-optimal cover with
summably small radii (`Metric.ediam_thickening_le`, `ENNReal.exists_pos_sum_of_countable`). At a
**fixed** scale `openCoverCost` is generally strictly larger than `coverCost`, so the equality
genuinely needs the scale limit; **no upper semicontinuity of `μH[d]` itself is claimed**, which
would be false.

`build/audit/CompactSliceAudit.lean` compiles strictly: the route's `L3` text `#check` and eleven
theorems — `target` restating it verbatim, `target_of_not_finiteDimensional`, `eilenberg_compact`
packaging `L1` with `L3` into the measurable-integrand Eilenberg bound that `L4`/`L5` will consume,
a measurability consumer, a continuous **non-Lipschitz** application, three computations on the
unit interval of the line showing `∫⁻ t, surfaceMeasure ℝ (Icc 0 1 ∩ {id = t}) = 1` against the
Eilenberg bound `2`, and two `preserved_*` named-argument signature checks — plus 29
`#print axioms` lines that all report only `propext`, `Classical.choice` and `Quot.sound`. Ten
earlier strict clients re-pass unedited (the Eilenberg client's four `preserved_*` theorems
re-confirm the two previous rounds' statements through named arguments), and the three WIP files
actually recompile with **3/3/5** direct holes, total **11** — unchanged, because `L3` fills none
of the original coarea holes. Default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/compactslice-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260914T213846.405397Z` matched all 416 snapshot
entries. HEAD stays `2965b32`; no commit/push. See
[the compact-slice decision](research/decisions/2026-09-15-compact-slice-measurable.md) and
`research/explorations/2026-09-15-compact-slice-measurable.json`.

Still unproved: **L4** (Borel-set slices, a.e. measurable) and **L5** (measurable weights) — `L3`
asserts nothing for a general Borel set, and the first original coarea hole is stated for `univ`,
so the compact version cannot fill it. Also all three original coarea holes, sharp `C^(finrank)`
`Analysis.sard` (no downstream consumer), `smoothConstant_le_minkowskiConstant`,
`smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants. No
certificate or Blueprint leanok scope was expanded.

## Eilenberg measurable-majorant round (2026-09-15)

**Superseded by the compact-slice measurability round above; retained as a dated snapshot.**
This round **proves obligation `L1`** of the weighted coarea route, with an explicit positive
constant: for `u` Lipschitz **on `S` only**, the slice function
`t ↦ surfaceMeasure V (S ∩ {u = t})` is dominated by a **measurable** `F` with
`∫⁻ F ≤ eilenbergConstant V * K * volume S`, where
`eilenbergConstant V = 4 ω_{n-1} / ω_n > 0` (`KLS.exists_measurable_majorant` and
`KLS.eilenbergConstant_pos` in `KLS/Geometry/SurfaceSlicing.lean`, over the Mathlib-only
`Analysis.exists_measurable_majorant` in `Analysis/HausdorffSlicing.lean`, which carries Mathlib's
diameter-gauge constant `2` on an arbitrary `EMetricSpace` with no dimension and no ambient
volume). Last round's `L2` is now the null special case, with **statements unchanged**. No
sharpness is claimed for the constant; the audit client computes it as `2` on the line and `4` in
dimension zero.

`S` is not assumed measurable, bounded, nonempty or of finite volume, `u` is not assumed globally
Lipschitz, differentiable or measurable, `K = 0` and `volume S = ∞` are explicit branches, and `V`
may be zero-dimensional — `[CompleteSpace V]` and `[Nontrivial V]` of the recorded `L1` are both
dropped as unused. Measurability is still asserted only of the **constructed** majorant: the slice
function itself is not known to be measurable, and `L1` supplies no such statement.

`build/audit/EilenbergMajorantAudit.lean` compiles strictly: the route's `L1` text `#check`, a
`target` theorem restating it verbatim with `[CompleteSpace V]` and `[Nontrivial V]`, a
`target_of_trivial` without `[Nontrivial V]`, six independent consumers (`L2` re-derived from the
majorant alone; **finiteness** of almost every slice measure when `volume S < ∞`, which `L2`
cannot give; `K = 0` forcing a vanishing integral; `S = univ` with no finiteness hypothesis; and
the constant computed as `2` on the line and `4` in dimension zero), four `preserved_*` theorems that re-check last round's statements
through **named** arguments so a renamed binder fails to elaborate, and 23 `#print axioms` lines
that all report only `propext`, `Classical.choice` and `Quot.sound`. Nine earlier strict clients
re-pass unedited, and the three WIP files actually recompile with **3/3/5** direct holes, total
**11** — unchanged, because `L1` fills none of the original coarea holes. Default `lake build` and
root `research/verify.py` pass; the final source-bound receipt is
`build/verification/latest.json`, with the final equality check in
`build/audit/eilenberg-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260914T211119.924157Z` matched all 414 snapshot
entries. HEAD stays `2965b32`; no commit/push. See
[the Eilenberg-majorant decision](research/decisions/2026-09-15-eilenberg-majorant.md) and
`research/explorations/2026-09-15-eilenberg-majorant.json`.

Still unproved: the **L3–L5 fibre-measurability bridge**, all three original coarea holes, sharp
`C^(finrank)` `Analysis.sard` (no downstream consumer),
`smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`, and
equality of the two Cheeger constants. No certificate or Blueprint leanok scope was expanded.

## Null slicing round (2026-09-15)

**Superseded by the Eilenberg measurable-majorant round above; retained as a dated snapshot.**
This round **proves obligation `L2`** of the weighted coarea route: a Lebesgue-null set has
`surfaceMeasure`-null slices along almost every level of a function that is Lipschitz **on that
set only**. The metric-space core is `Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero` in the
new `Analysis/HausdorffSlicing.lean` (local import closure empty, Mathlib only, arbitrary
`EMetricSpace`), and the normalized wrapper is
`KLS.ae_surfaceMeasure_inter_levelSet_eq_zero` in the new `KLS/Geometry/SurfaceSlicing.lean`.
`N` is not assumed measurable, bounded or nonempty, `u` is not assumed globally Lipschitz,
differentiable or measurable, `K = 0` is allowed and `V` may be zero-dimensional. Rademacher's
theorem does **not** give this; the proof is a covering argument with a **measurable majorant**,
so nothing is inferred from `∫⁻ f = 0` for a function not known to be measurable.

`build/audit/NullSlicingAudit.lean` compiles strictly: the route's `L2` text `#check`, a `target`
theorem restating it verbatim with `[CompleteSpace V]`, nine independent consumers (subset of a
null set with no measurability, `K = 0`, arbitrary `ℝ≥0∞` weight over slices, dimension zero and
its unit mass `ℋ^{0-1} univ = 1`, dimension one with its genuine exceptional level
`ℋ⁰ ({0} ∩ {id = 0}) = 1`, an `N`-only-Lipschitz discontinuous `u`, and a nondegenerate planar
segment of nonzero `ℋ¹`), plus 14 `#print axioms` lines that all report only `propext`,
`Classical.choice` and `Quot.sound`. Eight earlier strict clients re-pass unedited, and the three
WIP files actually recompile with **3/3/5** direct holes, total **11** — unchanged, because `L2`
fills none of the original coarea holes. Default `lake build` and root `research/verify.py` pass;
the final source-bound receipt is `build/verification/latest.json`, with the final equality check
in `build/audit/nullslicing-final-snapshot.json`. Certificates stay **24**, perimeter
infrastructure **missing**. The incoming passed receipt `20260914T194849.197366Z` matched all 410
snapshot entries. HEAD stays `2965b32`; no commit/push. See
[the null-slicing decision](research/decisions/2026-09-15-null-slicing.md) and
`research/explorations/2026-09-15-null-slicing.json`.

Still unproved: the **L3–L5 fibre-measurability bridge** (`L2` gives no measurability), all three
original coarea holes, the constant-carrying general `L1`, sharp `C^(finrank)` `Analysis.sard`
(no downstream consumer), `smoothConstant_le_minkowskiConstant`,
`smoothConstant_mul_lintegral_min_superlevel_le`, and equality of the two Cheeger constants. No
certificate or Blueprint leanok scope was expanded.

## Weighted coarea route exploration (2026-09-15)

**Superseded by the null-slicing round above; retained as a dated snapshot.**
This round proves no new theorem and changes no Lean library source. The proposed general theorem
combines weighted coarea and fiber AEMeasurable on any Borel restriction, for Lipschitz `u` in every
finite dimension and arbitrary ENNReal measurable weights. The three original targets remain
unchanged. The precise missing foundations are the Eilenberg measurable-majorant/null-slicing
lemma and the C¹ Whitney jet extension plus exact C¹ decomposition of Lipschitz functions.
The existing C¹ graph area formula and same-dimensional Jacobian theorem are ingredients, not
Lipschitz coarea. Fiber measurability can be proved independently of the equality, but needs compact
fiber measurability and null slicing; ambient surfaceMeasure is not SFinite in positive dimension.

`build/audit/WeightedCoareaRouteStatements.lean` has 17 strictly checked statements and no
new declaration, proof or axiom; a second strict client checks 20 existing infrastructure APIs.
Six previous clients re-pass strictly, and the three WIP files actually recompile with **3/3/5**
direct holes, total **11**. Default `lake build` and root `research/verify.py` pass; the final
source-bound receipt is `build/verification/latest.json`, with the final equality check in
`build/audit/coarea-final-snapshot.json`. Certificates stay **24**, perimeter infrastructure
**missing**. The incoming passed receipt `20260914T181901.237724Z` matched all 408 snapshot entries.
HEAD stays `2965b32`; no commit/push. See [the route decision](research/decisions/2026-09-15-weighted-coarea-route.md) and
`research/explorations/2026-09-15-weighted-coarea-route.json` for exact statements and hashes.

Still unproved: sharp C^(finrank) `Analysis.sard` (no downstream consumer), all three coarea
holes, `smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`,
and equality of the two Cheeger constants. Smooth Sard and `ae_exists_superlevel` remain proved
without `sorryAx`; the full chain is not closed. Next suggested step: L2 null slicing, then L3–L5
fiber measurability. No certificate or Blueprint leanok scope was expanded.

## Superlevel rewiring round (2026-09-15)

**Superseded by the weighted coarea route round above; retained as a dated snapshot.**
`SmoothDomain.ae_exists_superlevel` and `SmoothDomain.frontier_superlevel_subset` have moved out of
`KLS/WIP/CheegerInfimum.lean` into the new hole-free `KLS/Geometry/RegularSuperlevel.lean`, with
**byte-identical `pp.all` signatures** (diff-checked). The former is now proved from
`Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top`, a consequence of the proved
`Analysis.sard_smooth`, so **it no longer inherits `sorryAx`** — the first KLS conclusion freed
from the Sard dependency.

The packaging was deliberately not put back into `Geometry/SmoothDomain.lean`, whose docstring
keeps it independent of Sard; it sits one layer up. `WIP/CheegerInfimum.lean` swapped its import of
`WIP/AnalyticPrerequisites` for the new module and still compiles, which shows that Sard
consequence was its only real dependency there: **no module now imports
`KLS/WIP/AnalyticPrerequisites.lean` at all**, so the sharp Sard and coarea holes sit in a file
nothing depends on.

Holes are unchanged at **11** (3/3/5): what moved was a filled body, not a direct hole — this round
reduced `sorryAx` propagation, not the hole count. Certificates stay **24**, perimeter
infrastructure **missing**. `build/audit/SuperlevelSardScope.lean` now reports the boundary side by
side: `ae_exists_superlevel`, `frontier_superlevel_subset` and `Analysis.sard_smooth` carry only
standard axioms, while `Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero` still carry
`sorryAx`. Ten earlier audits re-pass strictly with no edits; default `lake build` passes
(3393 jobs). The incoming passed receipt `20260914T171940.461693Z` was matched byte-for-byte.
HEAD stays `2965b32`; no commit/push. See the
[new decision](research/decisions/2026-09-15-superlevel-rewire.md).

Next blocker: weighted coarea `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and its
level-set measurability, then the reverse Cheeger comparison. The sharp `C^n` `Analysis.sard` now
has no downstream consumer.

## Smooth Sard round (2026-09-15)

**Superseded by the superlevel rewiring round above; retained as a dated snapshot.**
**Sard's theorem for `C^∞` real-valued functions is proved**, in `Analysis/SmoothSard.lean`, with
standard three axioms only: `Analysis.sard_smooth_pi` on `Fin n → ℝ` in every dimension,
`Analysis.sard_smooth` on an arbitrary finite-dimensional real normed space, and
`Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top`. The critical set is not assumed measurable.

Second route correction: the recorded L3 (open-domain form of the flat layer) was **not needed**.
A cheaper replacement, `Analysis.exists_contDiff_eventuallyEq` (a bump-multiplied local smooth
extension), lets the induction stay global, so the already proved
`volume_image_flat_pow_univ_eq_zero` handles the top layer unchanged. The induction on dimension
splits the critical set by `critical_subset_layers`, turns each intermediate layer into a lower
dimension through `exists_flat_direction` and `exists_local_graph`, replaces the local graph by a
globally smooth map agreeing with it near the base parameter, applies the inductive hypothesis to
`u ∘ γ'`, and glues with Lindelöf.

`build/audit/SmoothSardAudit.lean` shows what this closes: `superlevel_without_sard` reproves the
statement of `SmoothDomain.ae_exists_superlevel` from the new theorem and reports **no `sorryAx`**,
while the WIP declaration itself, in the same log, still carries it. **No WIP file was changed this
round**, so `SmoothDomain.ae_exists_superlevel` still inherits `sorryAx`, holes stay **11**
(3/3/5), certificates **24**, perimeter infrastructure **missing**, and the sharp `C^n`
`Analysis.sard` keeps its statement and direct-hole status with the `n = 4, j = 2` obstruction
untouched. Rewiring WIP to the new theorem is a separate decision for the next round.

The module and its client pass `-DwarningAsError=true`; eight earlier audits re-pass strictly with
no edits; the three WIP files re-elaborate with **3/3/5** direct holes; default `lake build` passes
(3393 jobs). The incoming passed receipt `20260914T165021.064313Z` was matched byte-for-byte.
HEAD stays `2965b32`; no commit/push. See the
[new decision](research/decisions/2026-09-15-smooth-sard.md).

Still open: the WIP rewiring, the sharp `C^n` Sard, and — the main blocker for the reverse Cheeger
comparison — weighted coarea and its level-set measurability, both untouched.

## Smooth Sard ingredients round (2026-09-15)

**Superseded by the smooth Sard round above; retained as a dated snapshot.**
`Analysis/SmoothSard.lean` proves three of the seven lemmas listed by the route exploration, with
standard three axioms only: `critical_subset_layers` (L2, the layer decomposition of the critical
set), `exists_flat_direction` (L4, a nonvanishing derivative of order `j + 1` yields a scalar
`C^∞` function vanishing on the `j`-th layer with nonvanishing differential) and
`exists_local_graph` (L5, the regular zero set of such a function is locally the image of a map
`C^∞` on an open parameter set, with a fixed continuous parameter map).

One route correction: `ContDiffAt ℝ ∞` does **not** upgrade to `ContDiffOn ℝ ∞` on a
neighbourhood — `ContDiffAt.contDiffOn` carries the side condition `m = ∞ → n = ω`, and this is
real, not an interface defect. So the inverse function theorem's pointwise output is not enough
and L5 was strengthened to an open parameter set: shrink to the open region where the chosen
partial derivative of `w` is nonzero, rebuild the invertible differential at each of its points,
and apply `OpenPartialHomeomorph.contDiffAt_symm` pointwise. The chart is the map replacing one
coordinate by `w`; no manifold or implicit-function framework was built, and
`Analysis/ImplicitGraph.lean` still does not apply.

The module and its client pass `-DwarningAsError=true` with 10 standard-axiom reports, covering
dimension zero, the planar `j = 1` case and a concrete regular zero set. Seven earlier audits
re-pass strictly with no edits; the three WIP files re-elaborate with **3/3/5** direct holes.
**No `sorryAx` was removed and no statement changed**: general `Analysis.sard` and both its
consumers still inherit `sorryAx`, holes stay **11**, certificates **24**, perimeter
infrastructure **missing**. Default `lake build` passes (3393 jobs). The final root receipt is
`build/verification/latest.json`; the incoming passed receipt `20260914T162757.518089Z` was
matched byte-for-byte. HEAD stays `2965b32`; no commit/push.

Still missing before `C^∞` Sard exists: **L3** (open-domain form of the already proved flat
layer, which also needs the order-`n` remainder relaxed to an open domain), **L1** (the dimension
induction assembling L2/L4/L5 with Lindelöf), and **L6/L7** (transfer to a general
finite-dimensional space and the `C^∞` a.e. variant). See the
[new decision](research/decisions/2026-09-15-smooth-sard-ingredients.md).

## Sard route exploration round (2026-09-15)

**Superseded by the ingredients round above; retained as a dated snapshot.**
**No theorem was proved this round and no Lean source under `formalization/` changed.** The round
determined the route for the remaining Sard layers and produced type-checked statements only.

Main finding: the sharp `C^n` `Analysis.sard` is **not needed by any consumer**. Its only user is
`Analysis.ae_forall_fderiv_ne_zero`, whose only user is `SmoothDomain.ae_exists_superlevel`, and
that statement already assumes `ContDiff ℝ ∞ u` and downgrades ∞ to `finrank` at the call site.
Proving a `C^∞` Sard plus a `C^∞` variant of `ae_forall_fderiv_ne_zero` would free
`ae_exists_superlevel` from `sorryAx` without touching the sharp statement, which keeps its text
and its direct-hole status.

The sharp version's first genuine obstruction is located exactly: layer `A_j \ A_{j+1}` in
dimension `d` closes elementarily only when `j ≥ d-1`, and by hypersurface descent only when
`j ≤ 1`, so `n = 4, j = 2` is the first uncovered case — the restricted function is only `C²` on a
3-dimensional slice while 3-dimensional Sard needs `C³`. Sharp Sard in dimension 3 is reachable
with what exists today; dimension 4 and up is the Whitney–Morse–Sard difficulty and is not
attempted. Under `C^∞` the descent never exhausts regularity, which is the whole reason to switch.

The recommended inductive statement is over **open** domains, `ContDiffOn ℝ ∞ u O` with `IsOpen O`,
since that is exactly what the descent step supplies; `O = univ` recovers the global form. Seven
supporting lemmas are listed with effort estimates in the decision record. Mathlib turns out to
have all the ingredients for the hardest one (the local `C^∞` graph of a regular zero set) in
`Mathlib/Analysis/Calculus/ImplicitContDiff.lean`, including the graph characterization, not just
an inclusion; the repository's own `Analysis/ImplicitGraph.lean` still does not apply. There is no
ready-made smooth-extension-from-a-neighborhood lemma, which is why the open-domain formulation is
preferred over bump extensions.

`build/audit/SmoothSardRouteStatements.lean` passes `-DwarningAsError=true` with nine `#check`s and
contains no declaration, proof or placeholder axiom. Holes stay **11** (3/3/5), certificates **24**,
perimeter infrastructure **missing**; `Analysis.sard` and both consumers still inherit `sorryAx`.
Default `lake build` and `python3 research/verify.py` re-pass. HEAD stays `2965b32`; no commit/push.
See the [route decision](research/decisions/2026-09-15-smooth-sard-route.md).

## Higher-order flat layer round (2026-09-15)

**Superseded by the route exploration round above; retained as a dated snapshot.**
Both obligations recorded last round are proved verbatim, with standard three axioms only.
`Analysis.exists_uniform_pow_remainder` in `Analysis/TaylorRemainder.lean` gives the order-`n`
uniform remainder at points of a compact set where every derivative of order `1` to `n` vanishes,
on an arbitrary real normed domain — no finite-dimensionality, completeness, inner product or
measure. `Analysis.volume_image_eq_zero_of_oscillation_pow` in `Analysis/QuadraticCover.lean`
gives the `n`-dimensional covering lemma: a bounded `A ⊆ Fin n → ℝ` with a uniform `o(‖y-x‖ⁿ)`
modulus has null image, with no measurability anywhere. Combining them,
`Analysis.volume_image_flat_pow_eq_zero` and `Analysis.volume_image_flat_pow_univ_eq_zero` make
the fully flat layer null on a compact subset and on all of `Fin n → ℝ`.

The remainder is proved by induction on the order: the inductive step applies the statement to
`fderiv f` (vector-valued, hence an auxiliary same-universe lemma) and raises the power by one
convex mean-value inequality, without degrading the constant. The covering lemma replaces the
`ℤ × ℤ` grid by `Fintype.piFinset` over `Fin n → ℤ`, where `(2M+1)ⁿ` cells of image length
`O(ε rⁿ)` cancel exactly. `n = 0` and `n = 1` need no branch.

No duplicated proof was added: `exists_uniform_quadratic_remainder` and
`volume_image_eq_zero_of_quadratic_oscillation` are now corollaries, with their statements
**byte-identical** (diff-checked) and every existing client unchanged and still passing.

The two modules and the new client pass `-DwarningAsError=true`; 17 axiom reports use only
standard axioms, covering the two recorded obligations verbatim, the remainder on a
dimensionless normed space, dimensions zero, one and three, the unchanged planar interface, and
a constant function that is fully flat on **all of `ℝⁿ`** yet has null image. Six earlier audits
re-pass strictly with no edits; the three WIP files re-elaborate with **3/3/5** direct-hole
warnings only. General Sard and its two consumers still inherit `sorryAx`: holes stay **11**,
certificates **24**, perimeter infrastructure **missing**. Default `lake build` passes
(3393 jobs). The final root verification receipt is `build/verification/latest.json`; the incoming
passed receipt `20260914T154144.742286Z` was matched byte-for-byte. HEAD stays `2965b32`;
no commit/push.

This round completes the **top layer in dimension `n` only**. The intermediate layers
(`1 ≤ j < n`, derivatives of order `1..j` vanishing but order `j+1` not), the stacked
dimension-`n` Sard, and the general `Analysis.sard` over an arbitrary finite-dimensional space
are all still unproved; the first two are type-checked in
`build/audit/IntermediateLayerNextStatement.lean`. See the
[new decision](research/decisions/2026-09-15-higher-order-flat-layer.md).

## Planar Sard round (2026-09-14)

**Superseded by the higher-order flat layer round above; retained as a dated snapshot.**
`Analysis.sard_plane` is proved in
`formalization/FunctionalInequalities/Analysis/PlanarSard.lean`, with standard three axioms only:
the critical values of a `C²` function on `Fin 2 → ℝ` are Lebesgue null. The critical set is not
assumed measurable, bounded or compact. Its nonflat layer
`Analysis.volume_image_nonflat_eq_zero` and a one-dimensional covering lemma
`Analysis.volume_image_eq_zero_of_quadratic_bound` are proved alongside it.

The nonflat layer avoids the implicit function theorem. Near a point with `D²u ≠ 0` a
mean-value inequality with linear principal part shows the critical set is a Lipschitz graph over
one coordinate; that bound also forces injectivity of the coordinate, so the layer collapses onto
the one-dimensional covering lemma, whose cell count `O(r⁻¹)` already beats the image length
`O(r²)` without any `ε`-refinement. Lindelöf glues the local balls countably, so no compactness
hypothesis survives. The repository's `Analysis/ImplicitGraph.lean` was **not** reused: it needs
`C^∞` and an inner product, while `Du` is only `C¹` here. No new implicit-function framework was
built, no declaration moved, no signature changed, no WIP dependency, no certificate expansion.

`Analysis.sard_plane` is **not** `Analysis.sard`: the latter is the arbitrary-finite-dimension
statement and remains a direct hole, with both consumers still inheriting `sorryAx`. Holes stay
**11**, certificates **24**, perimeter infrastructure **missing**.

The two modules and the independent client pass `-DwarningAsError=true`; 16 axiom reports use only
standard axioms, covering the previously recorded compact-`K` obligation verbatim, an arbitrary
non-measurable subset, a constant function whose critical set is the **whole plane** yet has null
image, and `x ↦ (x 0)²` whose critical set is proved to be exactly the line `{x 0 = 0}`.
QuadraticCoverAudit, QuadraticRemainderAudit, SardLowDimAudit, AreaFormulaAudit and
SuperlevelSardScope re-pass strictly; the three WIP files re-elaborate with **3/3/5** direct-hole
warnings only. Default `lake build` passes (3393 jobs). The final root verification receipt is
`build/verification/latest.json`; the incoming passed receipt `20260914T150543.429034Z` was matched
byte-for-byte to the working tree. HEAD stays `2965b32`; no commit/push.

Next: the `n`-dimensional covering lemma and the order-`n` uniform remainder at fully flat points,
both type-checked but unproved in `build/audit/HigherSardNextStatement.lean`. They give only the
top layer in dimension `n`; the intermediate layers still need finite-order implicit charts and
per-order dimension descent with regularity loss. See the
[new decision](research/decisions/2026-09-14-planar-sard.md).

## Planar quadratic covering round (2026-09-14)

**Superseded by the planar Sard round above; retained as a dated snapshot.**
`Analysis.volume_image_eq_zero_of_quadratic_oscillation` and `Analysis.volume_image_flat_eq_zero`
are proved in `formalization/FunctionalInequalities/Analysis/QuadraticCover.lean`, with standard
three axioms only. The covering lemma is exactly the statement proposed last round: for a bounded
`A : Set (Fin 2 → ℝ)` and an arbitrary `f`, a uniform `|f y - f x| ≤ ε‖y-x‖²` on pairs of points of
`A` forces `volume (f '' A) = 0`. Neither `A` nor `f '' A` is assumed measurable and `f` has no
regularity anywhere; the empty set is covered. The proof grids `A` into `O(r⁻²)` cells of width
`r = min δ 1` indexed by `⌊·/r⌋ : ℤ × ℤ`, picks one `A`-representative per occupied cell, covers
its image by an interval of length `2εr²`, and sums with `measure_biUnion_finset_le`; the total
`2ε(2R+3)²` is independent of `r`, and `ENNReal.le_of_forall_pos_le_add` sends `ε → 0`. Dimension
two is used where the cell count `O(r⁻²)` meets the interval length `O(εr²)`.

Connecting it to `Analysis.exists_uniform_quadratic_remainder` gives the second-order flat layer:
for `C²` `u` and compact `K ⊆ Fin 2 → ℝ`, the image of `{x ∈ K | Du x = 0 ∧ D²u x = 0}` is null.
Flatness is pointwise on that **subset**; all of `K` is not assumed flat, and the subset is not
assumed measurable. `Analysis.volume_image_flat_univ_eq_zero` exhausts the plane by
`⋃ n : ℕ, closedBall 0 n` and drops compactness, boundedness and measurability entirely. Mathlib-only imports plus the local `Analysis/TaylorRemainder`; no existing
declaration moved or changed, no WIP dependency or certificate expansion.

The new module and independent client pass `-DwarningAsError=true`; 19 axiom reports use only
standard axioms, covering the empty set, a singleton with a completely arbitrary `f`, an arbitrary
bounded set with no measurability instance in the client at all, the hypothesis-free whole-plane
flat layer, and the flat layer of the nonconstant `x ↦ (x 0)³` on a closed ball, together with an
explicit nonflat point `![1,0]` and an explicit flat point `0` inside that ball. QuadraticRemainderAudit, SardLowDimAudit, AreaFormulaAudit
and SuperlevelSardScope re-pass strictly. The three WIP files actually re-elaborate with **3/3/5**
direct-hole warnings only. General Sard and its two consumers still inherit `sorryAx`: holes stay
**11**, certificates **24**, perimeter infrastructure **missing**. No coarea, reverse Cheeger
comparison or equality is proved. Default `lake build` passes (3393 jobs). The final root
verification receipt is `build/verification/latest.json`; the incoming passed receipt
`20260913T190354.174769Z` was matched byte-for-byte to all 390 files. HEAD stays `2965b32`;
no commit/push.

This round completes the **planar second-order flat layer only**. The planar nonflat layer
`{x ∈ K | Du x = 0 ∧ D²u x ≠ 0}` (type-checked, unproved, in
`build/audit/PlanarNonflatNextStatement.lean`), general Sard, weighted coarea and the reverse
Cheeger comparison are all still unproved, and nothing here closes the chain. See the
[new decision](research/decisions/2026-09-14-planar-quadratic-cover.md).

## Uniform quadratic remainder round (2026-09-14)

**Superseded by the planar covering round above; retained as a dated snapshot.**
`Analysis.exists_uniform_quadratic_remainder` is proved in
`formalization/FunctionalInequalities/Analysis/TaylorRemainder.lean`, with standard three axioms
only. For a C² real-valued function and compact K, every ε>0 has a single δ>0 such that
`|u y-u x| ≤ ε * ‖y-x‖²` whenever x∈K has Du(x)=D²u(x)=0 and ‖y-x‖<δ.
Not all of K must be flat; y may lie outside K. Empty K, zero dimension and y=x are included.
The proof works on arbitrary real normed spaces, without finite dimension, completeness,
inner product or domain measure. It uses Heine–Cantor's external-neighbourhood control and two
convex mean-value inequalities, rather than adding a Taylor framework. Mathlib-only imports;
no existing declaration moved or changed, no WIP dependency or certificate expansion.

The new module and independent client pass `-DwarningAsError=true`; 10 axiom reports use only
standard axioms, including cubic-function tests with nonflat points in K and an actual point
outside K. SardLowDimAudit, AreaFormulaAudit and SuperlevelSardScope re-pass strictly.
The three WIP files actually re-elaborate with **3/3/5** direct-hole warnings only.
General Sard and its two consumers still inherit `sorryAx`: holes stay **11**, certificates **24**,
perimeter infrastructure **missing**. No coarea, reverse Cheeger comparison or equality is proved.
Default `lake build` passes (3393 jobs). The final root verification receipt is
`build/verification/latest.json`; the incoming passed
receipt `20260913T184752.039532Z` was matched to all 387 files. HEAD stays `2965b32`; no commit/push.

Next: the bounded planar-set covering lemma turning uniform o(r²) oscillation into nullity of
the image, with no measurability assumption. Its precise statement and the remaining higher-order
and dimension-descent gaps are in the
[new decision](research/decisions/2026-09-14-uniform-quadratic-remainder.md).
The new estimate itself is not an image-nullity or general Sard theorem.

## Low-dimensional Sard round (2026-09-14)

**Superseded by the quadratic remainder round above; retained as a dated snapshot.**
`Analysis.sard_of_finrank_le_one` is proved in
`formalization/FunctionalInequalities/Analysis/Sard.lean`, with only
`propext`, `Classical.choice`, `Quot.sound`. It covers arbitrary finite-dimensional real normed
spaces of dimension at most one, with exactly `ContDiff ℝ (Module.finrank ℝ V) u`:
zero dimension uses a subsingleton domain and a singleton image; dimension one uses
`e : ℝ ≃L[ℝ] V`, the chain rule with zero derivative on the pulled-back critical set, and
Mathlib's equidimensional null-image theorem. Only the target's Lebesgue measure is used.
There is no domain measure, inner product, critical-set measurability, compact-support or
boundedness assumption. The new module imports Mathlib only, with no local dependency or migration.

The original general `Analysis.sard` and its consumers retain their statements and proofs.
`sard`, `ae_forall_fderiv_ne_zero` and `SmoothDomain.ae_exists_superlevel` each still carry
`sorryAx`. Direct holes remain **11 = 3 / 3 / 5**; certificates remain **24** and perimeter
infrastructure remains **missing**. General Sard, weighted coarea, its level-set measurability,
`h_S ≤ h_M`, equality of Cheeger constants and the full chain are still unproved.

`build/audit/AreaFormulaAudit.lean` now explicitly imports `Analysis.Divergence` and passes strict
compilation with six standard-axiom reports. The `ae_exists_superlevel` docstring now says `t-u`.
The low-dimensional independent client passes `-DwarningAsError=true`, with eight standard-axiom
reports covering general one-dimensional normed spaces, arbitrary functions on the zero-dimensional
space, real C¹ functions, constants, and the square function with a proved critical point and
nonconstancy. All 16 selected existing clients pass strictly; the Sard scope client's inherited
`sorryAx` is expected and separately recorded. The four selected hole-free modules pass strictly;
all three WIP modules actually re-elaborate with exactly 3/3/5 hole warnings and no other diagnostic.
Default `lake build` passes (3393 jobs). Root verification binds the final snapshot; its
authoritative final receipt is `build/verification/latest.json`, not the incoming receipt.

**Next bounded obligation:** the uniform quadratic remainder at points with vanishing first and
second derivatives on a compact set, stated precisely in the
[new decision](research/decisions/2026-09-14-low-dimensional-sard.md).
Mathlib already provides multivariate integral Taylor, inverse/implicit function, chain-rule and
countable-cover tools. Higher-order critical strata, regularity-preserving dimension descent and
the quantitative covering/null-image argument are still missing; naive descent loses regularity
on higher strata. A base case is not a completed induction.
Incoming receipt `20260913T182956.860385Z` was independently matched to all 384 files.
HEAD remains `2965b32`; no commit or push. All earlier uncommitted work is preserved.

## Superlevel round: the regular-value smooth-domain construction is proved and the Sard packaging is filled (2026-09-14)

**Superseded by the low-dimensional Sard round above; retained as a dated snapshot.**
Two results, deliberately kept apart.

**(1) Hole-free, no `sorryAx`.** `SmoothDomain.ofSuperlevel` and its `ofSuperlevel_carrier` are new
in `formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain.lean`: a strict superlevel set
`{x | t < u x}` of a `C^∞` function is a smooth domain as soon as `fderiv ℝ u` is nonzero on
**`frontier {x | t < u x}`** — not on the whole level set `{x | u x = t}` and not on the whole
space. The defining data is `W = {y | fderiv ℝ u y ≠ 0}`, open because `hu.continuous_fderiv` makes
`y ↦ fderiv ℝ u y` continuous, and `φ = t - u`, matching the structure's **negative**-sublevel
convention: `fderiv_const_sub` and `neg_ne_zero` give nonvanishing, and
`carrier ∩ W = {y ∈ W | φ y < 0}` is the pure rewrite `t - u y < 0 ↔ t < u y`. Empty frontier, empty
carrier, full carrier and dimension zero are covered by the construction itself, with no extra
hypothesis and no branch: in each of them the frontier is empty and the field's premise is vacuous.
The construction lives in the module that owns the structure and its other constructors
(`empty`, `univ`, `homothety`), needs only `NormedAddCommGroup` + `NormedSpace ℝ`, imports no WIP
module and builds no manifold framework.

**(2) Filled body that still inherits `sorryAx`.** `SmoothDomain.ae_exists_superlevel` in
`KLS/WIP/CheegerInfimum.lean` is no longer a direct hole: its statement text is unchanged and its
proof is `filter_upwards [Analysis.ae_forall_fderiv_ne_zero (hu.of_le ENat.LEInfty.out)]` followed
by `ofSuperlevel` applied through `frontier_superlevel_subset`. It **still depends on `sorryAx`**
through `Analysis.sard`, which is untouched, and must not be listed as a `sorryAx`-free result;
it closes the Sard-to-smooth-domain *packaging* gap only and frees nothing downstream. The order
reduction's side condition is `(Module.finrank ℝ V : WithTop ℕ∞) ≤ ∞`, discharged by
`ENat.LEInfty.out`: `le_top` does not apply (that type's top is `ω`, not `∞`) and `simp` makes no
progress.

No module migration. `frontier_superlevel_subset` stays in `KLS/WIP/CheegerInfimum.lean` — its only
consumer is the wrapper in the same file, and the frontier-form hypothesis means the hole-free
construction does not need it; it was only moved **above** the wrapper inside that file, carrying
its `omit ... in` prefix. `KLS/WIP/CheegerInfimum.lean` gains one import line,
`FunctionalInequalities.KLS.WIP.AnalyticPrerequisites`, which no module imported before. The filled
body makes `unusedSectionVars` fire (a `sorry` body is exempt from that linter), so the linter is
silenced for that one declaration with a comment; `omit` was **not** used, since it would narrow the
published signature.

Current holes: **11 = 3 / 3 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. Sard, the weighted coarea and
its level-set measurability are untouched direct holes, so this is **not** Sard, **not** the reverse
comparison, **not** an equality of Cheeger constants and **not** a completed chain.

`Geometry/SmoothDomain.lean` and the new `build/audit/SuperlevelDomainAudit.lean` pass
`-DwarningAsError=true`, the client's 8 axiom reports using only the standard three axioms and
covering the frontier-only hypothesis, the sign direction of the defining function, an
**everywhere-critical** level set with empty frontier (empty carrier), the full carrier, dimension
zero and an unbounded half-space with explicitly unbounded carrier and frontier. The separate
`build/audit/SuperlevelSardScope.lean` records that `ae_exists_superlevel` carries `sorryAx`.
The `pp.all` `#check` output for `ae_exists_superlevel` and `frontier_superlevel_subset` is
byte-identical before and after. `KLS/WIP/CheegerInfimum.lean` re-elaborates with exactly 3 hole
warnings and no other diagnostics. The `BoundaryChartAudit`, `CheegerInfimumAudit`,
`CutoffRouteReview`, `DilationAudit`, `DistanceCutoffAudit`, `GaussGreenAudit`,
`MinkowskiCoareaAudit`, `MinkowskiConstantAudit`, `MollifiedBoundaryScope`,
`PerimeterInterfaceAudit`, `RecoveryAudit` and `SubgraphDivergenceAudit` clients re-pass;
`build/audit/AreaFormulaAudit.lean` remains broken from an **earlier** round (it names
`Analysis.divergence` without importing `Analysis/Divergence.lean`) and was left as it is.
Read the [new decision](research/decisions/2026-09-14-regular-superlevel-smooth-domain.md).

**Route correction and completed base case:** `Analysis.sard_of_finrank_le_one` is now proved
as recorded above. Use `ContinuousLinearEquiv.ofFinrankEq` from ℝ to V, then the zero-derivative
chain rule and the equidimensional null-image theorem on ℝ. No isometry or measure-preserving
transport is needed. The original derivative `V →L[ℝ] ℝ` is not an endomorphism and must not be
assigned a determinant. The zero-dimensional branch uses only subsingletonness, not C¹.
The [new decision](research/decisions/2026-09-14-low-dimensional-sard.md) corrects the earlier
historical decision without rewriting it. The general Sard hole remains open.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Distance-cutoff round: the gradient integral estimate is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written, the dated rounds below
retain their earlier snapshots, and the
[route correction](research/decisions/2026-09-13-cutoff-route-audit-correction.md) supersedes the
status and next-step text of the round below it.**
`Isoperimetry.lintegral_enorm_gradient_distanceCutoff_le` is proved, with its original statement
text, in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean`, whose **local import
closure is empty** (Mathlib only): for every probability law `ν`, every `r > 0` and an **arbitrary**
`B` — not assumed nonempty, measurable, closed or bounded, and with no null boundary —
`∫ ‖∇w_r‖ dν ≤ (ν(B^r) - ν(closure B)) / r`,
with `closure B` on the right rather than the weaker `ν(B)`, and with the thickening still open.
The Haar measure `m`, its instance and `hac` are kept verbatim in the signature although the proof
does not use them; nothing in the interface changed.

The route is pointwise, not almost-everywhere. Empty `B` is a separate branch: Mathlib's
`Metric.infDist x ∅ = 0` makes `distanceCutoff ∅ r` the constant **`1`**, not `0`, so
`gradient_fun_const` gives zero on the left, while `thickening r ∅ = ∅` and `closure ∅ = ∅` make the
right-hand side zero — no `B.Nonempty` was added to dodge this. For nonempty `B`, `w_r` attains its
global maximum `1` on `closure B` and its global minimum `0` outside the open thickening, so
`IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero` make the gradient vanish **at every
point** of those two sets, the endpoint level sets `{d = 0}` and `{d = r}` included; neither lemma
needs a `DifferentiableAt` hypothesis, because Mathlib defines `fderiv` and `gradient` to be zero at
points of non-differentiability. On the open annulus `B^r ∖ closure B` — measurable because the
thickening is open and the closure closed, **not** because `B` is measurable —
`norm_fderiv_le_of_lipschitz` with the proved `lipschitzWith_distanceCutoff` bounds the gradient by
`1/r`. Then `lintegral_mono`, `lintegral_indicator_const`, `measure_sdiff` via
`Metric.closure_subset_thickening`, and `ENNReal.ofReal_inv_of_pos` with `ENNReal.div_eq_inv_mul` to
match the original division. No Rademacher, no Lebesgue density theorem, no general "the gradient
vanishes almost everywhere on a level set" lemma and no absolute continuity. The two unused-argument
linters are silenced for this one declaration with a comment, never file-wide, and no hypothesis was
deleted or given a fake use; the non-differentiability convention is local to this estimate and is
**not** a comparison result for singular laws.

Layer changes: `Geometry/DistanceCutoff.lean` is new, hole-free and Mathlib-only. The complete cutoff
basis moved there verbatim — `distanceCutoff`, `distanceCutoff_mem_Icc`,
`lipschitzWith_distanceCutoff`, `distanceCutoff_eq_one_of_mem_closure`,
`distanceCutoff_eq_zero_of_notMem_thickening` and the `L¹(ν)` convergence
`tendsto_distanceCutoff_indicator` — with all seven `pp.all` signatures byte-identical before and
after the move. `exists_smooth_approximation_lipschitz` was deliberately **not** moved: it is
already proved, but it belongs to the smooth-replacement interface rather than the cutoff basis and
would drag the `Energy.Euclidean.LipschitzApproximation` import into a geometry module. Sard, the
coarea obligations, the reverse comparison, the equality and the affine-support transport stay in
`KLS/WIP/CheegerInfimum.lean`, which gains one import line.
`Geometry/{MinkowskiConstant,CheegerInfimum,PerimeterRecovery}.lean` are untouched.

Current holes: **12 = 3 / 4 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. This is a gradient estimate on
the reverse-direction chain — **not** the reverse comparison, **not** an equality of Cheeger
constants, **not** a completed chain. `smoothConstant_le_minkowskiConstant` is still a direct hole,
and `minkowskiConstant_eq_smoothConstant`, which has a `le_antisymm` body, inherits `sorryAx`
through it.

The new module and `Geometry/{CheegerInfimum,MinkowskiConstant,MinkowskiContent}` pass
`-DwarningAsError=true`; the new `build/audit/DistanceCutoffAudit.lean` has 7 clients and 14 axiom
reports, all standard three axioms, covering an explicitly **non-measurable and unbounded** `B`, the
**empty set whose cutoff is constantly `1`**, the whole space, dimension zero, vanishing of the
gradient at **every** point of `closure B` (inner endpoint level set included), the same at the
**outer endpoint level set `{d = r}`**, and the migrated `L¹` convergence. The `CheegerInfimumAudit`,
`MinkowskiConstantAudit`, `MinkowskiCoareaAudit`, `RecoveryAudit`, `DilationAudit`,
`GaussGreenAudit` and `CutoffRouteReview` files re-pass. The three WIP files were re-elaborated with
exactly 3/4/5 hole warnings and no other diagnostics. The final root verification receipt is
`build/verification/latest.json`; the incoming passed receipt matched all 381 files. Read the
[new decision](research/decisions/2026-09-13-distance-cutoff-gradient-integral.md).

**What the reverse direction still needs, kept apart:** (1) weighted coarea
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` — **direct hole**; (2) level-set
integral measurability `Analysis.aemeasurable_lintegral_levelSet` — a **separate direct hole**;
(3) Sard `Analysis.sard` — **direct hole**, with `Analysis.ae_forall_fderiv_ne_zero` a filled body
inheriting `sorryAx` through it; (4) the Sard-to-smooth-superlevel packaging
`SmoothDomain.ae_exists_superlevel` — **still a direct hole, not a filled body**; (5) the assembly
`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (`C¹` specialization),
`smoothConstant_mul_lintegral_min_superlevel_le` and `smoothConstant_le_minkowskiConstant`.

**Next target: `SmoothDomain.ae_exists_superlevel`** — the packaging in (4), the clearest-bounded
remaining step. Proving it makes it a filled body that **still inherits `sorryAx` through
`Analysis.sard`**, so it closes the packaging gap only and frees nothing downstream; direct holes go
12 → 11 (3/3/5). Route: `carrier = {x | t < u x}` with `isOpen_lt`; the proved
`frontier_superlevel_subset` gives `u x = t` at a frontier point; `ae_forall_fderiv_ne_zero`, after
`hu.of_le` from `ContDiff ℝ ∞` down to `ContDiff ℝ (Module.finrank ℝ V)` — side condition
`(finrank : WithTop ℕ∞) ≤ ∞`, **not** `le_top`, since `∞` is not that type's top — gives
`fderiv ℝ u x ≠ 0`; take `W = {y | fderiv ℝ u y ≠ 0}`, open because `hu.continuous_fderiv` makes
`y ↦ fderiv ℝ u y` continuous; take `φ = fun y ↦ t - u y`, smooth by `contDiff_const.sub hu`, with
`fderiv_const_sub` and `neg_ne_zero` for nonvanishing and `carrier ∩ W = {y ∈ W | φ y < 0}` a pure
set rewrite; combine with `filter_upwards`. The two large analytic blocks, weighted coarea and Sard,
are untouched this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## One-sided Cheeger round: `h_M ≤ h_S` is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written, and its status and
next-step text are corrected by the
[route correction](research/decisions/2026-09-13-cutoff-route-audit-correction.md).**
`Isoperimetry.minkowskiConstant_le_smoothConstant` is proved, with its original statement text, in
the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean`: for every finite-dimensional
real inner-product space — **zero dimension included** — and every Borell density `ρ` of `ν`
relative to Lebesgue `volume`,
`minkowskiConstant ν ≤ smoothConstant ρ (interior ν.support) ν`.
No bounded support, no bounded domain, no finite total boundary measure, no finiteness or
positivity of either constant, no existence of an admissible smooth domain and no finiteness of
relative perimeters were added; the `iInf` definition of `smoothConstant`, the `relativePerimeter`
normalization, `Ω = interior ν.support` and all admissible sets are unchanged. The reverse
comparison, weighted coarea, Sard and every `sorryAx`-carrying WIP theorem are unused.

**Only one direction is proved.** `smoothConstant_le_minkowskiConstant` still has a direct `sorry`;
`minkowskiConstant_eq_smoothConstant` has a `le_antisymm` body but inherits `sorryAx` from
that reverse direction. The **equality of the two Cheeger constants is not established**,
and neither is the relative-perimeter comparison chain.

The route is: `simp only [smoothConstant]` and three `le_iInf` layers, then
`ENNReal.le_div_iff_mul_le` with `m ≠ 0` (from `lt_min` and `tsub_pos_of_lt`) and `m ≠ ⊤` (from
`prob_le_one`), reducing the goal to `h_M · m ≤ P_ρ(U)` → a case split on `P_ρ(U) = ⊤`, where
`le_top` finishes and `exists_smooth_recovery_sequence` is never invoked, so its finiteness
argument stays a branch-local fact rather than a hypothesis of the theorem → unpacking the
recovery sequence, with `ContDiff.of_le` down to `C¹` whose side condition `(1 : WithTop ℕ∞) ≤ ∞`
is discharged by `simp` and **not** by `le_top` (`∞` is not that type's top), and per-term
application of `minkowskiConstant_mul_lintegral_min_superlevel_le` → the already proved
`tendsto_lintegral_min_superlevel`, fed by `U.isOpen.measurableSet`, giving `I_j → m` →
`ENNReal.Tendsto.const_mul` with `Or.inl (m ≠ 0)`, which is exactly what keeps `h_M = ⊤`
legitimate, then `Tendsto.limsup_eq` and `limsup_le_limsup` against the recovery-sequence `limsup`
bound. `h_M` is never divided out and no limit is exchanged with an integral without proof. When no
admissible smooth domain exists, `le_iInf` has an empty premise and the bound is covered by the
`iInf` structure itself; no nonemptiness or positive-dimension assumption was added.

Layer changes: `Geometry/CheegerInfimum.lean` is new and hole-free, and its 32-module local import
closure contains **no WIP module**. `smoothConstant`, `smoothConstant_eq_top_of_subsingleton`,
`lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff` and
`tendsto_lintegral_min_superlevel` moved there verbatim from `KLS/WIP/CheegerInfimum.lean`; the
`pp.all` signatures of all six declarations — the newly proved theorem included — are byte-identical
before and after the move, and `unusedSectionVars` reports nothing on the filled body, so no
hypothesis or type changed. `Geometry/MinkowskiConstant.lean` was left untouched: no recovery,
relative-perimeter or WIP dependency was pushed into that base layer. Sard, weighted coarea, the
distance cutoffs, the reverse comparison, the equality and the affine-support transport stay in
`KLS/WIP/CheegerInfimum.lean`, which now imports only the new module.

Current holes: **13 = 3 / 5 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**.

The new module and `Geometry/{MinkowskiContent,MinkowskiConstant,PerimeterRecovery}` pass
`-DwarningAsError=true`; the new `build/audit/CheegerInfimumAudit.lean` has 6 clients and 14 axiom
reports, all standard three axioms, covering the general case with an explicitly unbounded support,
dimension zero with both infima `⊤`, **no admissible smooth domain** (so `h_S = ⊤` from the `iInf`
structure alone), a single admissible domain of **infinite relative perimeter** whose quotient is
`⊤` and constrains nothing, an admissible domain of **zero relative perimeter** forcing
`h_M = 0`, and `h_M = ⊤` forcing every admissible domain to have infinite relative perimeter with
no division. The `MinkowskiConstantAudit`, `MinkowskiCoareaAudit`, `RecoveryAudit`, `DilationAudit`
and `GaussGreenAudit` clients re-pass. The three WIP files were re-elaborated with exactly 3/5/5
hole warnings and no other diagnostics. The final root verification receipt is
`build/verification/latest.json`; the incoming passed receipt matched all 378 files. Read the
[new decision](research/decisions/2026-09-13-cheeger-infimum-one-sided.md).

**Next target: `lintegral_enorm_gradient_distanceCutoff_le`** — the only one of the three
reverse-direction gaps independent of Sard and coarea, so it can be finished on its own and takes
`WIP/CheegerInfimum` from 5 holes to 4. Route, with Mathlib names checked: empty `B` is a separate
branch where `Metric.infDist_empty` makes the cutoff constant and both sides vanish, so no
nonemptiness hypothesis is added; for nonempty `B`, `mem_closure_iff_infDist_zero` and
`mem_thickening_iff_infDist_lt` identify `closure B = {d = 0}` and `thickening r B = {d < r}`, and
`{0 < w_r < 1}` is the **open** annulus. The key step needs **no Lebesgue density theorem**: `w_r`
attains its global maximum `1` on `closure B` and its global minimum `0` on `{d ≥ r}`, so
`IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero` kill the gradient at **every point**
there, without a differentiability hypothesis. Mathlib defines `fderiv` and `gradient` as zero
at nondifferentiable points, and `norm_fderiv_le_of_lipschitz` likewise needs no differentiability
hypothesis. Thus a pointwise annulus bound followed by `lintegral_mono`,
`lintegral_indicator_const` and `measure_sdiff` suffices; no Rademacher theorem or use of `hac`
is needed for this route. Keep the original theorem signature, including `m` and `hac`.
For empty `B` the cutoff is specifically the constant **one**, with zero gradient and zero RHS.
`SmoothDomain.ae_exists_superlevel` remains a **direct hole**; only
`Analysis.ae_forall_fderiv_ne_zero` has a filled body inheriting `sorryAx` from Sard.
See the [audit correction](research/decisions/2026-09-13-cutoff-route-audit-correction.md),
which supersedes the corresponding route and status claims in the historical decision.
By contrast `exists_smooth_approximation_lipschitz` is already
**proved** from the certified `LipschitzApproximation.exists_smooth_bounded_L1` and needs no
further work; weighted coarea and Sard remain the two large blocks, untouched this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Minkowski-constant round: the integrated coarea bound is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`Isoperimetry.minkowskiConstant_mul_lintegral_min_superlevel_le` is proved, with its original
statement text, in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/MinkowskiConstant.lean`: for every probability
law `ν` on a finite-dimensional real inner-product space and every `C¹`, globally Lipschitz,
`[0,1]`-valued `u`,
`h_M · ∫₀¹ min {ν{u > t}, 1 - ν{u > t}} dt ≤ ∫ ‖∇u‖ dν`.
The law may be singular or atomic; no density, no absolute continuity, no nonatomicity, no positive
dimension, no finiteness or positivity of `h_M` and no null superlevel boundary were added, and the
admissible sets of `minkowskiConstant` and the definition of `minkowskiContent` are unchanged.
Neither the smooth recovery sequence, weighted coarea nor Sard is used.

The route is: `ae_measure_superlevel_lt_eq_le` — for **any** `SFinite` measure and **any**
measurable `u`, the strict and the closed superlevel sets have equal mass for Lebesgue-almost every
level, because the level sets `{u = t}` are pairwise disjoint
(`Measure.countable_meas_level_set_pos`, `Set.Countable.measure_zero`) → `minkowskiConstant_mul_min_le`,
the defining infimum in multiplied form `h_M · m(ν B) ≤ ν⁺(B)`, whose only case split is zero
balance, where `mul_zero` absorbs `⊤`, against intermediate mass, where `iInf_le` and
`ENNReal.le_div_iff_mul_le` apply, so degenerate levels are never substituted into the infimum and
`h_M` is never divided out → `measurable_min_measure_superlevel`, the measurability of the balance
for an arbitrary `u`, extracted from the inlined `hFmeas` of `tendsto_lintegral_min_superlevel`,
whose proof was migrated rather than duplicated → `lintegral_const_mul` to move `h_M` inside (the
only place `⊤ · I` could appear, after which `⊤` meets `m = 0` only pointwise), `lintegral_mono_ae`,
`setLIntegral_le_lintegral` to enlarge `Ioo 0 1` to the whole axis, and the proved
`lintegral_minkowskiContent_superlevel_le`. `t ↦ ν⁺({u ≥ t})` is still never assumed measurable.

Layer changes: `Geometry/MinkowskiConstant.lean` is new, hole-free, and its local import closure is
the single hole-free `Geometry/MinkowskiContent.lean`. `minkowskiConstant` and
`minkowskiConstant_eq_top_of_subsingleton` moved there verbatim from `KLS/WIP/CheegerInfimum.lean`;
the `pp.all` signatures of all three migrated declarations are byte-identical before and after the
move, so there is no compatibility alias, forwarding declaration, empty shim or duplicated proof.
`smoothConstant`, the layer-cake identities, `tendsto_lintegral_min_superlevel`, the distance
cutoffs and the two unfinished comparisons stay in `KLS/WIP/CheegerInfimum.lean`, which now imports
the new module. `hu01` is unused by the proof and is kept in the signature with the
`unusedVariables` linter silenced, so the statement is not narrowed.

Current holes: **14 = 3 / 6 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. This round is **not** a
weighted coarea formula, not Sard, not an equality of Cheeger constants and not a completed
comparison chain.

The new module and `Geometry/MinkowskiContent.lean` pass `-DwarningAsError=true`; the new
`build/audit/MinkowskiConstantAudit.lean` has 9 clients and 17 axiom reports, all standard three
axioms, covering a law that is singular against every Haar measure **and** has an atom, zero balance
at the empty and full sets with `h_M = ⊤`, dimension zero forcing the balance integral to vanish,
constant functions, a Dirac law, an explicit `h_M = ⊤` hypothesis forcing the balance integral to
vanish with no division, almost-everywhere superlevel agreement for a Dirac law, measurability of
the balance for an arbitrary `u`, and the one-dimensional instance. The `MinkowskiCoareaAudit`,
`RecoveryAudit`, `DilationAudit` and `GaussGreenAudit` clients re-pass. The three WIP files were
re-elaborated with exactly 3/6/5 hole warnings and no other diagnostics. The final root
verification receipt is `build/verification/latest.json`; the incoming passed receipt matched all
376 files. Read the
[new decision](research/decisions/2026-09-13-minkowski-constant-coarea-product.md).

**Next target: `minkowskiConstant_le_smoothConstant`.** Every API it needs is now checked and no new
analysis is required, but it is not "already done": five side conditions have to be written — three
`le_iInf` layers plus `ENNReal.le_div_iff_mul_le` with `m ≠ 0`, `m ≠ ⊤`; a case split on
`relativePerimeter = ⊤` (`le_top`, recovery sequence not invoked), since
`exists_smooth_recovery_sequence` demands finiteness; unpacking the recovery sequence, where
`ContDiff.of_le` down to `C¹` needs `(1 : WithTop ℕ∞) ≤ ∞` and **`le_top` does not apply** because
`∞` is not that type's top (`by simp` does); `tendsto_lintegral_min_superlevel` with
`U.isOpen.measurableSet`; and `ENNReal.Tendsto.const_mul` with `Or.inl (m ≠ 0)`, which is exactly
what keeps `h_M = ⊤` legitimate, followed by `Tendsto.limsup_eq` and `limsup_le_limsup`. A layering
decision comes with it: the assembled theorem will be `sorryAx`-free while `smoothConstant` and
`tendsto_lintegral_min_superlevel` are still in WIP, so that group should then move down with its
consumers. The opposite direction still needs Sard, weighted coarea,
`lintegral_enorm_gradient_distanceCutoff_le` and
`smoothConstant_mul_lintegral_min_superlevel_le`; none of them moved this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Minkowski coarea round: the coarea inequality is proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`Isoperimetry.lintegral_minkowskiContent_superlevel_le` is proved, with its original statement
text, in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean`: for every probability
law `ν` on a finite-dimensional real inner-product space and every `C¹` globally Lipschitz `u`,
`∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`, with closed superlevel sets, the integral over the whole real
axis and the unchanged `minkowskiContent` (open thickenings, `ENNReal` truncated subtraction,
`𝓝[>] 0` liminf). The law may be singular or atomic; no density, no absolute continuity, no
bounded range or compact support for `u`, no positive dimension, no extra integrability and no
null superlevel boundary were added. Neither weighted coarea nor Sard is used.

The route is: the local supremum `ballSup u r x = sup_{closedBall x r} u`, Lipschitz with the same
constant, so `0 ≤ (ballSup u r - u)/r ≤ K` and both functions are measurable → the near-neighbour
witness `thickening r {u ≥ t} ⊆ {u < t ≤ ballSup u r} ∪ {u ≥ t}`, giving the strip bound through
`tsub_le_iff_right` and `measure_union_le` rather than a set difference → product measurability of
the strip, `measurable_measure_prodMk_left` and Tonelli, so that Fatou is applied only to the
measurable strip quotient and `t ↦ ν⁺({u ≥ t})` is never assumed measurable → radii `1/(n+1)` with
`Tendsto.liminf_le_liminf_comp` in the direction that only enlarges the original neighbourhood
liminf → the one-sided growth bound `limsup ofReal((ballSup u r_n x - u x)/r_n) ≤ ‖∇u x‖ₑ` from
Fréchet differentiability, with `limsup_lintegral_le` dominated by the constant `K`.

Layer changes: `Geometry/MinkowskiContent.lean` is new, hole-free and has a **zero-module** local
import closure (Mathlib only). `minkowskiContent` and
`measure_closure_eq_of_minkowskiContent_ne_top` moved there with their full names unchanged;
`KLS/WIP/CheegerInfimum.lean` imports the new module and keeps the unfinished Cheeger-infimum
comparisons. No compatibility alias, forwarding declaration, empty shim or duplicated proof.

Current holes: **15 = 3 / 7 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. This round is **not** a
weighted coarea formula, not Sard, not an equality of Cheeger constants and not a completed
comparison chain.

The new module passes `-DwarningAsError=true`; the new `build/audit/MinkowskiCoareaAudit.lean` has
8 clients and 18 axiom reports, all standard three axioms, covering an arbitrary probability law
that is singular against every Haar measure and an `u` with unbounded range, constant functions,
dimension zero, an atomic (Dirac) law, `ballSup u 0 = u`, the near-neighbour witness, the growth
quotient bound, and `u = id` on the line. The three earlier clients re-pass unchanged. The three
WIP files were re-elaborated with exactly 3/7/5 hole warnings and no other diagnostics. The final
root verification receipt is `build/verification/latest.json`; the incoming passed receipt matched
all 374 files. Read the
[new decision](research/decisions/2026-09-13-minkowski-coarea-inequality.md).

**Next target: `minkowskiConstant_mul_lintegral_min_superlevel_le`.** Its only missing input is the
almost-everywhere agreement of open and closed superlevel masses (the level sets `{u = t}` are
disjoint and `ν` is finite, so only countably many carry mass); the zero- and full-mass levels need
no case split because `⊤ * 0 = 0` in `ENNReal`, and the outer `⊤ * 0` is avoided by moving the
constant inside the integral with `lintegral_const_mul` instead of dividing. After that,
`minkowskiConstant_le_smoothConstant` is pure assembly of the proved recovery sequence with the
proved `tendsto_lintegral_min_superlevel`. The opposite direction still needs Sard, weighted coarea
and `lintegral_enorm_gradient_distanceCutoff_le`; none of them moved this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Recovery-sequence round: smooth recovery sequence proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`RelativePerimeter.exists_smooth_recovery_sequence` is proved in the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean`, with the original
statement text: any finite-dimensional real inner-product space, any Borell density relative to
Lebesgue `volume`, any smooth domain, only the original finite-relative-perimeter hypothesis.
The sequence is globally `C^∞`, globally Lipschitz per term, `[0,1]`-valued, converges to `𝟙_U`
in `L¹(ν)` and has `limsup ∫ ‖∇u_j‖ dν ≤ P_ρ(U)`. No boundedness of the domain, its boundary or
the carrier, no finite total boundary measure, no positive dimension and no extra density
regularity were added; the Lipschitz constants are not claimed uniform in `j`. The finiteness
hypothesis is kept in the statement but is not used by the proof, so it is bound as `_hU`.

The route is: interior density ball and global upper bound from `DensityBounds` (its existing
private ball lemma was exposed, not reproved) → `ν ≪ volume` plus the Haar-null frontier →
exact mollification off the boundary at a fixed dilation, by local constancy on the bump's outer
ball → diagonal choice of `s_j = 1 - 1/(j+2)` with bump radii meeting both
`s_j φ_j.rOut / (1 - s_j) < r` and a vanishing `L¹` tolerance → the previously proved dilation
bound with its prefactor tending to one.

Layer changes: `Geometry/PerimeterRecovery.lean` is new and hole-free, with a 30-module local
closure and no WIP import; `LogConcave/DensityBounds.lean` gained `absolutelyContinuous` and
public `exists_ball_le`; `KLS/WIP/RelativePerimeter.lean` had no content left and was **deleted**;
`KLS/WIP/CheegerInfimum.lean` now imports the new module directly. No compatibility alias,
forwarding declaration or empty shim was used.

Current holes: **16 = 3 / 8 / 5** (AnalyticPrerequisites / CheegerInfimum / Energy-WIP-Cheeger).
Certificates stay **24**; perimeter infrastructure stays **missing**. Coarea, Sard, Cheeger
infima and singular-law comparisons are untouched, and this round is **not** a coarea bridge, a
Cheeger bridge or a completion of the relative-perimeter chain.

Eight hole-free modules and three independent clients pass `-DwarningAsError=true`; the new
`build/audit/RecoveryAudit.lean` has 9 clients and 14 axiom reports, all standard three axioms,
checking simultaneously unbounded domain/boundary/carrier, per-term Lipschitz and `[0,1]` range,
arbitrary `L¹` tolerance, zero perimeter giving `limsup = 0`, dimension zero, the whole space as
an unbounded zero-perimeter domain, mollification of the full and of the empty domain (kernel
direction and normalization), and arbitrarily small bump radii. The three remaining WIP files
were actually re-elaborated with exactly 3/8/5 hole warnings. The final root verification receipt
is `build/verification/latest.json`; the incoming passed receipt matched all 372 files. Read the
[new decision](research/decisions/2026-09-13-smooth-recovery-sequence.md).

**Next target: `lintegral_minkowskiContent_superlevel_le`** (Minkowski coarea inequality,
Ambrosio–Di Marino–Gigli 2017, Lemma 3.2), the one genuinely independent analytic lemma left on
the `h_M ≤ h_S` branch. With it, `minkowskiConstant_mul_lintegral_min_superlevel_le` follows from
the almost-everywhere agreement of open and closed superlevel masses, and
`minkowskiConstant_le_smoothConstant` becomes pure assembly of this round's recovery sequence with
the already proved `tendsto_lintegral_min_superlevel`. The opposite direction still needs Sard,
weighted coarea and `lintegral_enorm_gradient_distanceCutoff_le`; none of them moved this round.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Dilated gradient round: quantitative integral bound proved (2026-09-13)

**Superseded by the round above; this snapshot is retained as written.**
`RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le` is proved in
`formalization/FunctionalInequalities/KLS/Geometry/RelativePerimeter.lean`, with the original
statement text, normalized surface measure, Lebesgue density, all dimensions, unbounded domains
and carriers, and even infinite relative perimeter. No additional hypotheses were added.

The completed route is: pointwise gradient bound → measurable Tonelli on the locally finite
restricted boundary measure → weighted normalized boundary change of variables → log-concave
kernel-average bound, including exact zero contribution outside Ω. Zero dimension is handled
by empty frontier before converting natural subtraction to the real scaling exponent.

New layers: `Geometry/SurfaceHomothety.lean` provides weighted surface change of variables;
`LogConcave/DensityBounds.lean` owns the migrated density bounds and new positivity/support
interior inclusion; `Geometry/RelativePerimeter.lean` owns the perimeter, indicator-dilation
convergence and proved quantitative bound. Its 29-module local closure contains no WIP import.
`WIP/RelativePerimeter.lean` retains only `exists_smooth_recovery_sequence`.

Current holes: **17 = 1 / 3 / 8 / 5** (RelativePerimeter / AnalyticPrerequisites /
CheegerInfimum / Energy-WIP-Cheeger). Certificates stay **24**; perimeter infrastructure stays
**missing**. Coarea, Sard, Cheeger infima and singular-law comparisons are untouched.

Ten relevant modules and two independent clients pass `-DwarningAsError=true`; 39 axiom reports
(17 dilation + 22 GaussGreen) contain only the standard three axioms. The new clients check
outside-support zero contribution, zero and finite perimeter, dimension-three factor four,
line reflection, dimension zero, and the complete one-dimensional s=1/2 density coefficient.
All four WIP files were actually re-elaborated with exactly the expected 1/3/8/5 hole warnings.
The final root verification receipt is `build/verification/latest.json`; the incoming passed
receipt matched all 368 files. Read the [new decision](research/decisions/2026-09-13-dilated-gradient-integral.md).

**Next target: `exists_smooth_recovery_sequence`.** Select an interior density ball; establish
fixed-dilation L¹ mollification convergence using local constancy away from the null frontier;
combine the existing homothety convergence with diagonal bump radii, then use the now-proved
quantitative bound and convergence of its prefactor to one for the finite-perimeter limsup.
No coarea or Sard is needed for this route. Existing private positivity-interior nonemptiness
can be exposed when needed, without reproducing its proof.
HEAD remains `2965b32`; all earlier uncommitted work is preserved. No commit or push this round.

## Mollified gradient round: pointwise bound proved, recovery still open (2026-09-13)

**Current state supersedes the dated snapshots below.**
`SmoothDomain.enorm_gradient_mollified_le` is proved, with its original mathematical scope and
normalized `surfaceMeasure`, in `formalization/FunctionalInequalities/KLS/Geometry/MollifiedBoundary.lean`.
The proof uses the proved negative boundary-vector formula, actual boundary integrability,
the integral triangle inequality, unit outward normal and nonnegative bump kernel. No boundedness,
finite total surface measure or positive-dimension hypothesis was added.

The actual import cycle is removed: `Geometry/SmoothDomain.lean` holds the domain foundations;
`Geometry/Mollification.lean` holds the mollified indicator and its regularity; the scalar
Gauss--Green formula moved into `Geometry/GaussGreen.lean`; the mollified gradient formula and
new bound live in `Geometry/MollifiedBoundary.lean`. The two duplicated private indicator/convolution
helpers were consolidated into the original, now public, interfaces. Consumers were migrated;
no compatibility alias or forwarding proof remains. The new consequence module has 15 local
modules in its import closure, **zero WIP imports** and no coarea/Sard dependency.

Current direct holes are **18**: RelativePerimeter **2**, AnalyticPrerequisites **3**,
CheegerInfimum **8**, Energy/WIP/Cheeger **5**. AnalyticPrerequisites now has four public theorems:
three holes, and one filled Sard consequence that still inherits `sorryAx`. Certificates remain
**24**; `lem:relative-perimeter-smoothing` infrastructure remains **missing**.

Validation: seven geometry modules and the independent GaussGreen client pass
`-DwarningAsError=true`; 22 axiom reports use only the standard three axioms. The client includes
the unbounded half-space bound and zero gradient when the bump vanishes on the boundary, plus the
previous orientation, interval, empty-boundary and zero-dimensional checks. Four WIP files were
actually re-elaborated, with exactly 2/3/8/5 expected hole diagnostics and no others.
Default `lake build` passed (3393 jobs). The unified final-source receipt is
`build/verification/latest.json`, produced from the root by `python3 research/verify.py`.
The incoming receipt was passed and all 364 files matched before edits.

**Next target:** `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le`.
It needs a weighted normalized boundary change of variables (the existing total-mass homothety
identity is insufficient), measurable Tonelli on the locally finite restricted surface measure,
and the convex support argument that makes the kernel-averaged density zero outside Ω.
After that, recovery still needs fixed-dilation mollification convergence in L¹, selection of an
interior density ball, diagonal radii, and the finite-perimeter limsup argument. Neither step
needs coarea or Sard. See the [new decision and exact route](research/decisions/2026-09-13-mollified-gradient-bound.md).
HEAD remains `2965b32`; prior dirty and untracked work is preserved. No commit or push this round.

## Gauss--Green round: the global vector-field theorem is proved (2026-09-13)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
**global** vector-field Gauss--Green obligation is **no longer a `sorry`**, and the two downstream
formulas it feeds are free of transitive `sorryAx` as well. The four WIP files now total **19**
direct holes (`RelativePerimeter` 3, `AnalyticPrerequisites` 3, `CheegerInfimum` 8,
`Energy/WIP/Cheeger` 5). What changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean`:**
  `KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` —
  `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}` for **any** compactly supported `C¹` vector field on a
  smooth domain. The statement is the one that carried the `sorry`, verbatim: same name, same
  namespace, the same `ContDiff ℝ 1` and `HasCompactSupport` hypotheses, the same `surfaceMeasure`
  normalization and outward orientation. Nothing was added — not boundedness of the domain, not
  finite total surface measure, not higher smoothness of `F`, not `Nontrivial V`.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/PartitionOfUnity.lean`:**
  `Analysis.exists_finset_sum_eq_of_isOpen_cover`, the finite smooth decomposition. Given an open
  cover of `tsupport F`, it produces a `Finset` and a family `G` with `ContDiff`, compact support,
  **`tsupport (G i) ⊆ W i`** (closed support, so the derivative vanishes outside `W i` too) and
  `∑ i ∈ s, G i x = F x` at **every** point of the space — an identity of functions, which is what
  may be differentiated. Because of that, no partition-derivative term ever appears: the divergence
  splits by `Analysis.divergence_finset_sum` and the flux integrand by `sum_inner`. The route is
  Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate` on `V` modelled on itself, plus
  `LocallyFinite.finite_nonempty_inter_compact` on the compact `tsupport F`.
* **All three kinds of local block are handled, and it takes all three.** The cover is: one
  boundary-chart cylinder per frontier point (`BoundaryChart.self_mem_cylinder`, then the
  chart-local identity of `LocalGaussGreen.lean`), the domain `U` itself
  (`…_of_tsupport_subset_carrier`: no flux, because `∂U` misses the open `U`, and zero volume
  integral by `Analysis.integral_divergence_eq_zero`), and `(closure U)ᶜ`
  (`…_of_tsupport_subset_compl_closure`: both sides vanish). A support lying entirely inside or
  entirely outside the domain is therefore covered, as are an empty support, an empty frontier and
  dimension zero — with no nonemptiness or nontriviality hypothesis anywhere.
* **Integrability is proved, not assumed.** `Analysis/Divergence.lean` gains `traceLM`,
  `continuous_traceLM`, `continuous_divergence`, `hasCompactSupport_divergence` and
  `divergence_finset_sum`; `GaussGreen.lean` proves `norm_outwardNormal_le_one` and
  `integrableOn_inner_outwardNormal`, the latter from `‖ν‖ ≤ 1`, `measurable_outwardNormal` and
  `isLocallyFiniteMeasure_surfaceMeasure_frontier` only — no bound on `surfaceMeasure (∂U)` is used,
  so an unbounded frontier of infinite total measure stays in scope.
* **Migration, not restatement:** `isLocallyFiniteMeasure_surfaceMeasure_frontier` and
  `integrableOn_smul_outwardNormal` moved from `AnalyticPrerequisites` into `GaussGreen.lean`
  unchanged, and `Analysis.fderiv_eq_zero_of_notMem_tsupport` moved down from
  `SubgraphDivergence.lean` to `Divergence.lean`. No compatibility alias, no duplicated proof, no
  forwarding declaration; the single consumer was migrated.

**Count correction.** `AnalyticPrerequisites` now carries **six public theorems and no definitions:
three filled bodies, three direct holes (weighted coarea, its measurability, Sard), and two of the
filled bodies free of transitive `sorryAx`** —
`setIntegral_gradient_eq_integral_smul_outwardNormal` and `gradient_mollifiedIndicator_eq` are
complete theorems now; only `ae_forall_fderiv_ne_zero` still inherits `sorryAx`, from `sard`.
Before this round it carried nine public theorems, five filled bodies, four holes and two filled
bodies free of `sorryAx`. Earlier records keep their original text.

**Still open, explicitly.** Closing Gauss--Green does **not** close the relative-perimeter chain.
Weighted coarea and Sard are untouched, and so are the mollified gradient-integral estimate and the
recovery sequence; `lem:relative-perimeter-smoothing` keeps infrastructure status `missing`, with
refreshed evidence hashes and rewritten gaps, and no ledger certificate or Blueprint anchor
changed. Read the [global Gauss--Green record](research/decisions/2026-09-13-global-gauss-green.md).

## Subgraph divergence round: the chart-local Gauss--Green is proved, the global one is not (2026-09-13)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
**global** vector-field Gauss--Green obligation of `KLS/WIP/AnalyticPrerequisites.lean` is **still
an explicit `sorry`**, and the scalar form and `gradient_mollifiedIndicator_eq` still inherit it.
The four WIP files still total **20** direct holes (`RelativePerimeter` 3,
`AnalyticPrerequisites` 4, `CheegerInfimum` 8, `Energy/WIP/Cheeger` 5). What changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/SubgraphDivergence.lean`:** the divergence formula
  on a smooth subgraph. For an orthogonal splitting `V = ι H ⊕ ℝ e`, a `C¹` height function
  `g : H → ℝ`, the graph `Ψ y = x₀ + ι y + g y • e` and the region `S` strictly below it, every
  compactly supported `C¹` vector field satisfies
  `∫_S div F = ∫_H ⟪F (Ψ y), ι (-∇g y) + e⟫ dy` (`Analysis.integral_divergence_subgraph`). The
  right-hand side is the **unnormalized** flux: the graph Jacobian `√(1 + ‖∇g‖²)` has already
  cancelled against the denominator of the unit normal, and the tangential `-∇g` term is present.
  No boundedness, no global Lipschitz bound on `g`, no nontriviality of `H`. The route is a
  measure-preserving shear chart (`WithLp 2 (H × ℝ) ≃ₗᵢ V` plus Fubini and fibrewise translation
  invariance — no Jacobian determinant is ever computed), a basis-free trace splitting of the
  divergence (`LinearMap.trace_comp_comm'` plus the rank-one identity of `Analysis/Divergence.lean`),
  and the fundamental theorem of calculus along each fibre. The same module proves
  `Analysis.integral_divergence_eq_zero` — a compactly supported `C¹` field on `H` has divergence
  integrating to zero — by induction on `finrank`, since Mathlib's divergence theorem covers only
  boxes in `Fin (n+1) → ℝ`.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/GraphIntegral.lean`:** the weighted boundary
  change of variables. The area formula is an identity of *measures of sets*;
  `Analysis.map_graphChartMap_withDensity` upgrades it to
  `map Ψ ((volume.withDensity √(1+‖∇g‖²)).restrict s) = ℋ^k ⌊ (Ψ '' s)` using injectivity and
  measurability of the graph parametrization, and `setLIntegral_image_graphChartMap` /
  `setIntegral_image_graphChartMap` state the resulting change of variables. Only measurability is
  assumed, never integrability. This is the minimal interface the flux needs, not a general area
  or manifold integration library.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/KLS/Geometry/LocalGaussGreen.lean`:**
  `KLS.SmoothDomain.BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal` — for a
  compactly supported `C¹` field with `tsupport F ⊆ C.cylinder`,
  `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}`. The support hypothesis is what makes *both* `F` and
  `div F` vanish outside the cylinder, which is what localizes the volume integral and the flux.
  The globally extended graph is **not** identified with `∂U`: the two sets agree only inside the
  cylinder, and the support condition cancels the extra sheet. Boundary integrability is never
  assumed — the restriction steps are pointwise identities of indicator functions — so an
  unbounded frontier of infinite total surface measure stays in scope.
* **Refactor, not restatement:** `KLS.SmoothDomain.isGraphSplitting_tangent` keeps its name and
  statement and is now one line, calling the new general
  `Analysis.isGraphSplitting_orthogonal`; `Analysis.graphChartMap_injective` likewise calls the
  new `graphChartMap_injective_of_perp`. No duplicated proof, no compatibility alias.

**Still open, explicitly.** The global
`integral_divergence_eq_integral_inner_outwardNormal` now needs exactly **one** further piece: a
finite smooth partition of unity subordinate to a cover of the compact support by chart cylinders,
with the partition-derivative terms cancelling. Coarea, Sard and the recovery sequence remain
untouched. Read the
[subgraph record](research/decisions/2026-09-13-subgraph-divergence-and-local-gauss-green.md).
Nothing here registers `lem:relative-perimeter-smoothing`; its infrastructure status stays
`missing`, with refreshed evidence hashes and shortened gaps.

## Boundary chart round: the local smooth graph is proved, Gauss--Green is not (2026-09-13)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
vector-field Gauss--Green obligation of `KLS/WIP/AnalyticPrerequisites.lean` is **still an explicit
`sorry`**, and the scalar form and `gradient_mollifiedIndicator_eq` still inherit it. The four WIP
files still total **20** direct holes (`RelativePerimeter` 3, `AnalyticPrerequisites` 4,
`CheegerInfimum` 8, `Energy/WIP/Cheeger` 5). What changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/ImplicitGraph.lean`:** the local `C^∞` graph
  representation of a regular level set. For `φ` of class `C^∞` with `φ x₀ = 0` and
  `∇φ x₀ = c • e`, `c > 0`, inside an explicit cylinder `{φ = 0}` is *exactly* the graph
  `Ψ y = x₀ + ι y + g y • e` and `{φ < 0}` is *exactly* the part below it
  (`Analysis.exists_graphRepr`). The height function is **globally** `C^∞`. The route is the
  `C^k` inverse function theorem applied to the flattening chart, plus the openness of the
  invertible operators, which upgrades `ContDiffAt.to_localInverse`'s single-point conclusion to a
  neighbourhood; Mathlib's implicit function theorem gives only strict differentiability at one
  point. The same module proves the gradient identity
  `∇φ(Ψ y) = ⟨∇φ(Ψ y), e⟩ • (ι(-∇g y) + e)` and its normalization.
* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/KLS/Geometry/BoundaryChart.lean`:**
  `KLS.SmoothDomain.exists_boundaryChart` — every frontier point of a smooth domain has such a
  chart, with `∂U ∩ Cyl = Ψ '' param`, `U ∩ Cyl` exactly the region below the graph, and
  `ν = (ι(-∇g) + ν₀)/√(1 + ‖∇g‖²)` along the graph, the sign fixed rather than up to `±`.
  `BoundaryChart.surfaceMeasure_image` is the area identity
  `surfaceMeasure (Ψ '' s) = ∫_s √(1 + ‖∇g‖²)` against the Lebesgue measure of the tangent
  hyperplane, for one chart's parameter set — not for the whole boundary. The local-to-global
  regularity gap is closed by a `ContDiffBump` cutoff **inside** `exists_graphRepr`, so no consumer
  turns a `ContDiffOn` into a `ContDiff` and no global extension is assumed.
* **Migration, not restatement:** `SmoothDomain.outwardNormal` and its four proved lemmas
  (`outwardNormal_eq`, `norm_outwardNormal`, `continuousOn_outwardNormal`,
  `measurable_outwardNormal`) moved out of `AnalyticPrerequisites` into the new `BoundaryChart`
  module, below it, with names and statements unchanged; the single consumer was migrated. No
  compatibility alias, no duplicated proof, no forwarding declaration. The `SmoothDomain` structure
  itself did not move.

**Count correction.** `AnalyticPrerequisites` now carries **nine public theorems and no
definitions: five filled bodies, four direct holes, and only two of the filled bodies free of
transitive `sorryAx`.** Before the migration it carried **thirteen public theorems and one
definition** (`outwardNormal`), nine filled theorem bodies, four holes, six filled theorems free of
`sorryAx`. The "12 obligations, 8 filled" of the 2026-09-12 records subtracted the migrated
`divergence` *definition* from the *theorem* count; those records keep their original text and the
correction is recorded in the new decision record.

**Still open, explicitly.** `integral_divergence_eq_integral_inner_outwardNormal` now needs two
further pieces, one fewer than before: the local Gauss--Green identity on a subgraph (Fubini along
`V ≅ H × ℝ`, the fundamental theorem of calculus in the normal direction, differentiation under a
variable-limit integral in the tangential directions), and a finite smooth partition of unity to
glue the local identities. Coarea, Sard and the recovery sequence remain untouched. Read the
[boundary-chart record](research/decisions/2026-09-13-boundary-chart-and-area-interface.md).
Nothing here registers `lem:relative-perimeter-smoothing`; its infrastructure status stays
`missing`, with refreshed evidence hashes and shortened gaps.

## Gauss--Green round: the area formula is proved, the theorem is not (2026-09-12)

The ledger still has 24 certified nodes; this round added none and changed no certificate. The
two Gauss--Green targets of `KLS/WIP/AnalyticPrerequisites.lean` are **not** complete. What
changed:

* **Proved, standard axioms only, new module
  `formalization/FunctionalInequalities/Analysis/AreaFormula.lean`:** the codimension-one area
  formula for `C¹` graphs. For a linear isometry `ι : H →ₗᵢ V`, a unit `e` orthogonal to its range
  and `g : H → ℝ` of class `C¹`, the graph map `Ψ y = ι y + g y • e` satisfies
  `ℋ^k (Ψ '' s) = ∫_s √(1 + ‖∇g y‖²) dy` for every measurable `s`, in the normalized convention
  (`Analysis.hausdorffNormalized_image_graphMap`) and in Mathlib's convention
  (`Analysis.hausdorffMeasure_image_graphMap`). No boundedness anywhere; dimension zero included.
  This is the geometric input that the repository's own earlier assessment named as the residual
  sub-obligation of Gauss--Green ("the area formula for Lipschitz graphs"), and Mathlib has only
  the equal-dimension change of variables.
* **Proved, new module `Analysis/Divergence.lean`:** `divergence` (moved down out of WIP) with the
  rank-one trace identity `divergence (η • v) = ⟪∇η, v⟫` for a constant vector `v`.
* **Reduction, not a proof:** `setIntegral_gradient_eq_integral_smul_outwardNormal` (the scalar
  test form, `∫_U ∇η = ∫_{∂U} η ν`) is now *derived* from
  `integral_divergence_eq_integral_inner_outwardNormal` (the vector-field form) by taking
  `F = η • v` and commuting both integrals with the inner product. It therefore still depends on
  `sorryAx`, and so does `gradient_mollifiedIndicator_eq`. Only the vector-field form remains as
  an *independent* Gauss--Green obligation: `AnalyticPrerequisites` goes from 5 direct holes to 4,
  and the four WIP files from 21 to 20.

**Still open, explicitly.** `integral_divergence_eq_integral_inner_outwardNormal` needs three
further pieces, none of which is in Mathlib or in this repository:

1. a `C^∞` implicit-function representation of a `SmoothDomain` frontier as a graph over a tangent
   hyperplane, with the side condition and the identification `ν = (ι(-∇g) + e)/√(1 + ‖∇g‖²)`.
   Mathlib's implicit function theorem gives strict differentiability at one point, not `C¹`
   regularity on a neighbourhood; the `C^k` route goes through `ContDiffAt.to_localInverse`;
2. the local Gauss--Green identity on a subgraph, by Fubini along `V ≅ H × ℝ` plus the fundamental
   theorem of calculus in the normal direction and differentiation under a variable-limit integral
   in the tangential directions;
3. a finite smooth partition of unity subordinate to a cover of the compact support, to glue the
   local identities and cancel the partition derivatives.

Read the [Gauss--Green record](research/decisions/2026-09-12-gauss-green-area-formula.md). Closing
the area formula does **not** register `lem:relative-perimeter-smoothing`, and no Blueprint anchor
or task infrastructure status changed.

## Perimeter-chain interface integration (2026-09-12)

The current ledger still has 24 certified nodes; this round added none. The three interfaces whose
mathematical input was already present in the repository are now proved and wired in, so the WIP
hole count drops from 24 to 21: `RelativePerimeter` 5 → 3, `CheegerInfimum` 9 → 8,
`AnalyticPrerequisites` 5 (unchanged) and `Energy/WIP/Cheeger` 5 (unchanged). Formal certificates
still do not import any of these modules, and no WIP result was registered in the ledger or
anchored in the Blueprint. A completed proof body inside WIP is still not necessarily
`sorryAx`-free; the Sard and mollified-gradient consequences remain concrete examples.

Closed this round, each with only `propext / Classical.choice / Quot.sound`:

* `KLS.hausdorffNormalized_finrank_eq_volume`, from
  `Analysis.hausdorffMeasure_finrank_eq_smul_volume` (ω_n > 0 in every dimension; the
  zero-dimensional case is covered by the general input).
* `KLS.SmoothDomain.isLocallyFiniteMeasure_hausdorff_frontier`, from
  `Analysis.exists_hausdorffMeasure_levelSet_lt_top` applied in one defining neighbourhood at a
  time. Unbounded domains stay in scope; no hypothesis of finite total boundary measure was added.
* `KLS.Isoperimetry.exists_smooth_approximation_lipschitz`, from the certified
  `Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1`; the `[0,1]` range,
  smoothness, global Lipschitz property and the original measure hypotheses are unchanged.

The import direction that had blocked this is fixed by a module split, not by restating anything:
the base definitions `unitBallVolume / hausdorffNormalized / surfaceMeasure` moved down to
`formalization/FunctionalInequalities/KLS/Geometry/SurfaceMeasure.lean`, and the proved, KLS-independent
Hausdorff and level-set geometry moved out of `AnalyticPrerequisites` into
`formalization/FunctionalInequalities/Analysis/LevelSet.lean`. `RelativePerimeter` imports both;
`AnalyticPrerequisites` keeps only the open Gauss--Green, coarea and Sard obligations and still
imports `RelativePerimeter` for `mollifiedIndicator`. After the migration the prerequisite module
has 13 obligations: 8 filled bodies, 6 without transitive `sorryAx`.

Gauss--Green (C1/C2), coarea, Sard, the smooth recovery sequence, and the singular-law Cheeger
comparison remain open. Closing three interfaces does **not** register the perimeter chain as
proved. Read the [integration record](research/decisions/2026-09-12-perimeter-interface-integration.md),
the earlier [proof record](research/decisions/2026-09-12-outward-normal-interfaces-proofs.md) and
[closeout](research/decisions/2026-09-12-outward-normal-interfaces-closeout.md); both sorry prompts
and the earlier retention record are historical handoffs and keep their original counts.

Read [the audit record](research/decisions/2026-09-12-status-audit-and-wip-retention.md) before using older counts or infrastructure
assessments below. The unconditional singular-law Cheeger comparison remains unregistered; its
absolutely continuous scope is already certified as `cor:absolutely-continuous-relaxation-two-cheeger`.
The dimension-free KLS bound and the uniform conditional-fiber frame inequality remain open.

## Upstream research sync (2026-09-12)

The current research source is `kls-conjecture-search@34b5fcd57fef17089e781616005fe6d3641bd11e`.
Read [the synchronization record](research/decisions/2026-09-12-upstream-research-sync.md) for
wave-four/five results, the two July 2026 preprints, and the next formalization candidates.
The route source key `kls-exploration` is retained as an identifier; its URL and ledger path
now point to the renamed repository. Upstream `proved` with `assumes` remains conditional
here, and `proofs.mode: agent` is not Lean certification. The 24 local certificates are unchanged.

## Mathematical API organization (2026-09-08)

The public frontends are `SmoothTest`, `SmoothGradient`, `WeightedGradient`,
`CovarianceGradient`, and `LocalSlope`; `Ambient` and `Intrinsic` identify the carrier construction.
Probability pushforwards and L² pullbacks occupy their own layers. See [the naming guide](research/naming.md) and [the migration record](research/decisions/2026-09-08-mathematical-api-organization.md).

## Repository identity

- Canonical repository: `https://github.com/numina-functional-inequalities/kls-lean.git`.
- Publication branch: `main`, following
  [`research/explorations/2026-09-03-main-only-workflow.md`](research/explorations/2026-09-03-main-only-workflow.md).
- Phase-one alignment baseline: `5b1b44219050be0290c24e5765166f0298ff1ca4`.
- The Lake package is rooted at `formalization/`, not at the Git root.
- `legacy-fork` and `legacy-upstream` must be treated as read-only historical sources by project
  policy. In particular, `lyw-ops/numina-functional-inequalities-formalization` is not the
  repository named by this handoff and must not be used as the write target.

Verify the live checkout before changing anything:

```bash
git status --short --branch
git branch --show-current
git remote -v
git log -5 --oneline
```

## Read this first

| Purpose | Authority or entry point |
| --- | --- |
| Repository overview | [`README.md`](README.md) |
| Lean layout and build | [`formalization/README.md`](formalization/README.md) |
| Energy foundation boundary | [`formalization/FunctionalInequalities/Poincare/README.md`](formalization/FunctionalInequalities/Poincare/README.md) |
| Mathematical design contract | [`LEAN_DESIGN.md`](LEAN_DESIGN.md) |
| Executable dependency map | [`formalization/blueprint/README.md`](formalization/blueprint/README.md) |
| Certification lifecycle | [`research/a-series/ledger.yaml`](research/a-series/ledger.yaml) and [`research/ledger-schema.md`](research/ledger-schema.md) |
| Node certificates | [`solutions/README.md`](solutions/README.md) |
| Decisions and audits | [`research/decisions/`](research/decisions/) and [`research/explorations/`](research/explorations/) |

Older candidate, freeze, proof, and acceptance records are time-stamped, append-only evidence.
An earlier `drafted` or incomplete state never overrides a later accepted ledger state.
Historical freezes record the statement reviewed at that time; they do not impose permanent
signature stability under the current interface-evolution policy.

The 2026-09-06 follow-ups should be read in this order:

1. [Comparison proof acceptance](research/decisions/2026-09-06-poincare-comparison-proofs.md):
   the twelve Lean comparisons; the 77-label, 27-page snapshot.
2. [Analytic bridge resolution](research/decisions/2026-09-06-analytic-bridge-resolution.md):
   the subsequent analytic appendix and five generic Lean lemmas; the 86-label, 33-page snapshot.
3. [Review clarifications](research/decisions/2026-09-06-blueprint-review-clarifications.md):
   the later fiber-density dependency, BV/Minkowski convention, numerical wording, and Lean
   documentation corrections. Earlier counts describe their own validation runs.
4. [Rayleigh test-class alignment](research/decisions/2026-09-06-rayleigh-test-class-alignment.md):
   the explicit density-lemma reference and the mean correction preserving bounded support
   in the Cheeger--Buser proof.
5. [Workflow and documentation status](research/decisions/2026-09-06-workflow-and-documentation-status.md):
   the owner's CL policy and corrections aligning the live guides with the proved comparison
   bridges, analytic proof drafts, and 27 foundation axiom guards.
6. [Evolving interfaces and current proof certification](research/decisions/2026-09-06-evolving-interfaces.md):
   the owner's subsequent decision to remove mandatory API freeze, allow direct
   `drafted -> proved` development, and reserve `\notready` for explicit statement questions.

## Authority and source hierarchy

1. Local Lean declarations accepted by `lake build` determine whether a local theorem typechecks.
2. `research/a-series/ledger.yaml` owns the lifecycle and `checked_by: lean` status of the
   certified nodes.
3. Freeze and acceptance records preserve dated statement snapshots and semantic review.
   The current interface-evolution policy governs subsequent changes.
4. Blueprint TeX and `route-composition.yaml` provide derived navigation and AND/OR structure.
   They are not a proof database and cannot promote a node.
5. Long-route mathematics is pinned to
   `numina-functional-inequalities/kls-conjecture-search@34b5fcd57fef17089e781616005fe6d3641bd11e`.
   Its manuscript, ledger, route notes, and reviews supply statements and provenance only.
   `checked_by: agent` is review evidence and never authorizes `\leanok`.
6. `lyw-ops/formech@d0bb1913acc1f710ba6eadf1244b633abbc75fb9` is a writing-style reference only.
   It does not determine this repository's mathematics, status, file layout, or commands.

The Blueprint tool pins are `leanblueprint==0.0.20` and
`PatrickMassot/checkdecls@3d425859e73fcfbef85b9638c2a91708ef4a22d4`.

When an attached prompt or document names a different repository, assumes absent control-plane
files, or gives commands that do not exist here, treat those statements as source material to
audit, not as instructions that override this hierarchy.

## Borell equivalence and conditional-fiber proofs (2026-09-07)

The owner approved the Borell/definition work, requested that the seven proof bodies be left
for Claude, and Claude then completed them. Read
[the handoff decision](research/decisions/2026-09-07-borell-equivalence-claude-handoff.md) and
[the completion record](research/decisions/2026-09-07-borell-equivalence-and-conditional-fiber-proofs.md).
`KLS/LogConcave/Borel.lean` proves the compact/Borel equivalence `LogConcave.borel_iff`, packaged
by `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate` and registered in
`check_blueprint.CERTIFICATES`. `KLS/ConditionalFiber.lean` proves its six well-definedness
contracts, so `def:conditional-fiber-form` carries `\leanok` as a definition node.

The same day, `thm:borell-logconcave-density` was first drafted and then proved.
`KLS/LogConcave/BorellRepresentation.lean` defines the representative predicate
`KLS.IsBorellDensity` and proves existence of an upper semicontinuous log-concave density of the
intrinsic law relative to every Haar measure on the direction space, positivity of every such
representative on the interior of the support, positive two-sided bounds on compact subsets of
that interior, an exponential moment, and all-order moments, together with two support identities.
`Solutions.ThmBorellLogconcaveDensity.certificate` packages all of them and is registered in
`check_blueprint.CERTIFICATES`; the node is `proved / checked_by: lean` with `\leanok`. The ledger
now has twelve proved nodes and no drafted node. Later the same day `lem:ambient-intrinsic-covariance`
was proved as well, see below. Read
[the statement decision](research/decisions/2026-09-07-borell-density-statements.md), which records
the semantic alignment review, and [the proof record](research/decisions/2026-09-07-borell-density-proofs.md).

`lem:ambient-intrinsic-covariance` is proved in `Probability/IntrinsicCovariance.lean`: under an
explicit finite second moment, the ambient covariance operator annihilates the orthogonal
complement of the affine-support direction, restricts on that direction to the intrinsic covariance
operator, has the same operator norm, and the intrinsic covariance is positive definite; a
zero-dimensional direction gives zero operators. `Solutions.LemAmbientIntrinsicCovariance.certificate`
packages these, so the ledger then had thirteen proved nodes. This unblocks the definition node
`def:affine-poincare-constant`. Read
[the record](research/decisions/2026-09-07-ambient-intrinsic-covariance.md).

`def:affine-poincare-constant` is now implemented. `Energy/CovarianceGradient/Basic.lean`
defines the globally Lipschitz covariance-weighted gradient pre-energy `Energy.CovarianceGradient.preEnergy ν` with
`Σ = Covariance.operator ν`, its sequential `L²(ν)` relaxation, and the affine specialization
`Energy.CovarianceGradient.Intrinsic.energy μ` on the intrinsic law; `Poincare/CovarianceGradient/Intrinsic.lean` defines
`Poincare.CovarianceGradient.Intrinsic.constant μ` through `Poincare.L2Energy.constant` and proves that a zero-dimensional
direction gives constant zero. `KLS/LogConcave/Covariance.lean` proves the three log-concave
well-definedness contracts: intrinsic finite second moment, almost-everywhere differentiability of
every test by Rademacher, and representative independence of the energy. The Blueprint definition
carries `\leanok` as a definition node and does not enter the ledger. Closability, closed-form
identification and translation invariance are certified by the subsequent nodes below; the
definition alone asserts no Poincaré bound. Read
[the record](research/decisions/2026-09-07-affine-poincare-constant-definition.md).

`lem:covariance-core-closure` was proved on 2026-09-08. `Energy/Relaxation/LinearPMap.lean` proves,
for any closable partially defined operator `T` from a normed space into a Hilbert space, that the
sequential relaxation of `‖T f‖²` is `‖T̄ f‖²` on the domain of the closure and `⊤` outside it (via
a weak-topology-free Hilbert selection lemma), and that graph-norm dense cores have the same
closure. `Energy/Euclidean/WeakDerivative.lean` proves integration by parts for globally Lipschitz
functions against `C_c^∞` tests. `Energy/Euclidean/CovarianceGradient/{Operator,Closable,Core}.lean`
define the weighted gradient operator `g ↦ B ∘ ∇g` on `L²(ν)`, prove it closable under absolute
continuity, null support frontier and local domination of Haar measure, and prove dense domain and
the smooth-core closure identity. `KLS/LogConcave/WeightedGradient.lean` discharges these
hypotheses for every full-dimensional log-concave law and for the intrinsic law of any log-concave
law, and identifies `Energy.CovarianceGradient.Intrinsic.energy` with the operator relaxation for every `B` with
`⟪Σ v, v⟫ = ‖B v‖²`. `Solutions.LemCovarianceCoreClosure.certificate` packages dense domain,
closability, core independence and the relaxation identity; the ledger then had fourteen proved
nodes. Read [the record](research/decisions/2026-09-08-covariance-core-closure.md).

`thm:affine-covariance-relaxation-closed` was proved the same day. `Probability/CovarianceFactorization.lean`
gives a norm factorization `B` of any covariance quadratic form (`⟪Σ v, v⟫ = ‖B v‖²`, spectral theorem);
`Energy/CovarianceGradient/Translation.lean` proves that translating a law gives an `L²`
isometry preserving variance, covariance operator, covariance relaxation and optimal constant;
`KLS/LogConcave/ClosedForm.lean` shows for every log-concave law that the affine pre-energy has
dense realization, that `Energy.CovarianceGradient.Intrinsic.energy μ` is a closed quadratic form with the globally
Lipschitz tests as sequential core, and that it equals the squared-norm energy of the closure of
`B ∇` on the core `ℝ + C_c^∞` (the CMH closed form), with `Poincare.CovarianceGradient.Intrinsic.constant μ` its optimal
constant. `Solutions.ThmAffineCovarianceRelaxationClosed.certificate` packages these; the ledger
then had fifteen proved nodes. Read
[the record](research/decisions/2026-09-08-affine-covariance-relaxation-closed.md).

`lem:affine-poincare-translation-invariance` was proved later the same day.
`Energy/CovarianceGradient/Isometry.lean` transports a law, its covariance operator, the
gradient, the covariance relaxation and its optimal constant along a linear isometric equivalence;
`Poincare/CovarianceGradient/Translation.lean` shows that the ambient translate
`Probability.translateLaw μ b` has the translated affine support with the same direction, that
its intrinsic law is a translate of the isometric image of the intrinsic law of `μ`, and hence that
`Poincare.CovarianceGradient.Intrinsic.constant` is unchanged (for every Borel law), together with a variance-preserving
`L²` isometry intertwining the two affine relaxations and the barycenter identity for translates;
`KLS/LogConcave/Translation.lean` proves that translation keeps compact-set log-concavity,
that log-concave laws have a finite ambient second moment, and that translating by the negative
barycenter centers the law. `Solutions.LemAffinePoincareTranslationInvariance.certificate` packages
these; the ledger then had sixteen proved nodes. Read
[the record](research/decisions/2026-09-08-affine-poincare-translation-invariance.md).

`thm:affine-isotropic-reduction` was proved next. `Energy/CovarianceGradient/LinearEquiv.lean`
transports a law, its covariance operator (conjugated by the map and its adjoint), the gradient,
the covariance relaxation and its optimal constant along any continuous linear equivalence;
`Probability/CovarianceWhitening.lean` gives a self-adjoint whitening of a positive definite
covariance, with `W Σ W = I` but no positivity or uniqueness conclusion for `W`;
`Poincare/LipschitzGradient/Comparison.lean` identifies the optimal constant of
the identity-weighted Lipschitz gradient relaxation with the smooth-test and literature
constants and bounds the covariance relaxation by `‖Σ‖` times it (with the new scaled relaxation
comparison `PreEnergy.sequentialRelaxation_comp_le_mul`); `KLS/LogConcave/Isotropic.lean`
defines the three statements `KLS.IsotropicBound K`, `KLS.CovarianceBound K`, `KLS.AffineBound K`
over every finite-dimensional Euclidean space of a fixed universe and proves their equivalence by
centering and whitening the intrinsic law, together with `KLS.conjecture_of_affineBound`.
`Solutions.ThmAffineIsotropicReduction.certificate` packages these; the ledger then had seventeen
proved nodes. The same inspection recorded `thm:cmh-recovery-affine-poincare-bound` as `missing`
infrastructure (no Lean `W₂`, CMH constant or upstream proofs). Read
[the record](research/decisions/2026-09-08-affine-isotropic-reduction.md).

Isotropy, the isoperimetric scale and the affine covariance Poincaré constant are implemented
definitions. The Dirac raw-energy obstruction is a named, proved library result outside the ledger.
Twenty-five named StatementChecks, the six conditional-fiber guards, the five affine covariance
guards and the Dirac and normal-direction obstruction guards cover the implemented contracts with
the standard three axioms only. The Borell density/moment representation is Lean-certified; the downstream KLS routes
remain unproved. Local certification does not by itself imply publication or a remote CI pass.

## Dirichlet property of the smooth-gradient relaxation (2026-09-10)

`thm:smooth-gradient-relaxation-dirichlet` is proved in `Energy/SmoothGradient/Dirichlet.lean`.
The normal contraction is mollified on the real line (`Energy.NormalContraction.smoothed`: smooth,
`1`-Lipschitz, uniformly within `2/(j+1)` of the contraction); composing a smooth test with it gives
a smooth test with pointwise smaller gradient norm whose `L²` class converges to the contracted
class, which is the relaxed contraction bound on realized tests; the certified contraction-transfer
theorem then gives `Energy.Markovian` and `Energy.Dirichlet` for `Energy.SmoothGradient.relaxation μ`
for every Borel probability law, singular laws and dimension zero included, and the intrinsic-affine
relaxation `SmoothGradient.Intrinsic.energy μ` inherits the property.
`Solutions.ThmSmoothGradientRelaxationDirichlet.certificate` packages Markovianity and both Dirichlet
statements. Read
[the record](research/decisions/2026-09-10-smooth-gradient-relaxation-dirichlet.md).

## One-dimensional log-concave Poincaré bound, sharp constant 4 (2026-09-11)

`thm:one-dimensional-logconcave-poincare` now carries the sharp constant: every compact-set
log-concave law `ν` on `ℝ` has `Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal
(4 * variance id ν)` (`KLS/LogConcave/Line/SharpPoincare.lean`), zero variance included, and the
certificate `Solutions.ThmOneDimensionalLogConcavePoincare.certificate` packages the real and
extended-variance forms with `4`; Bobkov's `12` is a typed corollary and keeps its independent
proof. The proof follows the collaborator audit
`research/explorations/2026-09-11-poincare-constant-4-audit.md`: `Probability/Line/AffineProfile.lean`
(affine quantile model on the unit uniform law, variance closed form, `1/(√A+√B)⁴ ≤ Var`),
`KLS/LogConcave/Line/Profile.lean` (supporting line `ρ ≤ A(1−F)+BF`, profile bound `F(1−F) ≤ σρ`),
`Line/SharpHardy.lean` (tests clipped outside `[a,b] ⊆ Ω` straddling a median, integration by
parts, ground-state identity with boundary control on larger intervals, `Var(clip) ≤ 4·Var·∫f'²`),
and `Line/SharpPoincare.lean` (half-line Hardy bounds anchored at arbitrary interior points, now
generalized in `Line/Hardy.lean`, make the clipping tails vanish; a `(1+δ)`-split finishes). The
Blueprint statement changed from `12` to `4`; the published constant `4` (Alonso-Gutiérrez–Bastero
p. 11, credited to KLS 1995, no proof there) is now locally proved rather than imported. The fiber
corollary `cor:conditional-fiber-twelve-bound` was sharpened to `4C` on 2026-09-12, when it was
proved and certified.
Read [the record](research/decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md).

## One-dimensional log-concave Poincaré bound, constant 12 (2026-09-10)

`thm:one-dimensional-logconcave-poincare` was first proved with Bobkov's constant in
`KLS/LogConcave/Line/Poincare.lean`: every compact-set log-concave law `ν` on `ℝ` has
`Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal (12 * variance id ν)`, zero variance
(one-point affine support) included; this proof is kept as an independent corollary. The
supporting modules are `Probability/Line/Cdf.lean` (distribution function, continuity and
derivative under a density, median, uniform pushforward `map_cdf_eq_uniform`, centered moments
`1/12` and `0`), `Probability/Line/ExpIntegral.lean`, and `KLS/LogConcave/Line/{Density, Hazard,
Hardy, Variance}.lean`: the Borell line density `KLS.LineDensity`, the four-point inequality and the
median hazard bounds `2ρ(m)(1 − F) ≤ ρ`, `2ρ(m)F ≤ ρ`, the integration-by-parts Hardy inequality
giving `SmoothTest.Holds ν (1/ρ(m))²`, and the supporting-line variance bound
`1/(12ρ(m)²) ≤ Var`. The route differs from Bobkov's Cheeger argument and gives exactly the
Blueprint constant `12`; the node moves from an `imported` published input to a `proved` Lean
claim, and `KLS.logConcave_dirac` supplies the Dirac example.
The certificate then packaged the real and extended-variance forms with `12`; it now packages `4`.
Read [the record](research/decisions/2026-09-10-one-dimensional-logconcave-poincare.md).

## Normal-direction raw-energy obstruction (2026-09-10)

`obs:normal-direction-raw-energy` is a proved library obstruction in
`Energy/SmoothGradient/NormalDirection.lean`, outside the ledger like the Dirac obstruction: when
the direction space of the affine support of `μ` is proper, the coordinate `x ↦ ⟪n, x − a⟫` along a
unit normal `n` is zero in `L²(μ)` but is a smooth-gradient test of energy `1`, so
`Energy.SmoothGradient.preEnergy μ` fails `RespectsAmbientFibers`
(`SmoothGradient.not_respectsAmbientFibers`). Two default-build axiom guards were added to
`solutions/FoundationAxiomAudit.lean`. Read
[the record](research/decisions/2026-09-10-normal-direction-raw-energy.md).

## Raw/sequential-core agreement under density hypotheses (2026-09-10)

`thm:smooth-gradient-raw-core-agreement-density` is proved in `Energy/SmoothGradient/Core.lean`.
The Blueprint's density hypotheses are the structure `Energy.SmoothGradient.LocalDensity ν m` (open
carrier `Ω`, `ν(Ωᶜ) = 0`, density `ρ` on `Ω` for a Haar measure `m`, `ρ > 0` a.e. on `Ω`, `ρ⁻¹`
locally essentially bounded; the Blueprint's local bound on `ρ` is not used). They give absolute
continuity, a null support frontier and local domination of `m` by `ν` on compact subsets of `Ω`;
the closability theorem of `Energy/WeightedGradient/Closable.lean` was generalized from the
interior of the support to an arbitrary open carrier (`Probability.LocallyDominatesOn`,
`WeightedGradient.operator_isClosable_of_isOpen`; `LocallyDominates` is now the special case).
Smooth cutoffs put every smooth test in the closure domain of the unit-weight Lipschitz gradient
operator with closure value its gradient, recovery sequences give the Lipschitz relaxation at most
the smooth relaxation, and the closable-operator relaxation formula yields `AgreesOnTests` and
`IsSequentialCoreFor` for `SmoothGradient.preEnergy ν` and `SmoothGradient.relaxation ν`; the
intrinsic law is the named instance. `Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate`
packages both; the ledger has twenty proved nodes. Read
[the record](research/decisions/2026-09-10-smooth-gradient-raw-core-agreement-density.md).

## Conditional-fiber energy comparison (2026-09-11)

`lem:conditional-fiber-energy-comparison` is proved in `KLS/ConditionalFiber/EnergyComparison.lean`.
The fiber hypothesis is `KLS.ConditionalFiber.FiberBound μ ρ κ`: for base-law almost every
nondegenerate fiber, `Poincare.LocalSlope.Intrinsic.constant` of the fiber law is at most
`κ · eVar[T]`. For `μ ≪ m` (any Haar measure) and an admissible frame `ρ`,
`energy_le_of_fiberBound` bounds the conditional-fiber energy of every literature test
(`Energy.LocalSlope.Admissible`) by `κ` times its finite local-slope energy, which is
`κ ∫‖∇f‖² dμ` by `energy_eq_lintegral_gradient`; `literatureConstant_le_of_fiberBound` turns a
form-gap bound `Var_μ ≤ C · D_{μ,ρ}` on `domain μ ρ` into `C_P^lit(μ) ≤ κ C`. The proof transports
`Poincare.LocalSlope.Holds` across a measure-preserving isometric equivalence, so that the intrinsic
constant of a law with full affine support (Haar-absolutely continuous laws; real laws with nonzero
variance) is the infimum of its coordinate constants and a finite bound on it is a per-test
inequality; identifies the local slope of the line slice `t ↦ f(z + tθ)` with `|⟪θ, ∇f⟫|` at
Rademacher points; pushes the Rademacher null set and square integrability through the joint law
and the disintegration; and finishes with Tonelli and the frame identity.
`Solutions.LemConditionalFiberEnergyComparison.certificate` packages both conclusions; the ledger
has twenty-four proved nodes. The statement was written first as a `sorry` skeleton with
sentence-by-sentence alignment, then proved; read
[the statement record](research/decisions/2026-09-11-conditional-fiber-energy-comparison-statement.md)
and [the proof record](research/decisions/2026-09-11-conditional-fiber-energy-comparison-proofs.md).
Several private helpers (the `Holds` isometry transport, the two full-affine-support criteria, the
`evariance` transport, the fiber-wise almost-everywhere lemmas) belong in shared modules and are
listed in the proof record for a later move. `affineSupport_eq_top_of_absolutelyContinuous` was the
first of them to be made public, without a type change, for the corollary below. The downstream
corollary `cor:conditional-fiber-twelve-bound` is now proved and certified; see the next section.

## Cheeger identification, absolutely continuous scope (2026-09-12)

`cor:absolutely-continuous-relaxation-two-cheeger` is proved in `Energy/Cheeger.lean` and certified
by `Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate`, the twenty-fourth ledger
node. For a law whose intrinsic law is absolutely continuous with respect to a Haar measure on the
direction space, the smooth-gradient relaxation of the intrinsic law is the relaxed squared local
slope, hence `𝓔^can_μ = 2 Ch_μ` on ambient `L²(μ)`; every compact-set log-concave law satisfies the
hypothesis through the certified `lem:logconcave-intrinsic-absolute-continuity`, so the
identification is available throughout the KLS routes.

`Ch_μ` is the Blueprint's own local-slope convention, fixed by
`Energy.Cheeger.energy := Cheeger.ofLocalSlope` and nowhere else; the asymptotic-Lipschitz
relaxation is a separate definition and only the unconditional comparison
`LocalSlope.relaxation ≤ AsymptoticLipschitz.relaxation` is proved. The material that used to sit
in the single WIP module was split: `Energy/LocalSlope/Relaxation.lean` (both pre-energies and
their `L²` relaxations) and `Energy/Cheeger.lean` (the Cheeger energy, its affine-support
transport, the absolutely continuous identification and the log-concave corollary) are registered
and `sorry`-free, while `Energy/WIP/Cheeger.lean` now contains **only** the five open obligations
of the singular case, of which two are genuine (`LocalSlope.relaxation_eq_asymptoticLipschitz`,
`SmoothGradient.relaxation_eq_localSlope`) and three are their immediate consequences. The
unconditional `thm:smooth-gradient-relaxation-two-cheeger` stays open and uncertified. Read
[the statement record](research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md),
[the proof record](research/decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md)
and [the registration record](research/decisions/2026-09-12-cheeger-absolutely-continuous-registration.md).

## Log-concave conditional fibers (2026-09-12)

`cor:conditional-fiber-twelve-bound` is proved in `KLS/LogConcave/ConditionalFiber.lean` and
certified by `Solutions.CorConditionalFiberTwelveBound.certificate`, the twenty-third ledger node.
For a compact-set log-concave `μ ≪ m` (any Haar measure) with an admissible frame `ρ`, the
certificate packages the four steps of the Blueprint proof: base-law almost every conditional
kernel `kernel μ ρ b` is a compact-set log-concave law on `ℝ`; hence `FiberBound μ ρ 4`; hence
`D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ < ∞` on the literature test domain; hence `C_P^lit(μ) ≤ 4 C` from a
finite form-gap bound `C`. The Blueprint corollary, which previously recorded the literature
constant `12`, is restated with the sharp `4` supplied by
`thm:one-dimensional-logconcave-poincare`; the `12` versions remain as
`conditionalFiber_energy_le_twelve_mul_of_four` and
`conditionalFiber_literatureConstant_le_twelve_mul_of_four`.

The three gaps recorded with the statement skeleton are closed by new modules.
`Probability/Line/BrunnMinkowski.lean` proves compact one-dimensional Brunn--Minkowski, its
inner-regular convex-combination form, and the one-dimensional Prékopa--Leindler inequality with no
boundedness hypothesis; `KLS/LogConcave/Line/OfDensity.lean` turns it into `LineDensity.logConcave`,
the converse of `LogConcave.exists_lineDensity`. `Probability/HaarLine.lean` builds the linear
equivalence `θ^⊥ × ℝ ≅ E` and the Fubini splitting `c · ∫G dm = ∬G(z + sθ)`, the proportionality
constant depending on `θ` and never being evaluated. `KLS/ConditionalFiber/SliceKernel.lean` builds
the explicit slice kernel with density `t ↦ p(z + tθ)/Z(θ, z)`, proves
`baseLaw ⊗ₘ sliceKernel = jointLaw`, and concludes `ae_sliceKernel_eq` from Mathlib's uniqueness of
conditional kernels. Base points with vanishing or infinite slice mass carry a Dirac law, which is
log-concave by `KLS.logConcave_dirac`, so the assembly discards no exceptional set. Read
[the statement record](research/decisions/2026-09-11-conditional-fiber-twelve-bound-statement.md)
and [the proof record](research/decisions/2026-09-11-conditional-fiber-twelve-bound-proofs.md).
The route's remaining gate is `q:conditional-fiber-frame`, still open: no frame bound, no Poincaré
inequality for `μ` and no KLS statement follows from this corollary.

## Closed conditional-fiber form (2026-09-11)

`lem:conditional-fiber-form` is proved in `KLS/ConditionalFiber/Closed.lean`. The form of
`def:conditional-fiber-form` is packaged as the extended functional
`KLS.ConditionalFiber.functional μ ρ` on `L²(μ)`, and `KLS.ConditionalFiber.dirichlet` proves
`Energy.Dirichlet`: dense finite domain, lower semicontinuity, the extended quadratic identities and
the normal-contraction (Markov) property. The proof is the jump representation
`energyAt_eq_jump_div`: on a nondegenerate fiber the normalized variance is the squared jump
integral against the symmetric two-point measure `μ_{θ,z} ⊗ μ_{θ,z}` divided by `2 Var(T)`, using
the new two-point variance identity `Probability.two_mul_evariance_eq_lintegral_prod` (valid in
`[0, ∞]` without square integrability). Symmetry and reversibility are read as this representation
together with the swap invariance `twoPointMeasure_swap`. Closedness disintegrates an
almost-everywhere convergent subsequence through the joint law and applies Fatou on the two-point
space and on the base law; a globally `L`-Lipschitz test has energy at most `d L²`
(`energy_le_of_lipschitzWith`), so the smooth compactly supported core lies in the finite domain.
The Lean theorem needs no log-concavity, density, second moment or frame identity; the Blueprint
scope is a typed application. `Solutions.LemConditionalFiberForm.certificate` packages the Dirichlet
property, the jump representation, the swap invariance and the Lipschitz bound; the ledger has
twenty-one proved nodes. Read
[the record](research/decisions/2026-09-11-conditional-fiber-form.md). The same session recorded
`prop:weighted-spectator-obstruction` (no Lean statement of the stochastic-localization objects of
`ass:weighted-package`; no SDE theory in the pinned Mathlib) and `lem:relative-perimeter-smoothing`
(no smooth-domain surface measure, Gauss--Green or several-variable BV in the pinned Mathlib) as
`missing` infrastructure with concrete gaps; read
[the assessment](research/decisions/2026-09-11-spectator-and-relative-perimeter-infrastructure.md).
On 2026-09-12 those gaps first became seventeen KLS-independent typed obligations in `formalization/FunctionalInequalities/KLS/WIP/AnalyticPrerequisites.lean`:
isodiametric inequality via Prékopa--Leindler and Brunn--Minkowski (pins only the normalization of
`surfaceMeasure`; unlocks no node), Lipschitz-graph form of regular level sets with locally finite
`μH[n-1]`, Gauss--Green with an outward normal for `SmoothDomain`, weighted coarea for Lipschitz
functions, and Sard with the sharp `C^n` exponent. Two findings: the "restricted `μH[n-1]` is a
locally finite measure" form of the level-set statement is false for level sets inside an open set
(graph of `sin(1/x)`) and was replaced by a pointwise statement; and the only load-bearing gaps are
Gauss--Green (whose residual sub-obligation is the area formula for Lipschitz graphs), coarea and
Sard. Read [the statement record](research/decisions/2026-09-12-relative-perimeter-prerequisites-statement.md)
and [the proof prompt](research/decisions/2026-09-12-relative-perimeter-prerequisites-sorry-prompt.md).
The subsequent [proof round](research/decisions/2026-09-12-relative-perimeter-prerequisites-proofs.md)
filled 12 of those 17 bodies, leaving 5 explicit holes. Of the 12 filled bodies, 10 are free of
`sorryAx`; the Sard restatement and mollified-gradient formula still depend on unproved inputs.
The file remained unregistered, and at that point the companion perimeter/Cheeger files still had
5/9 holes. Those counts are the historical state of that round; the current numbers, and the
migration of the isodiametric/Hausdorff and level-set results out of that file into
`formalization/FunctionalInequalities/Analysis/LevelSet.lean`, are recorded in the section
"Perimeter-chain interface integration (2026-09-12)" at the top of this file.

## Current certified state

The local proof-atlas extension is described in
[`research/verification.md`](research/verification.md) and
[`research/decisions/2026-09-06-local-proof-atlas.md`](research/decisions/2026-09-06-local-proof-atlas.md).
`python3 research/verify.py` checks the current source snapshot, every Blueprint Lean anchor,
all twenty-four certificates and local module kernel replay. It also compares the elaborated local
statement-definition closure with the explicit golden and audits twenty-five named definition checks.
Afterwards export and query the task atlas. Task schema version 2 separates verification from
infrastructure assessment (`available`, `missing`, `unchecked`); these do not change mathematical
classification. Finish decisions before the final run so the resulting receipt stays current.
The new `FunctionalInequalities.KLS.Conjecture` is only a proposition declaration, with explicit
literature-facing definitions and typed checks. It is not itself a proved ledger node.
The weighted smooth-approximation/literature-comparison chain is the prioritized formalization
pilot. Its first node, `lem:covariance-test-core-density`, is now proved: all four contracts are
packaged by `Solutions.LemCovarianceTestCoreDensity.certificate`, with default-build transitive
axiom guards. The ledger records `proved / checked_by: lean`; the local approximation adapter
is assessed as `available`. See the
[acceptance record](research/decisions/2026-09-06-weighted-approximation-acceptance.md).
`thm:smooth-lipschitz-constant-equivalence` now has eight proved interfaces in
`Energy/LocalSlope/Gradient.lean` and `Poincare/LocalSlope/SmoothTestComparison.lean`.
The sole certificate in `solutions/ThmSmoothLipschitzConstantEquivalence.lean` packages all eight;
it and every component have default-build axiom guards. The ledger records
`proved / checked_by: lean`. Read the
[proof record](research/decisions/2026-09-06-smooth-literature-proofs.md).
The general log-concave extension is now proved as well. `KLS/LogConcave/AbsoluteContinuity.lean` derives
intrinsic absolute continuity directly from compact-set log-concavity, and
`KLS/LogConcave/Poincare.lean` identifies the selected and literature constants
without an added density premise. Two separate certificates record these exact results; the
full Borell density representative and moment theorem is separately certified by
`Solutions.ThmBorellLogconcaveDensity.certificate`. Read the
[general log-concave proof record](research/decisions/2026-09-06-general-logconcave-comparison.md).

Lean and Mathlib are pinned to `v4.33.0`. The production ledger contains twenty-four proved nodes,
each with `status: proved` and `checked_by: lean`.

| Ledger node | Public certificate |
| --- | --- |
| `lem:linear-test-lower` | `Solutions.LemLinearTestLower.certificate` |
| `lem:poincare-tensorization` | `Solutions.LemPoincareTensorization.certificate` |
| `lem:poincare-finite-tensorization` | `Solutions.LemPoincareFiniteTensorization.certificate` |
| `lem:poincare-gaussian-one-dimensional` | `Solutions.LemPoincareGaussianOneDimensional.certificate` |
| `lem:ambient-intrinsic-poincare-comparison` | `Solutions.LemAmbientIntrinsicPoincareComparison.certificate` |
| `lem:legacy-relaxed-poincare-comparison` | `Solutions.LemLegacyRelaxedPoincareComparison.certificate` |
| `lem:covariance-test-core-density` | `Solutions.LemCovarianceTestCoreDensity.certificate` |
| `thm:smooth-lipschitz-constant-equivalence` | `Solutions.ThmSmoothLipschitzConstantEquivalence.certificate` |
| `lem:logconcave-intrinsic-absolute-continuity` | `Solutions.LemLogConcaveIntrinsicAbsoluteContinuity.certificate` |
| `thm:selected-literature-constant-equivalence` | `Solutions.ThmSelectedLiteratureConstantEquivalence.certificate` |
| `thm:compact-borell-logconcavity-equivalence` | `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate` |
| `thm:borell-logconcave-density` | `Solutions.ThmBorellLogconcaveDensity.certificate` |
| `lem:ambient-intrinsic-covariance` | `Solutions.LemAmbientIntrinsicCovariance.certificate` |
| `lem:covariance-core-closure` | `Solutions.LemCovarianceCoreClosure.certificate` |
| `thm:affine-covariance-relaxation-closed` | `Solutions.ThmAffineCovarianceRelaxationClosed.certificate` |
| `lem:affine-poincare-translation-invariance` | `Solutions.LemAffinePoincareTranslationInvariance.certificate` |
| `thm:affine-isotropic-reduction` | `Solutions.ThmAffineIsotropicReduction.certificate` |
| `thm:smooth-gradient-relaxation-dirichlet` | `Solutions.ThmSmoothGradientRelaxationDirichlet.certificate` |
| `thm:one-dimensional-logconcave-poincare` | `Solutions.ThmOneDimensionalLogConcavePoincare.certificate` |
| `thm:smooth-gradient-raw-core-agreement-density` | `Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate` |
| `lem:conditional-fiber-form` | `Solutions.LemConditionalFiberForm.certificate` |
| `lem:conditional-fiber-energy-comparison` | `Solutions.LemConditionalFiberEnergyComparison.certificate` |
| `cor:conditional-fiber-twelve-bound` (the label keeps the literature `12`; the node states `4C`) | `Solutions.CorConditionalFiberTwelveBound.certificate` |
| `cor:absolutely-continuous-relaxation-two-cheeger` | `Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate` |

The reusable library also proves intrinsic real `L²` mean, centering and variance; extended
energies; sequential relaxation and recovery; quadratic relaxation as a closed quadratic form;
the ambient smooth-gradient closed form; affine support and intrinsic `L²` equivalence; the
intrinsic-affine closed form; and the generic optimal-constant order law. These are foundational
theorems, not a proof of KLS.

`Energy/Relaxation/Approximation.lean` contains the shared concrete-test selection steps used by
lower semicontinuity and recovery. The default build also compiles the usage and boundary examples
in `examples/PoincareFoundation.lean` and the 27 foundation and comparison guards in
`solutions/FoundationAxiomAudit.lean`. The four previous certificates retain their public contracts; two new certificates package the
comparison results with unchanged theorem signatures.

The comparison batch in `solutions/LemAmbientIntrinsicPoincareComparison.lean` and
`solutions/LemLegacyRelaxedPoincareComparison.lean` now has five and seven proved comparisons.
They are exported by `Poincare.Foundation` and the root aggregate. All 12 theorem dependencies
and both certificates have axiom guards. Read the
[comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md) and
[proof acceptance](research/decisions/2026-09-06-poincare-comparison-proofs.md).

## Current mathematical boundary

The Blueprint selects the intrinsic-affine smooth-gradient relaxation as the repository-facing
canonical frontend. Its optimal constant now equals the literature constant for every
finite-dimensional log-concave law; equality of energies is a separate question.
The generic `Poincare.L2Energy.constant μ E` remains an optimizer parameterized by an
arbitrary energy; it is not, by itself, the selected Poincare constant.

The following statements are not currently Lean-certified:

- identification with the literature normalization `2 Ch_μ`; the Dirichlet property of the smooth
  and intrinsic-affine relaxations is now certified;
- Cheeger--Poincare comparison, self-adjoint generator, and spectral-gap interfaces needed by the
  long routes; the closed covariance form, the ambient translation invariance of the affine
  constant and the affine/isotropic reduction (equivalence of the three KLS formulations for
  each fixed `K`) are now certified.

The 2026-09-06 analytic-comparison follow-up supplies complete written arguments for the
locally Lipschitz approximation, relative-perimeter Cheeger infimum, and CMH covariance-core
identification in Blueprint Appendix A. The approximation lemma and the covariance-core closure
are now Lean-certified; the relative-perimeter smoothing argument still awaits Lean
implementation (its remaining analytic prerequisites — Gauss--Green, weighted coarea and Sard —
are typed, unproved obligations in `KLS/WIP/AnalyticPrerequisites.lean`; the Hausdorff and
level-set inputs are proved in `Analysis/LevelSet.lean` and already wired into the perimeter
module). Five generic comparison theorems
are proved in Lean, with the foundation audit extended to 27 guards. See
`research/decisions/2026-09-06-analytic-bridge-resolution.md` for their exact scope and evidence.

The proved smooth-test-to-relaxed bridge does **not** require raw test/core agreement. One
direction uses the defining relaxation upper bound on each smooth test. The other uses recovery
sequences and continuity of `L²` variance. Raw/core agreement is a separate, stronger question.
It cannot hold without extra hypotheses: for `μ = δ₀`, the functions `0` and `x` represent the
same `L²(μ)` class but have raw gradient energies `0` and `1`.

Likewise, `ClosedQuadratic` contains no Markov property. The generic contraction-transfer theorem
is conditional; the concrete smooth-gradient Dirichlet property is now established separately by
mollifying the contraction (`Energy.SmoothGradient.dirichlet`).

## KLS route status

The target `conj:kls` is open. TeX `\uses{...}` records logical AND. The route sidecar records
that any one active branch may discharge the target. Its shared requirements are the
selected/literature frontend comparison and the affine/isotropic normalization adapter (both now
Lean-certified); they are repository-facing adapters and are not asserted to be premises of every
upstream argument.

- Eldan localization: the tight-prefix Carleson gate is open; its consumption theorem is proved
  only in the pinned upstream, with agent review.
- Moment-map spectral: the fixed-eigenfunction full-damping occupation estimate is open; the
  sufficiency implication is conditional and agent-reviewed upstream.
- Moment-map CMH: the recovery-envelope assumption is open; its sufficiency implication is
  conditional and agent-reviewed upstream. It is a sufficient condition, not a reformulation of
  KLS.
- Conditional-fiber frame: the test-independent frame question is open. The structural form
  statement `lem:conditional-fiber-form` has pinned upstream agent review and is now also
  Lean-certified (`Solutions.LemConditionalFiberForm.certificate`, for every Borel law and every
  direction law); the local energy comparison with an explicit finite input `κ`,
  `lem:conditional-fiber-energy-comparison`, is Lean-certified as well
  (`Solutions.LemConditionalFiberEnergyComparison.certificate`, for Haar-absolutely continuous
  laws and admissible frames). The one-dimensional input `thm:one-dimensional-logconcave-poincare` is now the sharp local Lean
  theorem `4 Var` (Bobkov's `12 Var` a corollary), and the log-concave specialization
  `cor:conditional-fiber-twelve-bound` that consumes it is Lean-certified too
  (`Solutions.CorConditionalFiberTwelveBound.certificate`), restated with the sharp `4C`; the
  literature `12C` is its immediate weakening. Failure of the natural simplex
  root frame does not refute the all-frame question. The frame construction uses positive
  dimensions; zero-dimensional KLS has zero variance and needs no frame. The sidecar explicitly
  includes affine/isotropic reduction for the passage to all affine supports.

The literal global-operator-norm weighted Eldan-B package is refuted in the pinned manuscript.
It is retained only as historical provenance and must not appear among the active alternatives.
Any replacement branch needs an explicit mathematical statement, traceable provenance, and an
accurate route status. A separate API freeze is not required.

The route chapter is a KLS-facing interface summary, not the transitive closure of the upstream
ledger. Missing Riccati, stochastic, moment-map and recovery inputs must be
formalized explicitly before an active route can become a Lean proof; the one-dimensional
`12 Var` input is now Lean-certified.

## Reproducible checks

From the repository root:

```bash
python3 research/check_ledger.py
python3 research/check_blueprint.py
python3 research/atlas.py check
python3 -m unittest discover -s research/tests -p 'test_*.py'
(cd formalization && lake build)
python3 research/verify.py
python3 research/atlas.py export
python3 research/atlas.py ready
```

`verify.py` already runs the structural checks, tests and build above, then the statement golden,
declaration/axiom audit and replay. The individual commands are useful for diagnosing a failed gate.
`python3 research/statement_snapshot.py check` builds and compares just the public statement
definition closure. Baseline changes require a new decision and the explicit update command in
[`research/verification.md`](research/verification.md); no automatic regeneration or API freeze.

For rendered Blueprint artifacts, create a temporary environment once and run:

```bash
python3 -m venv /tmp/kls-blueprint-venv
/tmp/kls-blueprint-venv/bin/pip install -r formalization/blueprint/requirements.txt
/tmp/kls-blueprint-venv/bin/python formalization/blueprint/build.py all
```

The generated PDF, web tree, and `lean_decls` file are ignored outputs. Do not edit them by hand.
A local pass, a pushed commit, and remote CI are three different facts; record only the one that
was actually checked for the named SHA.

For `575c82c` the `Lean certification` workflow passed and the `Lean Blueprint` workflow failed at
`checkdecls`, because the pinned checker imports every `lean_lib` root and the never-built `Dev`
scratchpad library had been declared. The library declaration is removed locally (the file stays,
loaded with `lake env lean Dev/Search.lean`); see
[the CI record](research/explorations/2026-09-07-blueprint-ci-checkdecls-dev-library.md). The fix
takes effect with the next push.

The 2026-09-08 semantic review and the owner's subsequent publication authorization are recorded
in [the affine-foundations publication CL](research/decisions/2026-09-08-affine-foundations-publication.md).
It corrects the whitening contract's wording and obsolete Borell status summaries, and records
the restoration of the reviewed foundation tree while retaining the earlier remote revert in
history. The candidate's verification receipt and exact-SHA GitHub workflows determine the
publication and CI evidence; earlier local-only records retain their dated meaning.

## Change discipline and next stages

- Owner workflow instruction (2026-09-06): “后面我们除了大的推送其他的都不用CL”.
  Use CL only for large pushes. Routine analysis, edits, documentation maintenance, and small
  pushes proceed without a CL workflow. Run local checks appropriate to the change.
- Owner interface policy (2026-09-06): public Lean interfaces may evolve, including proved
  interfaces. Do not require a freeze before proof work; new nodes may move directly from
  `drafted` to `proved`. There is no default backward-compatibility promise.
- `proved`, `checked_by: lean`, and `\leanok` certify the current statement and proof. After
  interface changes, migrate consumers and rerun the relevant build, semantic, and axiom checks.
  Record changes to mathematical assumptions, conclusions, domains, or normalization explicitly;
  synchronize the ledger and Blueprint and check whether the original goal is still covered.
  An unproved revision returns to `drafted` / `checked_by: null` without `\leanok`.
- Reserve Blueprint `\notready` for an explicit unresolved statement choice, such as its test
  domain or normalization. Possible future API changes alone do not justify the marker.
  Historical `frozen` records remain review snapshots; see `research/ledger-schema.md`.
- Public API naming follows [research/naming.md](research/naming.md): use namespaces for object
  roles and retain theorem conditions needed to distinguish mathematical claims.
- Keep decisions and explorations append-only. Record a correction in a new file instead of
  rewriting the historical state.
- Ordinary Mathlib `C∞` is `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` is analytic.
- Do not modify production ledger statements, route status, or Lean claims merely to make a
  diagram pass.

The next proof workstreams are deliberately separate; their numbering is not a fixed scheduling
decision:

1. Build the Cheeger, generator, and spectral interfaces on top of the now-proved Borell
   density/moment representation, the closed affine covariance form, its translation invariance
   and the affine/isotropic reduction.
2. Formalize one long KLS branch after an explicit branch-selection decision. The present route
   ordering is a navigation order, not a fixed scheduling priority. On the conditional-fiber
   branch, `cor:conditional-fiber-twelve-bound` now has its one-dimensional input
   `thm:one-dimensional-logconcave-poincare`, the structural form lemma
   `lem:conditional-fiber-form` and the comparison lemma
   `lem:conditional-fiber-energy-comparison` (fiber disintegration of the gradient energy)
   certified; what remains for the corollary is the log-concavity and nondegeneracy of almost every
   conditional fiber of a log-concave law, which instantiates `FiberBound` with `κ = 4`.

The ambient/intrinsic, smooth-test/relaxed, and general log-concave literature constant equalities
are Lean-certified, and so is the Borell density/moment representation of the intrinsic law. KLS,
`2 Ch_μ`, and the long routes still require their own local proofs; the Dirichlet property of the
smooth relaxation, the one-dimensional `12 Var` bound, raw/core agreement under local density
hypotheses, the Dirichlet structure of the conditional-fiber form and its comparison with the gradient energy under a fiber Poincaré input are certified. Unrestricted raw/core agreement is refuted by the recorded Dirac example
and, for the ambient pre-energy, by the normal-direction obstruction on proper affine supports.

## 全库命名补充整理（2026-09-08）

全库声明作用域和文件归属已进一步整理：33 个公共短名、12 个模块路径，
881 个公共签名及 1085 项展开后的类型/定义闭包核对一致。完整记录见
[research/decisions/2026-09-08-library-naming.md](research/decisions/2026-09-08-library-naming.md)。
最终验收读取 `build/verification/latest.json` 并核对当前源码快照；工作区改动尚未提交。
