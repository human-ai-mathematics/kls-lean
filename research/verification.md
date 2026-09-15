# Local verification and task atlas

The goal is to make the next formalization task and its evidence reproducible while retaining
the distinction between known mathematics, local arguments, open research, and Lean proofs.
This workflow runs locally and does not commit, push, dispatch agents, or publish artifacts.
Public interfaces remain editable under [the lifecycle](ledger-schema.md#lifecycle).

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
See [the L9 decision](decisions/2026-09-15-regular-coarea.md) and `research/explorations/2026-09-15-regular-coarea.json`.

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
[the open-graph decision](decisions/2026-09-15-open-graph-area.md) and
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
[the critical-slice decision](decisions/2026-09-15-critical-slice.md) and
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
See [the migration decision](decisions/2026-09-15-levelset-measurable-migration.md) and
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
See [the Borel-slice decision](decisions/2026-09-15-borel-slice-measurable.md) and
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
[the compact-slice decision](decisions/2026-09-15-compact-slice-measurable.md) and
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
[the Eilenberg-majorant decision](decisions/2026-09-15-eilenberg-majorant.md) and
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
[the null-slicing decision](decisions/2026-09-15-null-slicing.md) and
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
HEAD stays `2965b32`; no commit/push. See [the route decision](decisions/2026-09-15-weighted-coarea-route.md) and
`research/explorations/2026-09-15-weighted-coarea-route.json` for exact statements and hashes.

Still unproved: sharp C^(finrank) `Analysis.sard` (no downstream consumer), all three coarea
holes, `smoothConstant_le_minkowskiConstant`, `smoothConstant_mul_lintegral_min_superlevel_le`,
and equality of the two Cheeger constants. Smooth Sard and `ae_exists_superlevel` remain proved
without `sorryAx`; the full chain is not closed. Next suggested step: L2 null slicing, then L3–L5
fiber measurability. No certificate or Blueprint leanok scope was expanded.

## Superlevel rewiring round (2026-09-15)

**Superseded by the weighted coarea route round above; retained as a dated snapshot.**
`SmoothDomain.ae_exists_superlevel` and `SmoothDomain.frontier_superlevel_subset` moved from
`KLS/WIP/CheegerInfimum.lean` to the hole-free `KLS/Geometry/RegularSuperlevel.lean` with
byte-identical `pp.all` signatures, and the former is now proved from the smooth Sard theorem, so
**it no longer inherits `sorryAx`**. `WIP/CheegerInfimum.lean` dropped its import of
`WIP/AnalyticPrerequisites` and still compiles, so no module imports that file any more.

Holes are unchanged at **11** (3/3/5) — a filled body moved, not a direct hole; certificates stay
**24**, perimeter infrastructure **missing**. `build/audit/SuperlevelSardScope.lean` reports the
boundary: the moved statements and `Analysis.sard_smooth` carry only standard axioms, while
`Analysis.sard` and `Analysis.ae_forall_fderiv_ne_zero` still carry `sorryAx`. Ten earlier audits
re-pass strictly without edits; default `lake build` passes (3393 jobs). The incoming passed
receipt `20260914T171940.461693Z` was matched byte-for-byte. HEAD stays `2965b32`; no commit/push.
See the [new decision](decisions/2026-09-15-superlevel-rewire.md).

## Smooth Sard round (2026-09-15)

**Superseded by the superlevel rewiring round above; retained as a dated snapshot.**
Sard's theorem for `C^∞` real-valued functions is proved in `Analysis/SmoothSard.lean` with
standard three axioms only — `Analysis.sard_smooth_pi`, `Analysis.sard_smooth` and
`Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top` — with no measurability assumed on the
critical set. The recorded L3 turned out to be unnecessary: `Analysis.exists_contDiff_eventuallyEq`
keeps the induction global, so the already proved top layer applies unchanged.

`build/audit/SmoothSardAudit.lean` reproves the statement of `SmoothDomain.ae_exists_superlevel`
from the new theorem with **no `sorryAx`**, while the WIP declaration in the same log still carries
it. **No WIP file changed**: holes stay **11** (3/3/5), certificates **24**, perimeter
infrastructure **missing**, sharp `Analysis.sard` unchanged. Eight earlier audits re-pass strictly
without edits and default `lake build` passes (3393 jobs). The incoming passed receipt
`20260914T165021.064313Z` was matched byte-for-byte. HEAD stays `2965b32`; no commit/push. See the
[new decision](decisions/2026-09-15-smooth-sard.md).

## Smooth Sard ingredients round (2026-09-15)

**Superseded by the smooth Sard round above; retained as a dated snapshot.**
`Analysis/SmoothSard.lean` proves `critical_subset_layers`, `exists_flat_direction` and
`exists_local_graph` — lemmas L2, L4 and L5 of the route — with standard three axioms only.
L5 had to be strengthened beyond the recorded plan: `ContDiffAt ℝ ∞` does not upgrade to
`ContDiffOn ℝ ∞` on a neighbourhood, so the inverse function theorem's pointwise smoothness is
insufficient and the parameter map is now `C^∞` on an open set, obtained by applying
`OpenPartialHomeomorph.contDiffAt_symm` at every point of the region where the chosen partial
derivative is nonzero.

**No `sorryAx` was removed and no existing statement changed.** General `Analysis.sard` and both
consumers still inherit `sorryAx`; holes stay **11** (3/3/5), certificates **24**, perimeter
infrastructure **missing**. The module and its client pass `-DwarningAsError=true` with 10
standard-axiom reports; seven earlier audits re-pass strictly without edits; default `lake build`
passes (3393 jobs). The incoming passed receipt `20260914T162757.518089Z` was matched
byte-for-byte. HEAD stays `2965b32`; no commit/push.

Next: L3 (open-domain flat layer, requiring the order-`n` remainder on an open domain), L1 (the
dimension induction) and L6/L7. See the
[new decision](decisions/2026-09-15-smooth-sard-ingredients.md).

## Sard route exploration round (2026-09-15)

**Superseded by the ingredients round above; retained as a dated snapshot.**
**No theorem was proved and no Lean source under `formalization/` changed.** The round produced a
route and type-checked statements only. `build/audit/SmoothSardRouteStatements.lean` passes
`-DwarningAsError=true` with nine `#check`s and contains no declaration, proof or placeholder
axiom.

The sharp `C^n` `Analysis.sard` turns out to be needed by no consumer: its only user is
`Analysis.ae_forall_fderiv_ne_zero`, whose only user is `SmoothDomain.ae_exists_superlevel`, which
already assumes `ContDiff ℝ ∞ u`. A `C^∞` Sard plus a `C^∞` variant of the a.e. statement would
free that consumer from `sorryAx` while the sharp statement keeps its text and its direct-hole
status. The sharp version's first real obstruction is `n = 4, j = 2`; dimension 3 is reachable.
The recommended induction is over open domains (`ContDiffOn ℝ ∞ u O`, `IsOpen O`), and Mathlib's
`Analysis/Calculus/ImplicitContDiff.lean` supplies the local `C^∞` graph with a graph
characterization.

Holes stay **11** (3/3/5), certificates **24**, perimeter infrastructure **missing**;
`Analysis.sard` and both consumers still inherit `sorryAx`. Default `lake build` and
`python3 research/verify.py` re-pass. HEAD stays `2965b32`; no commit/push. See the
[route decision](decisions/2026-09-15-smooth-sard-route.md).

## Higher-order flat layer round (2026-09-15)

**Superseded by the route exploration round above; retained as a dated snapshot.**
Both obligations recorded last round are proved verbatim with standard three axioms only:
`Analysis.exists_uniform_pow_remainder` (order-`n` uniform remainder at fully flat points of a
compact set, on an arbitrary real normed domain) and
`Analysis.volume_image_eq_zero_of_oscillation_pow` (the `n`-dimensional covering lemma, no
measurability anywhere). `Analysis.volume_image_flat_pow_eq_zero` and
`Analysis.volume_image_flat_pow_univ_eq_zero` combine them into the fully flat layer on a compact
subset and on all of `Fin n → ℝ`.

The remainder is an induction on the order through `fderiv f`; the covering lemma swaps the
`ℤ × ℤ` grid for `Fintype.piFinset` over `Fin n → ℤ`, where `(2M+1)ⁿ` cells and `O(ε rⁿ)`
intervals cancel. `exists_uniform_quadratic_remainder` and
`volume_image_eq_zero_of_quadratic_oscillation` became corollaries with **byte-identical**
statements (diff-checked), so no proof content is duplicated and no client changed.

Holes stay **11**, certificates **24**, perimeter infrastructure **missing**; general
`Analysis.sard` and both its consumers still inherit `sorryAx`. The modules and the new client
pass `-DwarningAsError=true` with 17 standard-axiom reports (the two recorded obligations
verbatim, a dimensionless normed space, dimensions zero/one/three, the unchanged planar
interface, and a constant function fully flat on all of `ℝⁿ`). Six earlier audits re-pass
strictly without edits, the three WIP files re-elaborate with **3/3/5** direct holes, and default
`lake build` passes (3393 jobs). The incoming passed receipt `20260914T154144.742286Z` was matched
byte-for-byte; the final root receipt is `build/verification/latest.json`. HEAD stays `2965b32`;
no commit/push.

Next: the intermediate layers and the stacked dimension-`n` Sard, type-checked but unproved in
`build/audit/IntermediateLayerNextStatement.lean`. See the
[new decision](decisions/2026-09-15-higher-order-flat-layer.md).

## Planar Sard round (2026-09-14)

**Superseded by the higher-order flat layer round above; retained as a dated snapshot.**
`Analysis.sard_plane` is proved in
`formalization/FunctionalInequalities/Analysis/PlanarSard.lean` with standard three axioms only:
the critical values of a `C²` function on `Fin 2 → ℝ` are Lebesgue null, with no measurability,
boundedness or compactness assumption on the critical set. The nonflat layer
`Analysis.volume_image_nonflat_eq_zero` and the one-dimensional covering lemma
`Analysis.volume_image_eq_zero_of_quadratic_bound` are proved with it.

The nonflat layer uses no implicit function theorem. Near a point with `D²u ≠ 0` the mean value
inequality with linear principal part makes the critical set a Lipschitz graph over one
coordinate, which also forces injectivity of that coordinate, collapsing the layer onto the
one-dimensional covering lemma; Lindelöf glues the local balls countably. `Analysis/ImplicitGraph`
was not reused (it requires `C^∞` and an inner product, while `Du` is only `C¹`), and no new
framework was added.

`Analysis.sard_plane` is dimension two only and does **not** prove `Analysis.sard`, which stays a
direct hole with both consumers inheriting `sorryAx`. Holes stay **11**, certificates **24**,
perimeter infrastructure **missing**. The two modules and the independent client pass
`-DwarningAsError=true` with 16 standard-axiom reports, including the previously recorded compact-`K`
obligation verbatim, an arbitrary non-measurable subset, a constant function whose critical set is
the whole plane, and `x ↦ (x 0)²` whose critical set is proved to be exactly the line `{x 0 = 0}`.
Five earlier audits re-pass strictly, the three WIP files re-elaborate with **3/3/5** direct holes,
and default `lake build` passes (3393 jobs). The incoming passed receipt `20260914T150543.429034Z`
was matched byte-for-byte; the final root receipt is `build/verification/latest.json`.
HEAD stays `2965b32`; no commit/push.

Next: the `n`-dimensional covering lemma and the order-`n` uniform remainder at fully flat points,
type-checked but unproved in `build/audit/HigherSardNextStatement.lean`. See the
[new decision](decisions/2026-09-14-planar-sard.md).

## Planar quadratic covering round (2026-09-14)

**Superseded by the planar Sard round above; retained as a dated snapshot.**
`Analysis.volume_image_eq_zero_of_quadratic_oscillation` and `Analysis.volume_image_flat_eq_zero`
are proved in `formalization/FunctionalInequalities/Analysis/QuadraticCover.lean`, with standard
three axioms only. For a bounded `A : Set (Fin 2 → ℝ)` and an arbitrary `f`, a uniform
`|f y - f x| ≤ ε‖y-x‖²` over pairs of points of `A` gives `volume (f '' A) = 0`; neither `A` nor
`f '' A` is assumed measurable, `f` has no regularity anywhere, and the empty set is covered.
The proof grids `A` into `O(r⁻²)` integer-floor cells of width `r = min δ 1`, takes one
`A`-representative per occupied cell, covers its image by an interval of length `2εr²`, sums with
`measure_biUnion_finset_le`, and sends `ε → 0`; the intermediate bound `2ε(2R+3)²` is independent
of `r`. Dimension two is exactly where the cell count and the interval length cancel.
Connected to `Analysis.exists_uniform_quadratic_remainder`, this makes the image of the
**subset** `{x ∈ K | Du x = 0 ∧ D²u x = 0}` of a planar compact `K` null for `C²` `u`; all of `K`
is not assumed flat and the subset is not assumed measurable. A countable exhaustion by
`closedBall 0 n` upgrades this to `Analysis.volume_image_flat_univ_eq_zero` on the whole plane,
with no compactness, boundedness or measurability hypothesis left. Only Mathlib and the local
`Analysis/TaylorRemainder` are imported; no declaration moved, no signature changed, no WIP
dependency and no certificate expansion.

The new module and independent client pass `-DwarningAsError=true`; 19 axiom reports use only
standard axioms, covering the empty set, a singleton with a completely arbitrary `f`, an arbitrary
bounded set with no measurability instance in the client, the hypothesis-free whole-plane flat
layer, and the flat layer of the nonconstant `x ↦ (x 0)³` on a closed ball with an explicit nonflat
point `![1,0]` and an explicit flat point `0` in that ball. QuadraticRemainderAudit, SardLowDimAudit, AreaFormulaAudit and SuperlevelSardScope
re-pass strictly. The three WIP files actually re-elaborate with **3/3/5** direct-hole warnings
only. General Sard and its two consumers still inherit `sorryAx`: holes stay **11**, certificates
**24**, perimeter infrastructure **missing**. No coarea, reverse Cheeger comparison or equality is
proved. Default `lake build` passes (3393 jobs). The incoming passed receipt
`20260913T190354.174769Z` was matched byte-for-byte to all 390 files; the final root receipt is
`build/verification/latest.json`. HEAD stays `2965b32`; no commit/push.

Next: the complementary planar layer `{x ∈ K | Du x = 0 ∧ D²u x ≠ 0}`, type-checked but unproved in
`build/audit/PlanarNonflatNextStatement.lean`. This round finishes the planar second-order flat
layer only; the planar nonflat layer, general Sard, weighted coarea and the reverse Cheeger
comparison all remain unproved, and the chain is not closed. See the
[new decision](decisions/2026-09-14-planar-quadratic-cover.md).

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
[new decision](decisions/2026-09-14-uniform-quadratic-remainder.md).
The new estimate itself is not an image-nullity or general Sard theorem.

## Current low-dimensional Sard round (2026-09-14)

**Superseded by the quadratic remainder round above; retained as a dated snapshot.**
`Analysis.sard_of_finrank_le_one` is proved in
`../formalization/FunctionalInequalities/Analysis/Sard.lean`, with only
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
[new decision](decisions/2026-09-14-low-dimensional-sard.md).
Mathlib already provides multivariate integral Taylor, inverse/implicit function, chain-rule and
countable-cover tools. Higher-order critical strata, regularity-preserving dimension descent and
the quantitative covering/null-image argument are still missing; naive descent loses regularity
on higher strata. A base case is not a completed induction.
Incoming receipt `20260913T182956.860385Z` was independently matched to all 384 files.
HEAD remains `2965b32`; no commit or push. All earlier uncommitted work is preserved.

## Previous superlevel round (2026-09-14)

`Geometry/SmoothDomain.lean` (which gains the hole-free `SmoothDomain.ofSuperlevel` and
`ofSuperlevel_carrier`) and the new independent client `build/audit/SuperlevelDomainAudit.lean` pass
`-DwarningAsError=true`; the client's 8 axiom reports use only the standard three axioms and cover
the frontier-only regularity hypothesis, the sign direction of the defining function `φ = t - u`,
an everywhere-critical level set with empty frontier and empty carrier, the full carrier, dimension
zero, and an unbounded half-space with explicitly unbounded carrier and frontier. The separate
`build/audit/SuperlevelSardScope.lean` records the opposite fact for the packaging:
`SmoothDomain.ae_exists_superlevel` now has a proof body but **still depends on `sorryAx`** through
`Analysis.ae_forall_fderiv_ne_zero` and `Analysis.sard`, so it is **not** on any `sorryAx`-free
list. No module migrated; `frontier_superlevel_subset` only moved above its consumer inside
`KLS/WIP/CheegerInfimum.lean`, and the `pp.all` `#check` output of both declarations is
byte-identical before and after (`build/audit/superlevel-signature-{before,after}.log`).
Actual ordinary elaboration of the three WIP files reports exactly 3/3/5 holes and no other
diagnostics, so the direct-hole total is **11**; this does **not** mean Sard or any of its
transitive dependencies is gone. The re-run `BoundaryChartAudit`, `CheegerInfimumAudit`,
`CutoffRouteReview`, `DilationAudit`, `DistanceCutoffAudit`, `GaussGreenAudit`,
`MinkowskiCoareaAudit`, `MinkowskiConstantAudit`, `MollifiedBoundaryScope`,
`PerimeterInterfaceAudit`, `RecoveryAudit` and `SubgraphDivergenceAudit` clients pass strictly with
no `sorryAx`; `build/audit/AreaFormulaAudit.lean` remains broken from an earlier round, because it
names `Analysis.divergence` without importing `Analysis/Divergence.lean`, and was not rewritten.
Default `lake build` passes. The final root verification evidence is bound to
`build/verification/latest.json`; the starting passed receipt matched all 383 files.
The perimeter infrastructure remains missing and certificates remain 24. See the
[new decision](decisions/2026-09-14-regular-superlevel-smooth-domain.md) for the split between the
`sorryAx`-free construction and the Sard-dependent packaging, the actual statements of the three
remaining analytic holes, and the next target — the low-dimensional base case of Sard, which is a
base case only and will not fill `Analysis.sard`.
The dated rounds below describe their earlier snapshots.

## Current distance-cutoff round (2026-09-13)

The new hole-free `Geometry/DistanceCutoff.lean`, the unchanged
`Geometry/{CheegerInfimum,MinkowskiConstant,MinkowskiContent}.lean` and the new independent client
`build/audit/DistanceCutoffAudit.lean` pass `-DwarningAsError=true`; the client's 14 axiom reports,
and the re-run 14 Cheeger-infimum, 17 Minkowski-constant, 18 Minkowski-coarea, 14 recovery, 17
dilation and 22 GaussGreen reports, use only the standard three axioms, as does the re-run
`CutoffRouteReview` route check. `Geometry/DistanceCutoff` has a **zero-module** local import
closure. The complete cutoff basis, including `tendsto_distanceCutoff_indicator`, moved into it with
byte-identical `pp.all` signatures, verified by diffing the pre- and post-migration `#check` output
for all seven declarations; `exists_smooth_approximation_lipschitz` was deliberately left in place.
Actual ordinary elaboration of the three WIP files reports exactly 3/4/5 holes and no other
diagnostics, so the direct-hole total is **12**. Default `lake build` passes. The final root
verification evidence is bound to `build/verification/latest.json`; the starting passed receipt
matched all 381 files.
The perimeter infrastructure remains missing and certificates remain 24. This round proves a
gradient estimate on the reverse-direction chain, not the reverse comparison:
`smoothConstant_le_minkowskiConstant` is still a direct hole and
`minkowskiConstant_eq_smoothConstant`, which has a `le_antisymm` body, inherits `sorryAx` through
it, so the equality of the two Cheeger constants is still not established. See the
[new decision](decisions/2026-09-13-distance-cutoff-gradient-integral.md) for proof scope, the
separated reverse-direction dependencies and the next target,
`SmoothDomain.ae_exists_superlevel` — currently a direct hole, which when proved becomes a filled
body still inheriting `sorryAx` through Sard.
The dated rounds below describe their earlier snapshots.

## One-sided Cheeger round (2026-09-13)

The new hole-free `Geometry/CheegerInfimum.lean`, the unchanged
`Geometry/{MinkowskiContent,MinkowskiConstant,PerimeterRecovery}.lean` and the new independent
client `build/audit/CheegerInfimumAudit.lean` pass `-DwarningAsError=true`; the client's 14 axiom
reports, and the re-run 17 Minkowski-constant, 18 Minkowski-coarea, 14 recovery, 17 dilation and 22
GaussGreen reports, use only the standard three axioms. `Geometry/CheegerInfimum` has a 32-module
local import closure containing **no WIP module**. `smoothConstant`,
`smoothConstant_eq_top_of_subsingleton`, `lintegral_measure_symmDiff_superlevel`,
`min_measure_le_add_measure_symmDiff` and `tendsto_lintegral_min_superlevel` moved into it with
byte-identical `pp.all` signatures, verified by diffing the pre- and post-migration `#check` output
for all six declarations including the newly proved `minkowskiConstant_le_smoothConstant`; the
`unusedSectionVars` linter reports nothing on the filled body, so the section variables and hence
the hypotheses are unchanged. Actual ordinary elaboration of the three WIP files reports exactly
3/5/5 holes and no other diagnostics, so the direct-hole total is **13**. Default `lake build`
passes. The final root verification evidence is bound to `build/verification/latest.json`; the
starting passed receipt matched all 378 files.
The perimeter infrastructure remains missing and certificates remain 24, and **only one direction
is proved**: `smoothConstant_le_minkowskiConstant` is a direct hole;
`minkowskiConstant_eq_smoothConstant` has a `le_antisymm` body inheriting `sorryAx` from it.
The equality of the two Cheeger constants and the comparison chain are not established. See the
[new decision](decisions/2026-09-13-cheeger-infimum-one-sided.md) for proof scope and the next
target, `lintegral_enorm_gradient_distanceCutoff_le`.
The [audit correction](decisions/2026-09-13-cutoff-route-audit-correction.md) records the
pointwise cutoff route without Rademacher or `hac`, and corrects the status of
`SmoothDomain.ae_exists_superlevel` (still a direct hole).
The dated rounds below describe their earlier snapshots.

## Minkowski-constant round (2026-09-13)

The new hole-free `Geometry/MinkowskiConstant.lean`, the unchanged `Geometry/MinkowskiContent.lean`
and the new independent client `build/audit/MinkowskiConstantAudit.lean` pass
`-DwarningAsError=true`; the client's 17 axiom reports, and the re-run 18 Minkowski-coarea, 14
recovery, 17 dilation and 22 GaussGreen reports, use only the standard three axioms.
`Geometry/MinkowskiConstant` has a **one-module** local import closure, the hole-free
`Geometry/MinkowskiContent`, whose own closure is empty. `minkowskiConstant` and
`minkowskiConstant_eq_top_of_subsingleton` moved into it with byte-identical `pp.all` signatures,
verified by diffing the pre- and post-migration `#check` output; `KLS/WIP/CheegerInfimum.lean`
imports it and keeps the still-unproved Cheeger-infimum comparisons. Actual ordinary elaboration of
the three WIP files reports exactly 3/6/5 holes and no other diagnostics, so the direct-hole total
is **14**. Default `lake build` passes. The final root verification evidence is bound to
`build/verification/latest.json`; the starting passed receipt matched all 376 files.
The perimeter infrastructure remains missing and certificates remain 24: an integrated coarea bound
for `h_M` is not the weighted coarea formula, not Sard, not an equality of Cheeger constants and
not the completed comparison chain. See the
[new decision](decisions/2026-09-13-minkowski-constant-coarea-product.md) for proof scope and the
next target, `minkowskiConstant_le_smoothConstant`.
The dated rounds below describe their earlier snapshots.

## Minkowski-coarea round (2026-09-13)

The new hole-free `Geometry/MinkowskiContent.lean` and the new independent client
`build/audit/MinkowskiCoareaAudit.lean` pass `-DwarningAsError=true`; the client's 18 axiom
reports, and the re-run 14 recovery, 17 dilation and 22 GaussGreen reports, use only the standard
three axioms. `Geometry/MinkowskiContent` has a **zero-module** local import closure: it depends on
Mathlib alone. `minkowskiContent` and `measure_closure_eq_of_minkowskiContent_ne_top` moved into it
with unchanged full names; `KLS/WIP/CheegerInfimum.lean` imports it and keeps the still-unproved
Cheeger-infimum comparisons. Actual ordinary elaboration of the three WIP files reports exactly
3/7/5 holes and no other diagnostics, so the direct-hole total is **15**. Default `lake build`
passes (3393 jobs). The final root verification evidence is bound to
`build/verification/latest.json`; the starting passed receipt matched all 374 files.
The perimeter infrastructure remains missing and certificates remain 24: a Minkowski coarea
inequality is not the weighted coarea formula, not Sard, not an equality of Cheeger constants and
not the completed comparison chain. See the
[new decision](decisions/2026-09-13-minkowski-coarea-inequality.md) for proof scope and the next
target, `minkowskiConstant_mul_lintegral_min_superlevel_le`.
The dated rounds below describe their earlier snapshots.

## Recovery-sequence round (2026-09-13)

Eight relevant no-hole modules and three independent clients pass `-DwarningAsError=true`.
The 14 recovery, 17 dilation and 22 GaussGreen axiom reports use only the standard three axioms.
`Geometry/PerimeterRecovery` has a 30-module local import closure with zero WIP imports.
`KLS/WIP/RelativePerimeter.lean` had no remaining content and was deleted; its only consumer,
`KLS/WIP/CheegerInfimum.lean`, imports the new module directly. Actual ordinary elaboration of the
three remaining WIP files reports exactly 3/8/5 holes and no other diagnostics, so the direct-hole
total is **16**. The final default-build and root verification evidence is bound to
`build/verification/latest.json`; the starting passed receipt matched all 372 files.
The perimeter infrastructure remains missing and certificates remain 24: a recovery sequence is not
a coarea formula, not the Cheeger bridge, and not the completed relative-perimeter chain. See the
[new decision](decisions/2026-09-13-smooth-recovery-sequence.md) for proof scope and the next
target, the Minkowski coarea inequality. The dated rounds below describe their earlier snapshots.

## Dilation-integral round (2026-09-13)

Ten relevant no-hole modules and two independent clients pass `-DwarningAsError=true`.
The 17 dilation and 22 GaussGreen axiom reports use only the standard three axioms.
`Geometry/RelativePerimeter` has a 29-module local import closure with zero WIP imports.
Actual ordinary elaboration of the four WIP files reports exactly 1/3/8/5 holes and no other
diagnostics. The final default-build and root verification evidence is bound to
`build/verification/latest.json`; the starting passed receipt matched 368 files.
The perimeter infrastructure remains missing and certificates remain 24. See the
[new decision](decisions/2026-09-13-dilated-gradient-integral.md) for proof scope and the
remaining recovery-sequence work. The dated rounds below describe their earlier snapshots.

## Mollified-gradient round (2026-09-13)

Seven geometry modules and the independent `build/audit/GaussGreenAudit.lean` client pass
`-DwarningAsError=true`; all 22 reported transitive axiom sets contain only the standard three
axioms. The new consequence module's 15-module local closure has no WIP imports.
Actual ordinary WIP elaboration reports exactly 2/3/8/5 holes, all at exit 0 and without other
diagnostics. Default library build passes (3393 jobs). The final root verification receipt is
`build/verification/latest.json`; rerun `python3 research/verify.py` whenever its source snapshot
changes. The starting receipt passed and matched all 364 files before this round's edits.
Certificates remain 24, the perimeter-chain infrastructure remains missing, and no remote CI
claim is made. See the [new decision](decisions/2026-09-13-mollified-gradient-bound.md).
The dated audit counts below retain their historical meaning.

## Scope of the 2026-09-12 audit

All 24 certified nodes passed the local gates before this documentation update: 103 Python tests,
default Lake build, the KLS statement golden (26 local declaration dependencies), 349 selected
transitive axiom reports, and 149 local-module kernel replays. A separate environment-level audit
of the aggregate and the 24 certificate imports found 2,042 local declarations, including 1,631
theorem declarations and generated auxiliaries, with no nonstandard axioms, unsafe or partial
constants. These counts describe that audit snapshot, not a permanent coverage target.

Kernel replay includes the four WIP modules and can accept terms using `sorryAx`; the certified
import closure excludes WIP. Ordinary direct elaboration of each WIP file succeeds with its
expected `sorry` warnings. With `-DwarningAsError=true`, those warnings become errors and the
command exits nonzero. Thus neither ordinary elaboration nor replay certifies a WIP proof. The
hole-free modules added on 2026-09-12 — `KLS/Geometry/SurfaceMeasure.lean`,
`Analysis/LevelSet.lean`, `Analysis/AreaFormula.lean` and `Analysis/Divergence.lean` — do pass
`-DwarningAsError=true` at exit 0, as do the later hole-free modules `Analysis/ImplicitGraph.lean`,
`Analysis/SubgraphDivergence.lean`, `Analysis/GraphIntegral.lean`,
`Analysis/PartitionOfUnity.lean`, `KLS/Geometry/BoundaryChart.lean`,
`KLS/Geometry/LocalGaussGreen.lean` and `KLS/Geometry/GaussGreen.lean`, and the independent
audit clients; the four WIP files still do not, and their strict-mode failure is the control that
shows the flag is active.
The statement-only follow-up temporarily increased the total from 24 to 28. Its four boundary
interfaces now have standard-axiom proofs, returning the current total to 24; see the
[proof record](decisions/2026-09-12-outward-normal-interfaces-proofs.md) and
[closeout](decisions/2026-09-12-outward-normal-interfaces-closeout.md).
The earlier counts and gate results remain a historical [audit snapshot](decisions/2026-09-12-status-audit-and-wip-retention.md).

Verification trusts pinned third-party compiled imports; it is not a fresh independent Mathlib
rebuild or a remote CI result. Re-run `python3 research/verify.py` after source or metadata changes
to bind the receipt to the final working-tree snapshot.

## Reading path and authorities

1. [KLS statement](../formalization/FunctionalInequalities/KLS/Statement.lean) and
   [its definitions](../formalization/FunctionalInequalities/KLS/Definitions.lean): the literal
   current target, with finite universal constant, every natural dimension, finite second
   moment, compact-set log-concavity and the intrinsic local-slope literature constant.
2. [Blueprint](../formalization/blueprint/README.md): mathematical statements and declared
   dependencies; the route sidecar owns alternative branches, adapters and pinned provenance.
3. [Ledger](a-series/ledger.yaml): the twenty-four certified mathematical nodes. A compiled definition
   or conjecture declaration is not another proved ledger theorem.
4. [Task metadata](tasks.json): mathematical classification, retained assumptions, priority,
   evidence references and the retry policy. It contains no second copy of Lean proof status.
5. [Atlas exporter](atlas.py) and [verification runner](verify.py): derived navigation and
   snapshot-bound machine evidence. Neither parses informal prose to decide mathematical truth.

## Commands

Run from the repository root:

```bash
python3 research/atlas.py check
python3 research/verify.py
python3 research/atlas.py export
python3 research/atlas.py ready
python3 research/atlas.py show thm:selected-literature-constant-equivalence
```

`check` runs the existing ledger/Blueprint structural checks plus task classification, reference,
certificate coverage and cycle checks. The 88 navigation labels contain 75 mathematical nodes;
chapter labels are not tasks. Statement dependencies and those in the immediately following
proof are combined. The graph records declared dependencies, not an extraction of proof terms;
missing mathematical prerequisites can still be discovered while formalizing a node.

`verify.py` runs the Python tests, default Lake build, elaborated statement snapshot comparison,
declaration and axiom audit, and kernel
replay of every compiled module under `FunctionalInequalities`, `solutions`, and `examples`.
Before preparing replay it explicitly builds every current in-scope module with `lake build +Module`,
including WIP outside the default import closure. This prevents a development cache from masking
missing artifacts on clean CI; WIP is still excluded from the certificate axiom audit. See the
[CI repair and route audit](decisions/2026-09-12-ci-replay-scope-and-route-audit.md).
It copies the compiled parts of exactly the current source modules into the run's `local-olean/`
view, records their hashes, and replaces only the local entry in Lake's search path for replay.
This excludes orphaned modules and ignored duplicate artifacts in an old development cache
without deleting them. A missing current compiled module or any replay coverage mismatch fails.
Explicit prefixes are necessary: the package name `functional-inequalities` differs from the library name,
so bare `leanchecker` guesses the wrong module in this checkout. The runner clears an inherited
`LEAN_PATH` before invoking Lake, uses Lake's toolchain binary for the filtered replay, and limits
Lean worker threads to two. This view is made from the current build; it is not a source rebuild.

The generated declaration audit imports the built library and certificates, checks all Blueprint
Lean anchors, all local declarations reached by the statement snapshot, and the twenty-five named
definition checks in `solutions/StatementChecks.lean`, and inspects their transitive axioms.
The generated audit looks up exact declaration names in Lean's environment and calls
`Lean.collectAxioms`, the same transitive collector used by `#print axioms`. This keeps
compiler-generated auxiliary proofs in the audit without referencing their unstable names as
source identifiers. A missing declaration fails before collection; it cannot pass as axiom-free.
Missing reports or axioms outside `propext`,
`Classical.choice`, and `Quot.sound` fail acceptance. The twenty-four certificates additionally have
default-build guards. The expected certificate list comes from the existing explicit
Blueprint-to-ledger mapping; a new proved ledger node without a mapping is an error.

Each run writes immutable evidence under `build/verification/<UTC timestamp>/`, including logs,
the generated Lean audit, full printed certificate declarations, the input atlas, and a report.
`build/verification/latest.json` identifies the latest attempt, including a failed one.
The report hashes tracked and nonignored untracked source content, detects deletions, and records
HEAD separately. Sources must have identical hashes before and after verification. Editing any
source makes a prior receipt stale even when HEAD is unchanged. Build output is ignored by Git
and does not invalidate its own receipt. The input atlas saved inside a verification run predates
that run's successful receipt; export again afterwards for current dispatch actions.

`ready` lists actions and blockers. `complete` or `formalize` is available only with a passing
receipt matching the current source snapshot. Missing, failed or stale evidence produces
`verify_recorded` for a previously annotated declaration, and `verify_prerequisites` for an
unproved task whose mathematical and infrastructure prerequisites are ready. These both request
the same repository verification; neither claims a new proof. Every dispatch also records
`verification: current | required`, including tasks whose primary action is a dependency or
infrastructure action. This receipt is local workflow evidence, not a
tamper-resistant or adversarial proof-validation protocol.

To inspect changes against an earlier exported atlas:

```bash
python3 research/atlas.py diff --against build/verification/PREVIOUS_RUN/atlas.json
```

Replace `PREVIOUS_RUN` with an existing run directory. The diff reports statement text, proof,
dependency, task and declaration changes, followed by changed source files. A referenced
definition changing is visible even if the conjecture's displayed type remains identical.
This reports changes; it does not automatically classify them as stronger, weaker or equivalent.
Record changes to hypotheses, conclusions, domains or normalization in a decision entry and
check whether the original mathematical goal is still covered. No API freeze is introduced.

## Statement baseline and definition coverage

`research/StatementSnapshot.lean` inspects elaborated declarations using `pp.all` and explicit
proof printing at width 100. Starting from the seven target/domain/energy definitions, it follows
local declaration types and definition bodies, including structure constructors and their fields.
Local ownership comes from the imported module, not merely the declaration namespace. The initial
baseline covers 26 local declarations, including `literatureEnergy`, `Covariance.operator`,
`intrinsicMeasure`, the coordinate map and affine support. Adding a referenced local helper expands
the captured dependency set automatically. Theorem types are included; theorem proof bodies are
omitted. Opaque definition bodies are included. Unsafe, partial and axiom declarations fail capture.

The golden file is [statement-snapshot/golden.json](a-series/statement-snapshot/golden.json).
It records fully explicit printed types/bodies, direct references, the external leaf names, the
toolchain, Lake manifest hash and the decision establishing that baseline. Imported non-project
declarations are trust-boundary leaves covered by pinned dependencies, not recursively snapshotted
Mathlib bodies. This is a drift detector with an explicit coverage boundary, not semantic
equivalence checking, independent verification, or evidence that the target matches the literature.

The standalone command builds the target before inspecting its current declarations:

```bash
python3 research/statement_snapshot.py check
```

A missing or mismatched baseline fails; `verify.py` never regenerates it. For an intentional change,
append a decision explaining the old/new mathematical scope and whether the original goal remains
covered, or explaining a toolchain/printing-only change. Then explicitly run:

```bash
python3 research/statement_snapshot.py update --decision research/decisions/NEW-RECORD.md
```

The update requires a different nonempty decision path. Checking also verifies that the referenced
decision's bytes have not been rewritten. This enforces record linkage, not the quality of the
mathematical review. A definition change and its baseline update can be developed together under
the current evolving-interface policy. No prior freeze checkpoint is added.

Finish decision and documentation edits **before** the final verification. A decision can cite an
earlier preflight report; the final generated receipt in `build/verification/` records its own exact
source SHA256 and Git HEAD. Do not write that final hash back into a source file and claim the
receipt still matches: decisions are themselves included in the source hash.

## Atlas schema and scheduling semantics

`tasks.json` and generated atlas use schema version 2. This is a local data-schema version, not an
external Atlas product. Tasks have `policy` and a `nodes` object keyed by existing Blueprint labels.
Each entry has these fields, with `infrastructure` required for `local_argument` and `published`
and optional for `definition`. A definition may need a nontrivial construction or a
well-definedness adapter; opting into assessment does not change its mathematical classification.
Other mathematical classes still do not accept this field. This additive schema-2 extension is
recorded in [the Borell/Claude handoff](decisions/2026-09-07-borell-equivalence-claude-handoff.md).

| Field | Meaning |
| --- | --- |
| `mathematics` | `definition`, `published`, `local_argument`, `conjectural`, `refuted`, or `unknown` |
| `evidence` | References of the form `blueprint:<existing node id>`; the referenced block and route provenance identify sources |
| `assumptions` | Named open premises explicitly retained in the theorem being formalized |
| `priority` | Integer 0 through 9; smaller is earlier, not stronger evidence |
| `note` | Mathematical scope, review requirement or execution guidance |
| `infrastructure` | Assessed implementation prerequisites, independently of mathematical truth |

An infrastructure record has exactly `status`, `mathlib_revision`, `evidence` and `gaps`:

| Status | Required evidence | Scheduling when mathematical prerequisites are ready |
| --- | --- | --- |
| `unchecked` | Revision `null`, empty evidence and gaps; no assessment is claimed | `inspect_infrastructure` |
| `available` | Current Mathlib commit and nonempty source evidence; no identified gaps | `formalize`, `formalize_conditional`, or `verify_prerequisites` |
| `missing` | Current Mathlib commit, source evidence and concrete missing interfaces | `develop_infrastructure` |

Each evidence item is `{ "path": "repository-relative/source", "sha256": "content hash" }`.
Evidence files must exist inside the repository (including pinned Mathlib sources); changed bytes
or a changed Mathlib revision fail metadata validation. Reassess and update the evidence, or return
the record to `unchecked`. `available` is a documented implementation assessment, not a theorem.
`missing` may name a local adapter still to implement; it does not claim a whole field is absent
from Mathlib. A zero-length gaps list on an unchecked record does not mean no prerequisites exist.

Initial assessment is deliberately bounded: the existing Dirac checks supply the needed APIs;
the smooth-density pilot now has a proved local weighted-gradient cutoff/mollification adapter
and its source hashes are recorded as available. Mathlib already
contains `LipschitzWith.ae_differentiableAt`,
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`, and smooth approximation tools.
`HasCompactSupport.hasFDerivAt_convolution_right` differentiates a C¹ factor; it alone does not give
the desired derivative transport for a merely Lipschitz test. The smooth/literature comparison now
has eight proved local slope/gradient and finite-constant transport adapters, assessed as available
with source hashes. The new intrinsic absolute-continuity proof and general log-concave
comparison have available local adapters too. Other published/local argument task records remain explicitly unchecked; inspect `tasks.json`
for their current assessments. This is not a survey claiming Mathlib lacks SDE,
BV or spectral theory. It does not add an analytic premise to the pilot theorem.

Research, refuted and unresolved-statement classifications take precedence. Recorded declarations
retain their certification action. Missing mathematical prerequisites keep action `blocked`, while
the infrastructure record remains visible too. Missing or unchecked infrastructure never promotes
a task to proof completion or removes a retained open premise.

Every node without a Lean-certification annotation requires explicit classification. For already
annotated definitions/theorems, certification metadata is derived from Blueprint and, where
applicable, the ledger. Published inputs and agent-reviewed arguments never become Lean proofs
merely by being cited. Missing classifications fail closed. A `local_argument` may be a proof
plan or a written argument: read its note and evidence and review it before extended proof search.

The generated `build/atlas.json` joins statements, declaration anchors, source locations,
statement hashes, direct dependencies, classification, dispatch blockers, route compositions,
certificate mappings and the source snapshot. Each task key includes its node id, statement,
dependencies and the current snapshot. This deliberately conservative first implementation
invalidates tasks on any source change; finer dependency-local caching is deferred.

- `all_of` and `any_of` in the route sidecar are preserved verbatim. Repository adapters remain
  alignment metadata and never become synthetic logical edges into `conj:kls`.
- A task proving `A -> B` may retain A without a proof, once A has a built Lean statement.
  A is still a research node. A certified implication's unproved premises also block an
  unconditional downstream consumer unless explicitly retained there.
- Research nodes go to `research`; unresolved statement choices go to `clarify_statement`;
  unclassified mathematics goes to review. Refuted packages are excluded from proof search.
- A complete certificate certifies its displayed proposition; no route metadata automatically
  promotes the KLS conjecture or an open assumption.

These commands describe and validate tasks; they do not yet launch workers or implement leases.
The policy requests a pause for reassessment after three attempts on an unchanged task; no attempt
counter, automatic stopping or automatic mathematical reclassification is implemented. Coordinators must
record whether failures come from an API gap, missing known lemma, statement error, counterexample,
or research frontier in `explorations/`. A retry budget is not evidence that a statement is false.
No unattended retry executor is included in this phase.

## Borell equivalence and conditional-fiber proofs

The 2026-09-07 owner request deliberately retained seven `sorry` proofs for Claude: one
compact/Borel log-concavity equivalence and six conditional-fiber well-definedness contracts.
Claude then proved all seven. `thm:compact-borell-logconcavity-equivalence` is now a proved
ledger node with the sole certificate `Solutions.ThmCompactBorellLogconcavityEquivalence.certificate`,
registered in `check_blueprint.CERTIFICATES`, with `\leanok` on statement and proof and
default-build axiom guards. `def:conditional-fiber-form` carries `\leanok` as a definition node
because its six contracts are proved and guarded in `StatementChecks.lean`; it is not a ledger
theorem. The declaration audit still examines every Blueprint anchor and was not relaxed:
`STANDARD_AXIOMS` is unchanged and no anchor was omitted.

Definitions may opt into an infrastructure record while retaining `mathematics: definition`,
using the same source/pin/gap validation and scheduling as other assessed tasks. The
conditional-fiber record is now `available` with no gaps. Existing theorem infrastructure
requirements are unchanged.

The statement golden still covers its original 26 declarations; the new objects do not occur
in that root closure, so no baseline update is made. New anchors, twenty-five named typed checks,
six contract guards and the certificate guards provide the stated additional coverage, without
claiming an expanded golden. Source scope is in
[the handoff decision](decisions/2026-09-07-borell-equivalence-claude-handoff.md) and the
proofs are described in
[the completion record](decisions/2026-09-07-borell-equivalence-and-conditional-fiber-proofs.md).

## Borell density representation

`thm:borell-logconcave-density` was drafted and then proved on 2026-09-07. While drafted, its
five `sorry` obligations were deliberately kept out of the Blueprint `\lean` anchors, because the
declaration audit examines every anchor for standard-only axioms and would have failed on a
placeholder rather than hidden it. Now all five theorems, the predicate `KLS.IsBorellDensity`,
the two support identities and the certificate `Solutions.ThmBorellLogconcaveDensity.certificate`
are anchored with `\leanok`, the certificate is registered in `check_blueprint.CERTIFICATES`, and
the certificate file carries default-build axiom guards for the certificate and its nine main
dependencies. Statement design and the semantic alignment review are in
[the statement decision](decisions/2026-09-07-borell-density-statements.md); the proofs are
described in [the proof record](decisions/2026-09-07-borell-density-proofs.md).

## Affine covariance Poincaré constant

`def:affine-poincare-constant` was implemented on 2026-09-07 as a definition node.
`Energy.CovarianceGradient.preEnergy ν` has globally Lipschitz `L²(ν)` tests with integrable
`⟪Σ ∇g, ∇g⟫`, `Σ = Covariance.operator ν`; `Energy.CovarianceGradient.Intrinsic.energy μ` is its sequential relaxation
on the intrinsic law, and `Poincare.CovarianceGradient.Intrinsic.constant μ` is `Poincare.L2Energy.constant` of that
relaxation. The definition needs no log-concavity; for log-concave laws the three well-definedness
contracts of the Blueprint sentence (finite intrinsic second moment, a.e. differentiability of
tests, representative independence of the energy) are proved in
`KLS/LogConcave/Covariance.lean`. Twelve anchors carry `\leanok`; the node is not a ledger
theorem, `check_blueprint.CERTIFICATES` is unchanged, and the statement golden is unchanged
because the new objects do not occur in the KLS statement closure. The definition task record is
`available` with source and Mathlib evidence hashes. Five new named checks cover the unfolding,
the test fields, the energy integral, dimension zero and the ambient Dirac law. Read
[the record](decisions/2026-09-07-affine-poincare-constant-definition.md).

## Covariance-core closure

`lem:covariance-core-closure` was proved on 2026-09-08 and is the fourteenth certificate,
`Solutions.LemCovarianceCoreClosure.certificate`, registered in `check_blueprint.CERTIFICATES`.
The Blueprint operator `T g = Σ^{1/2} ∇g` is `KLS.LogConcave.weightedOperator` with an arbitrary
continuous linear `B` in place of the square root, following the certified approximation lemma.
The certificate packages dense domain, closability, closure independence of every core between
the smooth compactly supported classes and the full domain, and the identification of the
sequential relaxation of `‖T f‖²` with `‖T̄ f‖²` on the domain of the closure and `⊤` outside.
The generic relaxation/closure identification lives in `Energy/Relaxation/LinearPMap.lean` and
is reusable for other operators. Fourteen anchors carry `\leanok` on statement and proof; the
statement golden is unchanged. Read
[the record](decisions/2026-09-08-covariance-core-closure.md).

## Affine covariance closed form

`thm:affine-covariance-relaxation-closed` was proved on 2026-09-08 and is the fifteenth
certificate, `Solutions.ThmAffineCovarianceRelaxationClosed.certificate`. Quadraticity of the
affine pre-energy is expressed through a square root `B` of the intrinsic covariance
(`Covariance.exists_inner_eq_norm_sq`); the certificate packages dense realization, the closed quadratic form
`Energy.ClosedQuadratic (Energy.CovarianceGradient.Intrinsic.energy μ)`, the sequential core, translation of the intrinsic
law with its `L²` isometry, and the identification of the affine relaxation and constant with the
closed form on the core `ℝ + C_c^∞`. Seventeen anchors carry `\leanok` on statement and proof;
the statement golden is unchanged. Read
[the record](decisions/2026-09-08-affine-covariance-relaxation-closed.md).

## Affine constant translation invariance

`lem:affine-poincare-translation-invariance` was proved on 2026-09-08 and is the sixteenth
certificate, `Solutions.LemAffinePoincareTranslationInvariance.certificate`. The ambient translate
is `Probability.translateLaw μ b`; the certificate packages log-concavity of the translate,
invariance of the ambient covariance operator and of the affine-support direction, a
variance-preserving `L²` isometry intertwining the two affine relaxations, the identity
`Poincare.CovarianceGradient.Intrinsic.constant (translateLaw μ b) = Poincare.CovarianceGradient.Intrinsic.constant μ`, the ambient second
moment of a log-concave law and the zero mean of the translate by the negative barycenter. The
constant identity is proved for every Borel law. Sixteen anchors carry `\leanok` on statement and
proof; the statement golden is unchanged. Read
[the record](decisions/2026-09-08-affine-poincare-translation-invariance.md).

## Affine and isotropic KLS formulations

`thm:affine-isotropic-reduction` was proved on 2026-09-08 and is the seventeenth certificate,
`Solutions.ThmAffineIsotropicReduction.certificate`. The three statements `KLS.IsotropicBound K`,
`KLS.CovarianceBound K` and `KLS.AffineBound K` quantify over every finite-dimensional Euclidean space
of one fixed universe; the certificate packages their pairwise equivalences for every `K` and the
implication from `KLS.AffineBound K` (universe zero) to `KLS.Conjecture`. The proof centers and whitens
the intrinsic law (`Covariance.exists_whitening`), transports the covariance relaxation along
translations and continuous linear equivalences, and identifies the identity-weighted Lipschitz
gradient relaxation constant with the literature constant. Twenty-six anchors carry `\leanok` on
statement and proof; the route sidecar claim for the node is `proved` with Lean evidence; the
statement golden is unchanged. The same inspection records `thm:cmh-recovery-affine-poincare-bound`
as `missing` infrastructure with four concrete gaps. Read
[the record](decisions/2026-09-08-affine-isotropic-reduction.md).

## Dirichlet property of the smooth-gradient relaxation

`thm:smooth-gradient-relaxation-dirichlet` was proved on 2026-09-10 and is the eighteenth
certificate, `Solutions.ThmSmoothGradientRelaxationDirichlet.certificate`. It packages
`Energy.Markovian` and `Energy.Dirichlet` for `Energy.SmoothGradient.relaxation μ` and
`Energy.Dirichlet` for `Energy.SmoothGradient.Intrinsic.energy μ`, for every Borel probability law
on a finite-dimensional Euclidean space. The proof mollifies the normal contraction on the real line
and uses the certified contraction-transfer theorem; no absolute continuity is used. Thirteen anchors
carry `\leanok` on statement and proof; the statement golden is unchanged. Read
[the record](decisions/2026-09-10-smooth-gradient-relaxation-dirichlet.md).

## One-dimensional log-concave Poincaré bound

`thm:one-dimensional-logconcave-poincare` was proved on 2026-09-10 with Bobkov's constant `12`
and strengthened on 2026-09-11 to the sharp constant `4`; it is the nineteenth certificate,
`Solutions.ThmOneDimensionalLogConcavePoincare.certificate`. For every compact-set log-concave law
`ν` on `ℝ` it now packages `Poincare.LocalSlope.Intrinsic.constant ν ≤ ENNReal.ofReal
(4 * variance id ν)` and the extended-variance form, zero variance included; `12` is a typed
corollary with its own independent proof. The constant-`4` route (affine quantile model and profile
bound `F(1−F) ≤ σρ` in `Probability/Line/AffineProfile.lean` and `KLS/LogConcave/Line/Profile.lean`,
ground-state sharp Hardy inequality for clipped tests in `Line/SharpHardy.lean`, exhaustion through
anchored half-line Hardy bounds in `Line/SharpPoincare.lean`) follows the collaborator audit
`research/explorations/2026-09-11-poincare-constant-4-audit.md`; the Blueprint statement changed
from `12` to `4` and the certificate carries nine additional axiom guards. Read
[the constant-4 record](decisions/2026-09-11-one-dimensional-logconcave-poincare-four.md). The
original constant-`12` route is described next. The
Blueprint node previously carried Bobkov's Corollary 4.3 as an `imported` published input; the
route sidecar claim is now `proved` with Lean evidence and the published reference is kept as
provenance. The local proof route (distribution function and uniform pushforward in
`Probability/Line/Cdf.lean`, Borell line density, four-point inequality and median hazard bounds,
integration-by-parts Hardy inequality with constant `1/ρ(m)²`, supporting-line variance bound
`Var ≥ 1/(12 ρ(m)²)`) differs from Bobkov's Cheeger argument and reaches exactly the constant `12`.
Sixteen anchors carry `\leanok` on statement and proof; the statement golden is unchanged. Read
[the record](decisions/2026-09-10-one-dimensional-logconcave-poincare.md).

## Raw/sequential-core agreement under density hypotheses

`thm:smooth-gradient-raw-core-agreement-density` was proved on 2026-09-10 and is the twentieth
certificate, `Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate`. For every probability
law `ν` on a finite-dimensional inner-product space with a local density
(`Energy.SmoothGradient.LocalDensity ν m`) it packages `(preEnergy ν).AgreesOnTests (relaxation ν)`
and `(preEnergy ν).IsSequentialCoreFor (relaxation ν)`; the intrinsic law is the named instance.
The proof generalizes the closability theorem of the weighted gradient operator to an arbitrary
open carrier with local domination (`Probability.LocallyDominatesOn`,
`WeightedGradient.operator_isClosable_of_isOpen`; the former `LocallyDominates` is the special
case), uses smooth cutoffs as graph-norm approximations and recovery sequences, and the
closable-operator relaxation formula. Fifteen anchors carry `\leanok` on statement and proof; the
statement golden is unchanged. The same day added the proved obstruction
`obs:normal-direction-raw-energy` (`Energy/SmoothGradient/NormalDirection.lean`, two guards in
`FoundationAxiomAudit.lean`, not a ledger node). Read
[the record](decisions/2026-09-10-smooth-gradient-raw-core-agreement-density.md).

## Closed conditional-fiber form

`lem:conditional-fiber-form` was proved on 2026-09-11 and is the twenty-first certificate,
`Solutions.LemConditionalFiberForm.certificate`. For every Borel probability law `μ` on a
finite-dimensional inner-product space and every probability law `ρ` on its unit sphere it packages
`Energy.Dirichlet μ (KLS.ConditionalFiber.functional μ ρ)` (dense finite domain, lower
semicontinuity, quadratic identities, Markov property), the jump representation of the fiber energy
on nondegenerate fibers, the swap invariance of the two-point measure (reversibility) and the bound
`energy μ ρ g ≤ d L²` for globally `L`-Lipschitz tests. The Blueprint's log-concave, density, second
moment and frame hypotheses are not used and appear only as a typed application. The two-point
variance identity `Probability.two_mul_evariance_eq_lintegral_prod` (`Probability/TwoPointVariance.lean`)
is the new reusable input; the definition module `KLS/ConditionalFiber.lean` only made two
measurability lemmas public. Sixteen anchors carry `\leanok` on statement and proof; the route
sidecar claim keeps its upstream review and gains Lean evidence; the statement golden is unchanged.
Read [the record](decisions/2026-09-11-conditional-fiber-form.md). The same inspection records
`prop:weighted-spectator-obstruction` and `lem:relative-perimeter-smoothing` as `missing`
infrastructure with concrete gaps (stochastic-localization objects and SDE theory; smooth-domain
surface measure, Gauss--Green and several-variable BV); read
[the assessment](decisions/2026-09-11-spectator-and-relative-perimeter-infrastructure.md).
The 2026-09-12 statement round wrote those prerequisites as seventeen KLS-independent `sorry`
obligations in `KLS/WIP/AnalyticPrerequisites.lean` (isodiametric via Brunn--Minkowski,
Lipschitz-graph level sets, Gauss--Green with an outward normal, weighted coarea, Sard); the module is
unregistered and no registered module depends on it. The subsequent
[proof round](decisions/2026-09-12-relative-perimeter-prerequisites-proofs.md) filled 12 bodies,
leaving 5 explicit holes at that point. Four later boundary-regularity statements were also
proved, bringing that module to 21 obligations, 16 filled bodies and 5 explicit holes. On the same
day the proved, KLS-independent Hausdorff and level-set results moved out to
`Analysis/LevelSet.lean` (with their base definitions in `KLS/Geometry/SurfaceMeasure.lean`), so
that `KLS/WIP/RelativePerimeter.lean` can import them without a cycle: `AnalyticPrerequisites` now
carries 13 obligations, 8 filled bodies and the same 5 explicit holes, 6 of the filled bodies free
of `sorryAx`. The integration closed the two perimeter holes
`hausdorffNormalized_finrank_eq_volume` and `isLocallyFiniteMeasure_hausdorff_frontier`, and the
`CheegerInfimum` hole `exists_smooth_approximation_lipschitz`, all three with standard axioms only.

A later round of the same day proved the codimension-one **area formula** for `C¹` graphs in the
new module `Analysis/AreaFormula.lean` (standard axioms only) and moved `divergence` into
`Analysis/Divergence.lean` with the rank-one trace identity. Using that identity, the scalar-test
Gauss--Green statement `setIntegral_gradient_eq_integral_smul_outwardNormal` was **reduced** to
the vector-field statement `integral_divergence_eq_integral_inner_outwardNormal`, which is still a
`sorry`: the scalar form and `gradient_mollifiedIndicator_eq` therefore still depend on `sorryAx`,
and neither Gauss--Green target is complete. `AnalyticPrerequisites` now has 12 obligations, 8
filled bodies, 6 of them free of transitive `sorryAx`, and 4 direct holes; the four WIP files
total 20. Connecting the area formula to a `SmoothDomain` frontier needs a `C^∞` implicit-function
graph representation, a subgraph Fubini/FTC computation and a smooth partition of unity, none of
which exists yet.

A 2026-09-13 round closed the first of the three remaining Gauss--Green sub-obligations. Two new
`sorry`-free modules, `Analysis/ImplicitGraph.lean` and `KLS/Geometry/BoundaryChart.lean`, prove
the local `C^∞` graph representation of a `SmoothDomain` frontier
(`KLS.SmoothDomain.exists_boundaryChart`): inside an explicit cylinder the frontier is exactly the
graph of a globally `C^∞` height function over the tangent hyperplane, the domain is exactly the
part below that graph, and the outward unit normal along the graph is
`(ι(-∇g) + ν₀)/√(1 + ‖∇g‖²)` with the sign fixed. The area formula is connected to it by
`BoundaryChart.surfaceMeasure_image`, `surfaceMeasure (Ψ '' s) = ∫_s √(1 + ‖∇g‖²)` over one
chart's parameter set. The regularity route is the `C^k` inverse function theorem plus the openness
of the invertible operators, and the local-to-global gap is closed by a `ContDiffBump` cutoff
inside the representation theorem, so the height function handed to consumers is globally `C^∞`.
`SmoothDomain.outwardNormal` and its four proved lemmas moved down into the new `BoundaryChart`
module, unchanged.

**Current counts, superseding the paragraph above.** `AnalyticPrerequisites` carries **nine public
theorems and no definitions: five filled bodies, four direct holes, and only two filled bodies free
of transitive `sorryAx`.** Before the migration it held **thirteen public theorems and one
definition** (`outwardNormal`) — nine filled theorem bodies, four holes, six filled theorems free of
`sorryAx`; the "12 obligations, 8 filled" written above subtracted the migrated `divergence`
*definition* from the *theorem* count and is corrected here. The four WIP files still total 20
direct holes. Neither Gauss--Green target is complete: the vector-field statement is still an
explicit `sorry`, and what it lacks is now only the subgraph Fubini/FTC computation and a finite
smooth partition of unity. Read the
[boundary-chart record](decisions/2026-09-13-boundary-chart-and-area-interface.md).

A later 2026-09-13 round closed the **second** of the three sub-obligations and connected it to the
boundary chart. Three new `sorry`-free modules pass `-DwarningAsError=true` at exit 0:

* `Analysis/SubgraphDivergence.lean` proves `Analysis.integral_divergence_subgraph`,
  `∫_S div F = ∫_H ⟪F (Ψ y), ι(-∇g y) + e⟫ dy` for the region `S` strictly below the graph of a
  `C¹` height function and any compactly supported `C¹` field. The right-hand side is the
  unnormalized flux: the graph Jacobian has already cancelled against the denominator of the unit
  normal, and the tangential `-∇g` term is present. The module also proves
  `Analysis.integral_divergence_eq_zero` (no boundary term on the whole space) by induction on
  `finrank`, because Mathlib's divergence theorem covers only boxes in `Fin (n+1) → ℝ`. Nothing is
  assumed bounded, `g` needs no global Lipschitz bound, and a zero-dimensional tangent space is in
  scope — there the statement is the fundamental theorem of calculus on a half line.
* `Analysis/GraphIntegral.lean` upgrades the area formula from an identity of measures of *sets* to
  a change of variables for arbitrary integrands (`map_graphChartMap_withDensity`,
  `setLIntegral_image_graphChartMap`, `setIntegral_image_graphChartMap`), assuming only
  measurability, never integrability.
* `KLS/Geometry/LocalGaussGreen.lean` proves
  `KLS.SmoothDomain.BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`:
  `∫_U div F = ∫_{∂U} ⟪F, ν⟫ dℋ^{n-1}` **for a field with `tsupport F ⊆ C.cylinder`**. This is the
  chart-local identity, not the theorem for an arbitrary compactly supported field. Boundary
  integrability is not assumed anywhere; the set replacements are pointwise identities of indicator
  functions.

Counts are unchanged by this round: `AnalyticPrerequisites` still has nine public theorems, five
filled bodies, four direct holes and only two filled bodies free of transitive `sorryAx`, and the
four WIP files still total 20 direct holes (3 / 4 / 8 / 5, re-elaborated with exactly those
diagnostics and no others). The global vector-field Gauss--Green statement is still an explicit
`sorry` and now lacks exactly one input, the finite smooth partition of unity. A new audit client
`build/audit/SubgraphDivergenceAudit.lean` checks the orientation sign on a flat model, isolates the
`-∇g` term with a purely tangential field on a tilted graph, derives the one-dimensional
fundamental theorem of calculus from the zero-dimensional case, and instantiates the chart-local
identity on the open half space as a `SmoothDomain` with the concrete outward normal `+a`; all six
client theorems use only the standard axioms. Read the
[subgraph record](decisions/2026-09-13-subgraph-divergence-and-local-gauss-green.md).

### The global Gauss--Green theorem is proved (2026-09-13, third round)

`KLS.SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal` — `∫_U div F = ∫_{∂U} ⟪F, ν⟫
dℋ^{n-1}` for **any** compactly supported `C¹` field — is proved with only the standard axioms, and
moved out of `KLS/WIP/AnalyticPrerequisites.lean` into the new hole-free
`KLS/Geometry/GaussGreen.lean`. Its statement is unchanged: same name, same namespace, the same
`ContDiff ℝ 1` and `HasCompactSupport` hypotheses, the same `surfaceMeasure` normalization and
outward orientation, no boundedness of the domain or its frontier, no finite total surface measure,
no extra smoothness, no `Nontrivial V`.

* The gluing input is the new `Analysis/PartitionOfUnity.lean`
  (`Analysis.exists_finset_sum_eq_of_isOpen_cover`), which turns an open cover of `tsupport F` into
  a **finite** family with `tsupport (G i) ⊆ W i` — closed support, so the derivative also vanishes
  outside `W i` — and `∑ i ∈ s, G i x = F x` at **every** point of the space, not only on the
  support. That global identity is what may be differentiated, so no partition-derivative term ever
  appears.
* The cover takes three kinds of open set and all three are handled: one boundary-chart cylinder per
  frontier point (`BoundaryChart.self_mem_cylinder`, then the chart-local identity), the domain `U`
  itself (`integral_divergence_eq_integral_inner_outwardNormal_of_tsupport_subset_carrier`: no flux
  because `∂U` misses the open `U`, and zero volume integral by
  `Analysis.integral_divergence_eq_zero`), and `(closure U)ᶜ`
  (`…_of_tsupport_subset_compl_closure`: both sides vanish). A support lying entirely inside or
  entirely outside the domain is therefore in scope, as are an empty support, an empty frontier and
  dimension zero.
* Every exchange of the finite sum with an integral is proved, not assumed:
  `Analysis/Divergence.lean` gains `traceLM`, `continuous_divergence`,
  `hasCompactSupport_divergence` and `divergence_finset_sum`, and `KLS/Geometry/GaussGreen.lean`
  proves `integrableOn_inner_outwardNormal` from `‖ν‖ ≤ 1`, `measurable_outwardNormal` and
  `isLocallyFiniteMeasure_surfaceMeasure_frontier`. No bound on `surfaceMeasure (∂U)` is used.
* `isLocallyFiniteMeasure_surfaceMeasure_frontier` and `integrableOn_smul_outwardNormal` migrated
  verbatim into the same module, and `Analysis.fderiv_eq_zero_of_notMem_tsupport` moved down from
  `Analysis/SubgraphDivergence.lean` to `Analysis/Divergence.lean`: no alias, no duplicate, no
  forwarding declaration.

Consequently `setIntegral_gradient_eq_integral_smul_outwardNormal` and
`gradient_mollifiedIndicator_eq` are free of transitive `sorryAx` as well — they were reductions,
and the theorem they reduce to is now proved. `AnalyticPrerequisites` drops to **six public
theorems, no definitions, three filled bodies, three direct holes and two filled bodies free of
transitive `sorryAx`** (only `ae_forall_fderiv_ne_zero` still inherits from `sard`), and the four
WIP files total **19** direct holes (3 / 3 / 8 / 5, re-elaborated with exactly those diagnostics and
no others). The new audit client `build/audit/GaussGreenAudit.lean` covers a support inside the
domain, a support outside `closure U`, the half space with the global formula and its flux sign, the
two opposite endpoint normals of a bounded interval (`∫_α^β F' = F β - F α`), the empty frontier in
any dimension, a subsingleton space, and both downstream formulas; all eleven client theorems use
only the standard axioms, as do the four earlier audit clients, re-run unchanged.

Weighted coarea and Sard are still open, and so are the mollified gradient-integral estimate and the
relative-perimeter recovery sequence, so the infrastructure for
`lem:relative-perimeter-smoothing` remains incomplete and the node is not registered; closing
Gauss--Green is **not** closing the perimeter chain. Read the
[global Gauss--Green record](decisions/2026-09-13-global-gauss-green.md), the
[statement record](decisions/2026-09-12-relative-perimeter-prerequisites-statement.md), the
[integration record](decisions/2026-09-12-perimeter-interface-integration.md) and the earlier
[audit snapshot](decisions/2026-09-12-status-audit-and-wip-retention.md).

## Conditional-fiber energy comparison

`lem:conditional-fiber-energy-comparison` was proved on 2026-09-11 and is the twenty-second
certificate, `Solutions.LemConditionalFiberEnergyComparison.certificate`. For a law `μ ≪ m` (any
Haar measure), an admissible frame `ρ` and a finite `κ` with `KLS.ConditionalFiber.FiberBound μ ρ κ`
(the literature Poincaré constant of almost every nondegenerate fiber is at most `κ · eVar[T]`), it
packages `energy_le_of_fiberBound` (every `Energy.LocalSlope.Admissible` test has conditional-fiber
energy at most `κ` times its finite local-slope energy, that is `κ ∫‖∇f‖² dμ < ∞`) and
`literatureConstant_le_of_fiberBound` (a form-gap bound `C` on `domain μ ρ` gives
`Poincare.LocalSlope.Intrinsic.constant μ ≤ κ C`). The statement was first written as a `sorry`
skeleton aligned sentence by sentence with the Blueprint, then proved in the same module without
changing any type; the proof stays private to `KLS/ConditionalFiber/EnergyComparison.lean` (isometry
transport of `Poincare.LocalSlope.Holds`, full-affine-support criteria, line-slice slope identity,
disintegration of the Rademacher null set, Tonelli and the frame identity). No shared module changed.
The node is `available` with the used repository and Mathlib sources hashed; the Blueprint lemma
carries four anchors with `\leanok` on statement and proof; the route sidecar claim is `proved`
with Lean evidence. Read
[the statement record](decisions/2026-09-11-conditional-fiber-energy-comparison-statement.md) and
[the proof record](decisions/2026-09-11-conditional-fiber-energy-comparison-proofs.md).

## Log-concave conditional fibers

`cor:conditional-fiber-twelve-bound` was proved on 2026-09-11, registered on 2026-09-12 and is the
twenty-third certificate, `Solutions.CorConditionalFiberTwelveBound.certificate`. For a compact-set
log-concave `μ ≪ m` (any Haar measure) with an admissible frame `ρ` it packages the four steps of
the Blueprint proof: `ae_conditionalFiber_logConcave` (base-law almost every conditional kernel is
a compact-set log-concave law on `ℝ`), `conditionalFiber_fiberBound_four` (`FiberBound μ ρ 4`),
`conditionalFiber_energy_le_four_mul` (`D_{μ,ρ}(f) ≤ 4 ∫‖∇f‖² dμ < ∞` on the literature test
domain) and `conditionalFiber_literatureConstant_le_four_mul` (`C_P^lit(μ) ≤ 4 C` from a form-gap
bound `C`). The Blueprint corollary is restated with the sharp `4`; the literature constant `12` is
the immediate weakening and stays available as the `_of_four` versions.

Three new modules close the gaps recorded with the statement skeleton:
`Probability/Line/BrunnMinkowski.lean` (compact one-dimensional Brunn--Minkowski, its inner-regular
convex-combination form, and Prékopa--Leindler with no boundedness hypothesis),
`Probability/HaarLine.lean` (the linear equivalence `θ^⊥ × ℝ ≅ E` and the Fubini splitting of a
Haar measure along a line) and `KLS/ConditionalFiber/SliceKernel.lean` (the explicit slice kernel,
its disintegration of the joint law, and the almost-everywhere identification with the chosen
conditional kernel), together with `KLS/LogConcave/Line/OfDensity.lean`. The only change to an
existing shared module is that `affineSupport_eq_top_of_absolutelyContinuous` in
`KLS/ConditionalFiber/EnergyComparison.lean` lost its `private` marker; no type changed. The node
is `available` with the used repository and Mathlib sources hashed; the Blueprint corollary carries
five anchors with `\leanok` on statement and proof; the route sidecar claim is `proved` with Lean
evidence, while `q:conditional-fiber-frame` stays `open`. Read
[the statement record](decisions/2026-09-11-conditional-fiber-twelve-bound-statement.md) and
[the proof record](decisions/2026-09-11-conditional-fiber-twelve-bound-proofs.md).

## Cheeger identification, absolutely continuous scope

`cor:absolutely-continuous-relaxation-two-cheeger` was registered on 2026-09-12 and is the
twenty-fourth certificate, `Solutions.CorAbsolutelyContinuousRelaxationTwoCheeger.certificate`. For
a law whose intrinsic law is absolutely continuous with respect to a Haar measure on the direction
space it packages `SmoothGradient.relaxation = LocalSlope.relaxation` for the intrinsic law and
`𝓔^can_μ = 2 Ch_μ` on ambient `L²(μ)`; `KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger`
discharges the hypothesis for every compact-set log-concave law through the certified
`lem:logconcave-intrinsic-absolute-continuity`.

This is the absolutely continuous **scope** of `thm:smooth-gradient-relaxation-two-cheeger`, which
remains open, uncertified and without `\leanok`. The Cheeger energy is the Blueprint's local-slope
convention, fixed by one definition (`Energy.Cheeger.energy := Cheeger.ofLocalSlope`); the
asymptotic-Lipschitz convention is defined separately and its agreement with the local-slope one is
an explicit obligation, not a definitional identification. Registration split the former
work-in-progress module: `Energy/LocalSlope/Relaxation.lean` and `Energy/Cheeger.lean` are
registered and `sorry`-free, and `Energy/WIP/Cheeger.lean` retains only the five open obligations
of the singular case; no registered module depends on any of them, which the build enforces. Read
[the statement record](decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-statement.md),
[the proof record](decisions/2026-09-11-smooth-gradient-relaxation-two-cheeger-proofs.md) and
[the registration record](decisions/2026-09-12-cheeger-absolutely-continuous-registration.md).

## Definition checks

Default-build named checks cover constant admissibility/zero energy in every allowed dimension,
zero-dimensional covariance and the literal inequality for every finite C, local slope of the real
identity equal to one, and ambient identity energy one under a Dirac law. Each has a transitive
axiom guard and is also audited by the runner. The nonzero examples test the energy normalization;
the intrinsic literature constant uses the affine carrier, not the ambient raw identity energy.

Existing raw representative tests in `examples/PoincareFoundation.lean` and Gaussian transfer
checks in `solutions/LemLegacyRelaxedPoincareComparison.lean` remain the reusable coverage for those
contracts. The smooth/locally-Lipschitz comparison is now proved under intrinsic absolute
continuity; a concrete Gaussian literature specialization must still discharge that premise.
No placeholder is added for it. A bare `#check P` only checks
that P is a well-formed expression; acceptance uses proof terms with the expected proposition or
proved named theorems, followed by transitive axiom inspection.

## Pilot and falsification

The first priority is `lem:covariance-test-core-density`, then the smooth/locally-Lipschitz
comparison and selected/literature comparison; all three are now certified. The intrinsic
absolute-continuity input and the stronger Borell density/moment representation are separately
certified. The written arguments are in Blueprint Appendix A and the shared
bridges chapter; the weighted gradient approximation is not supplied by ordinary value-only
smooth density in L². Formalizers must identify or construct that analytic step explicitly.
The pipeline does not require the more general, unresolved Cheeger-energy identification.

Review new statements against the existing Dirac and normal-direction obstructions, zero
dimension, empty products, zero energy, infinite optimal constants, and Gaussian variance
normalization. Numerical tests are counterexample leads, not proofs or assurances of truth.
Formalizer/prover roles may be combined. A coordinator owns task selection and integration;
a reviewer checks scope and evidence; a falsifier checks boundary cases; a researcher handles
the explicit open gates. These are responsibilities, not six required persistent agents.

The approximation input has its own seventh certificate, and the smooth/literature comparison
under intrinsic absolute continuity has the eighth. Intrinsic absolute continuity from
compact-set log-concavity and the general constant equality now have the ninth and tenth.
The full Borell density/moment representation was subsequently certified as the twelfth node.
The original eight ledger claims were unchanged by the ninth and tenth additions; see the
[general proof record](decisions/2026-09-06-general-logconcave-comparison.md),
[approximation acceptance](decisions/2026-09-06-weighted-approximation-acceptance.md) and
[comparison proofs](decisions/2026-09-06-smooth-literature-proofs.md).

## Trust and release boundary

The kernel replay checks local module declarations using already compiled imported environments.
Pinned third-party compiled imports remain trusted; this is not `--fresh`, independent checker
verification, or a clean-source reconstruction. Comparator, an external checker, and isolated
release rebuilding are deferred. Ordinary draft modules may contain placeholders under the
ledger lifecycle; certification and axiom checks reject them in the audited claims' dependencies.

CI uses the same verification runner and uploads evidence as workflow artifacts. Editing its
configuration locally does not run remote CI or publish any source. No successful CI run or
remote publication is claimed by a local receipt.

## 全库命名补充整理（2026-09-08）

全库声明作用域和文件归属已进一步整理：33 个公共短名、12 个模块路径，
881 个公共签名及 1085 项展开后的类型/定义闭包核对一致。完整记录见
[decisions/2026-09-08-library-naming.md](decisions/2026-09-08-library-naming.md)。
最终验收读取 `build/verification/latest.json` 并核对当前源码快照；工作区改动尚未提交。
