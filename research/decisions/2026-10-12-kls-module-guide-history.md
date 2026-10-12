> Historical guide snapshot archived on 2026-10-12 from `formalization/FunctionalInequalities/KLS/README.md`.
> Counts, next steps and proof boundaries below retain their original dates; use the
> [current handoff](../../HANDOFF.md) and [paper register](../progress/LITERATURE.md) for current status.
> Prose is preserved; relative Markdown links are rebased to their original targets.

# KLS module guide

Semantic status recorded on 2026-09-20: **26 registered certificates; the library has only one intentionally retained `sorry`, the KLS conjecture in [Target.lean](../../formalization/FunctionalInequalities/KLS/Target.lean)**. The Cheeger infimum, identification of smooth-gradient relaxation with Cheeger energy, and `C_P^lit(μ) ≤ 4Ψ_KLS(μ)²` are proved. The general higher-dimensional Buser constant π and dimension-free KLS remain open at this stage; the old `Energy/WIP` and `KLS/WIP` directories no longer locate the current gaps. Consult the [progress page](../progress/README.md) and certificate ledger for current progress.

Historical semantic status (2026-09-19, before taking over the Cheeger line): 24 certificates;
**7 direct holes (0/2/5)** in two WIP modules (`WIP/CheegerInfimum.lean` and
`Energy/WIP/Cheeger.lean`). Sharp `Analysis.sard` is proved in `Analysis/Sard/Sharp.lean`
(the Morse route, with byte-identical `pp.all` signatures); `WIP/AnalyticPrerequisites.lean` was deleted.

Historical semantic status (2026-09-16): 24 certificates; 8 direct holes (1/2/5), confined to
three WIP modules. The recovery sequence `KLS.RelativePerimeter.exists_smooth_recovery_sequence`
is proved and its infrastructure is available. Blueprint links and completion markers were
added for existing proofs, without a new ledger certificate. Cheeger-infimum infrastructure
remains missing: specifically, the integrated superlevel bound and reverse comparison.
Coarea, smooth Sard, Gauss–Green, and recovery sequences are no longer missing prerequisites.
The rounds below retain their contemporary status; the status at this stage is recorded here
and in the [semantic-alignment record](2026-09-16-semantic-alignment.md).

Historical progress (2026-09-16, L13 round): **weighted coarea extended to locally Lipschitz functions**.
[`Geometry/Coarea/LocallyLipschitz.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/LocallyLipschitz.lean) proves
`KLS.coarea_of_locallyLipschitz`: assuming only `LocallyLipschitz u`, it gives the same weighted
equality and slice `AEMeasurable`, without a Lipschitz constant, C¹, boundedness, finite volume,
integrability, or SFinite. It **generalizes both L11 and L12**: neither original statement nor
proof changes, and neither is restated using it. Both `LipschitzWith K u` and `ContDiff ℝ 1 u`
imply `LocallyLipschitz u`. The generalization is **strict**: the client proves that
`x ↦ x² + ‖x‖` is locally Lipschitz, not globally Lipschitz for any constant, and not differentiable
at 0, so neither original theorem applies. The proof reduces to L12 on half-open annuli:
McShane extension on closed balls supplies globally Lipschitz representatives; each piece lies
inside an **open** ball, giving pointwise gradient equality and identical level slices; countable
disjoint additivity assembles the result. **No holes were migrated in this round**: direct holes
remain **8 (1/2/5)**, certificates **24**, and perimeter infrastructure **missing**.
See `research/audits/LocallyLipschitzCoareaAudit.lean` (10 standard-only reports, no WIP imports)
and the [L13 decision](2026-09-16-locally-lipschitz-coarea.md).

**The log-concave Cheeger–Buser line (alignment of the isoperimetric constants through two-sided
comparison with the Poincaré constant, including the two remaining holes in
`WIP/CheegerInfimum.lean`) was assigned to Haocheng Wang on 2026-09-16 and deliberately left untouched in this round.**

Previous round (2026-09-16, T2 migration): **the last original coarea hole was closed**.
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` moved from
`WIP/AnalyticPrerequisites.lean` to the end of the hole-free
[`Geometry/Coarea/Lipschitz.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Lipschitz.lean). Its `pp.all` signature was
**machine-checked byte for byte**: the same universe parameter `u`, six instances in the same
order (including the `CompleteSpace V` actually used by `gradient` in the statement), binders,
hypothesis names, and conclusion. It is proved by **L12** `KLS.coarea_of_lipschitz` in the same
file with `S = Set.univ`, without a compatibility alias, a repeated coarea proof, or added
C¹/positive-dimension/finite-volume/integrability/SFinite assumptions. **No new theorem was
proved in this round.** Direct holes decreased **9 (2/2/5) → 8 (1/2/5)**.
`WIP/AnalyticPrerequisites.lean` retains only sharp `C^(finrank)` `Analysis.sard`; its statement
and proof and those of `Analysis.ae_forall_fderiv_ne_zero` are unchanged. All three original
targets T1/T2/T3 are now connected. Certificates remain **24** and perimeter infrastructure
**missing**. See `research/audits/LipschitzCoareaMigrationAudit.lean` and the
[migration decision](2026-09-16-t2-coarea-migration.md).

Previous round (2026-09-16, L12 completion): `Analysis/Lipschitz/Jet.lean` proves **L6a** compact
jet extraction; `Analysis/Lipschitz/C1Pieces.lean` proves **L7** exact C¹ pieces; and
`Geometry/Coarea/Lipschitz.lean` proves **L12** weighted Lipschitz coarea and slice AEMeasurable,
without C¹, positive dimension, boundedness, finite volume, or finite weights. New client audits
prove the original L6a/L7/L12/T2 statements; all 15 axiom reports contain only standard axioms.
Every old Lean file remained byte-identical in that round; direct holes stayed **9 (2/2/5)**.

Historical round (2026-09-16, L6 completion):
[`Analysis/Whitney/Construction.lean`](../../formalization/FunctionalInequalities/Analysis/Whitney/Construction.lean) proves global C¹
extension of first-order jets on compact sets, preserving exact values and ambient derivatives,
including empty sets, sparse sets, and dimension zero. Quantitative covers, a smooth partition
of unity, and both uniform error estimates are constructed. A new client proves all quantifiers
of the original L6; 13 axiom reports are standard-only. Next: **L6a compact jet extraction →
L7 exact C¹ pieces → L12 Lipschitz coarea**. Direct holes **9 (2/2/5)**, certificates **24**,
and perimeter infrastructure **missing** are unchanged.

The following are historical snapshots; “unproved” and “next” refer to the respective round.

Historical round (2026-09-16, L6 boundary gluing): `Analysis/WhitneyExtension.lean` proves that
a C¹ candidate on the complement with quantitative jet estimates glues to a global C¹ extension,
preserving exact values and derivatives on the compact set. **No candidate satisfying the
estimates has yet been constructed, so general existence in L6 remains unproved.** Next are
Whitney covers, partitions of unity with derivative control, and affine-jet summation estimates.
The new client has 13 standard-only axiom reports. Direct holes **9 (2/2/5)**, certificates
**24**, and perimeter infrastructure **missing** are unchanged.

Previous round (2026-09-16, FirstOrderJet closeout): the uniform remainder condition for a
first-order jet on a compact set is proved **necessary** for global C¹ realization
(`Analysis.uniform_jet_remainder_of_contDiff`). **L6 extension existence remains unproved**
and is next; L6a/L7/Lipschitz coarea remain incomplete. Direct holes **9 (2/2/5)**,
certificates **24**, perimeter infrastructure **missing**.

Previous round (2026-09-16, C¹ coarea migration): **the second original coarea hole was closed**.
`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` moved from
`WIP/CheegerInfimum.lean` to hole-free
[`Geometry/Coarea/Isoperimetry.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Isoperimetry.lean), with a **byte-identical**
`pp.all` signature (machine `diff`, including unused `CompleteSpace`, `SecondCountableTopology`,
and hypothesis name `hK`). The proof uses the previous L11 with `S = univ` and **no longer
depends on `sorryAx`**. Direct holes **10 (2/3/5) → 9 (2/2/5)**; `WIP/CheegerInfimum.lean`
retains only two Cheeger comparisons. This round proves **no new theorem** and **does not**
prove Lipschitz coarea (`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` has no
`C¹` assumption and remains a direct hole requiring L12 → L7 → L6).
See the [migration decision](2026-09-16-isoperimetry-coarea-migration.md).

Previous round (2026-09-16, C¹ coarea): **L11 of the weighted-coarea route is proved**:
for **any** `C¹` real function, measurable set, and measurable `ℝ≥0∞` weight, it gives weighted
coarea and `AEMeasurable` slice integrals (`coarea_of_contDiff` in
[`Geometry/Coarea/Smooth.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Smooth.lean)). No Lipschitz, boundedness, or
compact-support condition on `u`; no boundedness or finite volume for `S`; `g` may be identically
`⊤`. **No derivative nondegeneracy is required** (the critical set may be the whole space).
L9 and L10 fit together here, and both are necessary: the critical set is closed and its
complement open, so L9 handles `S ∩ R`; the critical contribution on the left vanishes because
`gradient u = 0`; on the right L10 gives a.e. null critical slices, and the same a.e. equality
transfers L9's `AEMeasurable` to the full slice function. **Target T3 follows**, exactly the
statement of the direct hole `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
(which already assumes `ContDiff ℝ 1 u`; its `LipschitzWith` premise is unused).
**WIP is untouched this round**, so direct holes remain **10 (2/3/5)**. Migration can reduce
`WIP/CheegerInfimum.lean` from 3 holes to 2 and the total to **9**, in a separate round as usual.
**The Lipschitz case remains unproved**, requiring L12 → L7 → L6 closed-set Whitney extension,
all still unproved. See the [C¹ coarea decision](2026-09-16-smooth-coarea.md).

Previous round (2026-09-15, regular coarea): **both components of L9 are fully proved**.
`coarea_of_contDiffOn_of_fderiv_ne_zero` in
[`Geometry/Coarea/Regular.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Regular.lean) gives weighted C¹ coarea on
regular open domains and `AEMeasurable` slice integrals, without global C¹/Lipschitz,
boundedness, finite volume, integrability, positive dimension, or SFinite. Jointly parameterized
C¹ implicit functions, volume-preserving orthogonal splitting, fiberwise Jacobian substitution,
graph area, and disjoint Borel gluing are proved.
[`Geometry/Slice/OpenMeasurable.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Slice/OpenMeasurable.lean) handles local C¹
measurability independently. The results and clients have 29 axiom checks using only the three
standard axioms; 15 existing clients were rerun successfully. Existing Lean files and WIP are
unchanged. Direct holes remain **2/3/5, total 10**, certificates **24**, perimeter infrastructure
**missing**. L11/L12, L6/L6a/L7, both original coarea-equality holes, sharp Sard, the sharp
Eilenberg constant, and reverse Cheeger comparison/equality remain unproved.
See the [L9 decision](2026-09-15-regular-coarea.md).

The following historical rounds retain their contemporary “unproved” boundaries.

Previous round (2026-09-15, open-domain graph area): **L8 of the weighted-coarea route is proved**,
extending weighted graph-area substitution from globally `C¹` parameter functions to functions
`C¹` only on an open set `O` (`setLIntegral_image_graphMap_of_contDiffOn` in
`Analysis/OpenGraphIntegral.lean`). A `ContDiffOn` function on an open set generally **cannot**
extend globally as `C¹` (`x ↦ x⁻¹` on `(0,∞)`), so countable localization is required: at each
point choose a ball on which it agrees with a globally `C¹` function (multiplication by
`ContDiffBump`), use second countability for a countable subcover, partition with `disjointed`,
and use injectivity of `graphMap` for disjoint images and countable additivity on both sides.
This is localization **inside an open set**, **not** L6 closed-set Whitney extension (still
unproved). L8 gives **graph** area, not coarea: L9 still needs a level-parameterized C¹ implicit
family and equidimensional Jacobian substitution.
See the [open-domain graph-area decision](2026-09-15-open-graph-area.md).

Previous round (critical slices): **L10 of the weighted-coarea route is proved**. For a `C¹`
real function, the critical set `{x | fderiv ℝ u x = 0}` meets almost every level set in a
`surfaceMeasure`-null set ([`Geometry/Slice/Critical.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Slice/Critical.lean)).
This is **L1's first actual downstream consumer**: derivatives vanish on the critical set,
and the approximating linear maps in Mathlib's piecewise lemma are derivative values, hence
zero. Approximation becomes an `ε`-Lipschitz estimate. Apply L1 to the pieces in a ball,
sum, let `ε → 0`, and take the countable union over radii. **This is not Sard's theorem and
does not imply it**: Sard concerns nullity of critical **values** (generally requiring
`C^(finrank)`, still the direct hole `Analysis.sard`); L10 concerns codimension-one nullity of
the **critical part** of almost every level set and only requires `C¹`.
The client `constant_exceptional_level` uses a constant function to show that “a.e.” cannot
be strengthened to “everywhere.” No Lipschitz, boundedness, or compact-support assumption on
`u`; the critical set is automatically closed, so no measurability premise; dimension zero is
covered. Direct holes remain **10 (2/3/5)**. L8/L9/L11/L12 and weighted coarea equality remain
unproved. See the [critical-slice decision](2026-09-15-critical-slice.md).

Previous round (level-set measurability migration): **the first original coarea hole was closed**.
`Analysis.aemeasurable_lintegral_levelSet` moved from `WIP/AnalyticPrerequisites.lean` to
hole-free [`Geometry/Slice/Measurable.lean`](../../formalization/FunctionalInequalities/KLS/Geometry/Slice/Measurable.lean), with a
**byte-identical** `pp.all` signature (machine `diff`). It is proved by the previous L5 and
**no longer depends on `sorryAx`**. Direct holes **11 (3/3/5) → 10 (2/3/5)**; certificates
remain 24 and perimeter infrastructure missing. This round has **no new theorem**, only
migration and connection; weighted coarea equality is **not** proved.
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` and sharp `Analysis.sard` remain
direct holes. See the [migration decision](2026-09-15-levelset-measurable-migration.md).

Previous round (Borel slices and measurable weights): **L4 and L5 of the weighted-coarea route
are proved**, together with the **full statement of the first original target T1**.
L4 (`aemeasurable_surfaceMeasure_inter_levelSet`) combines three proved results: inner
regularity decomposes measurable `S` into an increasing compact sequence and a volume-null
remainder; use **L3** on compact pieces, continuity from below for the supremum, and **L2**
on the remainder. L5 (`aemeasurable_setLIntegral_inter_levelSet`) uses simple-function
approximation, expressing each simple-weight slice integral as a **finite sum** of slice
measures of measurable `S ∩ s ⁻¹' {c}`, **without parameter-integral theorems requiring SFinite**.
Both drop `[CompleteSpace V]` and weaken global Lipschitz continuity to continuity plus
Lipschitz continuity **only on `S`**. No boundedness, nonemptiness, or finite volume for `S`;
`g` may be unbounded, nonintegrable, or identically `⊤`. L4/L5 give **measurability, not equality**;
weighted coarea itself (L6–L12, targets T2/T3) is untouched.
See the [Borel-slice decision](2026-09-15-borel-slice-measurable.md).

Previous round (compact-slice measurability): **L3 of the weighted-coarea route is proved**.
For **compact** `S` and merely continuous `u`, `t ↦ surfaceMeasure V (S ∩ {u = t})` is Borel
measurable (`measurable_surfaceMeasure_inter_levelSet` in `../Analysis/Hausdorff/SurfaceSlicing.lean`,
using the new Mathlib-only `Analysis/Hausdorff/Content.lean`). L3 **does not follow from L1**,
which gives measurability only of a constructed majorant. The proof has two layers:
**open-cover** content at a fixed scale is upper semicontinuous in the level (compact `S \ U`
keeps `u` a positive distance from that level), and its scale limit is still `μH[d]` (thicken
each piece, absorb diameter growth in the slack and cost growth in a summable positive sequence).
At fixed scale `openCoverCost` is generally strictly greater than `coverCost`, so equality
requires the scale limit; **no upper semicontinuity of `μH[d]` itself is claimed** (it generally
fails). **L4 (Borel sets) and L5 (measurable weights) remain gaps**: L3 says nothing about general
Borel sets, and the first original coarea hole is stated for `univ`, so compact sets do not fill it.
See the [compact-slice decision](2026-09-15-compact-slice-measurable.md).

Previous round (Eilenberg upper bound): **L1 of the weighted-coarea route is proved**, with an
explicit positive constant; the previous **L2** becomes its null-set case with the statement
unchanged. If `u` is Lipschitz only on `S`, the slice function
`t ↦ surfaceMeasure V (S ∩ {u = t})` has a **measurable** majorant `F` satisfying
`∫⁻ F ≤ eilenbergConstant V · K · volume S`, where
`eilenbergConstant V = 4 ω_{n-1}/ω_n > 0` (`../Analysis/Hausdorff/SurfaceSlicing.lean`).
The underlying Mathlib-only `Analysis.exists_measurable_majorant`
(`Analysis/Hausdorff/Slicing.lean`) applies to any `EMetricSpace`, without dimension or ambient
measure, with constant `2` under Mathlib's diameter normalization. Sharpness is not claimed;
the client computes `2` on the line and `4` in dimension zero. No measurability, boundedness,
nonemptiness, or finite volume for `S`; no global Lipschitz continuity, differentiability, or
measurability for `u`. `K = 0` and `volume S = ⊤` are explicit branches; neither positive
dimension nor `[CompleteSpace V]` is required. Measurability holds **only** for the constructed
majorant: measurability of the slice function itself (L3–L5) remains a gap. All three original
coarea holes, sharp Sard, reverse comparison, the product superlevel bound, and equality of
the Cheeger constants remain unproved. Certificates 24; perimeter infrastructure missing
(direct holes 3/3/5 in that round, later reduced by migration to 2/3/5).
See the [Eilenberg-bound decision](2026-09-15-eilenberg-majorant.md),
[null-slicing decision](2026-09-15-null-slicing.md), and
[weighted-coarea route](2026-09-15-weighted-coarea-route.md).

This directory organizes definitions, log-concave tools, and concrete route objects for KLS.
Mathematical sources are documented at the start of each Lean module; proof status is recorded
jointly by the [ledger](../a-series/ledger.yaml) and current statements and proofs.

## Entry points

| File or directory | Responsibility and scope |
| --- | --- |
| [Definitions.lean](../../formalization/FunctionalInequalities/KLS/Definitions.lean) | Compact-set log-concavity, local slope, literature test domain and constant; shared definitions |
| [Statement.lean](../../formalization/FunctionalInequalities/KLS/Statement.lean) | Covariance-normalized KLS conjecture proposition; no KLS proof |
| [Target.lean](../../formalization/FunctionalInequalities/KLS/Target.lean) | `theorem kls : Conjecture := by sorry`: the KLS assertion itself, the repository's only intentionally retained direct hole; imported only by the aggregate root, outside every certificate closure and Blueprint `\lean` tag (2026-09-19; see `research/decisions/2026-09-19-kls-target-theorem.md`) |
| [LogConcave/](../../formalization/FunctionalInequalities/KLS/LogConcave/README.md) | Log-concave transport, compact/Borel equivalence, intrinsic absolute continuity, Borell density representation, the log-concave contract and closed form for the affine covariance constant, log-concavity under ambient translation and barycenters, affine/isotropic KLS reduction, and the one-dimensional `4·Var` Poincaré bound on the real line (`LogConcave/Line/`, retaining Bobkov's `12·Var` as a corollary) |
| [LocalSlope/Gradient.lean](../../formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean) | Relation between local slope and gradient, and identification of energies and test domains under absolute continuity; proved |
| [Isotropic.lean](../../formalization/FunctionalInequalities/KLS/Isotropic.lean) | Definitions of finite second moments, zero mean, and identity covariance; whitening in `Probability/Covariance/Whitening.lean`, affine/isotropic reduction in `LogConcave/Isotropic.lean` |
| [Isoperimetry.lean](../../formalization/FunctionalInequalities/KLS/Isoperimetry.lean) | Boundary content, isoperimetric constant, and inverse scale on the affine carrier; no Cheeger comparison |
| [ConditionalFiber/Basic.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber/Basic.lean) | Conditional-fiber energy construction and six proved well-definedness contracts; no closedness, Markov property, or frame bound in this file |
| [ConditionalFiber/Closed.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean) | Two-point jump representation, swap invariance of the two-point measure, Lipschitz bound `d·L²`, dense domain, lower semicontinuity, and Markov property, combined into `Energy.Dirichlet`; any Borel law and direction law, without gradient-energy comparison or a frame bound |
| [ConditionalFiber/EnergyComparison.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean) | Under the fiber Poincaré input `FiberBound μ ρ κ`, comparison with local-slope (gradient) energy `energy_le_of_fiberBound` (finite `D_{μ,ρ}(f) ≤ κ·∫‖∇f‖²`) and transfer of a form-gap bound `C` to `C_P^lit(μ) ≤ κC` via `literatureConstant_le_of_fiberBound`; requires `μ ≪ Haar` and an admissible frame, leaves `κ` unspecified, and supplies neither fiber log-concavity nor a frame bound |
| [ConditionalFiber/SliceKernel.lean](../../formalization/FunctionalInequalities/KLS/ConditionalFiber/SliceKernel.lean) | Explicit line-slice kernel `sliceKernel` for a Haar density `p` (density `t ↦ p(z+tθ)/Z(θ,z)`, Dirac law at bad base points); `compProd_baseLaw_sliceKernel` (`baseLaw ⊗ₘ sliceKernel = jointLaw`) and `ae_sliceKernel_eq` (a.e. equality with the selected conditional kernel); only a Haar density, no log-concavity assumption |
| [LogConcave/ConditionalFiber.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) | A.e. log-concavity of conditional fibers of full-dimensional log-concave laws, `ae_conditionalFiber_logConcave`, hence `FiberBound μ ρ 4`, `D_{μ,ρ}(f) ≤ 4·∫‖∇f‖²`, and `C_P^lit(μ) ≤ 4C` (Blueprint versions with `12` retained with `_of_four` suffixes); no frame bound, and `q:conditional-fiber-frame` remains open |
| [Geometry/SmoothDomain/Homothety.lean](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/Homothety.lean) | Hole-free weighted substitution: pushforward of normalized surfaceMeasure under inverse homothety and weighted lintegral substitution on arbitrary measurable sets and frontiers, without finiteness of the measure |
| [LogConcave/Density/Bounds.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/Density/Bounds.lean) | Hole-free density bounds: global upper bound and convex-combination density comparison migrated from WIP; the interior of the positivity set lies in the measure-support interior, giving zero contribution outside Ω; public lower-bound ball `exists_ball_le` and absolute continuity `absolutelyContinuous` |
| [Geometry/Perimeter/Relative.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/Relative.lean) | Hole-free relative-perimeter applications: perimeter definition, L¹ convergence of dilated indicators, kernel-average density bound, and proved `lintegral_enorm_gradient_mollified_homothety_le`; no bounded domain, finite total boundary measure, or finite relative perimeter required; dimension zero covered |
| [Geometry/Perimeter/Recovery.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/Recovery.lean) | Hole-free recovery: exact locally constant mollification formula `mollifiedIndicator_eq_indicator_of_const`, L¹(ν) selection at vanishing radius `exists_bump_lintegral_enorm_mollifiedIndicator_sub_lt`, and proved `RelativePerimeter.exists_smooth_recovery_sequence`; each term is `C^∞`, Lipschitz, and `[0,1]`-valued; no bounded domain/boundary/carrier or uniform Lipschitz constant; dimension zero and zero perimeter covered |
| [Geometry/Cheeger/MinkowskiContent.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/MinkowskiContent.lean) | Hole-free coordinate-space content (empty local import closure, Mathlib only): `minkowskiContent`, `measure_closure_eq_of_minkowskiContent_ne_top`, local supremum `ballSup`, its Lipschitz transfer and nearby witness `thickening_superlevel_subset`, and proved Minkowski coarea inequality `lintegral_minkowskiContent_superlevel_le`; any probability law, including singular and atomic laws, with only C¹ and global Lipschitz continuity for `u`; no density, absolute continuity, bounded range, or positive dimension |
| [Geometry/Cheeger/MinkowskiConstant.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/MinkowskiConstant.lean) | Hole-free Cheeger infimum (local import closure only the hole-free `Geometry/Cheeger/MinkowskiContent.lean`): unchanged WIP migrations `minkowskiConstant` and `minkowskiConstant_eq_top_of_subsingleton` (byte-identical `pp.all` signatures); product form `minkowskiConstant_mul_min_le` (zero/full mass handled by `⊤ * 0 = 0`, without substitution into the infimum); a.e. equality of strict/nonstrict superlevel masses `ae_measure_superlevel_lt_eq_le` (any `SFinite` measure and measurable `u`); balance measurability `measurable_min_measure_superlevel` (any `u`); proved `minkowskiConstant_mul_lintegral_min_superlevel_le`; any probability law, including singular and atomic laws, without density, nonatomicity, positive dimension, or finite `h_M` |
| [Geometry/Cheeger/DistanceCutoff.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/DistanceCutoff.lean) | Hole-free distance cutoffs (**empty local import closure**, Mathlib only): unchanged WIP migrations `distanceCutoff`, `distanceCutoff_mem_Icc`, `lipschitzWith_distanceCutoff`, two boundary-value lemmas, and L¹(ν) convergence `tendsto_distanceCutoff_indicator` (byte-identical `pp.all` signatures); proved gradient-integral estimate `lintegral_enorm_gradient_distanceCutoff_le`; arbitrary `B` (no nonempty, measurable, closed, or bounded premise), retaining `ν (closure B)` on the right and unused `m`/Haar/`hac` parameters. The result is **pointwise**: global extrema on the two constant-value sets allow `IsLocalMax/IsLocalMin.fderiv_eq_zero` without differentiability, so no Rademacher theorem, Lebesgue density theorem, or general level-set gradient lemma |
| [Geometry/Cheeger/Equality.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Equality.lean) | Hole-free equality layer (2026-09-19): seven public declarations migrated unchanged from deleted `WIP/CheegerInfimum.lean` (`exists_smooth_approximation_lipschitz`, two former holes, `minkowskiConstant_eq_smoothConstant`, three intrinsic transports; byte-identical `pp.all`), plus `smoothConstant_mul_min_le`, `relativePerimeter_le_lintegral_levelSet`, `lintegral_enorm_gradient_eq_lintegral_levelSet_density`, `lintegral_enorm_distanceCutoff_sub_indicator_le`, `min_measure_le_lintegral_min_superlevel_add`; no `sorryAx` dependency |
| [Geometry/Cheeger/Inequality.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Inequality.lean) | Hole-free Cheeger inequality layer (2026-09-19): L¹ Cheeger `minkowskiConstant_mul_lintegral_le`, positive-part-square bound, `h_M² Var ≤ 4∫‖∇g‖²` for bounded C¹ Lipschitz and all admissible tests, `smoothTest_constant_le` (`C_P^smooth(ν) ≤ 4/h_M²` for arbitrary Borel laws), `LogConcave.literatureConstant_le_four_mul_inverseScale_sq` (log-concave laws); Buser direction unproved at this stage |
| [Geometry/Cheeger/Median.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Median.lean) | Median existence `exists_median` (left/right continuity of the distribution function) |
| [Geometry/Cheeger/Infimum.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Infimum.lean) | Hole-free one-sided comparison (**no WIP**): unchanged WIP migrations `smoothConstant`, `smoothConstant_eq_top_of_subsingleton`, `lintegral_measure_symmDiff_superlevel`, `min_measure_le_add_measure_symmDiff`, `tendsto_lintegral_min_superlevel` (byte-identical `pp.all` signatures), and proved `minkowskiConstant_le_smoothConstant`; covers dimension zero, no eligible smooth domain, a domain of relative perimeter `⊤`, and constant `⊤`; no bounded support/domain, finite total boundary measure, finite constant, or finite relative perimeter. **Only one direction here**; see `Geometry/Cheeger/Equality.lean` for the reverse and equality |
| [Geometry/SmoothDomain/Basic.lean](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/Basic.lean) | Hole-free foundations: smooth-domain structure, frontier interface, `empty`/`univ`/homothety, local boundary finiteness, Haar nullity, and total-boundary Hausdorff scaling; regular-superlevel constructors `ofSuperlevel` and `ofSuperlevel_carrier` added 2026-09-14: the **strict** superlevel `{x | t < u x}` of a C∞ function is a smooth domain when `fderiv ℝ u` is nonzero on the **`frontier`**, using defining function `φ = t - u` with the negative-sublevel convention and neighborhood `{y | fderiv ℝ u y ≠ 0}`. No regularity of the entire level, globally nonzero derivative, positive dimension, or boundedness; empty frontier, empty/full carrier, and dimension zero are naturally covered |
| [Geometry/Perimeter/Mollification.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/Mollification.lean) | Hole-free mollification interface: `mollifiedIndicator`, local integrability of indicators, convolution representation, smoothness, Lipschitz continuity, and `[0,1]` range |
| [Geometry/Perimeter/MollifiedBoundary.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Perimeter/MollifiedBoundary.lean) | Hole-free consequences: `gradient_mollifiedIndicator_eq` and proved `enorm_gradient_mollified_le`; integrable vector integral, nonnegative kernel, unit outward normal; no bounded domain or finite total boundary measure |
| [Geometry/SmoothDomain/BoundaryChart.lean](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/BoundaryChart.lean) | Application layer (no `sorry`): outward normal `outwardNormal` and `outwardNormal_eq`, `norm_outwardNormal`, `continuousOn_outwardNormal`, `measurable_outwardNormal`, migrated from `WIP/AnalyticPrerequisites.lean` with names/statements unchanged; tangent hyperplane `tangentSpace`/`tangentEmbedding`/`tangentCoord`, orthogonal splitting `isGraphSplitting_tangent`, `finrank_tangentSpace`; local chart `BoundaryChart` and `exists_boundaryChart` (inside the cylinder the boundary is exactly the graph and the domain exactly its subgraph; outward normal along it is `(ι(-∇g)+ν)/√(1+‖∇g‖²)`); area equality `BoundaryChart.surfaceMeasure_image`. Directly imports hole-free `Geometry/SmoothDomain/Basic.lean`, no WIP dependency |
| [Geometry/SmoothDomain/LocalGaussGreen.lean](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/LocalGaussGreen.lean) | Application layer (no `sorry`): chart-local Gauss–Green `BoundaryChart.integral_divergence_eq_integral_inner_outwardNormal`, giving `∫_U div F = ∫_{∂U} ⟪F, ν⟫ ∂surfaceMeasure` for compactly supported C¹ vector fields with `tsupport F ⊆ C.cylinder`; localization lemmas `integral_divergence_carrier` (volume integral reduces to the global subgraph; both `F` and `divergence F` vanish outside the cylinder) and `integral_inner_outwardNormal_frontier` (flux reduces to one graph patch; Jacobian and unit-normal denominator cancel pointwise). **Not** a global theorem for arbitrary compactly supported fields; global gluing is in `Geometry/SmoothDomain/GaussGreen.lean`. No finite total boundary measure |
| [Geometry/SmoothDomain/GaussGreen.lean](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/GaussGreen.lean) | Application layer (no `sorry`): **global** Gauss–Green `SmoothDomain.integral_divergence_eq_integral_inner_outwardNormal`, giving `∫_U div F = ∫_{∂U} ⟪F, ν⟫ ∂surfaceMeasure` for arbitrary compactly supported C¹ fields, without bounded domain, finite total boundary measure, higher smoothness of `F`, or nontrivial `V`; local blocks `…_of_tsupport_subset_carrier` (interior), `…_of_tsupport_subset_compl_closure` (exterior), and chart blocks (via `LocalGaussGreen`); `isLocallyFiniteMeasure_surfaceMeasure_frontier` and `integrableOn_smul_outwardNormal` migrated unchanged from `WIP/AnalyticPrerequisites.lean`, plus `norm_outwardNormal_le_one` and `integrableOn_inner_outwardNormal` for exchanging finite sums |
| [../Analysis/Hausdorff/SurfaceSlicing.lean](../../formalization/FunctionalInequalities/Analysis/Hausdorff/SurfaceSlicing.lean) | L1–L5: explicit nonsharp Eilenberg upper bound, null-set slicing, Borel measurability of compact slices of continuous functions, and a.e. measurability of slices and measurable ENNReal-weight integrals for continuous functions Lipschitz on a measurable set. No finite volume, finite weight, positive dimension, or SFinite surfaceMeasure premise. Dimension zero uses ℋ⁰, not the zero measure. Only measurability and upper bounds here; later modules prove coarea equality |
| [../Analysis/Hausdorff/Measure.lean](../../formalization/FunctionalInequalities/Analysis/Hausdorff/Measure.lean) | Foundational definitions (no `sorry`): unit-ball volume `unitBallVolume`, normalized Hausdorff measure `hausdorffNormalized`, and surface measure `surfaceMeasure`; no theorems; shared by `Analysis/Hausdorff/Volume.lean` and perimeter modules. The normalized-volume identity is also in `Volume.lean` |
| [Geometry/SmoothDomain/RegularSuperlevel.lean](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/RegularSuperlevel.lean) | Hole-free regular-superlevel layer: `SmoothDomain.frontier_superlevel_subset` and `SmoothDomain.ae_exists_superlevel` migrated from `WIP/CheegerInfimum.lean` with byte-identical `pp.all` signatures. The latter now follows from **proved** smooth Sard `Analysis.sard_smooth` via `Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top` and **no longer inherits `sorryAx`**; it does not use sharp `C^(finrank)` `Analysis.sard`. `Geometry/SmoothDomain/Basic.lean` deliberately stays independent of Sard, so packaging belongs above it |
| [Geometry/Coarea/Isoperimetry.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Isoperimetry.lean) | Hole-free C¹ coarea delivery: `Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` migrated from `WIP/CheegerInfimum.lean` (byte-identical `pp.all`, machine `diff`), now proved by L11 `coarea_of_contDiff` with `S = univ`, **without `sorryAx`**. Unused `hK`, `CompleteSpace`, and `SecondCountableTopology` are retained to preserve the interface. **No** Lipschitz case |
| [Geometry/Coarea/Smooth.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Smooth.lean) | Hole-free C¹ coarea: `isOpen_regular` and `coarea_of_contDiff` (L11), weighted equality and slice `AEMeasurable` for arbitrary C¹ `u`, measurable `S`, and measurable `ℝ≥0∞` weight; no Lipschitz, boundedness, or finite-volume requirement; `g` may be identically `⊤` and the critical set the whole space. Assembles L9 (regular open domains) and L10 (null critical slices), both necessary. **Target T3 is the `S = univ` case**; **no** Lipschitz case (requires L12/L7/L6) |
| [Geometry/Slice/Critical.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Slice/Critical.lean) | Hole-free critical slices: `isClosed_critical`, `exists_lipschitzOnWith_critical_cover` (zero derivative on the critical set turns Mathlib's piecewise approximation into an `ε`-Lipschitz estimate on disjoint measurable pieces), and `ae_surfaceMeasure_critical_inter_levelSet_eq_zero` (L10). **L1's first downstream consumer**; no Lipschitz, boundedness, or compact support for `u`; dimension zero covered. **Not Sard**: no assertion about critical **values** |
| [Geometry/Slice/Measurable.lean](../../formalization/FunctionalInequalities/KLS/Geometry/Slice/Measurable.lean) | Hole-free level-set measurability: `Analysis.aemeasurable_lintegral_levelSet` migrated from `WIP/AnalyticPrerequisites.lean` (byte-identical `pp.all`, machine `diff`), now proved by L5 `KLS.aemeasurable_setLIntegral_inter_levelSet` with `S = univ`, **without `sorryAx`**. Retains namespace `Analysis` to preserve the public name; placed in `KLS/Geometry/` because its statement uses `KLS.surfaceMeasure`. **No** weighted coarea equality |
| (`WIP/` no longer exists) | On 2026-09-19, deleted `AnalyticPrerequisites.lean` (sharp Sard proved and moved to `Analysis/Sard/Sharp.lean`) and `CheegerInfimum.lean` (two holes proved; seven declarations moved to `Geometry/Cheeger/Equality.lean`). Historical description: `CheegerInfimum.lean` had two direct holes, the integrated superlevel bound and reverse comparison; equality and intrinsic corollaries inherited `sorryAx`. Original T1/T2/T3 all moved to hole-free geometry modules; these WIP files were outside the library-root aggregate and certificate import closures |

The following counts predate completion on 2026-09-19 and do not describe current source:
the two KLS WIP files had 3 direct `sorry`s, plus 5 in `Energy/WIP/Cheeger.lean`, for a total of 8.
Earlier rounds connected and proved interfaces for three existing mathematical inputs
(Hausdorff normalization, local boundary finiteness, and smooth Lipschitz approximation),
proved the codimension-one area formula (`Analysis/Graph/Area.lean`), and reduced scalar
Gauss–Green to its vector form.

### Historical construction records

These rounds retain their contemporary proof boundaries. Hole counts, unproved claims, and
pending migrations do not describe current status; consult the page opening and file table.

A round on 2026-09-13 proved local `C^∞` boundary graphs, domain-side identification, and the
outward-normal formula, and connected the area formula to `surfaceMeasure`
(`Analysis/ImplicitGraph.lean` and `Geometry/BoundaryChart.lean`, both without `sorry`).
A later round that day proved divergence on smooth subgraphs and weighted boundary-integral
substitution (`Analysis/Graph/Divergence.lean`, `Analysis/GraphIntegral.lean`), then connected
charts to **chart-local** Gauss–Green (`Geometry/LocalGaussGreen.lean`, all without `sorry`).
A third round used finite smooth partitions of unity (`Analysis/PartitionOfUnity.lean`) to
assemble chart, interior, and exterior blocks into **global** vector Gauss–Green
(`Geometry/GaussGreen.lean`, no `sorry`, only the three standard axioms), closing the scalar
form and mollified-indicator gradient formula. This round further proved the pointwise
mollified-gradient norm bound and removed all imports from geometry foundations to WIP.
The scalar form moved to `Geometry/GaussGreen.lean`; mollification consequences are in
`Geometry/MollifiedBoundary.lean`. The dilated integral estimate and smooth recovery sequence
were then closed, and `WIP/RelativePerimeter.lean` deleted. A preceding round proved Minkowski
coarea and moved `minkowskiContent` to hole-free `Geometry/MinkowskiContent.lean` (empty local
import closure); another proved the product coarea bound
`minkowskiConstant_mul_lintegral_min_superlevel_le` and moved `minkowskiConstant` to hole-free
`Geometry/MinkowskiConstant.lean`; another proved the **one-sided** comparison
`minkowskiConstant_le_smoothConstant` and moved `smoothConstant` and layer-integral helpers to
hole-free `Geometry/Cheeger/Infimum.lean`. This round proved the distance-cutoff gradient
integral estimate `lintegral_enorm_gradient_distanceCutoff_le` and moved all cutoff foundations
to hole-free `Geometry/DistanceCutoff.lean`, with no local dependencies.
The low-dimensional base case `Analysis.sard_of_finrank_le_one` was proved without holes in
`Analysis/Sard.lean`, using only standard axioms and covering zero-dimensional C⁰ and
one-dimensional C¹ on general real normed spaces, without a domain measure.
`C^∞` Sard was proved in `Analysis/SmoothSard.lean`, allowing `ae_exists_superlevel` to leave
WIP and **no longer inherit `sorryAx`**. Sharp `C^(finrank)` `Analysis.sard`, weighted coarea,
measurability of level-set integrals, and **reverse** comparison remained open at this stage.
Equality of the two Cheeger constants was **unproved**, with 24 certificates. See the
[distance-cutoff gradient-integral record](2026-09-13-distance-cutoff-gradient-integral.md),
[route and status correction](2026-09-13-cutoff-route-audit-correction.md),
[one-sided Cheeger comparison](2026-09-13-cheeger-infimum-one-sided.md),
[Minkowski constant record](2026-09-13-minkowski-constant-coarea-product.md),
[Minkowski coarea record](2026-09-13-minkowski-coarea-inequality.md),
[recovery sequence record](2026-09-13-smooth-recovery-sequence.md),
[dilated integral bound and recovery route](2026-09-13-dilated-gradient-integral.md),
[pointwise gradient bound and next route](2026-09-13-mollified-gradient-bound.md),
[global Gauss–Green record](2026-09-13-global-gauss-green.md),
[subgraph divergence record](2026-09-13-subgraph-divergence-and-local-gauss-green.md),
[boundary-chart record](2026-09-13-boundary-chart-and-area-interface.md),
[Gauss–Green progress](2026-09-12-gauss-green-area-formula.md),
[interface integration](2026-09-12-perimeter-interface-integration.md), and
[proof record](2026-09-12-outward-normal-interfaces-proofs.md).
Some complete proof bodies still transitively depended on `sorryAx`; see the
[contemporary audit and retention policy](2026-09-12-status-audit-and-wip-retention.md).

Read `Definitions` and `Statement` first to identify the target, then follow the LogConcave
subdirectory's reading order. The literature-constant comparison is in
[KLS/LogConcave/Poincare.lean](../../formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean); see the
[Poincaré comparison guide](../../formalization/FunctionalInequalities/Poincare/Euclidean/README.md) for complete usage instructions.

## File placement

Log-concave properties and representation theorems belong in `LogConcave/`; shared target
definitions and other route objects remain at this level. The `LogConcave` predicate is still
defined in `Definitions.lean`, imported directly by the subdirectory. Directory names do not
indicate proof completion: each node's status comes from its ledger and certificate, not from
successful compilation of the root module.

Declaration namespaces remain `FunctionalInequalities.KLS`; module paths are organized by topic.
Place future files by mathematical responsibility; completion of a proof does not trigger a
file move. See the [migration record](../explorations/2026-09-07-logconcave-module-layout.md)
for old-to-new paths.

The uniform second-order remainder `Analysis.exists_uniform_quadratic_remainder` was proved
without holes in `Analysis/Sard/TaylorRemainder.lean`: arbitrary real normed spaces, C²,
flat base points in a compact set, and nearby points possibly outside it, all controlled by
one δ. This does not prove nullity of the image. Holes remained 11 and certificates 24;
see the [decision record](2026-09-14-uniform-quadratic-remainder.md).

The planar quantitative cover `Analysis.volume_image_eq_zero_of_quadratic_oscillation` and
second-order flat layer `Analysis.volume_image_flat_eq_zero` were proved without holes in
`Analysis/Sard/QuadraticCover.lean`: uniform quadratic oscillation on a bounded planar set
implies a null image without measurability or regularity. Combining it with the remainder
theorem gives a null image for the **second-order flat subset** of a planar compact set
(the entire compact set need not be flat). Countable exhaustion then gives the whole-plane
version `Analysis.volume_image_flat_univ_eq_zero`, without compactness or measurability
assumptions. See the [cover decision](2026-09-14-planar-quadratic-cover.md).

The nonflat layer `Analysis.volume_image_nonflat_eq_zero` and **planar Sard**
`Analysis.sard_plane` were proved without holes in `Analysis/PlanarSard.lean`: critical values
of C² functions on `Fin 2 → ℝ` are null, without a measurable, bounded, or compact critical
set. The nonflat layer uses a mean-value inequality with linear leading term to express the
critical set as a Lipschitz graph over one coordinate, **without the implicit function theorem**,
then reduces to the one-dimensional covering lemma. This is only two-dimensional: general
`Analysis.sard` (arbitrary finite dimension) remained a direct hole, and two consumers still
inherited `sorryAx`; weighted coarea and reverse comparison remained unproved.
See the [planar decision](2026-09-14-planar-sard.md).

Order and dimension were then parameterized: `Analysis.exists_uniform_pow_remainder` gives
uniform remainders of arbitrary order; `Analysis.volume_image_eq_zero_of_oscillation_pow`
gives the covering lemma in arbitrary dimension; `Analysis.volume_image_flat_pow_eq_zero`
and its whole-space version give nullity for the **fully flat layer** of C^n functions on
`Fin n → ℝ`. Second-order and planar versions become corollaries with unchanged statements.
This is only the top layer in dimension `n`: intermediate layers, `n`-dimensional Sard, and
general `Analysis.sard` remained unproved. Holes 11, certificates 24; see the
[decision record](2026-09-15-higher-order-flat-layer.md).

`Analysis/SmoothSard.lean` collected three components for C^∞ Sard dimension reduction:
stratification, flat directions, and local C^∞ graphs of regular zero sets, all without holes
and using only standard axioms. These were only components: Sard itself remained unproved,
no `sorryAx` dependency was removed, and sharp C^n `Analysis.sard` retained its statement and
direct-hole status. See the [decision record](2026-09-15-smooth-sard-ingredients.md).

Building on these, `Analysis/SmoothSard.lean` **proved Sard's theorem for C^∞ real-valued functions**
(`sard_smooth_pi`, `sard_smooth`, `ae_forall_fderiv_ne_zero_of_contDiff_top`), in arbitrary finite
dimension, without a measurable critical set, using only standard axioms. An audit client
reproved the statement of `ae_exists_superlevel` without `sorryAx`. However, **no WIP file was
changed in that round**, so the declaration still inherited `sorryAx`, holes remained 11,
and sharp C^n `Analysis.sard` remained a direct hole. See the
[decision record](2026-09-15-smooth-sard.md).
