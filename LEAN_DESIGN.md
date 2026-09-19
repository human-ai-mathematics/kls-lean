# Lean design: Poincaré certificates

命名空间已表达的内容不再重复进声明短名；见[短名补充记录](research/decisions/2026-09-08-namespace-short-names.md)。
比较名称也只写一次共有操作，见[比较短名记录](research/decisions/2026-09-08-comparison-short-names.md)。

This document records the implemented Lean architecture and semantic contracts for the Issue #2
linear-test lower bound, Issue #6 two-factor Poincaré tensorization, Issue #7 finite-product
tensorization with optimal-constant equality, and the sharp one-dimensional Gaussian Poincaré
constant. Multivariate Gaussian and log-Sobolev inequalities, Bakry--Émery, Otto--Villani,
mode-indicator tests, and the KLS conjecture itself remain outside the certified scope.

The interfaces described here may evolve as proofs and downstream uses clarify the design.
There is no mandatory freeze before proof work or default promise of backward compatibility.
Proof certification refers to the current statement. Record mathematical scope changes and
migrate affected consumers; the [current lifecycle](research/ledger-schema.md#lifecycle) gives
the validation rules. Historical freeze records below preserve their reviewed snapshots.

## Current semantic boundary (2026-09-16)

The ledger has 24 certified nodes. Three WIP modules retain 8 direct holes: sharp finite-regularity
Sard (1), the smooth Cheeger superlevel bound and reverse infimum comparison (2), and singular-law
Cheeger energy comparisons (5). Smooth Sard, Gauss–Green, smooth perimeter recovery, compact
Whitney extension, exact C¹ pieces and weighted coarea through locally Lipschitz functions are
proved auxiliary results. They are not additional ledger certificates. The forward comparison
`h_M ≤ h_S` is proved; the reverse and equality are not. The log-concave Cheeger–Buser workstream
is assigned separately, as recorded in the current handoff.

The canonical energy is `2 Ch` in the local-slope convention when the intrinsic law is absolutely
continuous, including every log-concave law. The arbitrary singular-law identity and the
asymptotic-Lipschitz identification remain open. One-dimensional Poincaré has coefficient 4,
including Dirac laws; optimality of 4 is not a separately certified conclusion. `KLS.Conjecture`
is the dimension-free proposition, not a theorem. See the
[alignment review](research/decisions/2026-09-16-semantic-alignment.md).

The dated construction sections below preserve their historical design context. Statements about
what a particular round had not proved describe that round; the boundary above and current source
determine completion today.

## Mathematical API organization (2026-09-08)

The public frontends are `SmoothTest`, `SmoothGradient`, `WeightedGradient`,
`CovarianceGradient`, and `LocalSlope`; `Ambient` and `Intrinsic` identify the carrier construction.
Probability pushforwards and L² pullbacks occupy their own layers. See [the naming guide](research/naming.md) and [the migration record](research/decisions/2026-09-08-mathematical-api-organization.md).

`FunctionalInequalities/Analysis/` (added 2026-09-12) holds KLS-independent geometric analysis:
statements about a finite-dimensional real inner-product space that would be legitimate Mathlib
targets on their own. `Analysis/LevelSet.lean` is its first module (Prékopa--Leindler,
Brunn--Minkowski, the isodiametric inequality, the Hausdorff normalization, and finiteness of
`μH[n-1]` near a regular level set); `Analysis/AreaFormula.lean` proves the codimension-one area
formula for `C¹` graphs; `Analysis/Divergence.lean` carries `div F = tr (DF)` with the
rank-one trace identity; and `Analysis/ImplicitGraph.lean` (added 2026-09-13) proves the local
`C^∞` graph representation of a regular level set, through the `C^k` inverse function theorem
rather than Mathlib's implicit function theorem, together with the gradient identity along the
graph and the area formula for a translated graph. `Analysis/SubgraphDivergence.lean` and
`Analysis/GraphIntegral.lean` (added 2026-09-13) prove the divergence formula on the region below
a `C¹` graph and the weighted change of variables that turns the area formula into an integral
identity, and `Analysis/PartitionOfUnity.lean` (added 2026-09-13) proves the finite smooth
decomposition of a compactly supported map subordinate to an open cover of its support. The
layering rule this enforces: base
definitions go below (`KLS/Geometry/Surface/Measure.lean`), general geometry in the middle, and the
perimeter application layer on top, so an application module can import a general theorem without
the general theorem importing the application. The `SmoothDomain`-specific consequences of the
general graph geometry — `outwardNormal`, the tangent hyperplane, the boundary chart and its
surface-measure identity — live in the application layer,
`KLS/Geometry/BoundaryChart.lean`, which is also `sorry`-free, the chart-local Gauss--Green
identity (for a field whose support lies in one chart cylinder) in
`KLS/Geometry/LocalGaussGreen.lean`, and the **global** Gauss--Green theorem for an arbitrary
compactly supported `C¹` field in `KLS/Geometry/GaussGreen.lean`, all likewise `sorry`-free. A
completed obligation therefore leaves `KLS/WIP/` rather than staying there with a filled body: the
global theorem, the local finiteness of the restricted surface measure and the
boundary-integrability lemmas moved down on 2026-09-13, keeping their names and statements.
The remaining unfinished obligations (coarea, Sard) stay in `KLS/WIP/`; nothing in `Analysis/` may
carry a `sorry`. See
[the integration record](research/decisions/2026-09-12-perimeter-interface-integration.md),
[the boundary-chart record](research/decisions/2026-09-13-boundary-chart-and-area-interface.md),
[the subgraph record](research/decisions/2026-09-13-subgraph-divergence-and-local-gauss-green.md)
and [the global Gauss--Green record](research/decisions/2026-09-13-global-gauss-green.md).

## Smooth-domain and mollification layering (2026-09-13)

The current dependency split replaces the former `BoundaryChart → WIP/RelativePerimeter` edge.
`KLS/Geometry/SmoothDomain.lean` now owns the domain structure, local defining-function API,
normalization check, homotheties, local boundary finiteness and Haar-null frontier.
`BoundaryChart` imports these foundations directly. `Geometry/Mollification.lean` owns the
indicator convolution, its local integrability, smoothness, Lipschitz property and `[0,1]` range.
The previously duplicated private convolution and integrability helpers are now single public
interfaces in that module. Names are preserved without compatibility aliases.

The scalar Gauss--Green formula belongs beside the vector theorem in `Geometry/GaussGreen.lean`.
`Geometry/MollifiedBoundary.lean` combines it with `Mollification` to prove the negative boundary
formula and `SmoothDomain.enorm_gradient_mollified_le`. All 15 local modules in this consequence's
import closure are WIP-free. Coarea and Sard stay in `WIP/AnalyticPrerequisites`; the two remaining
perimeter recovery obligations stayed, at that date, in `WIP/RelativePerimeter`, which imported
the proved consequence; that layer has since been emptied and removed.
This changes no mathematical scope or surface-measure normalization and adds no certificate.
The [decision](research/decisions/2026-09-13-mollified-gradient-bound.md) records the proof and the
remaining weighted homothety, support-localization and recovery dependencies.

## Quantitative relative-perimeter layer (2026-09-13)

`Geometry/Surface/Homothety.lean` now proves the normalized measure pushforward under an inverse
homothety and the resulting weighted set/boundary lintegral change of variables. The unique
homothety homeomorphism is public in `Geometry/SmoothDomain.lean`, alongside the shared frontier
transport identity. A total-boundary-mass equality is not used as a substitute for weighted
change of variables.

`LogConcave/DensityBounds.lean` holds the former WIP density bounds and the positivity-interior
inclusion into the measure-support interior. It depends only on BorellRepresentation.
`Geometry/RelativePerimeter.lean` combines those density estimates, SurfaceHomothety and
MollifiedBoundary to prove the original outward-dilation gradient-integral bound. The perimeter
definition and indicator-homothety convergence moved there with unchanged names. Its 29 local
imports contain no WIP module; `WIP/RelativePerimeter` retained, at that date, only the
recovery-sequence obligation, and the other analytic WIP modules remain separate. No certificate was added.
See the [decision and recovery dependencies](research/decisions/2026-09-13-dilated-gradient-integral.md).

## Perimeter recovery layer (2026-09-13)

`Geometry/PerimeterRecovery.lean` is the hole-free application layer on top of
`Geometry/RelativePerimeter.lean`. It owns the two mollification-convergence interfaces
(`SmoothDomain.mollifiedIndicator_eq_indicator_of_const`,
`SmoothDomain.exists_bump_lintegral_enorm_mollifiedIndicator_sub_lt`) and the proved
`RelativePerimeter.exists_smooth_recovery_sequence`. Its 30 local imports contain no WIP module.
`LogConcave/DensityBounds.lean` gained `IsBorellDensity.absolutelyContinuous` and made the
existing ball lemma public rather than duplicating it.

A completed obligation leaves `KLS/WIP/` instead of staying there with a filled body, and an
emptied WIP layer is removed rather than kept as a shim: `KLS/WIP/RelativePerimeter.lean` was
deleted once its last obligation moved down, and `KLS/WIP/CheegerInfimum.lean` now imports
`Geometry/PerimeterRecovery` directly. Names, namespaces, the `surfaceMeasure` normalization and
the `volume` reference are unchanged, and no certificate was added. The remaining WIP obligations
are coarea and Sard in `WIP/AnalyticPrerequisites` and the eight Cheeger-infimum bodies.
See the [recovery decision](research/decisions/2026-09-13-smooth-recovery-sequence.md).

## Superlevel rewiring (2026-09-15)

A completed obligation leaves `KLS/WIP/`: `SmoothDomain.ae_exists_superlevel` and
`SmoothDomain.frontier_superlevel_subset` moved to the new hole-free
`KLS/Geometry/RegularSuperlevel.lean`, with `pp.all` signatures byte-identical before and after.
The packaging was deliberately **not** returned to `Geometry/SmoothDomain.lean`, which the design
keeps independent of Sard; it sits one layer above, importing `Geometry/SmoothDomain` and
`Analysis/SmoothSard`. `WIP/CheegerInfimum.lean` swapped its `WIP/AnalyticPrerequisites` import for
the new module and still compiles, so the sharp Sard and coarea holes now live in a file that no
module imports. Hole count is unchanged: a filled body moved, not a direct hole. See the
[decision](research/decisions/2026-09-15-superlevel-rewire.md).

## Smooth Sard (2026-09-15)

`Analysis/SmoothSard.lean` now carries the `C^∞` Sard theorem itself, proved by induction on the
dimension over the ingredients it already owned. The design choice worth recording is that the
induction stays **global**: rather than relaxing the flat layer and the order-`n` remainder to open
domains, the module proves one small extension lemma, `exists_contDiff_eventuallyEq`, and replaces
each local graph by a globally smooth map agreeing with it near the base parameter. The already
proved `volume_image_flat_pow_univ_eq_zero` is then used unchanged. The module states the smooth
theorem only; the sharp `C^n` `Analysis.sard` in `KLS/WIP/AnalyticPrerequisites.lean` keeps its
text and its direct-hole status, and no WIP file was rewired. See the
[decision](research/decisions/2026-09-15-smooth-sard.md).

## Smooth Sard ingredients (2026-09-15)

`Analysis/SmoothSard.lean` owns the three descent ingredients `critical_subset_layers`,
`exists_flat_direction` and `exists_local_graph`; its only local import is
`Analysis/QuadraticCover`. The chart in `exists_local_graph` is the inverse function theorem
applied to the map replacing one coordinate by the defining function, so no manifold layer and no
second implicit-function framework enters the repository, and `Analysis/ImplicitGraph.lean` — which
needs `C^∞` data with an inner-product graph splitting — is deliberately not reused. The module is
explicitly a set of ingredients: it states no Sard theorem, and the sharp `C^n` `Analysis.sard`
keeps its text and its direct-hole status. See the
[decision](research/decisions/2026-09-15-smooth-sard-ingredients.md).

## Higher-order flat layer (2026-09-15)

The order and the dimension are now parameters rather than the literal `2`.
`Analysis/TaylorRemainder.lean` owns `Analysis.exists_uniform_pow_remainder`, proved by induction
on the order through `fderiv f`; the vector-valued induction runs in a private same-universe
auxiliary lemma so the public real-valued statement keeps arbitrary universes and needs no
finite-dimensionality. `Analysis/QuadraticCover.lean` owns
`Analysis.volume_image_eq_zero_of_oscillation_pow` over `Fintype.piFinset`, plus the fully flat
layer in dimension `n`. A generalized statement replaces its own special case rather than sitting
beside it: `exists_uniform_quadratic_remainder` and
`volume_image_eq_zero_of_quadratic_oscillation` are corollaries with byte-identical statements, so
no client moved and no proof content is duplicated. The dimension-`n` restriction to the fully
flat layer is explicit in the names; general `Analysis.sard` is untouched. See the
[decision](research/decisions/2026-09-15-higher-order-flat-layer.md).

## Planar Sard analysis layer (2026-09-14)

`Analysis/PlanarSard.lean` owns `Analysis.volume_image_nonflat_eq_zero` and `Analysis.sard_plane`;
its only local import is `Analysis/QuadraticCover`. The nonflat layer is deliberately built from a
mean-value inequality with linear principal part plus elementary `Fin 2` linear algebra rather than
from an implicit function theorem: `Analysis/ImplicitGraph.lean` requires `C^∞` and an inner
product and does not apply to the merely `C¹` map `Du`, and no new implicit-function framework is
introduced. Compactness is dissolved by Lindelöf, so the public statements carry no `K`. The
dimension-two restriction is kept in the name, and general `Analysis.sard` is untouched. See the
[decision](research/decisions/2026-09-14-planar-sard.md).

## Planar covering analysis layer (2026-09-14)

`Analysis/QuadraticCover.lean` owns `Analysis.volume_image_eq_zero_of_quadratic_oscillation` and
`Analysis.volume_image_flat_eq_zero`. Its only local import is `Analysis/TaylorRemainder`; it adds
no outer-measure or covering framework, using Mathlib's `Finset` subadditivity, `Real.volume_Icc`,
integer floors and `ENNReal.le_of_forall_pos_le_add` directly. The covering lemma keeps the
proposed scope verbatim — dimension two, bounded set, uniform quadratic oscillation — and assumes
no measurability anywhere. The flat-layer corollary is deliberately the **subset** form
`{x ∈ K | Du x = 0 ∧ D²u x = 0}`, never "all of K is flat"; its whole-plane version is a countable
exhaustion, not a new argument. No migration or certificate expansion.
The [decision](research/decisions/2026-09-14-planar-quadratic-cover.md) separates this planar layer
from the planar nonflat layer and from general Sard, both still unproved.

## Uniform remainder analysis layer (2026-09-14)

`Analysis/TaylorRemainder.lean` owns `Analysis.exists_uniform_quadratic_remainder`, independent of
Sard and KLS, with Mathlib-only imports. The compact-base, flat-point C² estimate is proved for
any real normed domain, without finite-dimensionality or completeness. It combines compact
external-neighbourhood uniform continuity of D²u with two convex mean-value bounds. One δ works
for all flat x∈K and all nearby y, including y outside K. No migration or certificate expansion.
The [decision](research/decisions/2026-09-14-uniform-quadratic-remainder.md) separates this proved
estimate from the still-missing planar covering/null-image lemma and general Sard.

## Independent low-dimensional Sard layer (2026-09-14)

`Analysis/Sard.lean` owns `Analysis.sard_of_finrank_le_one`, with Mathlib-only imports and no WIP
edge. Its general real normed-space statement assumes finrank ≤ 1 and C^(finrank), including C⁰
in dimension zero. It proves nullity of the critical **values**, without domain measure or inner
product assumptions. Dimension one uses a continuous linear equivalence ℝ → V and zero-derivative
chain rule; the determinant occurs only for the resulting ℝ endomorphism. General `Analysis.sard`
stays unchanged in WIP with `sorryAx`, as do its consumers. There is no compatibility alias,
module migration or certificate expansion. See the
[proof and corrected next obligation](research/decisions/2026-09-14-low-dimensional-sard.md).

## Regular superlevel sets and the Sard packaging (2026-09-14)

`KLS/Geometry/SmoothDomain.lean` — the module that already owns the structure, the local
defining-function API and the `empty` / `univ` / `homothety` constructors — gains one more
constructor, `SmoothDomain.ofSuperlevel`, with its `ofSuperlevel_carrier`. It is hole-free and
depends on the standard three axioms only. The layering rule it follows is the one this document
already states: a completed obligation is proved in the lowest layer that can carry it, and the
`sorryAx`-dependent application stays in `KLS/WIP/`.

The hypothesis is deliberately the weakest one the structure needs: nonvanishing of `fderiv ℝ u` on
`frontier {x | t < u x}` only. Requiring the whole level set `{x | u x = t}` to be regular, or the
derivative to be nonzero on the whole space, would be a strictly stronger interface with no gain,
and would make the degenerate cases need extra hypotheses instead of falling out. The defining data
is `W = {y | fderiv ℝ u y ≠ 0}`, open as the preimage of `{0}ᶜ` under the continuous
`y ↦ fderiv ℝ u y`, and `φ = t - u`, which matches the structure's convention that the domain is the
**negative** sublevel set of `φ` inside `W`: `carrier ∩ W = {y ∈ W | φ y < 0}` is exactly
`t - u y < 0 ↔ t < u y`. Empty frontier, empty carrier, full carrier and dimension zero need no
branch and no extra hypothesis, because in each of them the frontier is empty and the
`exists_defining` premise is vacuous. Nothing here builds a manifold framework; the construction
needs only `NormedAddCommGroup` and `NormedSpace ℝ`.

`SmoothDomain.ae_exists_superlevel` stays in `KLS/WIP/CheegerInfimum.lean`, which is where a
statement that depends on `Analysis.sard` belongs. It now has a proof body — `filter_upwards` on
`Analysis.ae_forall_fderiv_ne_zero`, the order reduction discharged by `ENat.LEInfty.out` rather
than `le_top`, then `ofSuperlevel` through `frontier_superlevel_subset` — but it **still inherits
`sorryAx`**, so a filled body is not a certified result and it is not listed as one. No module
migrated: `frontier_superlevel_subset`'s only consumer is the wrapper in the same file, and the
frontier-form hypothesis means the hole-free construction never needs it, so it was only reordered
above its consumer with its `omit ... in` prefix. The WIP file gains one import of
`KLS/WIP/AnalyticPrerequisites`, a WIP-to-WIP edge that leaves the hole-free layer untouched.
No certificate was added and no mathematical scope changed.
See the [decision](research/decisions/2026-09-14-regular-superlevel-smooth-domain.md).

## Distance-cutoff layer (2026-09-13)

`KLS/Geometry/DistanceCutoff.lean` is hole-free and imports **no local module at all**: its import
closure is Mathlib only, like `Geometry/MinkowskiContent.lean`. It owns the complete distance-cutoff
basis — `Isoperimetry.distanceCutoff` with its range, Lipschitz and boundary-value lemmas, and the
`L¹(ν)` convergence `tendsto_distanceCutoff_indicator` — all migrated verbatim from
`KLS/WIP/CheegerInfimum.lean` with byte-identical `pp.all` signatures, together with the proved
gradient estimate `Isoperimetry.lintegral_enorm_gradient_distanceCutoff_le`.

The estimate is pointwise rather than almost-everywhere: the cutoff attains a global extremum on
each of its two constant-value sets, so `IsLocalMax.fderiv_eq_zero` and
`IsLocalMin.fderiv_eq_zero` — neither of which needs a differentiability hypothesis, since Mathlib
defines `fderiv` and `gradient` to be zero at points of non-differentiability — kill the gradient at
every point of them, endpoint level sets included. That is why the module needs no Rademacher
theorem, no Lebesgue density theorem and no absolute continuity, and why its import closure can stay
empty. The published interface is unchanged all the same: the Haar measure and `hac` remain in the
signature, silenced by two declaration-local linter options rather than removed.

The migration was decided by actual dependency, not by moving a whole WIP file:
`tendsto_distanceCutoff_indicator` came along because it is hole-free and its only dependencies are
the four cutoff lemmas, so leaving it behind would split one API across two modules, while
`exists_smooth_approximation_lipschitz` stayed in `KLS/WIP/CheegerInfimum.lean` — already proved,
but part of the smooth-replacement interface and carrying an `Energy.Euclidean` import that does not
belong in a geometry module. No certificate was added and no mathematical scope changed.
See the [decision](research/decisions/2026-09-13-distance-cutoff-gradient-integral.md).

## One-sided Cheeger comparison layer (2026-09-13)

`KLS/Geometry/Cheeger/Infimum.lean` is hole-free and its 32-module local import closure contains no
work-in-progress module: it sits on the two finished chains `Geometry/PerimeterRecovery` (the smooth
recovery sequence) and `Geometry/MinkowskiConstant` (the integrated Minkowski coarea bound). It owns
`Isoperimetry.smoothConstant` with `smoothConstant_eq_top_of_subsingleton`, the layer-cake identity
`lintegral_measure_symmDiff_superlevel`, the balance estimate
`min_measure_le_add_measure_symmDiff`, the convergence `tendsto_lintegral_min_superlevel` — all five
migrated verbatim from `KLS/WIP/CheegerInfimum.lean` with byte-identical `pp.all` signatures — and
the proved `Isoperimetry.minkowskiConstant_le_smoothConstant`.

Exactly one direction is proved. `smoothConstant_le_minkowskiConstant`, which still needs Sard, the
weighted coarea formula and the distance-cutoff gradient estimate, and the equality
`minkowskiConstant_eq_smoothConstant` stay in `KLS/WIP/CheegerInfimum.lean` together with the
affine-support transport that consumes them; nothing in the hole-free layer claims the two Cheeger
infima agree. `Geometry/MinkowskiConstant.lean` was deliberately left untouched, so no recovery,
relative-perimeter or WIP dependency entered that base layer, whose closure is still the single
`Geometry/MinkowskiContent`. The migrated set is the minimum the new theorem actually uses; the
distance cutoffs, which only the reverse direction needs, stayed behind. No certificate was added,
and no mathematical scope changed.
See the [decision](research/decisions/2026-09-13-cheeger-infimum-one-sided.md).
The [audit correction](research/decisions/2026-09-13-cutoff-route-audit-correction.md)
supersedes its cutoff route: extrema and Lipschitz derivative bounds apply pointwise,
so Rademacher and `hac` are unnecessary for this estimate; retain the original signature.
`SmoothDomain.ae_exists_superlevel` now has a body but still inherits `sorryAx` through general Sard.

## Minkowski constant layer (2026-09-13)

`KLS/Geometry/MinkowskiConstant.lean` is hole-free and its local import closure is the single
hole-free `KLS/Geometry/MinkowskiContent.lean`. It owns the Minkowski Cheeger infimum
`Isoperimetry.minkowskiConstant` and `minkowskiConstant_eq_top_of_subsingleton`, migrated verbatim
from `KLS/WIP/CheegerInfimum.lean` with byte-identical `pp.all` signatures; the multiplied form of
the defining infimum `minkowskiConstant_mul_min_le`; the almost-everywhere agreement
`ae_measure_superlevel_lt_eq_le` of strict and closed superlevel masses, stated for any `SFinite`
measure and any measurable function; the measurability `measurable_min_measure_superlevel` of the
superlevel balance for an arbitrary function; and the proved integrated coarea bound
`Isoperimetry.minkowskiConstant_mul_lintegral_min_superlevel_le`.

`minkowskiConstant` moved down this round for the reason the layering rule prescribes: the finished
theorem must be hole-free, and a hole-free module may not import the work-in-progress layer.
`measurable_min_measure_superlevel` was extracted from the inlined measurability step of
`tendsto_lintegral_min_superlevel`, and that consumer was migrated to the new lemma rather than the
proof being duplicated. `smoothConstant`, the layer-cake identities, the distance cutoffs and the
two unfinished comparisons stay in the application layer `KLS/WIP/CheegerInfimum.lean`, which now
imports the new module and no longer imports `MinkowskiContent` directly. No certificate was added,
and no mathematical scope changed.
See the [decision](research/decisions/2026-09-13-minkowski-constant-coarea-product.md).

## Minkowski content layer (2026-09-13)

`KLS/Geometry/MinkowskiContent.lean` is hole-free and imports **no local module at all**: its
import closure is Mathlib only. It owns the coordinate-space outer Minkowski content
`Isoperimetry.minkowskiContent` (open thickenings, `ENNReal` truncated subtraction, `𝓝[>] 0`
liminf), the migrated `measure_closure_eq_of_minkowskiContent_ne_top`, the local supremum
`Isoperimetry.ballSup` with its Lipschitz transfer and near-neighbour witness, and the proved
Minkowski coarea inequality `Isoperimetry.lintegral_minkowskiContent_superlevel_le`.

The definition keeps its `KLS.Isoperimetry` namespace and full name, so the migration renames
nothing and needs no alias; that is why the module sits in `KLS/Geometry/` rather than in
`Analysis/`, even though the theorem is KLS-independent — the zero-module import closure is the
honest record of that independence. The unfinished Cheeger-infimum comparisons
(`minkowskiConstant`, `smoothConstant`, the two product inequalities and the two one-sided
comparisons) stay in the application layer `KLS/WIP/CheegerInfimum.lean`, which now imports the
new module. No certificate was added and no surface-measure normalization changed. See the
[coarea decision](research/decisions/2026-09-13-minkowski-coarea-inequality.md).

## Layered `L²` and energy foundation (2026-09-04)

Downstream applications and smoke tests may import `FunctionalInequalities.Poincare.Foundation`;
reusable library modules import only their exact direct dependencies. The accepted smooth-test API
below remains available for its existing certificates, but it is no longer the architectural base
for future KLS layers. The finite-dimensional comparison now proves equality of the two optimal constants.

The 12 comparison declarations in `Poincare.Relaxation`, `Energy.SmoothGradient.Intrinsic.Comparison`,
`Poincare.SmoothGradient.Comparison` and `Poincare.SmoothTest.Comparison` now have complete
proofs with unchanged signatures. Both ledger nodes are proved and exported by the foundation;
see the [comparison guide](formalization/FunctionalInequalities/Poincare/Euclidean/README.md)
and [proof acceptance](research/decisions/2026-09-06-poincare-comparison-proofs.md).

The new dependency direction is:

```text
ProbabilityMeasure + intrinsic real L² variance + affine support coordinates
  → extended energy and its finite domain
  → concrete pre-energy + quadratic law + dense realization
  → sequential relaxation + l.s.c. + recovery + closed-quadratic structure
  → optional core-agreement / contraction / Dirichlet properties
  → finite-valued TestFamily on that domain
  → ENNReal Rayleigh supremum and Poincaré constant.
```

`Poincare.TestFamily.constant` is the supremum of extended Rayleigh quotients. Its checked boundary
semantics are `0 / 0 = 0`, positive variance divided by zero energy equals `⊤`, and a single such
test forces the optimal constant to be `⊤`. `Poincare.L2Energy.constant` applies this optimizer to
the finite domain of `Q : Lp ℝ 2 μ → ENNReal`; `finiteValue` requires a proof that `Q f ≠ ⊤`, so
infinite energy is never silently converted to zero.

`Energy.SmoothGradient.relaxation` realizes globally `C∞`, square-integrable,
finite-gradient tests in `L²` and sequentially relaxes their `NNReal` gradient integral on a
finite-dimensional real Hilbert space with Borel, second-countable measurable topology. In
Mathlib v4.33, ordinary infinite differentiability is `ContDiff ℝ ∞`; `ContDiff ℝ ⊤` means the
strictly stronger analytic regularity and is not used by either live smooth-test frontend.

The following statements are now proved rather than assumed:

- compactly supported `C∞` tests give a dense realization;
- the concrete gradient pre-energy is quadratic;
- sequential relaxation is lower semicontinuous in every pseudometric ambient space and has
  recovery sequences at finite points, or at all points under dense realization;
- relaxation preserves the full extended parallelogram identity and nonzero quadratic
  homogeneity, hence the smooth-gradient relaxation is a densely defined `ClosedQuadratic`;
- continuous transformations satisfying the explicit test-level relaxed contraction bound
  contract the relaxation;
- the affine span of the support is the smallest closed affine subspace of full measure, and the
  original and intrinsic-coordinate real `L²` spaces are linearly isometrically equivalent;
  the intrinsic-affine smooth relaxation is therefore also `ClosedQuadratic`.

The original closed-quadratic results above are supplemented by three later certificates:
`thm:smooth-gradient-relaxation-dirichlet` proves the normal-contraction estimate and Dirichlet
property for every Borel probability law; `thm:smooth-gradient-raw-core-agreement-density` proves
`AgreesOnTests` and the sequential-core property under `SmoothGradient.LocalDensity`; and
`cor:absolutely-continuous-relaxation-two-cheeger` identifies the intrinsic canonical energy with
`2 Ch` in the local-slope convention when the intrinsic law is Haar-absolutely-continuous, hence
for every log-concave law. The unconditional singular-law Cheeger comparison and the equivalence
with the asymptotic-Lipschitz convention remain isolated WIP obligations. See the
[current status record](research/decisions/2026-09-12-status-audit-and-wip-retention.md).

For singular measures, raw ambient gradients need not be constant on an `L²` fiber (`0` and `x ↦ x` already
differ under `δ₀`). This obstructs a raw-test core theorem, but it does not obstruct the closed
quadratic relaxation itself. The intrinsic affine reduction removes normal directions and gives
a canonical coordinate presentation; it does not by itself prove raw-test agreement for atomic
or other singular laws. Anisotropic energies will carry their metric/operator parameter
explicitly and will not reuse the unqualified canonical-energy name.

The complete current tree, quantified interface, nonclaims, build command, and migration order are
in [`formalization/FunctionalInequalities/Poincare/README.md`](formalization/FunctionalInequalities/Poincare/README.md).

## Tensorization design and accepted statements (2026-09-03)

The tensorization proofs are complete, and the node is recorded as **proved** with
`checked_by: lean`. The user's acceptance, complete public signatures, and ledger statement are
recorded in `research/decisions/2026-09-03-tensorization-freeze.md`. Source correspondence,
semantic review, and validation evidence are recorded in
`research/explorations/2026-09-03-tensorization-acceptance.md`. That record distinguishes local
verification from CI for the final published commit.

The binary Hilbert product is `WithLp 2 (E × F)`, using Mathlib's
`Analysis.InnerProductSpace.ProdL2`. Ordinary `E × F` has the maximum norm, which is not the
Hilbert product norm. No global or local replacement of its norm/inner-product instances is
permitted. The measurable structure is Mathlib's transported structure from
`Analysis.Normed.Lp.MeasurableSpace`.

Define `Poincare.SmoothTest.prodMeasure μ ν := (μ.prod ν).map (WithLp.toLp 2)`. This is the same product
probability law expressed on the Hilbert product, not a change of normalization. Use the
measurable equivalence `MeasurableEquiv.toLp 2 (E × F)` to transport integrability, variance,
and integrals. Its continuous linear counterpart is `WithLp.prodContinuousLinearEquiv`.

The public results apply under these ambient assumptions: real separable Hilbert spaces with
their Borel sigma algebras, including finite-dimensional Euclidean factors of any natural-number
dimension. Their use has the following form; the complete elaborated signatures are in the
freeze record:

```lean
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

example
    {μ : Measure E} {ν : Measure F} {C C' : ℝ}
    (hμ : Poincare.SmoothTest.Holds μ C) (hν : Poincare.SmoothTest.Holds ν C') :
    Poincare.SmoothTest.Holds (Poincare.SmoothTest.prodMeasure μ ν) (max C C') :=
  Poincare.SmoothTest.Holds.prod hμ hν

example
    {μ : Measure E} {ν : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Poincare.SmoothTest.constant (Poincare.SmoothTest.prodMeasure μ ν) ≤
      max (Poincare.SmoothTest.constant μ) (Poincare.SmoothTest.constant ν) :=
  Poincare.SmoothTest.constant_prod_le
```

`Holds` already carries probability normalization and nonnegative constants. The accepted ledger
statement is: for Borel probability measures on real separable Hilbert spaces, if the smooth
L2 finite-energy Poincaré inequalities hold with constants C and C', the Hilbert product law
satisfies the same inequality with max(C,C'); consequently its extended optimal constant is at
most max(C_P(mu),C_P(nu)), including infinite constants. The normalization remains
`Var(f) ≤ C ∫ ‖gradient f‖²`.

The proof architecture does not differentiate an integral. Smoothness restricts to every
section, but the L2 and finite-energy fields restrict only to almost every section. For example,
with `ν = δ₀` and `f(x,y) = y² exp(x²)`, the product test and its gradient vanish on the support,
whereas a section at `y ≠ 0` need not be L2 for a Gaussian first factor. Thus the section lemmas
are a.e. statements. Neither `Admissible` nor either tensorization theorem requires every section
to be admissible.

The proof establishes the gradient projections and their squared-norm sum, then a.e.
admissibility of sections. It assembles the bound through the two-factor variance inequality
`Var(f) ≤ ∫ Var(f(·,y)) dν + ∫ Var(f(x,·)) dμ`, using Fubini and L2 estimates. Every use of a real
integral retains explicit integrability evidence. The optimal-constant argument uses finite
valid constants strictly below a hypothetical counterexample to the infimum bound in `ENNReal`;
no attainment or finiteness of the optimal constants is assumed.

The existing `Admissible`, `energy`, `Holds`, and `constant` definitions remain the semantic
contract. In particular, this theorem concerns globally smooth real-valued L2 tests with finite
gradient energy. It does not identify that test class with a closed Dirichlet domain, a Sobolev
space, or all locally Lipschitz tests for arbitrary Borel measures. The source comparison with
BGL Proposition 4.3.1 and the use in the manuscript's `prop:products` are recorded in
`research/explorations/2026-09-03-tensorization-source-alignment.md`. The finite-product extension
is described below as an accepted Lean certificate; the further inputs to the product-case
KLS result remain follow-up work.

The initial encoding audit and statement/proof ownership decision remain in
`research/decisions/2026-09-03-hilbert-product-tensorization.md` and
`research/decisions/2026-09-03-statement-proof-separation.md`. Those historical records describe
the earlier draft stage; the freeze and acceptance records document the current state.

## Reproducible project

The project under `formalization/` pins Lean and Mathlib to release `v4.33.0`.
`formalization/lake-manifest.json` resolves Mathlib to commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. From the repository root, build it with:

```bash
cd formalization
lake build
```

The default targets compile the reusable `FunctionalInequalities` library and all certificates
listed in [`solutions/README.md`](solutions/README.md). The six original entry points are
`solutions/LemLinearTestLower.lean`,
`solutions/LemPoincareTensorization.lean`,
`solutions/LemPoincareFiniteTensorization.lean`,
`solutions/LemPoincareGaussianOneDimensional.lean`,
`solutions/LemAmbientIntrinsicPoincareComparison.lean`, and
`solutions/LemLegacyRelaxedPoincareComparison.lean`. The certificate entry points belong to the
`Solutions` default target, together with `solutions/GaussianAxiomAudit.lean` and
`solutions/FoundationAxiomAudit.lean`. The `Examples` default target compiles the usage and boundary
examples in `examples/PoincareFoundation.lean`; the foundation guide explains their reading order.

## Formalized statement

The source is Definition 2.1 and the linear-test part of Remark 3.8 in `KLS.pdf`. For a probability
measure with finite second moment on a finite-dimensional real Hilbert space, the certificate
proves both

$$
R_\mu(f)\le C_P(\mu)
$$

for every admissible test and

$$
\lambda_{\max}(\operatorname{Cov}_\mu)\le C_P(\mu).
$$

The second conclusion is obtained from the first by testing with
$f_v(x)=\langle v,x\rangle$. The proof uses the definition of the optimal Poincaré constant,
the linear-test variance and energy identities, and finite-dimensional Rayleigh--Ritz.

## Semantic contract

`FunctionalInequalities.Poincare.SmoothTest.Basic` implements the manuscript normalization

$$
\operatorname{Var}_\mu(f)\le C\int \lVert\nabla f\rVert^2\,d\mu.
$$

The exact choices are:

- `Poincare.SmoothTest.Admissible μ f` means that `f` is globally smooth, belongs to $L^2(\mu)$, and has
  integrable squared gradient. The finite-energy field prevents Lean's totalized real integral
  from silently assigning an unintended value to a nonintegrable energy. This is the smooth
  finite-energy core; no equivalence with a closed Sobolev or spectral-gap domain is claimed.
- `Poincare.SmoothTest.energy μ f` is the real integral of the squared norm of Mathlib's canonical gradient.
  A bridge theorem identifies it with the squared operator norm of the Fréchet derivative.
- `Poincare.SmoothTest.Holds μ C` is a `Prop`-valued structure containing probability normalization,
  nonnegativity of `C`, and the fixed-constant inequality for every admissible test.
- `Poincare.SmoothTest.constant μ : ℝ≥0∞` is the infimum of all finite nonnegative constants satisfying
  `Poincare.SmoothTest.Holds μ C`. It is `⊤` exactly when no finite valid constant exists.
- `Poincare.SmoothTest.rayleigh μ f : ℝ≥0∞` divides only after mapping variance and energy into extended
  nonnegative reals. Thus positive variance over zero energy is `⊤`, while `0 / 0 = 0`. At
  positive energy it equals the ordinary real quotient from the manuscript.

The theorem quantifies over every `Poincare.SmoothTest.Admissible` test, including constant functions. The
formal statement does not use “nonconstant” as a substitute for positive energy, since that
implication fails for an arbitrary measure.

## Centered covariance and the spectral supremum

Mathlib's `ProbabilityTheory.covarianceOperator` is an uncentered second-moment operator, so it is
not the covariance object used in the manuscript. `Covariance.operator μ` is instead the Riesz
operator associated with Mathlib's centered `covarianceBilin μ`. Under `MemLp id 2 μ`, its
quadratic form is the variance of the corresponding linear test.

Mathlib totalizes `covarianceBilin`; outside its square-integrability regime it does not express
the intended finite centered covariance. The certificate therefore states `MemLp id 2 μ`
explicitly rather than relying on the totalized value.

`Covariance.rayleighMax μ : ℝ` is the supremum of the covariance-operator Rayleigh quotient over
nonzero vectors. The formal API proves that:

1. it equals the supremum of $v^T\operatorname{Cov}_\mu v$ over the unit sphere;
2. it is nonnegative because the centered covariance form is positive semidefinite;
3. in a nontrivial finite-dimensional space it is attained and is an eigenvalue of the centered
   covariance operator; and
4. `Covariance.lambdaMax μ : ℝ≥0∞` is `ENNReal.ofReal (Covariance.rayleighMax μ)`, with `toReal`
   equal to `Covariance.rayleighMax μ`.

The name `lambdaMax` follows the manuscript's notation. The current Lean eigenvalue theorem is
limited to nontrivial finite-dimensional spaces; the infinite-dimensional covariance compactness
argument has not been formalized. Mathematically, finite second moment makes a Hilbert probability's
centered covariance positive and trace-class: apply
[Blanchard--Bousquet--Zwald, Theorem 2.1](https://doc.ml.tu-berlin.de/publications/publications/BlaBouZwa06.pdf#page=8)
to the centered random vector. Compact self-adjoint spectral theory then gives attainment of its
Rayleigh maximum on any nontrivial Hilbert space, including when the covariance is zero.
In dimension zero there are no nonzero vectors or eigenvectors; the empty Rayleigh supremum and
`lambdaMax` are defined to be `0`. This makes the certificate uniform in `D : ℕ`, including `D = 0`.

On a finite-dimensional Euclidean space, `MemLp id 2 μ` is the coordinate-free assumption of a
finite second moment that makes the centered covariance matrix finite.

## Proof and module boundary

- `formalization/FunctionalInequalities/Poincare/SmoothTest/Basic.lean`: admissibility, energy, fixed constants, and
  the optimal extended Poincaré constant.
- `formalization/FunctionalInequalities/Poincare/SmoothTest/Linear.lean`: linear tests, extended Rayleigh quotients,
  centered covariance, the finite-dimensional eigenvalue bridge, and the fixed/optimal bounds.
- `solutions/LemLinearTestLower.lean`: the sole Issue #2 certificate, directly combining the
  reusable Rayleigh and covariance lower bounds.
- `formalization/FunctionalInequalities/Poincare/Product/Geometry.lean`: transported product law and proved
  smoothness/gradient identities.
- `formalization/FunctionalInequalities/Poincare/Product/Variance.lean`: L2/Fubini variance decomposition
  and the two-factor variance inequality.
- `formalization/FunctionalInequalities/Poincare/Product/Admissible.lean`: finite-energy bounds and a.e.
  admissibility of sections.
- `formalization/FunctionalInequalities/Poincare/Product/Tensorization.lean`: the two proved public theorems.
- `solutions/LemPoincareTensorization.lean`: the sole Issue #6 certificate, directly combining
  both product bounds, with a typed Euclidean application check including dimension zero.
- `formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean`: measure-preserving coordinate
  lifts and exact transport under real linear isometry equivalences.
- `formalization/FunctionalInequalities/Poincare/Product/Reverse.lean`: binary coordinate reverse
  bounds and optimal-constant equality.
- `formalization/FunctionalInequalities/Poincare/FiniteProduct/Geometry.lean`: the dependent
  `PiLp 2` product law, coordinate projections, reindexing, and Option splitting.
- `formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean`: finite
  fixed-constant tensorization, reverse bounds, optimal equality, and boundary consequences.
- `solutions/LemPoincareFiniteTensorization.lean`: the sole Issue #7 certificate, retaining the
  45 public interface checks plus eight Euclidean families and six boundary applications.
- `formalization/FunctionalInequalities/Poincare/Gaussian/Density.lean`: real Gaussian density
  differentiation, tail identities, and the density/integrability bridge.
- `formalization/FunctionalInequalities/Poincare/Gaussian/Hardy.lean`: finite-interval
  FTC--Cauchy, Tonelli rearrangements, and the left/right Gaussian energy estimates.
- `formalization/FunctionalInequalities/Poincare/Gaussian/Real.lean`: the valid Gaussian
  Poincaré constant, the identity-test lower bound, and sharp optimal equality.
- `solutions/LemPoincareGaussianOneDimensional.lean`: the sole Gaussian node certificate,
  retaining all 20 public interface checks and seven typed boundary/normalization applications.
- `solutions/GaussianAxiomAudit.lean`: a default-build `#guard_msgs` check fixing the Gaussian
  certificate's transitive axiom set to `propext`, `Classical.choice`, and `Quot.sound`.

Compilation is enforced by `lake build`, whose default targets include all current root-level
certificates. Among the original certificates, the linear-test certificate covers the two lower-bound conclusions above; the
two tensorization certificates cover the binary and finite product results; the Gaussian
certificate covers its fixed and optimal real-line constants. None proves the nonlinear parts of
Remark 3.8 or a multivariate Gaussian theorem.

## Repository certification

`research/a-series/ledger.yaml` connects `lem:linear-test-lower`,
`lem:poincare-tensorization`, `lem:poincare-finite-tensorization`, and
`lem:poincare-gaussian-one-dimensional` to their respective files under `solutions/`, all with
`status: proved` and `checked_by: lean`. The dependency-free command

```bash
python3 research/check_ledger.py
```

checks that each certificate exists below `solutions/`, names its node, contains no Lean escape
tokens in itself or its local imports, and belongs to a default Lake target. Its focused
regression tests run with:

```bash
python3 -m unittest discover -s research/tests -p 'test_*.py'
```

The checker establishes repository structure and provenance; `lake build` performs compilation,
and semantic agreement with the reference remains a separate review obligation.

The lifecycle and checker rules are specified in `research/ledger-schema.md`. New nodes may move
directly from `drafted` to `proved`; draft declarations may contain placeholders and must still
compile in the default build. The checker also accepts historical `frozen` snapshots as unproved
nodes. Only proved nodes may claim `checked_by: lean`; their entry points and local imports
undergo the static escape-token check. Semantic review and axiom inspection concern the current
statement and proof, without a separate mandatory freeze checkpoint. The metadata checker
validates the current state rather than approval history or signature stability.

`.github/workflows/lean.yml` runs on pushes and pull requests whose changed paths include
`**/*.lean`; non-Lean-only commits do not trigger it. It uses Python 3.12 without third-party packages and the official
`leanprover/lean-action@v1` to set up Lean in `formalization`. CI then enumerates the local
library and solution files' direct Mathlib imports, downloads those modules and their upstream
dependencies with `lake exe cache get`, and runs the complete default `lake build`. The action's
whole-`.lake` GitHub cache and unrestricted Mathlib fetch are disabled to avoid exhausting runner
disk space. `MATHLIB_NO_CACHE_ON_UPDATE=1` also prevents the dependency-update hook from fetching
all of Mathlib. This changes cache scope, not the compiled targets or proof checks.

## Contribution workflow (2026-09-03)

Work directly on `main`. Keep unfinished follow-up work as local, uncommitted changes and push
completed work directly to `origin/main` after its acceptance checks pass. Do not create feature
branches or pull requests for this workflow. Human statement review and the statement/proof role
separation still apply before proof work begins.

## Finite tensorization acceptance (2026-09-03; Issue #7)

The node `lem:poincare-finite-tensorization` is **proved** with `checked_by: lean`; the two
existing nodes retain their proved status and certificate signatures. Issue #7 adds
binary coordinate reverse bounds and optimal equality, dependent finite-product upper bounds,
and `constant (piMeasure μ) = ⨆ i, constant (μ i)` in `ENNReal`.

The finite Hilbert carrier is `PiLp 2 E`; its law is
`piMeasure μ := (Measure.pi μ).map (WithLp.toLp 2)`. Every factor is a Borel probability on a
complete real inner product space with second-countable topology. The finite fixed-constant
interface uses `C : ι → NNReal` and casts `Finset.univ.sup C` to `ℝ` for `Holds`. There is no
index nonempty assumption: empty products have fixed and optimal constant zero. Singleton
families, zero-dimensional factors and infinite optimal constants are included, without moment,
density, positive-dimension, finite-constant or attainment assumptions. Binary reverse bounds
explicitly assume probability of each factor separately.

The accepted modules are `Poincare/Transport`, `Poincare/Product/Reverse`,
`Poincare/FiniteProduct/Geometry`, and `Poincare/FiniteProduct/Tensorization`.
Their 45 retained public declarations have library implementations, recorded in
`research/explorations/2026-09-03-finite-tensorization-proofs.md`.
`solutions/LemPoincareFiniteTensorization.lean` contains the sole node certificate in the
`Solutions` default target. It also prints the 45 reusable public signatures and checks
eight Euclidean statement families and six concrete boundary applications through typed uses of
the general API. The eight former specialization wrappers and their duplicate obligations remain
removed. No proof placeholders remain in the accepted finite-product modules or certificate.

The `Project/` layer has been removed. Each proved node has one certificate directly combining
library results; Euclidean specializations are checked without another named forwarding theorem.
The reusable mathematics, binary signatures reviewed at the time, both retained certificate
signatures, and ledger statements were unchanged by that migration. See `formalization/README.md`
for the current source map.

The accepted signatures are preserved in
`research/decisions/2026-09-03-finite-tensorization-freeze.md`; final semantic and structural
acceptance is recorded in
`research/explorations/2026-09-03-finite-tensorization-acceptance.md`. The earlier review package is
`research/explorations/2026-09-03-certificate-deduplication.md`, including all 45 public
signatures and the full Euclidean check source. The original 53-name candidate remains in
`research/decisions/2026-09-03-finite-tensorization-candidate.md` as history. The source/API audit
and proof route remain in `research/explorations/2026-09-03-finite-tensorization-design.md`.
BGL supplies the upper-bound source correspondence and its finite iteration; coordinate lifting
independently supplies the reverse direction. No Dirichlet or Sobolev domain equivalence is
claimed. The publication commit and matching CI result are tracked in Issue #7 rather than
inferred from earlier local or remote runs.

The root `FunctionalInequalities.lean` aggregate imports the accepted
`Poincare/Product/Reverse`, `Poincare/FiniteProduct/Tensorization`, and
`Poincare/Gaussian/Real` modules. This finite-product
certificate is one component of the product-case KLS path; a one-dimensional log-concave bound
and Cheeger--Poincaré comparison remain separate obligations.

## Gaussian proof and acceptance (2026-09-04)

The node `lem:poincare-gaussian-one-dimensional` is **proved** with `checked_by: lean` after
human semantic and mathematical review. The two main interfaces assert, for every `m : ℝ` and
`v : NNReal`,
`Poincare.SmoothTest.Holds (gaussianReal m v) (v : ℝ)` and
`Poincare.SmoothTest.constant (gaussianReal m v) = (v : ENNReal)`. The test-domain definitions above are
used unchanged. The variance parameter v is the constant; v = 0 is the Dirac law at m.

The 20 declarations are all proved and split by responsibility. `Poincare/Gaussian/Density.lean`
contains 7 Mathlib-based density/calculus and integrability interfaces;
`Poincare/Gaussian/Hardy.lean` contains 9 interval, Tonelli and half-line energy interfaces; and
`Poincare/Gaussian/Real.lean` contains 4 fixed-upper-bound, identity-test-lower-bound and
sharp-constant interfaces. The right and left tail weights are v times the density, and the
half-line energy bounds add without an extra factor. Explicit density-weighted integrability
prevents real-integral totalization from replacing a necessary hypothesis. No global Lebesgue L²
condition on f′, test-function decay, or infimum-attainment assumption is added.
The two first-moment tail identities now quantify over every endpoint `t`; their former
endpoint-order premises were unused. Downstream half-line arguments obtain the required order
facts from their integration regions, so this is a strict API generalization rather than a
change of claim.

The manuscript's Gaussian covariance family supplies the positive centered one-dimensional
Poincaré claim. Arbitrary means, zero variance, the exact smooth finite-energy domain, and
the direct density route are local specifications; the source itself proves its upper bound
through Bakry–Émery and LSI. See the [source/API audit](research/explorations/2026-09-04-gaussian-poincare-design.md).

The proof first minimizes variance against the fixed center `f m`, applies FTC and
Cauchy--Schwarz on each finite interval, and uses nonnegative Tonelli plus the Gaussian
first-moment tails on the two half-lines. This yields the upper bound for positive variance;
the zero-variance case is proved separately from the Dirac-law identity. The identity test has
variance v and energy one and supplies the matching lower bound. Thus the result has neither a
missing factor nor an unstated positivity or boundary assumption.

The [reading guide](formalization/FunctionalInequalities/Poincare/Gaussian/README.md) gives the
mathematical meaning, proof flow, examples and file map. The earlier
[candidate package](research/decisions/2026-09-04-gaussian-poincare-candidate.md) and
[signature snapshot](research/explorations/2026-09-04-gaussian-poincare-signatures.txt) remain
append-only records of human statement review and do not override the current proved status.
`solutions/LemPoincareGaussianOneDimensional.lean` contains the single certificate
`Solutions.LemPoincareGaussianOneDimensional.certificate`, prints all 20 interfaces and checks
seven typed applications. It is compiled by the `Solutions` default target, and the root proved
aggregate exports `Poincare/Gaussian/Real`. The same default target compiles
`solutions/GaussianAxiomAudit.lean`, whose guarded output fixes the certificate's transitive
axiom set to `propext`, `Classical.choice`, and `Quot.sound`.

The review confirmed the exact source normalization and scope: arbitrary mean and zero variance
are local extensions, while the theorem concerns the existing globally smooth Gaussian-L²,
finite-gradient-energy domain only. It does not establish a closed Sobolev/spectral-gap domain
equivalence. The [Gaussian freeze](research/decisions/2026-09-04-gaussian-poincare-freeze.md)
records the approved contract; the
[acceptance record](research/explorations/2026-09-04-gaussian-poincare-acceptance.md) records the
proof closeout, final architecture and validation gates. Local certification is complete;
publication and remote CI status must still be reported from the actual final commit rather than
inferred from this review.

## Public naming

Use the mathematical object's namespace for its role: `Poincare.SmoothGradient.Intrinsic.constant`,
`Poincare.SmoothGradient.Ambient.constant`, and `Poincare.L2Energy.constant` distinguish the selected frontend,
ambient relaxation, and an optimizer parameterized by an energy. `Energy.SmoothGradient.Intrinsic.energy`
retains the intrinsic-affine construction in its definition. These names do not assert Cheeger
or Dirichlet identifications. Theorems on `KLS.LogConcave` support proof-receiver calls such as
`hμ.canonical_eq_literature`. Keep domain, integrability and boundary distinctions in theorem
names when they matter; see [the naming guide](research/naming.md).
