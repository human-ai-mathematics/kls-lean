# Source layout and proof organization review

Reviewed on 2026-10-27. Supporting infrastructure for BKL arXiv:2610.05474v1
Theorems 4.1 and 1.1, Letwin arXiv:2607.24164v1 Theorem 1.2 and Lemma 2.2,
and BB arXiv:1207.6128v1 Theorem 2.24(ii). Mathematical coverage, source
hypotheses, constants, normalization, dimensions and certificate states are unchanged.

The [consolidated proof organization map](consolidated-proof-organization-map.json)
records the current cross-family reuse, eight declaration-owner moves and the
individual disposition of all forty proof-fragment candidates. The previous
[Sard organization map](sard-organization-map.json) retains its coordinate-change
supports and direct prerequisites. The previous
[reuse and ownership map](cover-coordinate-gaussian-map.json) retains its separate
physical moves, exact name migrations and contract mergers.
The previous [Gaussian/wave map](norm-gaussian-wave-map.json),
[foundation organization map](foundation-organization-map.json),
[mathematical organization map](mathematical-organization-map.json) and
[layout map](source-layout-map.json) retain their respective migrations.
The [2026-10-29 layout map](2026-10-29-layout-map.json) records the path-only moves of
32 library modules into family directories and of the 179 audit clients that sat directly in
`research/audits/` into per-family directories, with the edited records and validation inputs.
The [2026-10-29 round-2 layout map](2026-10-29-layout-round2-map.json) records the path-only
moves of 91 library modules into the Newtonian, iteration, heat-semigroup and moment-measure
family directories and three content-only module merges, with the edited records and validation inputs.
The [2026-10-29 round-3 layout map](2026-10-29-layout-round3-map.json) records the path-only
moves of 22 library modules: 20 into the Convex `Legendre/` and `SecondOrder/` and the iterated-derivative
`Schauder/` and `Bootstrap/` family directories, `Convex/HalfBall` to `Analysis/Elliptic/` and the Newtonian
`Schauder/PoissonFreezing` to `IteratedDerivative/Schauder/`, with the edited records and validation inputs.
The [2026-10-29 round-4 layout map](2026-10-29-layout-round4-map.json) records the path-only
moves of 12 library modules: the smooth-domain layer from `KLS/Geometry/` to `Analysis/SmoothDomain/`,
`LinearAreaFormula` to `Analysis/Vector/`, the radial cutoff bound to `Analysis/Cutoff/RadialLipschitz`, the radial
kernel chain to `Newtonian/Kernel/Radial/` and `GaugeCone/Normalization` to `GaugeCone/PrescribedAtom`, with the edited
records and validation inputs. It also records the decision not to split the remaining `KLS/` families: they
depend on the KLS target statement and on each other.
The [2026-10-29 Letwin/CEK readability map](2026-10-29-letwin-readability-map.json) records the
section reorganization of six Lean files, two declaration-owner moves and the complete declaration list of
the affected modules (see [below](#letwincek-readability-batch-2026-10-29)).
The [completed Letwin delivery map](completed-letwin-delivery-map.json) records the release scope: the 39
auxiliary library files and 55 audit clients of the superseded variational route that are not part of the
release snapshot (see [below](#completed-letwin-delivery-scope-2026-10-29)).
Old paths in those maps are migration inputs. The
[compiler API directory](../../formalization/API.md) gives current owners.

## Letwin/CEK readability batch (2026-10-29)

**Status: source/interface accepted; the final verification result is governed by the task's
`verification.json` (see Evidence below).** The batch supports Letwin
arXiv:2607.24164v1 Lemma 2.2, Theorem 2.5 and their source consumers, and CEK arXiv:1304.0630v1
Theorem 2. It changes no mathematics: public names, statements, binder names, order and kinds, universes,
hypotheses, constants, dimensions, proof bodies, proof states, certificates and lemma-map relations are
unchanged. No module is moved, no import changes, and no alias, wrapper, structure or typeclass is added.

The [readability map](2026-10-29-letwin-readability-map.json) lists every declaration of the six modules
(101 existing declarations: 64 public API, 35 private, and two compiler-generated equation theorems,
`FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn.eq_1` and
`FunctionalInequalities.Probability.Stein.hessianMatrix.eq_1`, which are non-private but not public API).
Each entry gives the old and new source, the section and the kind of change.

**Section adjustments.**

- **`KLS/Letwin/MomentMap.lean`.** Four private blocks are hoisted verbatim, in their relative order, ahead
  of the source section; each keeps its own weaker binders:
  - the given-potential calculus helper;
  - the `Translation` section;
  - the bounded-support helper;
  - the coercion helper.

  Their code references none of the nine public source theorems. The nine public theorems then form one
  named section, `BoundedOpenConvexSource`:
  - the Lemma 2.2 source-class hypotheses `hn … hiso` are declared once, in their original order and
    binder kinds;
  - each theorem has its own `include … in`;
  - finite-potential (`φ`) and extended-real-potential (`ψ`) hypotheses stay in the theorem headers.

  The three Hessian helpers and the strong-class `exists_centered_regular_potential` are unchanged.
- **`KLS/Letwin/SteinKernel.lean`.** The same section and variable block are added in
  `Probability.MomentMeasure`, with per-declaration includes. They cover the private given-potential helper
  (which already had the full prefix) and the three public Stein-kernel producers. The strong-class section
  `RegularClass` and `sharp_smooth_stein_of_trace_bound` are unchanged.
- **`KLS/CEK/Uniqueness.lean`.**
  - One context replaces the duplicated `noncomputable section`/namespace/`open`/`E` structure blocks.
  - The scalar `EReal` helper precedes the `E` block, and its redundant `omit` is removed.
  - Named sections `FinitePotential` and `EssentiallyContinuousPotential` keep the original declaration
    order.

The section variables spell out `EuclideanSpace ℝ (Fin n)` instead of these files' local notation
`E => EuclideanSpace ℝ (Fin n)`. Under Lean 4.33, writing this particular `E` (a notation over the
section variable `n`) in these section-variable types was observed to elaborate the affected
declarations to `sorry`. This was found in this batch's attempts and a minimal reproduction recorded in
the task history; no broader claim about notations is made. The expansion is the same term, so
elaborated types are unaffected, and theorem headers and proofs still use `E`.

**Declaration-owner moves** (full names, exact types and proof bodies unchanged; old copies deleted):

| Declaration | From | To |
|---|---|---|
| `FunctionalInequalities.Analysis.bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef` | `KLS/Letwin/MomentCalculus` | `Analysis/BakryEmery/Hessian/Coordinates` |
| `FunctionalInequalities.Analysis.logDetHessian_std_eq_log_det_hessianMatrix` | `KLS/Letwin/MomentCalculus` | `Analysis/BakryEmery/MongeAmpere` |

Each is placed in a named section with `variable {n : ℕ}` and the local notation `E`, which adds three
private notation constants per owner. The log-det bridge sits outside the generic-`E` `BakryEmery` context.
The lower owners import no paper module, and consumers reach both bridges through the existing chain
`MomentCalculus → Hessian.Trace → MongeAmpere → Coordinates`.

**Namespace naming: reviewed only, nothing migrated.** Producer conclusions about moment potentials stay in
`Probability.MomentMeasure`; Stein conclusions could belong to `Probability.Stein`; generic Hessian
calculus belongs in `Analysis`. Consistency alone does not justify API churn, so the regular-class and
literal-class distinctions and all public names are retained. A future producer migration needs its own
declaration-by-declaration ownership review.

**Evidence.** The independent source/interface acceptance is recorded in
`build/history/2026-10-29-letwin-style-20261029T091203Z/source-interface-acceptance.json`. The checks
were made against the frozen pre-batch compiled view (1219 artifacts, zero hash drift):
- a production `lake --wfail build` and an exact replay-scope build (1127 modules), both with exit code 0;
- a strict `Expr.equal` comparison, with binder names and annotations included:
  - all 7086 public declarations and all 12557 existing local declarations are identical;
  - there are exactly the two expected owner moves;
  - the only additions are six reviewed private syntax, macro and unexpander constants from the two
    local `E` notations, each accepted by its full name;
- 83 proof and definition bodies, which are textually unchanged.

The worker's strict compiles, narrow-import clients and axiom audit are supporting evidence only. The
final verification result is governed by
`build/history/2026-10-29-letwin-style-20261029T091203Z/verification.json`. The batch is fully accepted
only when that file reports `status: passed`.

## Completed Letwin delivery scope (2026-10-29)

The release candidate is rebuilt from `origin/main` rather than from the unpublished local commit
`04ef798`. It keeps every published module and public declaration owner with its import closure, and adds
the completed Letwin/CEK results, Proposition 2.8 for full-dimensional laws and the proved Klartag supports.
That gives 798 library modules, each byte-identical to the verified primary checkout. The
[delivery map](completed-letwin-delivery-map.json) lists the selection rule and roots.

**Not copied:**
- 39 library files used only by the superseded auxiliary variational route to Letwin Lemma 2.2 (Alexandrov
  sections, Caffarelli W²,p contacts, domain Monge–Ampère measures, Dirichlet and gauge-cone references,
  Pogorelov, CNS elliptic and log-radial barriers);
- the 55 audit clients that import them.

No retained file imports an excluded module, and no excluded path is the owner of a module published on
`origin/main`.

**Metadata changes:**
- The 52 Blueprint statements formalized only in those files keep their text, hypotheses and `\uses`, but
  lose `\leanok` and the excluded `\lean` names.
- Mixed statements keep their retained declarations as partial supports, not as completion.
- The register and the smooth-route record no longer cite excluded declarations.
- Their mathematical gaps remain open; they are not formalization targets.

This is a scope selection. It changes no statement, proof body, namespace or certificate. Earlier migration
maps and dated records below keep their original paths. Rows and paragraphs that describe excluded files are
marked as outside the release snapshot.

## Public statement mergers

The [public statement merger map](public-statement-merge-map.json) records six
duplicate-statement groups, their full old/replacement names and three separate
declaration-owner moves. Euclidean functional expansions and bilinear norm bounds
share the existing Euclidean-coordinate owner. Generic Hölder cutoffs own their
real-distance conversion and no longer import Newtonian kernels. BKL row
contraction uses the generic Tensor theorem; time-derivative consumers use the
earlier generator limit. Gradient pairing uses pinned Mathlib's
`inner_gradient_left`. Removed names have no compatibility aliases.

The C² compact-multiplier weak-generator identity retains its exact public type
as a corollary of the existing C¹ producer. Both names and the separate primed
identity remain. No hypothesis, constant, normalization, dimension range, target
or certificate entry, paper coverage or proof status is changed. Maintained
clients check legacy telescopes, narrow imports and removed-name absence.

## Temperate integrability and same-file private mergers

The [temperate/private merger map](temperate-private-merge-map.json) records six
private integrability declarations replaced by the single generic
`Probability.integrable_of_hasTemperateGrowth`, three same-file private pairs,
and two private-to-public proof inlines. Existing public names and types remain.
The shared L1 result uses Mathlib's `SecondCountableTopologyEither`: scalar
targets retain the original unrestricted-source scope, while vector callers
retain their finite-dimensional-source contracts. No completeness of the target,
probability normalization, finite-measure instance or restricted exponential radius
is added. The existing L2 statement is unchanged.

Bochner tensor gradient components, Gaussian smoothing density integrability and
the zero-time inverse derivative each keep one existing private proof. The public
smooth-test/local-slope energy and BKL suspension cumulant-entry statements own
their proofs directly. No production module or compatibility alias is added;
mathematical coverage, constants, dimensional scope and certificate status stay
unchanged. Maintained clients retain the original scalar/vector contracts and
check the lower dependency direction and removed-private-name absence.

## Cross-file private mergers

The [cross-file private merger map](cross-file-private-merge-map.json) records
three groups and four removed private names. Gradient-image support uses the
existing `Analysis.gradient_le_increment` in `Convex/Subgradient/Basic`.
Regular-law centering uses `Probability.memLp_id_two_translateLaw` in
`Probability/Transport`, whose translated second-moment contract needs only a
normed additive group and its Borel structure. The gradient support retains its
complete real inner-product space hypothesis.

The L² identity `L2.norm_sq_eq_integral_norm_sq` belongs in the existing
`L2/Pairing` owner beside the energy and inner-product identities. Componentwise
Parseval and the temperate heat model import this lower owner. The identity
retains arbitrary measures, arbitrary measurable sources and real inner-product
targets without completeness, finite dimension or separability assumptions.
No production module, compatibility alias or reverse application import is added.

Maintained clients check the original contracts, named arguments, lower imports,
all four removed private names and existing public consumers. Raw public types
and non-theorem definition closures are compared separately from theorem proofs;
strict compilation, standard-axiom audits and local-module kernel replay check
the proofs. Mathematical coverage, constants, dimensional scope and certificate
states are unchanged.

## Consolidated shared proof organization

The review covers every production module, public/private declaration names,
family placement, dependency direction and exact cross-file proof fragments.
Forty original candidates have concrete repairs. Seven residual matches are
local frontend setup or retain distinct scalar/vector, zero-dimensional or
compact/temperate scopes; their individual explanations are in the current map.
A second scan normalizing local hypothesis names finds only the two already
reviewed heat frontend setup blocks. These scans do not certify the absence of
every possible semantic duplication.

- `MeasurableCover` owns subordinate measurable partitions, independently of
  measure finiteness; `MetricCover` remains measure-free. Scalar/vector graph,
  local slicing and regular coarea consumers share the construction.
- `Lipschitz/ZeroDerivative` owns small-Lipschitz covers. Local vector coarea
  owns chart slice measurability; Regular owns global patching and assembly from
  actual null critical fibres. Zero-derivative and rank-deficient producers
  remain distinct. Scalar Eilenberg bounds specialize the existing vector bound
  at the exact real unit-ball volume 2, retaining zero and infinite cases.
- `BakryEmery/Tilt/Basic` owns the shifted-generator integral algebra and the
  Taylor tensor successor rule. Cumulant owns the shared third-moment contraction.
  Compact and temperate-growth integrability producers keep their separate inputs.
- `Cheeger/MinkowskiContent`, `DistanceCutoff` and `Equality` own generic
  measurable-majorant estimates, integrated cutoff error and smooth-test control
  of the infimum. Local-slope and stability frontends reuse those properties.
- `Semigroup/Generated/TimeDerivative` owns measure-free backward orbit
  derivatives, continuity and zero-time convergence. HeatSemigroup owns the AE
  slope bound, while WeakGamma and regularized-norm derivative rules stay separate.
- Existing probability, L2, metric-BV, tensor and posterior owners supply norm
  exponential radius monotonicity, support under a tilted pushforward,
  subsingleton constants, cutoff slopes, finite-coordinate sums and fixed-dimension
  standardization. No result-bearing framework or compatibility alias is added.

## Sard coordinate changes and prerequisites

`Sard/CoordinateChange` owns shared coordinate-replacement regularity, its
differential and its continuous-linear equivalence. Three properties are public
for the two actual chart consumers; the one-use injectivity support is private.
Finite, smooth and analytic regularity orders use the same regularity proof.
Eight old private support copies are removed. The zero-hyperplane identities
in Chart and Smooth use Mathlib's `Fin.insertNth_removeNth` directly.
The finite global graph and smooth open-parameter chart retain distinct contracts.
The original linear-only `PiCoordinates` module stays unchanged.

Chart still imports its local extension and inverse-function prerequisites;
its narrow client excludes Smooth and QuadraticCover. Disk imports its actual
Mathlib calculus, finite-dimensional and real inner-product prerequisites,
preserving the exact original `IsDisk` and `FlatAlong` definition values.
Sharp imports QuadraticCover directly for the oscillation-cover theorem.
Its finite-regularity proof chain no longer loads the separate smooth route.
MorseVanishing still assembles the Chart and Disk owners explicitly.

Smooth's source comments now describe its proved smooth descent and point to
the separately proved sharp Sard and regular-value results. This corrects
comments without changing theorem statements, proof status or paper coverage.

## Shared cover, coordinate and moment proofs

- `Probability/ExponentialMoments/Norm.integrable_norm_pow_of_exp` is the single
  finite-measure norm-moment proof. Borell, intrinsic and Stein consumers use it
  directly. The probability-only copy is removed, with its exact probability
  contract compiled independently; this is a specialization merger, not a rename.
- `Hausdorff/Content.exists_cover_familyCost_lt` supplies the scalar and vector
  slicing covers. Both ten-line copies are removed. The existing `familyCost`
  retains the Nonempty guard for empty pieces, arbitrary real gauges and every
  positive scale. The removed `S` argument becomes the existing `A` argument;
  universe alpha-renaming and definitional unfolding are explicit merger facts.
  The vector layer does not import scalar slicing.
- `Analysis/PiCoordinates` owns finite-product nonzero-functional detection.
  Smooth, finite-Ck and planar Sard charts share it. The product norm is distinct
  from the Euclidean-coordinate tools; finite and infinite chart regularity
  contracts remain separate, including empty finite indices where applicable.

## Gaussian and linear-image owners

- `Probability/Gaussian/CharacteristicFunction` owns the characteristic function
  and scaled-standard-law identification, independently of KLS and Poincare.
  The inverse variance parameter remains positive and the variance `1/(2s)`;
  dimension zero remains included.
- `Poincare/Gaussian/Multivariate` owns the radial-Gaussian smooth-test bound.
  Gaussian smoothing owns convolution and optimum assembly. The three public
  contracts retain their exact types under explicit namespace/name migrations.
- `Probability/Moments.memLp_four_map_linear` owns linear-image fourth moments,
  shared by Letwin's regular-class and Gaussian quadratic-variance consumers.
  Its original finite-dimensional inner-product telescope remains explicit;
  the proof uses the generic pinned Mathlib map/composition facts.

## Operator norms, Gaussian laws and shared analytic proofs

- `IteratedDerivative/OperatorNorm` owns eight private scoped instances at the
  concrete second/third spatial derivative and scalar-time derivative types.
  Eleven consumers explicitly open `DerivativeNorms`; 46 public numbered or
  anonymous implementation aliases are removed. All old and new providers
  equal the original nested CLM operator-norm instances by `rfl`.
- `Probability/Gaussian/Kernel` owns the real/extended kernels, normalization
  and centered law. `Probability/Gaussian/Moments` owns the Laplace transform,
  mean, directional second moment, variance, fourth moment and bounded
  Lipschitz C1 integration by parts. Neither module imports KLS. Definitions
  remain total in `s`; the probability/moment theorems retain `s > 0`, variance
  `1/(2s)` and dimension zero. Gaussian smoothing owns convolution densities
  and their moments. BKL’s three standard-Gaussian endpoints specialize the
  shared results at `s = 1/2`, with one local normalization identification.
- `WaveSplitting/Basic`, `Energy`, `Stability` and `FlowDerivative` share
  coefficient-pairing smoothness/support, the component-jet integral and the
  exact step-derivative/residual identity. Higher energy/time-average modules
  consume these properties. Component support alone remains sufficient for
  coupling support; finite indices and all original test/measure scopes remain.
- `Analysis/UpperSemicontinuity` owns multiplication of an upper semicontinuous
  real function by a strictly positive continuous real weight. Its two density
  consumers share the same proof on arbitrary topological source spaces.

## Shared foundations

- `L2/Pairing` owns compact-continuous scalar multiplication of L2 fields.
  Three heat-chain-rule/reverse-Poincare/self-improvement copies are removed.
  The shared theorem needs only measurable opens and finiteness on compact
  sets; its maintained Lebesgue client has infinite total measure.
- `Cutoff/Profile` owns compact support after composition with a potential
  having a compact sublevel. The strong and weak inverse-Hessian cutoffs
  use the same topological support criterion, without convexity or smoothness.
- `BakryEmery/WeakHessian` owns the essentially bounded total Hessian-entry
  core. The CEK and generic weak-evolution consumers share it; the existing
  L2 API also uses this bound. No C2 or equation premise is introduced.
- `WaveSplitting/Basic` owns `State.ext` and its generated `ext_iff` companion
  for arbitrary types and indices.
  Seven private extensionality copies are removed. Four private ENNReal power
  wrappers are replaced by pinned Mathlib `orderIsoRpow`, its generated apply
  lemma and `OrderIso.map_iSup`. Simp uses inline congruence locally, so it
  exports no upstream-named congruence helper; no wrapper module is added.
- The earlier local-extension, exponential-moment, L2 convergence, cutoff,
  tensor, operator and Taylor-field owners remain in place.

## Responsibilities and dependency direction

| Family | Mathematical responsibility |
| --- | --- |
| `Convex/Subgradient/Basic` | Supporting inequalities, global/domain images, elementary comparison, closed graph and a pointwise slope bound; no Rademacher or Legendre layer |
| `Subgradient/Existence` | Actual support existence and uniform compact-local slope bounds |
| `Subgradient/Image` | Affine transport and compactness of domain images |
| `Subgradient/Regularity` | Differentiability, continuous support selection and C1 from unique supports |
| `Subgradient/Measure` | Almost-everywhere differentiability and supporting-slope uniqueness |
| `Subgradient/Taylor` | Quadratic expansion from support expansion |
| `Subgradient/Stability` | Supporting images under locally uniform convergence |
| `Subgradient/Piecewise` | Support transport and convex gluing across a ball (superseded auxiliary route; not in the release snapshot) |
| `Convex/Viscosity/Touching` | C2 touching tests, Taylor bounds and lower-quadratic-test transfer |
| `Viscosity/Pointwise` | Equation identification at an actual quadratic expansion |
| `Viscosity/Mollification` | Mollified log-determinant inequality |
| `Viscosity/Equation` | Almost-everywhere equation identification |
| `BakryEmery/Hessian/Composition` | Coordinate chain derivatives and compact-local weak composition before any inverse-Hessian PDE application |
| `IntegrationByParts/WeakHessian/Flux` | First RHS weak derivatives, unweighted flux and trace forcing |
| `WeakHessian/Weighted` | Weighted curvature/Gram evolution identity |
| `WeakHessian/Testing` | Extension to bounded compact weak tests |
| `WeakHessian/Directional` | Directional weak subsolution and rough square tests |

Basic subgradient clients do not load support existence, C1, AE uniqueness or
stability producers. Touching-only clients do not load mollification or AE
identification. Hessian composition does not import inverse-Hessian integration
by parts. Actual affine-image, stability, Dirichlet-envelope, log-det and
Hessian-bound consumers import the owning layers they use; the Dirichlet-envelope
consumer belongs to the excluded auxiliary development.

The public namespaces and statements are preserved across file moves.
The shared ball slope bound is public in Basic because existence and stability
both use it. Lower-quadratic-test transfer stays beside its private touching
support rather than exposing that one-use implementation solely for a split.
No result-bearing structure, compatibility module or old-name alias is added.

## Naming and interfaces

The unconditional names `eventually_measure_closedBall_ne_zero` and
`cumulant_eq_taylorComp` replace their former `_cond` versions. Their complete
statements and universes are identical. Genuine conditional operations and
numerical mathematical constants, including `153`, retain their distinctions.

The compiler index contains **6,750 public declarations across
802 production modules**. All **6,732 pre-existing public interfaces**
retain exact raw types, universe parameters, non-proof definition values and
rendered binders/kinds/safety/partiality. Eight existing declarations move only
to their mathematical owners under the explicit map; full names stay unchanged.
Two automatically generated congruence lemmas have different first-consumer
owner provenance, with identical raw types and values, recorded separately.
Eighteen shared properties are added. Prior renames and equivalent-contract
mergers retain their separate records.

The retained definition closure contains **7,469 local declarations**,
including **737 private/internal supports**.
No expression, instance or proof-witness normalization is used. Theorem proof
bodies are excluded from interface fingerprints and receive separate axiom and
kernel checks.

## Scope and verification

Shared concrete skew-coefficient and drift-point models live in
`examples/EllipticDrift`, registered in the existing Examples build and replay
scope. The standalone elliptic audits, now excluded from the release snapshot with
their auxiliary library modules, imported this model instead of other audit modules. Seven original declarations keep their exact types,
universes, definition values and parameter signatures, with proof blocks moved
verbatim. Checker scripts remain unchanged; the production CNS/elliptic sources are
not part of the release snapshot.

Four additional strict narrow-import clients exercise the new partition,
negative-radius exponential, subsingleton-L2, finite-coordinate and generic
backward-Hilbert-orbit properties. Earlier maintained clients retain their
separate scopes and import guards. All current validation inputs are maintained
in [SourceLayout](../audits/SourceLayout/).
The final full local verifier checks metadata, every independent client,
standard-axiom dependencies and current local/vendor-module kernel replay.
Pinned compiled Mathlib imports remain trusted. Interface fingerprints exclude
theorem proof bodies and do not independently certify every paper statement.

In the excluded auxiliary development, the generated Dirichlet reference was C1 inside
the domain, and the given-classical Pogorelov estimates assumed interior C4 and ambient C2
at every closure point, with their equation, positivity, sign and boundary inputs. The mathematical
completion boundary in [HANDOFF.md](../../HANDOFF.md) is unchanged.

Current owner/evidence references, API/module navigation and generated progress
views follow the new layout. Progress generation uses a temporary index;
original staging and unrelated work are preserved. No commit, push or remote
CI is part of this maintenance.
