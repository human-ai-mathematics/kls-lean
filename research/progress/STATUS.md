# Formalization progress register

[Progress hub](README.md) · [Route diagrams](README.md#proof-progress-tree)

**75 local Blueprint nodes · 24 registered Lean certificates.**

Generated from staged canonical records. These are recorded proof/definition statuses,
not a fresh Lean run or a remote CI receipt. A missing local proof means only that this
register does not certify it; unregistered auxiliary progress appears in the diagram directory below.

**✓** Recorded Lean proof or implemented definition · **○** Not recorded as complete.
Upstream status is shown only where an explicit upstream mapping exists; no mapping is inferred
from a similar title. Upstream `proved` does not mean Lean-proved.

## Local nodes

| Node ID | Upstream / mathematical record | Our Lean record | Certificate / statement |
| --- | --- | --- | --- |
| `ass:cmh-recovery-envelope` | Upstream: open | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L206) |
| `ass:tight-prefix-carleson` | Upstream: open | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L41) |
| `ass:weighted-package` | Upstream: refuted | — Excluded: refuted | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L87) |
| `cert:ambient-intrinsic-comparison` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L96) · [Lean certificate](../../solutions/LemAmbientIntrinsicPoincareComparison.lean) |
| `cert:binary-tensorization` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L35) · [Lean certificate](../../solutions/LemPoincareTensorization.lean) |
| `cert:finite-tensorization` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L52) · [Lean certificate](../../solutions/LemPoincareFiniteTensorization.lean) |
| `cert:gaussian-one-dimensional` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L70) · [Lean certificate](../../solutions/LemPoincareGaussianOneDimensional.lean) |
| `cert:legacy-relaxed-comparison` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L111) · [Lean certificate](../../solutions/LemLegacyRelaxedPoincareComparison.lean) |
| `cert:linear-test-lower` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L21) · [Lean certificate](../../solutions/LemLinearTestLower.lean) |
| `conj:kls` | Upstream: open | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L176) |
| `cor:absolutely-continuous-relaxation-two-cheeger` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L92) · [Lean certificate](../../solutions/CorAbsolutelyContinuousRelaxationTwoCheeger.lean) |
| `cor:ambient-intrinsic-constant-equality` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L292) |
| `cor:cmh-recovery-sequence-suffices` | Upstream: conditional | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L219) |
| `cor:conditional-fiber-twelve-bound` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L459) · [Lean certificate](../../solutions/CorConditionalFiberTwelveBound.lean) |
| `cor:tight-window-consumption` | Upstream: proved | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L55) |
| `def:affine-poincare-constant` | Local classification: definition | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L297) |
| `def:affine-support-intrinsic-law` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L64) |
| `def:conditional-fiber-form` | Local classification: definition | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L259) |
| `def:extended-energy` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L25) |
| `def:intrinsic-affine-energy` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L94) |
| `def:isoperimetric-cheeger-scale` | Local classification: definition | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L103) |
| `def:isotropic-law` | Local classification: definition | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L246) |
| `def:l2-energy-poincare-constant` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L84) |
| `def:l2-mean-variance` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L11) |
| `def:legacy-smooth-test-poincare` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L9) |
| `def:literature-poincare-constant` | Local classification: definition | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L153) |
| `def:log-concave-law` | Local classification: definition | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L18) |
| `def:poincare-test-family` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L71) |
| `def:preenergy-relaxation` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L37) |
| `def:selected-canonical-frontend` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L116) |
| `def:smooth-gradient-preenergy` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L12) |
| `def:smooth-gradient-relaxation` | Local definition; no upstream mapping | ✓ Definition implemented | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L39) |
| `lem:affine-poincare-translation-invariance` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L408) · [Lean certificate](../../solutions/LemAffinePoincareTranslationInvariance.lean) |
| `lem:ambient-intrinsic-covariance` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L260) · [Lean certificate](../../solutions/LemAmbientIntrinsicCovariance.lean) |
| `lem:conditional-fiber-energy-comparison` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L387) · [Lean certificate](../../solutions/LemConditionalFiberEnergyComparison.lean) |
| `lem:conditional-fiber-form` | Upstream: proved | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L308) · [Lean certificate](../../solutions/LemConditionalFiberForm.lean) |
| `lem:covariance-core-closure` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L52) · [Lean certificate](../../solutions/LemCovarianceCoreClosure.lean) |
| `lem:covariance-test-core-density` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L14) · [Lean certificate](../../solutions/LemCovarianceTestCoreDensity.lean) |
| `lem:finite-energy-factor-poincare` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L241) |
| `lem:logconcave-intrinsic-absolute-continuity` | Local classification: published | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L69) · [Lean certificate](../../solutions/LemLogConcaveIntrinsicAbsoluteContinuity.lean) |
| `lem:mutual-test-approximation-relaxation` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L223) |
| `lem:preenergy-poincare-relaxation` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L121) |
| `lem:relative-perimeter-cheeger-infimum` | Local classification: local_argument | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L170) |
| `lem:relative-perimeter-smoothing` | Local classification: local_argument | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L128) |
| `lem:smooth-tests-affine-restriction-extension` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L246) |
| `obs:dirac-raw-energy` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L9) |
| `obs:normal-direction-raw-energy` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L129) |
| `prop:spectral-sufficiency` | Upstream: conditional | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L140) |
| `prop:weighted-spectator-obstruction` | Upstream: proved | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L101) |
| `q:conditional-fiber-frame` | Upstream: open | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L513) |
| `q:mm-spectral-occupation` | Upstream: open | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L128) |
| `q:smooth-gradient-raw-core-agreement` | Local classification: conjectural | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L159) |
| `thm:affine-covariance-relaxation-closed` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L347) · [Lean certificate](../../solutions/ThmAffineCovarianceRelaxationClosed.lean) |
| `thm:affine-isotropic-reduction` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L460) · [Lean certificate](../../solutions/ThmAffineIsotropicReduction.lean) |
| `thm:ambient-intrinsic-relaxation-equality` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L266) |
| `thm:borell-logconcave-density` | Local classification: published | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L95) · [Lean certificate](../../solutions/ThmBorellLogconcaveDensity.lean) |
| `thm:cmh-recovery-affine-poincare-bound` | Local classification: local_argument | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L176) |
| `thm:compact-borell-logconcavity-equivalence` | Local classification: published | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L33) · [Lean certificate](../../solutions/ThmCompactBorellLogconcavityEquivalence.lean) |
| `thm:intrinsic-affine-constant-order` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L139) |
| `thm:intrinsic-affine-energy-closed` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L103) |
| `thm:intrinsic-l2-equivalence` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L76) |
| `thm:klartag-density-frontend-identification` | Local classification: local_argument | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L133) |
| `thm:l2-energy-holds-order` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L101) |
| `thm:legacy-canonical-constant-comparison` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L34) |
| `thm:legacy-relaxed-holds-equivalence` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L13) |
| `thm:logconcave-cheeger-poincare-comparison` | Local classification: published | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L180) |
| `thm:one-dimensional-logconcave-poincare` | Local classification: published | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L539) · [Lean certificate](../../solutions/ThmOneDimensionalLogConcavePoincare.lean) |
| `thm:quadratic-relaxation-closed` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L51) |
| `thm:selected-literature-constant-equivalence` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L81) · [Lean certificate](../../solutions/ThmSelectedLiteratureConstantEquivalence.lean) |
| `thm:smooth-gradient-quadratic-dense` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L25) |
| `thm:smooth-gradient-raw-core-agreement-density` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L171) · [Lean certificate](../../solutions/ThmSmoothGradientRawCoreAgreementDensity.lean) |
| `thm:smooth-gradient-relaxation-closed` | Local Lean result; no upstream mapping | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L48) |
| `thm:smooth-gradient-relaxation-dirichlet` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L25) · [Lean certificate](../../solutions/ThmSmoothGradientRelaxationDirichlet.lean) |
| `thm:smooth-gradient-relaxation-two-cheeger` | Local classification: unknown | ○ Pending | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L65) |
| `thm:smooth-lipschitz-constant-equivalence` | Local classification: local_argument | ✓ Proof recorded | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L58) · [Lean certificate](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean) |

## Pending-node dependencies and infrastructure

Dependencies below are statement dependencies, not a claim that each dependency is open.
Infrastructure gaps are the recorded assessment and may cover a broader parent task.

### `ass:cmh-recovery-envelope`

Dependencies: none recorded.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `ass:tight-prefix-carleson`

Dependencies: none recorded.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `conj:kls`

Dependencies: `def:literature-poincare-constant`, `def:log-concave-law`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `cor:cmh-recovery-sequence-suffices`

Dependencies: `ass:cmh-recovery-envelope`, `def:affine-poincare-constant`, `lem:affine-poincare-translation-invariance`, `thm:affine-isotropic-reduction`, `thm:cmh-recovery-affine-poincare-bound`.

Retained assumptions: `ass:cmh-recovery-envelope`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `cor:tight-window-consumption`

Dependencies: `ass:tight-prefix-carleson`, `thm:logconcave-cheeger-poincare-comparison`.

Retained assumptions: `ass:tight-prefix-carleson`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `lem:relative-perimeter-cheeger-infimum`

Dependencies: `def:isoperimetric-cheeger-scale`, `lem:covariance-test-core-density`, `lem:relative-perimeter-smoothing`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `lem:relative-perimeter-smoothing`

Dependencies: `thm:borell-logconcave-density`.

Recorded gaps:

- Weighted Lipschitz coarea is a DIRECT HOLE, as is its C1 Isoperimetry specialization. Selected route needs Eilenberg measurable majorants (L1), C1 Whitney jet extension (L6), compact jet extraction (L6a), exact C1 pieces (L7), and regular/critical C1 coarea (L9-L11). Existing C1 graph area and same-dimensional Jacobian change of variables alone do not prove this. Exact checked statements: build/audit/WeightedCoareaRouteStatements.lean; route: research/decisions/2026-09-15-weighted-coarea-route.md.
- Fiber AEMeasurable is CLOSED: Analysis.aemeasurable_lintegral_levelSet has been migrated out of KLS/WIP/AnalyticPrerequisites.lean into the hole-free KLS/Geometry/LevelSetMeasurable.lean with a machine-checked byte-identical pp.all signature, and is proved from L5 with standard three axioms only; it no longer carries sorryAx and direct holes are 10 (2/3/5). Its whole route is proved in KLS/Geometry/SurfaceSlicing.lean over the Mathlib-only Analysis/HausdorffSlicing.lean and Analysis/HausdorffContent.lean: L1 KLS.exists_measurable_majorant (measurable majorant with the explicit positive constant eilenbergConstant V = 4 omega_(n-1)/omega_n, no sharpness claimed), L2 KLS.ae_surfaceMeasure_inter_levelSet_eq_zero, L3 KLS.measurable_surfaceMeasure_inter_levelSet (compact S, continuous u), L4 KLS.aemeasurable_surfaceMeasure_inter_levelSet (measurable S) and L5 KLS.aemeasurable_setLIntegral_inter_levelSet (measurable ENNReal weight), all with CompleteSpace dropped and global Lipschitz weakened to continuity plus LipschitzOnWith on S, no finiteness of S or of g, g may be identically infinity, dimension zero covered, and NO parametric-integral theorem used so the inner measure is never assumed SFinite. WHAT IS STILL MISSING for this node is the EQUALITY, not the measurability: see the weighted-coarea gap. Exact statements: build/audit/LevelSetMeasurableAudit.lean, build/audit/BorelSliceAudit.lean, build/audit/CompactSliceAudit.lean, build/audit/EilenbergMajorantAudit.lean, build/audit/NullSlicingAudit.lean; decisions: research/decisions/2026-09-15-levelset-measurable-migration.md, research/decisions/2026-09-15-borel-slice-measurable.md, research/decisions/2026-09-15-compact-slice-measurable.md, research/decisions/2026-09-15-eilenberg-majorant.md and research/decisions/2026-09-15-null-slicing.md.
- Sard Analysis.sard is a DIRECT HOLE in WIP/AnalyticPrerequisites: the critical values of a C^n real-valued function on an n-dimensional space are Lebesgue null, C^n being sharp for target dimension one. Analysis.ae_forall_fderiv_ne_zero is a FILLED BODY that inherits sorryAx through it. ROUTE EXPLORATION 2026-09-15: no consumer needs the sharp C^n form. Analysis.sard is used only by Analysis.ae_forall_fderiv_ne_zero, which is used only by SmoothDomain.ae_exists_superlevel, and that statement already assumes ContDiff R infinity u and downgrades infinity to finrank at the call site. A C-infinity Sard plus a C-infinity variant of the a.e. statement would free the consumer from sorryAx while Analysis.sard keeps its text and its direct-hole status. The sharp version's first genuine obstruction is n=4, j=2 (the restricted function is only C2 on a 3-dimensional slice while 3-dimensional Sard needs C3); sharp dimension 3 is reachable today. Recommended induction is over open domains with ContDiffOn. Nothing is proved yet. See research/decisions/2026-09-15-smooth-sard-route.md. INGREDIENTS 2026-09-15: three of the seven route lemmas are proved with standard axioms only in Analysis/SmoothSard.lean - critical_subset_layers (L2), exists_flat_direction (L4) and exists_local_graph (L5). Route correction: ContDiffAt R infinity does NOT upgrade to ContDiffOn R infinity on a neighbourhood (ContDiffAt.contDiffOn has the side condition m = infinity implies n = omega), so L5 was strengthened to give C-infinity smoothness on an open parameter set. Still missing: L3 (open-domain flat layer plus the order-n remainder on an open domain), L1 (the dimension induction) and L6/L7. No sorryAx removed; Analysis.sard unchanged. See research/decisions/2026-09-15-smooth-sard-ingredients.md. SMOOTH SARD PROVED 2026-09-15: Analysis.sard_smooth_pi, Analysis.sard_smooth and Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top prove Sard's theorem for C-infinity real-valued functions in every dimension with standard axioms only, on an arbitrary finite-dimensional real normed space and with no measurability of the critical set. The audit client reproves the statement of SmoothDomain.ae_exists_superlevel from it with NO sorryAx. However NO WIP file was changed this round, so SmoothDomain.ae_exists_superlevel still inherits sorryAx, direct holes remain 11 and the sharp C^n Analysis.sard keeps its statement and direct-hole status. Rewiring WIP to the new theorem is a separate decision. See research/decisions/2026-09-15-smooth-sard.md. REWIRED 2026-09-15: SmoothDomain.ae_exists_superlevel and frontier_superlevel_subset moved to the hole-free KLS/Geometry/RegularSuperlevel.lean with byte-identical pp.all signatures, and the former is proved from Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top, so it NO LONGER inherits sorryAx. KLS/WIP/CheegerInfimum.lean dropped its import of KLS/WIP/AnalyticPrerequisites and still compiles, so no module imports that file any more. Direct holes are UNCHANGED at 11: a filled body moved, not a hole. The sharp Analysis.sard and Analysis.ae_forall_fderiv_ne_zero remain unproved and still carry sorryAx, now with no downstream consumer. See research/decisions/2026-09-15-superlevel-rewire.md.
- DONE this round, kept here only to record what it does NOT close: the Sard-to-smooth-superlevel packaging SmoothDomain.ae_exists_superlevel in WIP/CheegerInfimum is no longer a direct hole. Its statement is unchanged and its body is filter_upwards on Analysis.ae_forall_fderiv_ne_zero, with the order reduction hu.of_le ENat.LEInfty.out (le_top does NOT apply: the top of WithTop ENat is omega, not infinity, and simp makes no progress), composed with the new hole-free construction SmoothDomain.ofSuperlevel in Geometry/SmoothDomain.lean. ofSuperlevel needs fderiv u nonzero only on frontier {x &#124; t < u x}, not on the whole level set and not on the whole space; it uses W = {y &#124; fderiv u y != 0} and phi = t - u, and covers empty frontier, empty carrier, full carrier and dimension zero with no extra hypothesis. ofSuperlevel and ofSuperlevel_carrier depend only on the standard three axioms, but ae_exists_superlevel STILL INHERITS sorryAx through Analysis.sard and must not be listed as sorryAx-free. Direct holes went 12 -> 11 (3/3/5); Sard, weighted coarea and the level-set measurability are untouched.
- Final assembly still to do after those: the C1 specialization Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet (a direct hole that would only become a sorryAx-inheriting filled body until the general coarea is proved, so it is cosmetic on its own), smoothConstant_mul_lintegral_min_superlevel_le and smoothConstant_le_minkowskiConstant. Until they are done, smoothConstant_le_minkowskiConstant, minkowskiConstant_eq_smoothConstant, constant_eq_smoothConstant_intrinsic and inverseScale_eq_inv_smoothConstant_intrinsic all depend transitively on sorryAx: only h_M <= h_S is proved.
- By contrast the reverse direction needs no further work on exists_smooth_approximation_lipschitz, which is already PROVED from the certified sorryAx-free Energy.Euclidean.LipschitzApproximation.exists_smooth_bounded_L1, nor on the distance cutoffs, whose range, Lipschitz, boundary-value, L1-convergence and gradient-integral lemmas are now all proved in the hole-free KLS/Geometry/DistanceCutoff.lean.
- DONE: Analysis.sard_of_finrank_le_one in Analysis/Sard.lean, standard axioms only. Zero dimension: subsingleton image is null without C1. Dimension one: ContinuousLinearEquiv.ofFinrankEq gives e : R equivL V; zero derivative chain rule and Mathlib equidimensional null-image lemma apply to u composed with e; surjectivity identifies the critical-value image. No isometry, source measure transport, or determinant of V -> R is used. General Sard stays a direct hole; both consumers still inherit sorryAx. DONE: Analysis.exists_uniform_quadratic_remainder is proved on arbitrary real normed spaces, with C2 and compact K, first and second derivatives zero at selected base points, and nearby y allowed outside K. Standard axioms only. DONE: Analysis.volume_image_eq_zero_of_quadratic_oscillation in Analysis/QuadraticCover.lean proves exactly that covering lemma - bounded A in R^2, arbitrary f, uniform quadratic oscillation on pairs of points of A implies volume (f image A) = 0 - with standard axioms only and no measurability of A or of its image. The proof uses an O(r^-2) integer-floor grid, one A-representative per occupied cell, an interval of length 2 eps r^2 per cell and Finset subadditivity; the total 2 eps (2R+3)^2 is independent of r. DONE: Analysis.volume_image_flat_eq_zero connects it to the uniform remainder and makes the image of the SUBSET {x in K &#124; Du x = 0 and D2u x = 0} null for C2 u on a planar compact K; all of K is NOT assumed flat and the subset is NOT assumed measurable. DONE: Analysis.volume_image_flat_univ_eq_zero upgrades that to the whole plane by a countable closedBall exhaustion, keeping no compactness, boundedness or measurability hypothesis. DONE: Analysis.volume_image_nonflat_eq_zero proves the complementary planar layer volume (u image {x &#124; Du x = 0 and D2u x != 0}) = 0 with standard axioms only, and without any implicit function theorem: near a point with D2u != 0 the mean value inequality with linear principal part makes the critical set a Lipschitz graph over one coordinate, which also forces injectivity of that coordinate, so the layer collapses onto a new one-dimensional covering lemma Analysis.volume_image_eq_zero_of_quadratic_bound; Lindelof glues the local balls countably so no compactness hypothesis survives. Analysis/ImplicitGraph.lean was NOT reused because it needs C-infinity and an inner product while Du is only C1. DONE: Analysis.sard_plane combines the flat and nonflat layers and proves Sard's theorem for C2 real functions on Fin 2 -> R, with the critical set not assumed measurable, bounded or compact. This is dimension two ONLY and does NOT prove the general Analysis.sard, which stays a direct hole with both consumers inheriting sorryAx. DONE: both of those are now proved with standard axioms only. Analysis.exists_uniform_pow_remainder gives the order-n uniform remainder at points of a compact set where every derivative of order 1..n vanishes, on an arbitrary real normed domain with no finite-dimensionality, by induction on the order through fderiv f (the vector-valued induction sits in a private same-universe auxiliary lemma). Analysis.volume_image_eq_zero_of_oscillation_pow gives the n-dimensional covering lemma over Fintype.piFinset, where (2M+1)^n cells and O(eps r^n) intervals cancel. Analysis.volume_image_flat_pow_eq_zero and Analysis.volume_image_flat_pow_univ_eq_zero combine them into the fully flat layer on a compact subset and on all of Fin n -> R. The quadratic remainder and the planar covering lemma became corollaries with byte-identical statements, so no client changed and no proof content is duplicated. NEXT: the intermediate layers, 1 <= j < n with derivatives of order 1..j vanishing but order j+1 not, and the stacked dimension-n Sard; type-checked only in build/audit/IntermediateLayerNextStatement.lean. The planar case n=2, j=1 is proved by the Lipschitz-graph collapse, but for general n the same estimate only gives an (n-1)-dimensional graph and still needs Sard on that graph with the regularity loss of the restriction, which is the Whitney-Morse-Sard difficulty and is NOT touched. Exact statements and the remaining gaps: research/decisions/2026-09-14-planar-sard.md. General Sard, weighted coarea and the reverse comparison all remain unproved; planar Sard is not Sard.

[Task record](../../research/tasks.json)

### `prop:spectral-sufficiency`

Dependencies: `q:mm-spectral-occupation`, `thm:affine-isotropic-reduction`.

Retained assumptions: `q:mm-spectral-occupation`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `prop:weighted-spectator-obstruction`

Dependencies: none recorded.

Recorded gaps:

- Lean statement of ass:weighted-package: definitions of Eldan's stochastic localization process on a finite-dimensional Euclidean space (the tilted measures mu_t driven by a Brownian motion), of a balanced finite-perimeter cut and its excess e_t along the process, of the weighted covariance A_t and its operator norm, of the stopping time tau_eta, and of the paired absorptive weighted Stein-trace estimate (only stated in the upstream module modules/kls/20-eldan-statements.tex)
- Stochastic calculus in the pinned Mathlib: Brownian motion exists only as a process with prescribed finite-dimensional laws (IsBrownianReal), with stopping and hitting times; there is no stochastic integral, no Ito formula and no existence/uniqueness theory for the localization SDE, so the process quantities cannot yet be defined
- Local proof of the exponential-spectator computation: the upstream dossier solutions/prop-weighted-spectator-obstruction.tex (kls-exploration) is not in this repository, and the violation is asserted at a positive time 0 < T <= T_0, so the product-of-exponentials and cylinder-set calculation must be re-derived along the process rather than from the initial data alone

[Task record](../../research/tasks.json)

### `q:conditional-fiber-frame`

Dependencies: `def:conditional-fiber-form`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `q:mm-spectral-occupation`

Dependencies: none recorded.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `q:smooth-gradient-raw-core-agreement`

Dependencies: `def:smooth-gradient-preenergy`, `def:smooth-gradient-relaxation`, `obs:dirac-raw-energy`, `obs:normal-direction-raw-energy`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `thm:cmh-recovery-affine-poincare-bound`

Dependencies: `def:affine-poincare-constant`, `def:log-concave-law`, `thm:affine-covariance-relaxation-closed`.

Recorded gaps:

- Lean definition of the quadratic Wasserstein distance W_2 between probability laws on a finite-dimensional Euclidean space and of W_2 convergence (not in the pinned Mathlib)
- Lean definition of the CMH constant CMH(mu) with the pinned source's regular compact-target moment-map class, canonical moment-map kernel and weak zero-flux closed Stein-generator convention
- local proof of lem:affine-poincare-w2-liminf (lower semicontinuity of Poincare.CovarianceGradient.Intrinsic.constant under W_2 convergence of centered log-concave laws)
- local proof of thm:cmh-implies-affine-poincare (Poincare.CovarianceGradient.Intrinsic.constant mu_k <= CMH(mu_k) for the regular class)

[Task record](../../research/tasks.json)

### `thm:klartag-density-frontend-identification`

Dependencies: `def:affine-support-intrinsic-law`, `def:isoperimetric-cheeger-scale`, `def:literature-poincare-constant`, `def:log-concave-law`, `lem:relative-perimeter-cheeger-infimum`, `thm:borell-logconcave-density`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `thm:logconcave-cheeger-poincare-comparison`

Dependencies: `def:isoperimetric-cheeger-scale`, `def:literature-poincare-constant`, `def:log-concave-law`, `lem:covariance-test-core-density`, `thm:klartag-density-frontend-identification`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

### `thm:smooth-gradient-relaxation-two-cheeger`

Dependencies: `def:selected-canonical-frontend`.

See the linked statement and task record for the remaining proof obligation.

[Task record](../../research/tasks.json)

## Diagram-level auxiliary progress

Derived from the reviewed diagrams, including results not registered as separate Blueprint nodes.
These markers preserve the diagram assessment; this generator does not independently audit proofs.

| Diagram node | Recorded progress | Source |
| --- | --- | --- |
| `KLS` | ○ KLS conjecture — Dimension-free bound | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Statement.lean) |
| `ANY` | OR — Any one completed route | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `DENS` | ✓ Log-concave densities — Intrinsic affine support | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean) |
| `NORM` | ✓ Centering and whitening — Affine ⇔ Covariance-normalized ⇔ Isotropic | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) |
| `FORMS` | ✓ Closed quadratic energies — Normal contractions and Dirichlet property | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean) |
| `ENERGY` | ✓ Canonical energy = 2 × Cheeger energy — For log-concave laws; local-slope convention | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/Cheeger.lean) |
| `CONST` | ✓ Smooth, intrinsic and local-slope — Poincaré constants agree for log-concave laws | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean) |
| `CB` | ○ Cheeger–Buser comparison — Not yet Lean-certified | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| `EG` | ○ Tight-prefix absorptive — Carleson estimate | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `EC` | ○ Tight-window consumption — Upstream reviewed implication; not Lean | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `EAND` | ○ Eldan localization route — All required inputs (AND) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `SG` | ○ Fixed-eigenfunction — Full-damping occupation bound | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `SC` | ○ Full-damping sufficiency — Upstream reviewed implication; not Lean | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `SAND` | ○ Moment-map spectral route — All required inputs (AND) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `MH` | ○ W₂ lower semicontinuity — and CMH → affine Poincaré bound — Upstream reviewed; not Lean | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `MG` | ○ Uniformly bounded — CMH recovery envelope | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `MT` | ✓ Affine Poincaré constant — Translation invariance and closed form | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Translation.lean) |
| `MC` | ○ One CMH recovery sequence suffices — Upstream reviewed implication; not Lean | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `MAND` | ○ Moment-map CMH route — All required inputs (AND) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `FC` | ✓ Conditional-fiber — Closed Dirichlet form | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean) |
| `ONE` | ✓ One-dimensional log-concave bound — Poincaré constant ≤ 4 × variance | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean) |
| `FLOG` | ✓ Almost-everywhere — Fiber log-concavity | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| `FP` | ✓ Energy comparison — Given a fiber Poincaré bound | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean) |
| `F4` | ✓ Fiber energy — ≤ 4 × gradient energy | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| `FG` | ○ Test-independent frame — Universal bound Var ≤ C × fiber energy | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `FAND` | ◐ Conditional-fiber frame route — All required inputs (AND) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `GG` | ✓ Global Gauss–Green | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean) |
| `REC` | ✓ Smooth recovery sequences | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean) |
| `FWD` | ✓ Forward comparison — h_M ≤ h_S | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean) |
| `MINK` | ✓ Minkowski coarea inequality | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean) |
| `SARD` | ✓ Smooth Sard theorem — Regular superlevel sets | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/SmoothSard.lean) |
| `MEAS` | ✓ Level-set integral measurability | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean) |
| `GRAPH` | ✓ Weighted graph area — On open domains | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean) |
| `REG` | ✓ Coarea on regular open domains — Parametric inverse and substitution | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean) |
| `CRIT` | ✓ Critical slices are null — For almost every level | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean) |
| `C1` | ○ Assemble general C¹ coarea — Next proof step | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l11) |
| `WHIT` | ○ Whitney extension — Exact Lipschitz-to-C¹ pieces | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l6) |
| `LIP` | ○ General Lipschitz — Weighted coarea formula | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l12) |
| `SCI` | ○ Smooth coarea inequality | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `CUT` | ✓ Distance-cutoff estimates — and smooth approximation | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean) |
| `REV` | ○ Reverse comparison — h_S ≤ h_M | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `EQ` | ◐ Equality h_M = h_S — Lean proof still incomplete | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `FRONT` | ○ Density Cheeger — Frontend identification; not Lean | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |

## Provenance

Upstream revision: `34b5fcd57fef17089e781616005fe6d3641bd11e`. The selected upstream snapshot contains
20 records; this register is not an inventory of the entire upstream ledger.

Canonical input digest: `1fc1e6084dc74aeea394830ddb1ed6ce770b0315c2d279bab8818b8c82482e27`.
Diagram digest: `7b1206bef12569866b0b08adc9fb956997f7cb440a616c2e6da5abc9a5801a72`.

Regenerate with `python3 research/progress/update.py` after staging the intended source and
metadata updates. Unstaged unrelated metadata is deliberately excluded.
