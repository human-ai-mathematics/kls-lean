# Formalization progress register

[Progress hub](README.md) · [Route diagrams](README.md#proof-progress-tree)

**75 local Blueprint nodes · 24 registered Lean certificates.**

Generated from staged canonical records. These are recorded proof/definition statuses,
not a fresh Lean run or a remote CI receipt. A missing local proof means only that this
register does not certify it; unregistered auxiliary progress appears in the diagram directory below.

**✓** Formalized in Lean (proof or definition) · **○** Not recorded as complete.
Upstream status is shown only where an explicit upstream mapping exists; no mapping is inferred
from a similar title. Upstream `proved` does not mean Lean-proved.

## Local nodes

Descriptions explain the mathematical statement; the Lean column separately reports completion.
See the linked statement for full hypotheses and scope.

| Node ID | Plain-English description | Upstream / mathematical record | Our Lean record | Certificate / statement |
| --- | --- | --- | --- | --- |
| `ass:cmh-recovery-envelope` | Seek a regular moment-map approximation of every centered log-concave law with a dimension-free CMH bound. | Upstream: open | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L206) |
| `ass:tight-prefix-carleson` | Control the accumulated localization source by time, the remainder, and an absorbable share of damping. | Upstream: open | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L41) |
| `ass:weighted-package` | The historical covariance-weighted estimate for near-minimizing cuts; its universal claim was refuted. | Upstream: refuted | ![— Excluded: refuted](badges/excluded.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L87) |
| `cert:ambient-intrinsic-comparison` | Package equality of ambient and intrinsic relaxed energies and Poincaré constants. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L96) · [Lean certificate](../../solutions/LemAmbientIntrinsicPoincareComparison.lean) |
| `cert:binary-tensorization` | Bound the Poincaré constant of two independent factors by the larger factor constant. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L35) · [Lean certificate](../../solutions/LemPoincareTensorization.lean) |
| `cert:finite-tensorization` | Identify the constant of a finite independent product with the supremum of its factor constants, including degenerate cases. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L52) · [Lean certificate](../../solutions/LemPoincareFiniteTensorization.lean) |
| `cert:gaussian-one-dimensional` | Identify a one-dimensional Gaussian's optimal Poincaré constant with its variance, including zero variance. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L70) · [Lean certificate](../../solutions/LemPoincareGaussianOneDimensional.lean) |
| `cert:legacy-relaxed-comparison` | Transfer smooth-test bounds to relaxed-energy constants; this certificate does not identify Cheeger energy. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L111) · [Lean certificate](../../solutions/LemLegacyRelaxedPoincareComparison.lean) |
| `cert:linear-test-lower` | Use linear tests to bound the Poincaré constant below by the largest covariance eigenvalue. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L21) · [Lean certificate](../../solutions/LemLinearTestLower.lean) |
| `conj:kls` | Seek one dimension-free Poincaré bound for all isotropic log-concave laws, equivalently a covariance-scaled bound. | Upstream: open | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L176) |
| `cor:absolutely-continuous-relaxation-two-cheeger` | Identify canonical energy with twice Cheeger energy when the intrinsic law has a density, including log-concave laws. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L92) · [Lean certificate](../../solutions/CorAbsolutelyContinuousRelaxationTwoCheeger.lean) |
| `cor:ambient-intrinsic-constant-equality` | Show that ambient and intrinsic relaxed energies have the same optimal Poincaré constant, including infinity. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L292) |
| `cor:cmh-recovery-sequence-suffices` | Deduce KLS if every centered log-concave law has a regular recovery sequence with a universal CMH bound. | Upstream: conditional | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L219) |
| `cor:conditional-fiber-twelve-bound` | For full-dimensional log-concave laws, bound fiber energy by four times gradient energy; the historical ID retains “twelve”. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L459) · [Lean certificate](../../solutions/CorConditionalFiberTwelveBound.lean) |
| `cor:tight-window-consumption` | Turn the assumed tight-prefix estimate into a dimension-free boundary bound and then KLS. | Upstream: proved | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L55) |
| `def:affine-poincare-constant` | Define the affine Poincaré constant using relaxed covariance-weighted gradient energy on the affine support. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L297) |
| `def:affine-support-intrinsic-law` | Describe the smallest affine space carrying the law and its probability distribution in intrinsic coordinates. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L64) |
| `def:conditional-fiber-form` | Define energy by averaging conditional variances along lines, normalized by each fiber's coordinate variance. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L259) |
| `def:extended-energy` | Define an energy that may be infinite and the domain where it is finite. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L25) |
| `def:intrinsic-affine-energy` | Transport relaxed smooth-gradient energy from intrinsic coordinates back to ambient L² classes. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L94) |
| `def:isoperimetric-cheeger-scale` | Define the Cheeger constant from boundary expansion relative to the smaller mass, and define its reciprocal scale. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L103) |
| `def:isotropic-law` | Define an isotropic law as centered with identity covariance, including the zero-dimensional case. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L246) |
| `def:l2-energy-poincare-constant` | Define the optimal variance-to-energy constant for an extended energy on L². | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L84) |
| `def:l2-mean-variance` | Define mean, centering, and variance independently of the representative of an L² class. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L11) |
| `def:legacy-smooth-test-poincare` | Define the Poincaré inequality and its optimal constant using globally smooth tests with finite gradient energy. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/40-certified-models.tex#L9) |
| `def:literature-poincare-constant` | Define the literature Poincaré constant using locally Lipschitz tests and local slopes on the affine support. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L153) |
| `def:log-concave-law` | Define log-concavity by the mass inequality for convex combinations of compact sets, allowing lower-dimensional support. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L18) |
| `def:poincare-test-family` | Define variance-to-energy quotients and their optimal bound on a specified test domain, with zero-energy conventions. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L71) |
| `def:preenergy-relaxation` | Extend a test energy by taking the least limiting energy among convergent test sequences. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L37) |
| `def:selected-canonical-frontend` | Choose intrinsic relaxed smooth-gradient energy as the canonical energy and define its Poincaré constant. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L116) |
| `def:smooth-gradient-preenergy` | Assign each admissible smooth function the integral of its squared gradient. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L12) |
| `def:smooth-gradient-relaxation` | Extend smooth-gradient energy to L² by sequential relaxation. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L39) |
| `lem:affine-poincare-translation-invariance` | Show that translating a log-concave law preserves log-concavity and its affine Poincaré constant. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L408) · [Lean certificate](../../solutions/LemAffinePoincareTranslationInvariance.lean) |
| `lem:ambient-intrinsic-covariance` | Identify ambient covariance with intrinsic covariance on the support and zero on normal directions, preserving the operator norm. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L260) · [Lean certificate](../../solutions/LemAmbientIntrinsicCovariance.lean) |
| `lem:conditional-fiber-energy-comparison` | Turn an assumed fiber Poincaré bound with coefficient κ into a gradient-energy comparison and a κC global bound. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L387) · [Lean certificate](../../solutions/LemConditionalFiberEnergyComparison.lean) |
| `lem:conditional-fiber-form` | Establish closed quadratic and Markov properties of the conditional-fiber energy under the stated density and moment assumptions. | Upstream: proved | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L308) · [Lean certificate](../../solutions/LemConditionalFiberForm.lean) |
| `lem:covariance-core-closure` | Close the transformed gradient operator and identify its Lipschitz and smooth-core closures for log-concave densities. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L52) · [Lean certificate](../../solutions/LemCovarianceCoreClosure.lean) |
| `lem:covariance-test-core-density` | Approximate locally Lipschitz tests and their transformed gradients by compactly supported smooth tests under absolute continuity. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L14) · [Lean certificate](../../solutions/LemCovarianceTestCoreDensity.lean) |
| `lem:finite-energy-factor-poincare` | Transfer a Poincaré bound between energies when one is bounded by a finite multiple of the other. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L241) |
| `lem:logconcave-intrinsic-absolute-continuity` | Show that a log-concave law has a density in its intrinsic affine space, even if singular in the ambient space. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L69) · [Lean certificate](../../solutions/LemLogConcaveIntrinsicAbsoluteContinuity.lean) |
| `lem:mutual-test-approximation-relaxation` | Identify two relaxed energies when each test family approximates the other without increasing limiting energy. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L223) |
| `lem:preenergy-poincare-relaxation` | Show that sequential relaxation preserves valid Poincaré bounds and the optimal constant. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L121) |
| `lem:relative-perimeter-cheeger-infimum` | Identify the Cheeger infimum over Borel sets with the weighted-perimeter infimum over smooth domains. | Local classification: local_argument | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L170) |
| `lem:relative-perimeter-smoothing` | Approximate a smooth-domain indicator by smooth Lipschitz functions whose limiting gradient integral is at most its perimeter. | Local classification: local_argument | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L128) |
| `lem:smooth-tests-affine-restriction-extension` | Restrict smooth tests to the affine support and extend intrinsic tests back while controlling gradient energy. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L246) |
| `obs:dirac-raw-energy` | Exhibit two functions equal for a Dirac law whose raw gradient energies differ, explaining the need for relaxation. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L9) |
| `obs:normal-direction-raw-energy` | Show that a function vanishing on the affine support can still have positive ambient gradient energy in a normal direction. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L129) |
| `prop:spectral-sufficiency` | Deduce a dimension-free Poincaré bound from the assumed full-damping occupation estimate. | Upstream: conditional | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L140) |
| `prop:weighted-spectator-obstruction` | Use independent exponential factors to refute the historical weighted package, without refuting KLS. | Upstream: proved | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L101) |
| `q:conditional-fiber-frame` | Seek a frame independent of the test function that controls variance by fiber energy with a universal constant. | Upstream: open | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L513) |
| `q:mm-spectral-occupation` | Seek a universal-time source estimate for a fixed eigenfunction along localization, uniform through regular approximation. | Upstream: open | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L128) |
| `q:smooth-gradient-raw-core-agreement` | Determine when raw energy descends to L² and how sequential approximation relates to graph-norm density. | Local classification: conjectural | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L159) |
| `thm:affine-covariance-relaxation-closed` | Identify the relaxed covariance energy of a log-concave law with the closed affine form used by the CMH route. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L347) · [Lean certificate](../../solutions/ThmAffineCovarianceRelaxationClosed.lean) |
| `thm:affine-isotropic-reduction` | Show that isotropic, covariance-scaled, and affine-energy KLS bounds are equivalent, including lower-dimensional laws. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L460) · [Lean certificate](../../solutions/ThmAffineIsotropicReduction.lean) |
| `thm:ambient-intrinsic-relaxation-equality` | Show that ambient and intrinsic smooth-gradient relaxations agree on the same L² space. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L266) |
| `thm:borell-logconcave-density` | Represent a log-concave law by an intrinsic log-concave density, positive with locally bounded reciprocal inside its convex support. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L95) · [Lean certificate](../../solutions/ThmBorellLogconcaveDensity.lean) |
| `thm:cmh-recovery-affine-poincare-bound` | Bound the affine Poincaré constant of a W₂ limit by the limiting CMH constants of a regular recovery sequence. | Local classification: local_argument | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L176) |
| `thm:compact-borell-logconcavity-equivalence` | Show that compact-set log-concavity is equivalent to the Borel-set formulation using inner measure. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L33) · [Lean certificate](../../solutions/ThmCompactBorellLogconcavityEquivalence.lean) |
| `thm:intrinsic-affine-constant-order` | Characterize a valid intrinsic-affine Poincaré bound by comparison with the optimal extended constant. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L139) |
| `thm:intrinsic-affine-energy-closed` | Establish that intrinsic relaxed energy is a densely defined closed quadratic energy on ambient L². | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L103) |
| `thm:intrinsic-l2-equivalence` | Identify ambient and intrinsic L² spaces by inverse linear isometries. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L76) |
| `thm:klartag-density-frontend-identification` | Identify the intrinsic Cheeger constant with the smooth-boundary density formulation for non-Dirac log-concave laws. | Local classification: local_argument | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L133) |
| `thm:l2-energy-holds-order` | Show that an L² energy inequality holds at a finite constant exactly when the optimal constant is no larger. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L101) |
| `thm:legacy-canonical-constant-comparison` | Identify the smooth-test, ambient relaxed, and canonical intrinsic Poincaré constants. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L34) |
| `thm:legacy-relaxed-holds-equivalence` | Show that smooth tests and ambient relaxed energy admit exactly the same finite Poincaré bounds. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L13) |
| `thm:logconcave-cheeger-poincare-comparison` | Compare Poincaré and inverse-Cheeger scales in both directions for log-concave laws, with factors 4 and π. | Local classification: published | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L180) |
| `thm:one-dimensional-logconcave-poincare` | Bound a one-dimensional log-concave law's Poincaré constant by four times its variance, including zero variance. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L539) · [Lean certificate](../../solutions/ThmOneDimensionalLogConcavePoincare.lean) |
| `thm:quadratic-relaxation-closed` | Show that relaxing a quadratic pre-energy with dense linear realization gives a closed quadratic form. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L51) |
| `thm:selected-literature-constant-equivalence` | Identify canonical and local-slope Poincaré constants for finite-dimensional log-concave laws. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L81) · [Lean certificate](../../solutions/ThmSelectedLiteratureConstantEquivalence.lean) |
| `thm:smooth-gradient-quadratic-dense` | Show that smooth-gradient pre-energy is quadratic and its test realizations are dense in L². | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L25) |
| `thm:smooth-gradient-raw-core-agreement-density` | Under explicit positive-density and local reciprocal bounds, identify intrinsic raw energy with its relaxation on the smooth core. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L171) · [Lean certificate](../../solutions/ThmSmoothGradientRawCoreAgreementDensity.lean) |
| `thm:smooth-gradient-relaxation-closed` | Establish closed quadratic structure and a dense finite-energy domain for ambient relaxed gradient energy. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L48) |
| `thm:smooth-gradient-relaxation-dirichlet` | Show that normal contractions decrease relaxed gradient energy, giving the ambient and intrinsic energies the Dirichlet property. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L25) · [Lean certificate](../../solutions/ThmSmoothGradientRelaxationDirichlet.lean) |
| `thm:smooth-gradient-relaxation-two-cheeger` | Seek identification of canonical energy with twice metric Cheeger energy for general laws, beyond the proved density case. | Local classification: unknown | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L65) |
| `thm:smooth-lipschitz-constant-equivalence` | Identify smooth-test and locally Lipschitz Poincaré constants when the intrinsic law is absolutely continuous. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L58) · [Lean certificate](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean) |

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

## Diagram-level progress

Generated from the same resolved records as the README diagram and result table.
Blueprint mappings derive status from staged proof annotations. Auxiliary assessments
retain their evidence source; generating this view does not run Lean.

| Diagram node | Description | Our Lean record | Source |
| --- | --- | --- | --- |
| `MG` | Seek a regular moment-map approximation of every centered log-concave law with a dimension-free CMH bound. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `EG` | Control the accumulated localization source by time, the remainder, and an absorbable share of damping. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `KLS` | Seek one dimension-free Poincaré bound for all isotropic log-concave laws, equivalently a covariance-scaled bound. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Statement.lean) |
| `ENERGY` | Identify canonical energy with twice Cheeger energy when the intrinsic law has a density, including log-concave laws. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/Cheeger.lean) |
| `MC` | Deduce KLS if every centered log-concave law has a regular recovery sequence with a universal CMH bound. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `F4` | For full-dimensional log-concave laws, bound fiber energy by four times gradient energy; the historical ID retains “twelve”. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| `EC` | Turn the assumed tight-prefix estimate into a dimension-free boundary bound and then KLS. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `MT` | Show that translating a log-concave law preserves log-concavity and its affine Poincaré constant. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Poincare/CovarianceGradient/Translation.lean) |
| `FP` | Turn an assumed fiber Poincaré bound with coefficient κ into a gradient-energy comparison and a κC global bound. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/EnergyComparison.lean) |
| `FC` | Establish closed quadratic and Markov properties of the conditional-fiber energy under the stated density and moment assumptions. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/ConditionalFiber/Closed.lean) |
| `SC` | Deduce a dimension-free Poincaré bound from the assumed full-damping occupation estimate. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `FG` | Seek a frame independent of the test function that controls variance by fiber energy with a universal constant. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `SG` | Seek a universal-time source estimate for a fixed eigenfunction along localization, uniform through regular approximation. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `NORM` | Show that isotropic, covariance-scaled, and affine-energy KLS bounds are equivalent, including lower-dimensional laws. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean) |
| `DENS` | Represent a log-concave law by an intrinsic log-concave density, positive with locally bounded reciprocal inside its convex support. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/BorellRepresentation.lean) |
| `MH` | Bound the affine Poincaré constant of a W₂ limit by the limiting CMH constants of a regular recovery sequence. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `FRONT` | Identify the intrinsic Cheeger constant with the smooth-boundary density formulation for non-Dirac log-concave laws. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| `CB` | Compare Poincaré and inverse-Cheeger scales in both directions for log-concave laws, with factors 4 and π. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| `ONE` | Bound a one-dimensional log-concave law's Poincaré constant by four times its variance, including zero variance. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean) |
| `CONST` | Identify canonical and local-slope Poincaré constants for finite-dimensional log-concave laws. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean) |
| `FORMS` | Show that normal contractions decrease relaxed gradient energy, giving the ambient and intrinsic energies the Dirichlet property. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean) |
| `MEAS` | Slice measurability | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/LevelSetMeasurable.lean) |
| `GRAPH` | Open-domain — Graph area | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/OpenGraphIntegral.lean) |
| `REG` | Regular-domain — Coarea | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/RegularCoarea.lean) |
| `CRIT` | Critical-slice nullity | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CriticalSlice.lean) |
| `C1` | General C¹ coarea — Next step | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l11) |
| `WHIT` | Whitney extension — Exact C¹ pieces | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l6) |
| `LIP` | Lipschitz coarea | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-15-weighted-coarea-route.md#l12) |
| `GG` | Global Gauss–Green | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/GaussGreen.lean) |
| `REC` | Smooth recovery | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean) |
| `FWD` | h_M ≤ h_S | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/CheegerInfimum.lean) |
| `SARD` | Smooth Sard | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/SmoothSard.lean) |
| `SCI` | Smooth coarea — Inequality | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `CUT` | Distance cutoffs | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/DistanceCutoff.lean) |
| `REV` | h_S ≤ h_M | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `EQ` | h_M = h_S | ![◐ Partially formalized](badges/partial.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `MINK` | Minkowski coarea | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/MinkowskiContent.lean) |
| `EAND` | AND — Eldan route | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `SAND` | AND — Spectral route | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `MAND` | AND — CMH route | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `FLOG` | Fiber log-concavity | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| `FAND` | AND — Fiber route | ![◐ Partially formalized](badges/partial.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `ANY` | OR — Any completed route | OR | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |

## Provenance

Upstream revision: `34b5fcd57fef17089e781616005fe6d3641bd11e`. The selected upstream snapshot contains
20 records; this register is not an inventory of the entire upstream ledger.

Canonical input digest: `1fc1e6084dc74aeea394830ddb1ed6ce770b0315c2d279bab8818b8c82482e27`.
Diagram digest: `3f13f3a8d153e3c8adb2b0ff05960a73e0c846183d0cd1619de8cf3798abc7ca`.
View input digest: `7af70f8acd6411bd75aae053cb833ae46a826f7f54e6f646544f657191b878db`.

Regenerate with `python3 research/progress/update.py` after staging the intended source and
metadata updates. Unstaged unrelated metadata is deliberately excluded.
