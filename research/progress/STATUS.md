# Formalization progress register

[Progress hub](README.md) · [Route diagrams](README.md#proof-progress-tree)

**75 local Blueprint nodes · 26 registered Lean certificates.**

Generated from staged canonical records. These are recorded proof/definition statuses,
not a fresh Lean run or a remote CI receipt. A missing local proof means only that this
register does not certify it; unregistered auxiliary progress appears in the diagram directory below.

![✓ Formalized in Lean](badges/formalized.svg) · ![○ Not yet formalized](badges/pending.svg) · ![◐ Partially formalized](badges/partial.svg) · ![— Excluded: refuted](badges/excluded.svg)

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
| `cor:absolutely-continuous-relaxation-two-cheeger` | Identify canonical energy with twice Cheeger energy when the intrinsic law has a density, including log-concave laws. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L121) · [Lean certificate](../../solutions/CorAbsolutelyContinuousRelaxationTwoCheeger.lean) |
| `cor:ambient-intrinsic-constant-equality` | Show that ambient and intrinsic relaxed energies have the same optimal Poincaré constant, including infinity. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L321) |
| `cor:cmh-recovery-sequence-suffices` | Deduce KLS if every centered log-concave law has a regular recovery sequence with a universal CMH bound. | Upstream: conditional | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L219) |
| `cor:conditional-fiber-twelve-bound` | For full-dimensional log-concave laws, bound fiber energy by four times gradient energy; the historical ID retains “twelve”. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L459) · [Lean certificate](../../solutions/CorConditionalFiberTwelveBound.lean) |
| `cor:tight-window-consumption` | Turn the assumed tight-prefix estimate into a dimension-free boundary bound and then KLS. | Upstream: proved | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L55) |
| `def:affine-poincare-constant` | Define the affine Poincaré constant using relaxed covariance-weighted gradient energy on the affine support. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L328) |
| `def:affine-support-intrinsic-law` | Describe the smallest affine space carrying the law and its probability distribution in intrinsic coordinates. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L64) |
| `def:conditional-fiber-form` | Define energy by averaging conditional variances along lines, normalized by each fiber's coordinate variance. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L259) |
| `def:extended-energy` | Define an energy that may be infinite and the domain where it is finite. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L25) |
| `def:intrinsic-affine-energy` | Transport relaxed smooth-gradient energy from intrinsic coordinates back to ambient L² classes. | Local definition; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L94) |
| `def:isoperimetric-cheeger-scale` | Define the Cheeger constant from boundary expansion relative to the smaller mass, and define its reciprocal scale. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L103) |
| `def:isotropic-law` | Define an isotropic law as centered with identity covariance, including the zero-dimensional case. | Local classification: definition | ![✓ Formalized in Lean](badges/formalized.svg) (definition) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L277) |
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
| `lem:affine-poincare-translation-invariance` | Show that translating a log-concave law preserves log-concavity and its affine Poincaré constant. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L439) · [Lean certificate](../../solutions/LemAffinePoincareTranslationInvariance.lean) |
| `lem:ambient-intrinsic-covariance` | Identify ambient covariance with intrinsic covariance on the support and zero on normal directions, preserving the operator norm. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L291) · [Lean certificate](../../solutions/LemAmbientIntrinsicCovariance.lean) |
| `lem:conditional-fiber-energy-comparison` | Turn an assumed fiber Poincaré bound with coefficient κ into a gradient-energy comparison and a κC global bound. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L387) · [Lean certificate](../../solutions/LemConditionalFiberEnergyComparison.lean) |
| `lem:conditional-fiber-form` | Establish closed quadratic and Markov properties of the conditional-fiber energy under the stated density and moment assumptions. | Upstream: proved | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L308) · [Lean certificate](../../solutions/LemConditionalFiberForm.lean) |
| `lem:covariance-core-closure` | Close the transformed gradient operator and identify its Lipschitz and smooth-core closures for log-concave densities. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L52) · [Lean certificate](../../solutions/LemCovarianceCoreClosure.lean) |
| `lem:covariance-test-core-density` | Approximate locally Lipschitz tests and their transformed gradients by compactly supported smooth tests under absolute continuity. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L14) · [Lean certificate](../../solutions/LemCovarianceTestCoreDensity.lean) |
| `lem:finite-energy-factor-poincare` | Transfer a Poincaré bound between energies when one is bounded by a finite multiple of the other. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L253) |
| `lem:logconcave-intrinsic-absolute-continuity` | Show that a log-concave law has a density in its intrinsic affine space, even if singular in the ambient space. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L69) · [Lean certificate](../../solutions/LemLogConcaveIntrinsicAbsoluteContinuity.lean) |
| `lem:mutual-test-approximation-relaxation` | Identify two relaxed energies when each test family approximates the other without increasing limiting energy. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L235) |
| `lem:preenergy-poincare-relaxation` | Show that sequential relaxation preserves valid Poincaré bounds and the optimal constant. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L121) |
| `lem:relative-perimeter-cheeger-infimum` | Identify the Cheeger infimum over Borel sets with the weighted-perimeter infimum over smooth domains. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L173) · [Lean certificate](../../solutions/LemRelativePerimeterCheegerInfimum.lean) |
| `lem:relative-perimeter-smoothing` | Approximate a smooth-domain indicator by smooth Lipschitz functions whose limiting gradient integral is at most its perimeter. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/60-analytic-comparison-proofs.tex#L128) |
| `lem:smooth-tests-affine-restriction-extension` | Restrict smooth tests to the affine support and extend intrinsic tests back while controlling gradient energy. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L275) |
| `obs:dirac-raw-energy` | Exhibit two functions equal for a Dirac law whose raw gradient energies differ, explaining the need for relaxation. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L9) |
| `obs:normal-direction-raw-energy` | Show that a function vanishing on the affine support can still have positive ambient gradient energy in a normal direction. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L158) |
| `prop:spectral-sufficiency` | Deduce a dimension-free Poincaré bound from the assumed full-damping occupation estimate. | Upstream: conditional | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L140) |
| `prop:weighted-spectator-obstruction` | Use independent exponential factors to refute the historical weighted package, without refuting KLS. | Upstream: proved | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L101) |
| `q:conditional-fiber-frame` | Seek a frame independent of the test function that controls variance by fiber energy with a universal constant. | Upstream: open | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L513) |
| `q:mm-spectral-occupation` | Seek a universal-time source estimate for a fixed eigenfunction along localization, uniform through regular approximation. | Upstream: open | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L128) |
| `q:smooth-gradient-raw-core-agreement` | Determine when raw energy descends to L² and how sequential approximation relates to graph-norm density. | Local classification: conjectural | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L188) |
| `thm:affine-covariance-relaxation-closed` | Identify the relaxed covariance energy of a log-concave law with the closed affine form used by the CMH route. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L378) · [Lean certificate](../../solutions/ThmAffineCovarianceRelaxationClosed.lean) |
| `thm:affine-isotropic-reduction` | Show that isotropic, covariance-scaled, and affine-energy KLS bounds are equivalent, including lower-dimensional laws. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L491) · [Lean certificate](../../solutions/ThmAffineIsotropicReduction.lean) |
| `thm:ambient-intrinsic-relaxation-equality` | Show that ambient and intrinsic smooth-gradient relaxations agree on the same L² space. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L295) |
| `thm:borell-logconcave-density` | Represent a log-concave law by an intrinsic log-concave density, positive with locally bounded reciprocal inside its convex support. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L95) · [Lean certificate](../../solutions/ThmBorellLogconcaveDensity.lean) |
| `thm:cmh-recovery-affine-poincare-bound` | Bound the affine Poincaré constant of a W₂ limit by the limiting CMH constants of a regular recovery sequence. | Local classification: local_argument | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/50-kls-routes.tex#L176) |
| `thm:compact-borell-logconcavity-equivalence` | Show that compact-set log-concavity is equivalent to the Borel-set formulation using inner measure. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/00-orientation-and-status.tex#L33) · [Lean certificate](../../solutions/ThmCompactBorellLogconcavityEquivalence.lean) |
| `thm:intrinsic-affine-constant-order` | Characterize a valid intrinsic-affine Poincaré bound by comparison with the optimal extended constant. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L139) |
| `thm:intrinsic-affine-energy-closed` | Establish that intrinsic relaxed energy is a densely defined closed quadratic energy on ambient L². | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L103) |
| `thm:intrinsic-l2-equivalence` | Identify ambient and intrinsic L² spaces by inverse linear isometries. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L76) |
| `thm:klartag-density-frontend-identification` | Identify the intrinsic Cheeger constant with the smooth-boundary density formulation for non-Dirac log-concave laws. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L133) |
| `thm:l2-energy-holds-order` | Show that an L² energy inequality holds at a finite constant exactly when the optimal constant is no larger. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L101) |
| `thm:legacy-canonical-constant-comparison` | Identify the smooth-test, ambient relaxed, and canonical intrinsic Poincaré constants. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L34) |
| `thm:legacy-relaxed-holds-equivalence` | Show that smooth tests and ambient relaxed energy admit exactly the same finite Poincaré bounds. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L13) |
| `thm:logconcave-cheeger-poincare-comparison` | Compare Poincaré and inverse-Cheeger scales in both directions for log-concave laws, with factors 4 and π. | Local classification: published | ![○ Not yet formalized](badges/pending.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L197) |
| `thm:one-dimensional-logconcave-poincare` | Bound a one-dimensional log-concave law's Poincaré constant by four times its variance, including zero variance. | Local classification: published | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L570) · [Lean certificate](../../solutions/ThmOneDimensionalLogConcavePoincare.lean) |
| `thm:quadratic-relaxation-closed` | Show that relaxing a quadratic pre-energy with dense linear realization gives a closed quadratic form. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/10-canonical-basic.tex#L51) |
| `thm:selected-literature-constant-equivalence` | Identify canonical and local-slope Poincaré constants for finite-dimensional log-concave laws. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex#L81) · [Lean certificate](../../solutions/ThmSelectedLiteratureConstantEquivalence.lean) |
| `thm:smooth-gradient-quadratic-dense` | Show that smooth-gradient pre-energy is quadratic and its test realizations are dense in L². | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L25) |
| `thm:smooth-gradient-raw-core-agreement-density` | Under explicit positive-density and local reciprocal bounds, identify intrinsic raw energy with its relaxation on the smooth core. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L200) · [Lean certificate](../../solutions/ThmSmoothGradientRawCoreAgreementDensity.lean) |
| `thm:smooth-gradient-relaxation-closed` | Establish closed quadratic structure and a dense finite-energy domain for ambient relaxed gradient energy. | Local Lean result; no upstream mapping | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/20-smooth-gradient-and-affine.tex#L48) |
| `thm:smooth-gradient-relaxation-dirichlet` | Show that normal contractions decrease relaxed gradient energy, giving the ambient and intrinsic energies the Dirichlet property. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L25) · [Lean certificate](../../solutions/ThmSmoothGradientRelaxationDirichlet.lean) |
| `thm:smooth-gradient-relaxation-two-cheeger` | Seek identification of canonical energy with twice metric Cheeger energy for general laws, beyond the proved density case. | Local classification: local_argument | ![✓ Formalized in Lean](badges/formalized.svg) | [Statement](../../formalization/blueprint/src/chapters/30-open-canonical-bridges.tex#L65) · [Lean certificate](../../solutions/ThmSmoothGradientRelaxationTwoCheeger.lean) |
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

### `thm:logconcave-cheeger-poincare-comparison`

Dependencies: `def:isoperimetric-cheeger-scale`, `def:literature-poincare-constant`, `def:log-concave-law`, `lem:covariance-test-core-density`, `thm:klartag-density-frontend-identification`.

Recorded gaps:

- Generation of a symmetric contraction semigroup from the closed energy form. The pinned Mathlib has no strongly continuous one-parameter semigroup (no C0Semigroup type, no Hille-Yosida or Lumer-Phillips generation theorem) and no spectral or Borel functional calculus for unbounded self-adjoint operators: Analysis/InnerProductSpace/Spectrum.lean states in its own header that it assumes compactness of the operator or finite-dimensionality, and Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ covers bounded C*-algebra elements only. The THEOREM is therefore absent, but the construction is not blocked: the classical Yosida route is assemblable from pieces that do exist. Analysis/InnerProductSpace/LaxMilgram.lean gives the resolvent of a bounded coercive form on a Hilbert space, which applies on the form domain even though the energy form is unbounded on L^2; Analysis/InnerProductSpace/Dual.lean gives Riesz representation; Analysis/Normed/Algebra/Exponential.lean gives NormedSpace.exp for the bounded Yosida approximation; and Analysis/InnerProductSpace/LinearPMap.lean gives the adjoint and closedness of an unbounded densely defined operator. The repository already supplies the form side as a densely defined closable operator (Energy/Relaxation/LinearPMap.lean, KLS/LogConcave/WeightedGradient.lean weightedOperator_isClosable and dense_domain_weightedOperator, KLS/LogConcave/ClosedForm.lean intrinsicCovariance_closedQuadratic) and the Cheeger energy itself (Energy/Cheeger/Basic.lean). What must be built is the passage from that closed form to P_t = exp(-t T*T): form domain as a Hilbert space, resolvent, contraction and self-adjointness of the resolvent, Yosida approximation, strong convergence of exp(-t L_s), and the semigroup and generator laws. This is large but elementary, and is general Hilbert-space material independent of KLS, so it is the natural first cut and an upstreamable contribution. Route: research/decisions/2026-09-19-semigroup-generation-route.md. Update 2026-09-19: of the listed pieces, the form domain as a Hilbert space (S1), the resolvent with its contraction, self-adjointness and nonnegativity (S2-S4, resolventCLM in Analysis/Semigroup/Resolvent/Basic.lean) and the contraction property of exp(-t L) for a bounded nonnegative L, hence of the Yosida approximation (S5, Analysis/Semigroup/Exponential/Contraction.lean, proved without self-adjointness), are local hole-free Lean proofs. Still missing: the strong convergence of exp(-t L_s) as s -> 0 (S6), which needs the self-adjointness of T*T and density of its domain, and the semigroup and generator laws (S7, S8). Records: research/decisions/2026-09-19-semigroup-form-proofs.md, research/decisions/2026-09-19-semigroup-yosida-proof.md. Update 2026-09-19 (later): von Neumann's theorem for T*T (self-adjointness, dense domain, (1 + s T*T) J_s = 1) and the strong convergence and commutation of the resolvents are now local hole-free Lean proofs (Analysis/Semigroup/AdjointComp.lean, VonNeumann.lean, Resolvent/Limit.lean). Still missing: S6 (strong convergence of exp(-t L_s)), S7, S8. Update 2026-09-19 (S6): the strong convergence of exp(-t L_s) as s -> 0 is a local hole-free Lean proof (Analysis/Semigroup/Yosida/Limit.lean). Still missing: S7 (the limit is a strongly continuous semigroup of self-adjoint contractions, which first requires naming the limit as an operator P_t) and S8 (its generator is T*T). Update 2026-09-19 (S7-S8): the semigroup construction is complete as abstract Hilbert-space material: for T closed and densely defined, P_t = Analysis.Semigroup.semigroupApply is a strongly continuous semigroup of self-adjoint contractions with generator -T*T on D(T*T) (Analysis/Semigroup/Generated/Basic.lean, Generated/Laws.lean, Exponential/MeanValue.lean, Generated/Generator.lean). What this gap still lacks is the specialisation to the repository's energy operator (the weighted gradient of KLS/LogConcave/WeightedGradient.lean as T, with the L^2(mu) identification) and everything in the following three gaps; the THEOREM (Buser for n >= 2 with constant pi) remains absent. Update 2026-09-19 (specialisation): the specialisation to the weighted gradient is done (KLS/LogConcave/HeatSemigroup/Basic.lean, heatSemigroup and intrinsicHeatSemigroup, Dirichlet form = closed energy). This gap is closed as far as the construction of the symmetric contraction semigroup goes; what the THEOREM still lacks is entirely in the following three gaps.
- Dirichlet form and Markov semigroup theory: no Dirichlet form in the functional-analytic sense and no Markovian property (sub-Markov contraction on L^1 and L^infinity, preservation of positivity and of total mass) anywhere in the pinned Mathlib; the only 'Dirichlet' files are Dirichlet characters and L-series, and the only 'Markov' files are CategoryTheory/MarkovCategory, the Chebyshev-Markov inequality and Riesz-Markov-Kakutani. Without the Markov property the pointwise bounds of the Ledoux argument have no meaning.
- Bakry-Emery Gamma-calculus: no carre du champ operator Gamma, no iterated Gamma_2, no curvature-dimension condition CD(K, infinity), and in particular no gradient commutation estimate of the form &#124;&#124;grad P_t f&#124;&#124; <= exp(-Kt) P_t &#124;&#124;grad f&#124;&#124;. This is the analytic engine of Ledoux's proof of Buser's inequality and of the constant pi in De Ponti-Mondino; nothing in the repository supplies it either.
- Small-time heat semigroup estimates: no heat kernel and no heat semigroup on a weighted Euclidean space, hence neither of the two inequalities Ledoux's proof combines on indicator-like tests, namely the L^1 approximation bound &#124;&#124;P_t f - f&#124;&#124;_1 <= C sqrt(t) times the total variation of f and the smoothing bound &#124;&#124;grad P_t f&#124;&#124;_infinity <= C t^{-1/2} &#124;&#124;f&#124;&#124;_infinity.
- Alternative route (b), Lovasz-Simonovits localization: no needle or bisection decomposition of a log-concave law on a finite-dimensional space into one-dimensional log-concave marginals, and no Prekopa-Leindler or Brunn-Minkowski theorem in the pinned Mathlib (the repository has only its own one-dimensional Probability/Line/BrunnMinkowski.lean). A transfer lemma carrying a one-dimensional conclusion to the ambient isoperimetric constant is also absent, so the proved Stage 1 bound Psi_KLS^2 <= 12 C_P^lit for affine support of dimension at most one cannot be upgraded to n >= 2 by localization either.

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
| `ENERGY` | Identify canonical energy with twice Cheeger energy when the intrinsic law has a density, including log-concave laws. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/Cheeger/Basic.lean) |
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
| `DENS` | Represent a log-concave law by an intrinsic log-concave density, positive with locally bounded reciprocal inside its convex support. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation.lean) |
| `MH` | Bound the affine Poincaré constant of a W₂ limit by the limiting CMH constants of a regular recovery sequence. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/50-kls-routes.tex) |
| `FRONT` | Identify the intrinsic Cheeger constant with the smooth-boundary density formulation for non-Dirac log-concave laws. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| `CB` | Compare Poincaré and inverse-Cheeger scales in both directions for log-concave laws, with factors 4 and π. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex) |
| `ONE` | Bound a one-dimensional log-concave law's Poincaré constant by four times its variance, including zero variance. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpPoincare.lean) |
| `CONST` | Identify canonical and local-slope Poincaré constants for finite-dimensional log-concave laws. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean) |
| `FORMS` | Show that normal contractions decrease relaxed gradient energy, giving the ambient and intrinsic energies the Dirichlet property. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Energy/SmoothGradient/Dirichlet.lean) |
| `MEAS` | Slice measurability | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Slice/Measurable.lean) |
| `GRAPH` | Open-domain — Graph area | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/Graph/OpenIntegral.lean) |
| `REG` | Regular-domain — Coarea | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Coarea/Regular.lean) |
| `CRIT` | Critical-slice nullity | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Slice/Critical.lean) |
| `C1` | General C¹ weighted coarea | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Coarea/Smooth.lean) |
| `WHIT` | Compact-set C1 Whitney extension and exact C1 pieces of Lipschitz functions (L6/L6a/L7); no arbitrary noncompact closed-set extension is claimed. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-16-lipschitz-coarea.md) |
| `LIP` | Weighted coarea for locally Lipschitz functions (L11/L12/L13; T1/T2/T3 wired) | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Coarea/LocallyLipschitz.lean) |
| `GG` | Global Gauss–Green | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/GaussGreen.lean) |
| `REC` | The exact smooth recovery sequence for finite relative perimeter is proved and registered in Blueprint, including unbounded domains and carriers. This is not the full Cheeger comparison or a separate ledger certificate. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Perimeter/Recovery.lean) |
| `FWD` | h_M ≤ h_S | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Infimum.lean) |
| `SARD` | Smooth Sard | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/Sard/Smooth.lean) |
| `SCI` | Integrated smooth Cheeger superlevel inequality; the coarea formula itself is already proved. This pending step belongs to the separately assigned Cheeger-Buser workstream. | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `CUT` | Distance cutoffs | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Cheeger/DistanceCutoff.lean) |
| `REV` | h_S ≤ h_M | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `EQ` | h_M = h_S | ![◐ Partially formalized](badges/partial.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/WIP/CheegerInfimum.lean) |
| `MINK` | Minkowski coarea | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/Geometry/Cheeger/MinkowskiContent.lean) |
| `EAND` | AND — Eldan route | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `SAND` | AND — Spectral route | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `MAND` | AND — CMH route | ![○ Not yet formalized](badges/pending.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `FLOG` | Fiber log-concavity | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) |
| `FAND` | AND — Fiber route | ![◐ Partially formalized](badges/partial.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `ANY` | OR — Any completed route | OR | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/blueprint/route-composition.yaml) |
| `VREG` | Coarea on an open region where the derivative is surjective, with normalized Hausdorff fibres; this is not general vector coarea. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/Vector/Coarea/Regular.lean) |
| `VZERO` | Slice measurability and nullity of almost every slice of the zero-derivative set; intermediate positive ranks are not covered. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/formalization/FunctionalInequalities/Analysis/Vector/Slice/Critical.lean) |
| `VR123` | Rank stratification, the kernel identity and pointwise/uniform approximate right inverses are proved. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/audits/RightInverseBoundAudit.lean) |
| `VR4` | The tangential small-Lipschitz estimate on fibres is proved; it is a supporting result for the critical-set argument. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-17-tangential-lipschitz.md) |
| `VFULL` | General codimension-m weighted coarea for C1 maps is proved, including the rank-deficient critical part. This does not prove the Lipschitz vector case, sharp finite-regularity Sard, or KLS. | ![✓ Formalized in Lean](badges/formalized.svg) | [Source](https://github.com/numina-functional-inequalities/kls-lean/blob/main/research/decisions/2026-09-17-rank-deficient-coarea.md) |

## Provenance

Upstream revision: `34b5fcd57fef17089e781616005fe6d3641bd11e`. The selected upstream snapshot contains
20 records; this register is not an inventory of the entire upstream ledger.

Canonical input digest: `3dcc0f6303e9b6ee7adb3239242b89de22a74dfd1428fdb240017f43faf17af6`.
Diagram digest: `572dc65fc60dcd2e3fd91dc78bf90737c03de4e80d1d1094ed49724d61b5e27e`.
View input digest: `832285b1f8d10dbfc54643529e909911d6fd588a274b295d37fa6aa93484189b`.

Regenerate with `python3 research/progress/update.py` after staging the intended source and
metadata updates. Unstaged unrelated metadata is deliberately excluded.
