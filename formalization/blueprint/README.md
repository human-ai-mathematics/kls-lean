# KLS Lean Blueprint

This Blueprint is the live dependency map for the canonical `L²`/energy foundation and the
remaining route to KLS. It is deliberately narrower than the upstream mathematical manuscript:
it records only interfaces that this repository intends to formalize, together with four audited
sufficient-route alternatives. The alternatives share analytic infrastructure; no logical or
probabilistic independence is asserted.

Public Lean interfaces may evolve throughout this exploratory stage. Proof work does not
require a prior freeze, and certification does not promise signature stability. The graph
distinguishes current proof evidence from unresolved choices in a statement:

- `\lean{...}` plus statement and proof `\leanok`: the declaration and proof are certified by
  the local Lean build;
- an exact statement without `\leanok`: mathematically stated but not Lean-certified here;
- `\notready`: the statement has an explicit unresolved choice, such as its test domain,
  hypotheses, or normalization. The nearby text identifies the choice. An open proof or the
  possibility of future API changes alone does not justify this marker.

Removing `\notready` means only that no such statement choice is currently recorded. It does
not add `\leanok`, certify a proof, or change the route sidecar's mathematical status. See the
[current lifecycle](../../research/ledger-schema.md#lifecycle).

Upstream `checked_by: agent` metadata is provenance, never Lean certification. The proved
relaxation/recovery bridge now identifies the legacy and selected canonical constants.
That bridge does not require
raw-test/core agreement; raw/core is an optional stronger statement and is obstructed for general
singular measures (`obs:dirac-raw-energy`) and, for the ambient pre-energy, on every proper
affine support (`obs:normal-direction-raw-energy`, Lean-certified in
`Energy/SmoothGradient/NormalDirection.lean`). Under the local density hypotheses of
`thm:smooth-gradient-raw-core-agreement-density` the agreement is Lean-certified by
`Solutions.ThmSmoothGradientRawCoreAgreementDensity.certificate`.

The Blueprint keeps three unweighted frontend levels visible:

- `C_P(μ; E)` is the energy-parametrized optimizer for an arbitrary extended `L²` energy;
- `C_P^can(μ)` selects the intrinsic-affine smooth-gradient relaxation used by this repository;
- `C_P^lit(μ)` is the locally Lipschitz constant used in the KLS literature.

Selection is a repository convention, not a proof of `E_can = 2 Ch`. Equality of selected and
legacy constants is Lean-certified. Their comparison with the literature constant now has a
cutoff-and-convolution proof in Appendix A. Its approximation input and eight smooth/literature
interfaces are Lean-certified under intrinsic absolute continuity. The general log-concave
comparison is now certified using the new precise intrinsic absolute-continuity lemma; the
stronger Borell density/moment representation is separately Lean-certified. See the
[general proof record](../../research/decisions/2026-09-06-general-logconcave-comparison.md) and
[Borell proof record](../../research/decisions/2026-09-07-borell-density-proofs.md).

Appendix A also supplies the relative-perimeter and covariance-core proofs. Outward dilation
before smoothing handles the carrier boundary in the first; graph-norm approximation and
closability identify the exact source domain in the second. These statements specify their
current domains and normalization and remain open to revision during formalization. The
covariance-core closure and the closed affine covariance form are now Lean-certified
(`Solutions.LemCovarianceCoreClosure.certificate`,
`Solutions.ThmAffineCovarianceRelaxationClosed.certificate`); the relative-perimeter smoothing
argument still awaits Lean implementation. The separate abstract
relaxation and finite-factor comparison lemmas in the appendix have actual Lean proofs. The
Dirichlet property of the smooth-gradient relaxation (`thm:smooth-gradient-relaxation-dirichlet`)
is Lean-certified by `Solutions.ThmSmoothGradientRelaxationDirichlet.certificate`. The
one-dimensional log-concave bound `C_P^lit(ν) ≤ 4 Var_ν` (`thm:one-dimensional-logconcave-poincare`),
formerly an imported published input with Bobkov's constant `12` (now a corollary), is Lean-certified by
`Solutions.ThmOneDimensionalLogConcavePoincare.certificate`; its route sidecar claim is `proved`.

Separately, $C_{\mathrm P}^{\mathrm{aff}}(\mu)$ is the optimal constant of the closed
covariance-weighted form used by the CMH route. It is defined from the globally Lipschitz
covariance pre-energy by sequential $L^2$ relaxation on the intrinsic law; the definition is
implemented as `Poincare.CovarianceGradient.Intrinsic.constant` and carries `\leanok` as a definition node, with its
log-concave well-definedness contracts proved. It is neither a fourth
name for the unweighted constant of one fixed law nor a raw locally Lipschitz optimum. Translation
invariance and the CMH recovery-sequence bound are separate named nodes, so neither the
centered-to-arbitrary reduction nor the upstream lower-semicontinuity endpoint is hidden in proof
prose; the translation invariance and the affine/isotropic reduction are now Lean-certified
(`Solutions.LemAffinePoincareTranslationInvariance.certificate`,
`Solutions.ThmAffineIsotropicReduction.certificate`), while the CMH recovery-sequence bound is
recorded as missing infrastructure.

## Research source (2026-09-12)

The route source now pins `kls-conjecture-search@34b5fcd57fef17089e781616005fe6d3641bd11e`.
The stable source identifier remains `kls-exploration`. Upstream uses `proofs.mode` and
explicit `assumes`; a proved implication with open assumptions remains conditional locally.
See the [research synchronization record](../../research/decisions/2026-09-12-upstream-research-sync.md) for
the two 2026 preprints, new spectral/CMH/cone/fiber results and the scoped formalization queue.
These additions are research navigation, not new certified or dispatch-ready Lean nodes.

## Build

The [task atlas](../../research/verification.md) now derives 75 mathematical nodes from these
sources, preserving proof dependencies, route alternatives and adapter metadata. It separately
classifies research, local arguments, published inputs and refuted packages. Readiness requires
a current local verification receipt. The two target definitions now have Lean implementations;
`conj:kls` links to a proposition declaration without `\leanok` or a claimed proof.

Create a Python environment and install the pinned web-builder dependency:

```bash
python3 -m venv /tmp/kls-blueprint-venv
/tmp/kls-blueprint-venv/bin/pip install -r formalization/blueprint/requirements.txt
```

Then, from the repository root:

```bash
python3 research/check_blueprint.py
(cd formalization && lake build)
/tmp/kls-blueprint-venv/bin/python formalization/blueprint/build.py all
```

The helper writes the PDF to `formalization/blueprint/print/print.pdf`, the website to
`formalization/blueprint/web/`, and the declaration list to
`formalization/blueprint/lean_decls`. It uses direct commands because the Lake package is nested
under `formalization/`.

`route-composition.yaml` is intentionally a JSON subset. TeX `\uses{...}` means logical AND;
the sidecar supplies the one required logical OR: any one of the four route alternatives may
discharge `conj:kls`. The `any_of` records alternative sufficiency only; it conveys neither route
independence nor certification.

The conditional-fiber branch lists the structural upstream form node and frame question, the
local comparison with an explicit input `κ`, the verified one-dimensional bound `4 Var`,
and the local affine/isotropic bridge. With the certified log-concave input the resulting
numerical bound is `4C`; generally it is `κC`. The sharpness example remains outside Lean certification.
Its frame question has one finite constant outside the dimension and measure quantifiers, and
the frame construction uses positive dimensions. The zero-dimensional KLS conclusion is handled
separately by zero variance. Finite-gradient-energy literature tests are explicitly included in
the maximal fiber-form domain before the form-gap bound is used. The structural form lemma
`lem:conditional-fiber-form` (densely defined, closed, symmetric, Markovian, reversible) is
Lean-certified by `Solutions.LemConditionalFiberForm.certificate` for every Borel law and every
direction law; its route sidecar claim carries that Lean evidence beside the upstream review. The
local comparison `lem:conditional-fiber-energy-comparison` (`D_{μ,ρ}(f) ≤ κ ∫‖∇f‖² dμ < ∞` under
the fiber input `κ`, hence `C_P^lit(μ) ≤ κ C` from a form-gap bound `C`) is Lean-certified by
`Solutions.LemConditionalFiberEnergyComparison.certificate` for Haar-absolutely continuous laws and
admissible frames; its sidecar claim is `proved` with Lean evidence. Its log-concave
specialization `cor:conditional-fiber-twelve-bound` is Lean-certified by
`Solutions.CorConditionalFiberTwelveBound.certificate` and restated with the sharp constant `4`
supplied by `thm:one-dimensional-logconcave-poincare`; the literature `12` is its immediate
weakening. The remaining gate of the route is the frame question `q:conditional-fiber-frame`.

The `targets[].adapters` expression records repository-facing interfaces used to align the
imported route statements with this Blueprint's selected constants and normalizations. An adapter
is metadata about that alignment, not a logical prerequisite of the target, and listing one does
not create a TeX `\uses{...}` edge. Any logical use of an adapter must instead be declared on the
specific consuming node. For the KLS target the adapters expression must have root operator
`all_of`: repository integration expects every listed adapter, but this does not make them
conjuncts of the target theorem. In particular, `thm:selected-literature-constant-equivalence` is
not a logical prerequisite of `conj:kls`.

The sidecar's `state: open` field is the mathematical proof/lifecycle axis. TeX `\notready`
separately identifies an unresolved statement choice. No node currently carries the marker:
`thm:smooth-gradient-relaxation-two-cheeger` lost it on 2026-09-12, when the local-slope
convention was fixed and its absolutely continuous scope was certified as
`cor:absolutely-continuous-relaxation-two-cheeger`; what remains there is an open proof for
singular measures, which the absence of `\leanok` already records. All interfaces remain editable
even without this marker. A node may be both `open` and `\notready`; neither field supplies proof
evidence.
