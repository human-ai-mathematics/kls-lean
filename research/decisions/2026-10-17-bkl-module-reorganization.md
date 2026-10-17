# BKL responsibility and dependency reorganization (2026-10-17)

## Target, scope and placement plan

The owner authorized implementation of the six findings in the current BKL layout review.
The literature target remains Bizeul–Klartag–Lehec arXiv:2610.05474v1, Theorems 4.1 and 1.1,
with their existing accepted supporting construction. This task changes module ownership and
dependencies, with all hypotheses, constants, normalization, dimensions, names, namespaces,
visibility, declaration bodies and certificate status preserved.

The dirty source baseline, actual staging bytes/entries/flags, source slices and planned
declaration destinations are saved in [the maintenance evidence directory](../../build/file-management/2026-10-17-bkl-reorganization/).
The [source review](../../build/file-management/2026-10-17-bkl-structure-review/FINDINGS.json)
records the evidence that motivated each boundary. No provider or proof-generation task is involved.

| Owner and actual scope | Destination / decision | Import direction and API impact |
| --- | --- | --- |
| General cumulant estimate from moments and one positive exponential radius | New `Analysis/BakryEmery/Cumulant/MomentBound.lean` in the existing cumulant family | Imports the existing local cumulant and logarithmic-derivative tools; no BKL import. The original Analysis namespace and full theorem remain. |
| Generic diffusion-generator product rule | Extend `Probability/Diffusion/Generator.lean` | No BKL import. The private subtraction helper remains with its existing covariance-generator consumer. |
| Paper-level cumulant energies, coordinate-form identification and isotropic a-priori bounds | `BKL/CumulantEnergy/{Basic,Conjugation,Bound}.lean` | General law/energy objects precede posterior/process specializations. No log-concavity or compactness is added to general statements. |
| Compact-posterior energy bounds, smoothness, generator identities/estimates and integrated process estimate | `BKL/Localization/Energy/{Bound,Regularity,Generator,Integral}.lean` | Imports the general cumulant-energy owners and the particular process/claim prerequisites. No general object needs the stochastic process. |
| Cutoff process construction and bounded-functional integration | `BKL/Localization/Process/{Basic,Integral}.lean` | Integral imports Basic. Process integration no longer requires the entire cutoff induction. |
| Weighted cutoff energy claim, second-order base case, boundary control, cumulant transfer and induction | `BKL/Localization/CutoffEnergy/{Basic,Base,Boundary,ToCumulant,Induction,Step}.lean` | The definition precedes its clients; process integrals precede boundary/integrated estimates; Step and Induction remain separate from final theorem assembly. |
| Compact-posterior covariance algebra/radius, joint regularity, whitening, noise, moments and initial response | `BKL/Posterior/{Covariance,Regularity,Standardization,Noise,Moments,Response}.lean` | Existing generic Probability/Posterior stays below the BKL specializations. Localization coefficients import posterior regularity; standardized estimates import standardization. |
| Lyapunov construction and exact pointwise calculus, quantitative generator bound, process moment estimate | `BKL/Localization/Lyapunov/{Basic,Bound,Moment}.lean` | Construction and exact calculus stay together because of shared private operator helpers. Bound imports the energy-generator estimates; Moment takes its actual process/generator-bound hypotheses. No duplicate helper definitions are introduced. |
| Source Theorem 4.1 and final Poincaré/KLS assembly | Keep substantive `BKL/Theorem41.lean`; create `BKL/Poincare.lean` | Theorem41 does not need the Poisson/Taylor-to-Poincaré reduction. Poincare imports Theorem41, Reduction and the proved compact Letwin input. Source theorem-number navigation is retained. |

`PoissonIterate/` and `Suspension/` retain their existing family structure. Their prerequisite
imports may change when a moved declaration has a new owner. Generic product-calculus bridges
inside the coherent log-Laplace-generator argument remain a separately reviewed candidate;
they are not silently renamed or moved to an Analysis module under a new public namespace.

## Preservation and acceptance

The [complete module and declaration map](../api-migration/2026-10-17-bkl-module-map.json)
records one-to-many source splits, exact authored-declaration destinations, compiler-private
identifier pairs, and the new owners of all affected elaborated constants. No old-path wrappers,
forwarding theorems or compatibility aliases are added. Existing source slices, including
declaration documentation, proof bodies and scoped options, are retained; duplicated enclosing
section/namespace scaffolding is checked through the elaborated interfaces.

Before refreshing evidence, compare all affected declaration types, universe parameters,
binder information/names, safety/partiality flags and non-theorem definition closures.
Compiler/private identifier changes require explicit pairs. The sole remaining structural type
difference is the real normed-space instance path in the moved diffusion product rule: reconstruct
both complete types and require a kernel-checked `Eq.refl` equality before acceptance. No change
to hypotheses, binder interfaces or definition bodies is accepted through this check.
The baseline also includes unchanged BKL families and the existing
generic generator module. Compiler-generated executable auxiliaries are recorded with their
actual flags rather than silently omitted. Equality of elaborated theorem proof values is not claimed.

Update direct consumers, module-name guards, exact source/declaration records, current links,
Blueprint anchors and live infrastructure evidence. Match each old evidence digest to the saved
baseline before replacing it. Historical decisions, handoffs, earlier maps and verification
receipts retain their recorded contents and scope. Regenerate progress with a private index;
run the full verifier in its normal Git environment so fixture repositories do not inherit it.

Acceptance requires source/semantic preservation, real-client compilation, standard-axiom audits,
full build, full local verifier and current-module kernel replay, progress regression/checks,
link checks and actual-index/history preservation. Mathematical and paper-coverage statuses do
not advance. The [completion receipt](../../build/file-management/2026-10-17-bkl-reorganization/COMPLETION.json)
records actual outcomes; this decision alone does not claim acceptance.
No commit, push, tag, remote CI, publication or credential access is authorized by this task.
