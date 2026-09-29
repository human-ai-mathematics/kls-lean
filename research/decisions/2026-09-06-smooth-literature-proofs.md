# Smooth tests and the literature constant: eight proofs and local certification

Date: 2026-09-06. After the eight-statement handoff, the user explicitly requested completion
of the `sorry`s as well. This batch completes all eight proofs and registers
`thm:smooth-lipschitz-constant-equivalence` as `proved / checked_by: lean`.
Local HEAD is `70ca1c19c4d207a31716c2e589c0b096521a5490`; the tree includes earlier uncommitted
work. No commit/push, rewriting of historical decisions/explorations, or change to prior staging.

## Sources and reading order

1. [Original statement record](2026-09-06-smooth-literature-statements.md): the eight targets, coordinate conventions, and sources.
2. [Local slope and gradient](../../formalization/FunctionalInequalities/KLS/LocalSlopeGradient.lean): pointwise, a.e., and extended-energy identities and finite-energy test domain.
3. [Constant comparison](../../formalization/FunctionalInequalities/Poincare/Euclidean/LiteratureComparison.lean): finite-constant equivalence, coordinate infimum, ambient/intrinsic/literature constant chain, and selected-constant corollary.
4. [Combined certificate](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean): eight conjoined components, each universally quantified; the certificate and each reusable declaration have a default-build axiom guard.

Mathematical sources remain the local Blueprint's written argument and original definitions.
Proofs reuse certified weighted smooth approximation, intrinsic restriction/normal-constant
extension, L² variance continuity, and legacy/relaxed comparison, without new mathematical assumptions.

## Proofs and scope review

- Pointwise slope: the Fréchet derivative remainder gives the upper bound; local difference-quotient bounds give the derivative-operator-norm lower bound; then use the Hilbert gradient-norm identity. No unit vector is chosen, so zero and infinite-dimensional spaces are covered.
- A.e. identities and test domain: Rademacher plus absolute continuity transfers null sets, then a.e. invariance of lintegral and gradient measurability identify energies and L² conditions. Extended-energy equality allows infinity; a totalized real integral is not used to pretend finiteness.
- Finite constants: specialize certified approximation to identity B, obtaining L² convergence of functions and gradients. Continuity of variance and the integral of the squared gradient norm transfers the smooth-test bound with the same C to literature tests. Conversely, smoothness implies local Lipschitz continuity. No energy identity or convergence conclusion to be proved is assumed additionally.
- Optima: directly compare extended infima of the valid finite-constant sets, allowing C=0, empty sets, and infinite optima without attainment. Write the coordinate infimum explicitly to avoid intrinsicizing an already intrinsic law again.
- Coordinates: restriction does not increase energy; normal-constant extension preserves energy; measure-preserving reconstruction preserves variance. Finally combine the existing selected/legacy equality. Only the intrinsic measure must be absolutely continuous with respect to Haar on its direction space; the ambient law may be singular. Zero-dimensional affine support is retained, without second moments, a positive density lower bound, or raw/core agreement.

Two public signatures are slightly generalized: `localSlope_ae_eq_norm_gradient` and
`literatureEnergy_eq_lintegral_gradient` drop redundant `SecondCountableTopology E` instance
parameters, supplied by finite-dimensional real normed spaces. Original explicit mathematical
premises and conclusions are retained, so the original targets remain covered. The other six
mathematical signatures are unchanged. Certificate components are quantified separately;
packaging does not add finite dimension or absolute continuity to the pointwise theorem.
Private helpers add neither parallel constant definitions nor compatibility aliases.

This does not yet prove intrinsic absolute continuity of general log-concave measures.
`thm:borell-logconcave-density` and `thm:selected-literature-constant-equivalence` without an
explicit absolute-continuity premise remain uncertified. Cheeger-energy identification,
Dirichlet properties, long routes, and KLS are not proved by this batch.

## Registration and protected scope

The certificate map uses the existing Blueprint node and adds `leanok` to the corresponding
statement/proof, without a new graph node. The ledger now has eight proved nodes; the original
seven objects are unchanged. All `tasks.json` mathematical classifications remain unchanged;
only this node's implemented adapter becomes `available`, clearing resolved infrastructure
gaps and updating proof-source hashes. Route status, KLS Definitions/Statement, golden files,
and historical records are unchanged. Current guides reflect certification;
`StatementChecks.lean` only corrects obsolete prose, adding no Gaussian specialization proof
or placeholder.

## Verified prechecks and final verification boundary

The source snapshot before writing this record has SHA256
`f129aab7e1ef351df40f990b17d9cee977dc234be388c4375ac55eb1d50f967d`, with HEAD as above.
Ledger, Blueprint, and atlas structure checks passed at this stage: 8 certificates,
73 mathematical nodes, 86 navigation labels, 4 active routes, no dependency cycles;
97 Python unit tests passed. `lake build solutions.ThmSmoothLipschitzConstantEquivalence`
passed with 3094 jobs and no warnings. The eight declarations and combined certificate have
exactly `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Escape-marker
checks passed for the new proof modules and the certificate's local import closure.
Precheck logs are `build/smooth-literature-proofs/certificate-preflight.log`,
`build/smooth-literature-proofs/structural-checks.log`, and
`build/smooth-literature-proofs/python-tests.log`.

After writing this record, run `python3 research/verify.py` for the final source's default
build, Python tests, public-definition golden files, axiom coverage, and kernel replay of all
local modules. Generated `build/verification/<UTC timestamp>/report.json` records actual gate
results and final source SHA256; export the atlas after success. This record does not claim
a successful full run in advance or write its final hash back into source, invalidating the receipt.

Local replay trusts pinned third-party compiled imports. No external independent check,
isolated source rebuild, remote CI, or publication was performed. Current proof certification,
final-snapshot verification, and remote publication are separately verified facts.
