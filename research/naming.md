# Lean public naming and parameter organization

Follow the [classification and delivery workflow](workflow.md) before adding modules, splitting
files or migrating an API. Public names express mathematical objects, operations and conclusions;
namespaces may span modules. Certificate entry points, ledger node IDs and source labels retain
stable identities. `FunctionalInequalities` is omitted below.

For interface entry points, carriers and test classes, use the [frontend guide](../LEAN_DESIGN.md)
and the [generated API directory](../formalization/API.md).

## Short names do not repeat the namespace

Do not repeat the object or role supplied by the namespace. Use `apply`, `energy`, `toL2` and
`constant`; theorem short names describe their properties, without encoding every assumption.

- `WeightedGradient.IsTest.memLp_apply`, `apply_add_ae`, `apply_smul_ae`.
- `LocalSlope.apply`, `apply_const`, replacing the redundant `LocalSlope.slope`.
- `LipschitzApproximation.exists_smooth_weighted_L2`, without repeating `approximation`.
- `ConditionalFiber.energyAt` is energy at one base point; `energy` is integrated energy.
- `SmoothTest.linear`, `energy_linear`; `ProductVariance.decomposition`, `integral_le`.

Still identify the other side of a comparison, another operator or another space. A helper about
ordinary `gradient` inside `WeightedGradient` must not sound like a weighted-gradient result.
`pullbackEquiv` distinguishes an equivalence of L² pullbacks from the underlying-space equivalence.
Comparison names write `relaxation`, `constant` or `holds` once and distinguish the target:
`CovarianceGradient.relaxation_eq_lipschitz`, `relaxation_eq_ofLinearPMap`,
`relaxation_le_mul_lipschitz`, `SmoothTest.constant_eq_ambient`, `constant_eq_intrinsic`,
`constant_eq_lipschitz`. Retain `mul` for multiplicative comparisons; a coefficient is not direct domination.
Name length or absence of an external consumer alone does not justify renaming or privatizing
a mathematical lemma.

## Distinguish objects, carriers and scope

- `weighted` always means an arbitrary external operator B, not necessarily a covariance factor.
- `Ambient` and `Intrinsic` distinguish carriers: intrinsic smooth-gradient energy is pulled back to ambient L²; intrinsic covariance energy remains in L² of `intrinsicMeasure`.
- Keep distinct test classes, weights, carriers and relaxations separate. Comparing optimal constants does not identify energies; `ClosedQuadratic` does not include Markov/Dirichlet properties (`Energy.SmoothGradient.markovian`, `dirichlet`, `Intrinsic.dirichlet`).
- Distinguish coordinate-law `Poincare.LocalSlope.Holds` from `LocalSlope.Intrinsic.constant`, which first takes the intrinsic law.
- Energy invariance belongs in `Energy.CovarianceGradient`; optimal-constant invariance in `Poincare.CovarianceGradient`.
- `Probability.translateLaw`, `mapLinearIsometryEquiv`, `mapContinuousLinearEquiv` distinguish translations, Euclidean isometries and general linear equivalences.
- `L2.Translation`, `L2.LinearIsometry`, `L2.ContinuousLinearEquiv` use `pullback` from image-law L² to source-law L²; `pullbackInv` composes with the inverse map.
- `Poincare.CovarianceGradient.Intrinsic.constant_translateLaw` states ambient-law translation invariance; `constant_eq_translate_intrinsicMeasure` compares the expression after translating the intrinsic law.
- `Covariance.exists_inner_eq_norm_sq` and `exists_intrinsic_inner_eq_norm_sq` assert only `∃ B, ∀ v, ⟪Σ v,v⟫ = ‖B v‖²`, not B² = Σ, self-adjointness, positivity or uniqueness; whitening is a self-adjoint W with WΣW = id and does not assert that W is the unique positive inverse square root.
- Retain weighted, L¹/L², ae, compact-support, boundary, finiteness and directional qualifiers. Borel sets and Borell representation differ; `LocalThirdCumulant` retains its positive-radius distinction.
- Scope suffixes describe actual premises: `_of_le` places a Hardy anchor on the median's side; `_of_fiberBound`, `_of_letwin`, `_of_letwinCompact`, `_of_cutoffs`, `_of_absolutelyContinuous`, `_of_hasTemperateGrowth`, `_of_poisson_chain`, `_of_normalized` retain their respective inputs.
- Put 4 in `localSlope_constant_le_four_variance` and `smoothTest_holds_four_variance`; 12 derived from 4 uses `_of_four`, as in `localSlope_constant_le_twelve_variance_of_four`.
- `_on_range` marks the local-potential hypotheses on `closure K ⊇ range ∇φ`; `_mul` retains a coefficient (`symmetric_trace_integral_extension_mul`, `exists_symm_integral_norm_sq_sub_le_mul`).
- `_Lp` marks Lp-class arguments (`tiltAverage_Lp_eq_inner`); `_components` marks componentwise lifts; `_adjointComp` marks statements on the domain of T̄†T̄.
- `exists_toLp_mem_…` existentially quantifies the `MemLp` witnesses; `exists_approx_eigenvector_of_gap` and `exists_centered_approx_eigenfunction` promise quantitative approximate eigenvectors, not eigenvectors.
- `Tensor.Coord` avoids Lean's core type `Array`; `stdHessianMatrix` uses `stdOrthonormalBasis` (`StdBasisIndex`); `scaled` marks real-radius cutoffs, `bounded_source` an a.e. source bound, and `real_` a finite real representative.
- Keep `Probability.lowerQuantile` distinct from `Probability.Line.affineQuantile`; `energyWithKernel` indicates an external kernel, and `LipschitzApproximation.kernelDerivativeMass` a derivative-norm integral normalized by kernel mass.
- Use existing expressions rather than new definitions for `cfc (· ^ α) A`, `fun s => Real.smoothTransition (2 - s)`, explicit uniform-interval potentials/tests, and curvature `∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v`.

## Property proofs and local names

Log-concave corollaries remain in `KLS.LogConcave`, inferring the measure from its property proof:

```lean
hμ.intrinsicSmooth_constant_eq_localSlope
hμ.intrinsicCovariance_closedQuadratic
hμ.intrinsicCovariance_energy_eq_operator m B hB
hμ.intrinsicCovariance_constant_eq_normSq m B hB
hμ.intrinsic_frontier_support_eq_zero
hμ.intrinsicWeightedOperator m B
```

Tests support `f.energy` and `f.toL2`, and weighted-test properties support `hf.memLp`.
Use property/object dot notation: `d.pos`, `d.mul_le_mul_of_add_eq`, `d.two_mul_cdf_le`,
`d.smoothTest_holds`, `d.one_div_le_variance` for `LineDensity`; `h.exists_lintegral_le` in
`LocallyDominatesOn`; `D.absolutelyContinuous`, `D.locallyDominatesOn` for `LocalDensity`.
Structures such as `RegularPotential` hold assumptions; consequences live in its namespace (`hV.law`).
`KLS.clip` is a top-level definition with lemmas in namespace `clip` (`clip.of_le`, `clip.of_mem`).

## Scopes and parameters

1. Organize differential properties first, then measure/L², Haar/absolute-continuity and log-concavity assumptions. Group local sections by required structure; do not pile strong assumptions at the top and disable `unusedSectionVars`.
2. Measures/tests inferred from objects or property proofs are implicit; chosen measures, weight operators and required references are explicit. Use instances for structure and explicit proof parameters for key premises.
   Examples: fiber lemmas take `(κ b)`, form lemmas `(μ ρ)`; `FiberBound`'s κ and the form-gap C are inferred, while `m` and `hac` are explicit. `LocalDensity` conclusions take `(ν m D)`; affine-quantile parameters are ordered `a b p u`.
3. `variable (hμ : LogConcave μ)` does not enter a statement merely because its proof uses hμ: put it in the theorem header or use theorem-local `include hμ in`, and inspect elaborated parameters.
   Repeated premises may use a named section with `variable` in original parameter order and theorem-local `include`; result-specific arguments stay in headers and unrelated helpers outside the inclusion.
4. Local `omit ... in` may mix levels of generality; keep checks enabled. Consecutive results with the same responsibility may share a named-section `omit` context, closed before stronger assumptions.
   Record and verify redundant-instance removal, explicitness/order changes and lemma mergers separately; they are not pure renames. Retain unused anonymous instances directly in theorem headers, preserving telescope order: `include` takes names, and naming an instance to silence a linter can change its label.
5. One-use proof helpers should be `private`; keep `open`, notation, `include`, instances and options local. Do not shorten parameters by bundling assumptions into a new structure or typeclass.
6. Preserve the mathematical qualifiers above. Names locate results; types and documentation give their complete assumptions and conclusions, rather than spelling out the theorem in its name.

## Source documentation

Module comments and docstrings describe mathematics, exact hypotheses/scope, pinned source versions
and locators, and useful proof explanations. Preserve paper attributions and license/author notices.
Task/route-node IDs, rounds, worker allocation and integration/failure logs belong in the local
archive outside the published tree. Archive removed process passages verbatim; preserve non-comment
code and reassess matching source-evidence hashes without changing proof/certificate status.
Verification receipts continue to certify their recorded snapshots.

## File and declaration scope

Files belong to their primary mathematical object's family: `Poincare/SmoothTest/`,
`Energy/LocalSlope/Gradient.lean`, and log-concave corollaries in
`LogConcave/{Covariance,Translation,ClosedForm,WeightedGradient,Isotropic,Poincare}`.
Use the object's namespace and short declaration headers, not `_root_.FunctionalInequalities.…`
to escape an incorrect outer namespace. Cross-object comparisons use their common parent namespace.
For example, write `theorem apply_eq_norm_gradient` inside `Energy.LocalSlope`.
Review file responsibilities separately from public API names (`Generated.preserves_domain`,
`generator_comm`, `right_derivative` retain generator-domain, right-limit and arbitrary-weight scope).

### Family names belong in directories, not filenames

1. **Three or more** modules for one mathematical object must form a family directory.
2. Two modules may form a directory only as a genuine foundational/extension pair; merely adjacent modules remain at the existing level.
3. Do not keep both `X.lean` and `X/`: move the genuine foundation to `X/Basic.lean`. `Basic.lean` is reserved for a family's genuine foundational module, never a catch-all; neither are `Misc` or `Utils`. The library-root `FunctionalInequalities.lean` alongside `FunctionalInequalities/` is exempt.
4. Retain at the root only cross-family infrastructure, stable public entry points or modules belonging to no single object.
5. Organize directories by **primary mathematical object**, not a one-off proof route.
6. A file move preserves namespaces, declaration names, statements, proofs, assumptions, dimensional scope and certificate status; namespace/public-name changes are separate API migrations with their own maps and validation.
7. Provide no old-path compatibility modules or name aliases, including aliases merely to shorten calls; resolve old references through migration maps.

For families, put the family name in the directory and only distinguishing terms in basenames:
`Poincare/SmoothTest/`, `Energy/LocalSlope/Gradient.lean`, `Energy/CovarianceGradient/`,
`KLS/LogConcave/Line/`, `Analysis/Semigroup/{Resolvent,Exponential,Yosida,Generated}/`,
`KLS/{ConditionalFiber,Geometry/Cheeger,Geometry/Coarea}/`.
Use `LogConcave/Covariance.lean`, not `LogConcave/AffineCovariance.lean`; new `Analysis/` modules
follow the same rule. `Analysis/Convex/LegendreVariation/{Attainment,Perturbation,Derivative}`
drops `Legendre*` basenames while `Convex/Legendre.lean` retains its separate object identity.

Exceptions to rule 5 remain: `Poincare/Euclidean/`, `Poincare/FiniteProduct/`, `Poincare/LipschitzGradient/`.

**Per-paper folders (owner decision 2026-10-07, amendment to rule 5).** Paper-specific iterates,
numbered lemmas for them, main-theorem assembly and witnesses live under `KLS/<Paper>/`
(currently `KLS/BKL/`, `KLS/CEK/`); audit clients/route statements use `research/audits/<Paper>/`
(currently BKL and CEK), dropping the paper prefix from filenames. Generic Bochner, tilt, tensor,
semigroup, summation and heat-model-generator tools stay in object families, which must never
import per-paper modules. Create other paper folders (Letwin, Song–Zhang) only with their first module.

## Migration checks

Keep a complete old/new path or name map and update consumers, imports, Blueprint anchors, guards,
snapshots, evidence paths and current documentation. Review before updating golden files or source
hashes; check verification snapshots under the [workflow](workflow.md#6-deliver-with-evidence-proportional-to-the-change).
