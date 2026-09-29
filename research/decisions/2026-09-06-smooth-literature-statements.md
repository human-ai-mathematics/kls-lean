# Smooth Test and Literature Constants: Eight Statements and Handoff to Claude

Date: 2026-09-06. User agrees to "accept weighted approximation, and prepare statements for the next batch of constants comparison, leaving sorry placeholders."

This batch adds eight statements to `thm:smooth-lipschitz-constant-equivalence`, preserving `by sorry`.

Ledger is **`drafted / checked_by: null`**. Seven previously proven nodes are separately recorded from this draft.

## Reading Entry and Sources

1. [HANDOFF](../../HANDOFF.md): current scope, proof certification, and append-only record rules.
2. [Blueprint Shared Analysis Bridge](../../formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex):
   `thm:smooth-lipschitz-constant-equivalence`'s original statement and proof; followed by
   `thm:selected-literature-constant-equivalence` still retaining independent Borell input.
3. [KLS/LocalSlopeGradient.lean](../../formalization/FunctionalInequalities/KLS/LocalSlopeGradient.lean):
   Four proof holes for slope, gradient, energy, and test domain.
4. [Poincare/Euclidean/LiteratureComparison.lean](../../formalization/FunctionalInequalities/Poincare/Euclidean/LiteratureComparison.lean):
   Four proof holes for finite constants, optimal values, and intrinsic coordinate comparison.
5. [Default Build Entry](../../solutions/ThmSmoothLipschitzConstantEquivalence.lean): only `#check` eight
   complete signatures, no new certificates. This batch does not import aggregated roots from certified libraries or old certificates, nor does it add `lean` anchors to Blueprint for unproven statements.

Precise mathematical sources are local written arguments and existing definitions; mathematical classification remains `local_argument`. Pointwise slope identification, test domain characterization, and coordinate infima are local interfaces that explicitly state implicit steps in the original proof, not attributed to unverified papers.

## Proof Order

The first four entries in the table are located at `FunctionalInequalities.KLS`; the last four at
`FunctionalInequalities.Poincare.Euclidean`.

| Order | Statement | Precise Purpose |
| --- | --- | --- |
| 1 | `localSlope_eq_norm_gradient_of_differentiableAt` | At differentiable points, the existing local slope defined by moving one point equals `ENNReal.ofReal ‖gradient f x‖`; no requirement for finite dimension or positive dimension |
| 2 | `localSlope_ae_eq_norm_gradient` | In finite dimensions, under ν ≪ Haar, locally Lipschitz functions satisfy the above equality ν-a.e. |
| 3 | `literatureEnergy_eq_lintegral_gradient` | Identifies slope energy as the integral of the extended gradient squared, allowing infinite energy |
| 4 | `literatureAdmissible_iff_memLp_gradient` | The original LiteratureAdmissible is exactly equivalent to locally Lipschitz, function L², and gradient L² |
| 5 | `holds_iff_literatureHolds` | For each C : NNReal, the smooth test and original literature test have equivalent admissible constant conditions |
| 6 | `constant_eq_literatureInfimum` | Under the same coordinate measure ν, the infimum of effective finite constants from two sets is equal |
| 7 | `constant_eq_intrinsic_and_literature` | For μ whose intrinsic measure is absolutely continuous, the original measure smooth constant equals the intrinsic measure smooth constant equals literatureConstant μ |
| 8 | `intrinsicAffineSmoothGradientRelaxationConstant_eq_literatureConstant` | Combining the existing legacy/selected certificate, connects the above equality to the selected constant in the project, retaining the same intrinsic absolute continuity assumption |

Step 1 expands from Fréchet differentiable remainder and operator norm upper and lower estimates to establish `localSlope`'s inf/sup; Hilbert gradient norm equals derivative norm. Special handling of the zero space must not rely on existence of a unit vector.
Step 2 reuses the recently proven local Lipschitz Rademacher, then transfers the zero measure set via ν ≪ m.
Steps 3 and 4 must complete a.e. energy conversion, measurability, and square integrability, without additional assumptions of target energy identity.

Step 5's one direction follows from smooth test being locally Lipschitz; the other direction uses the certified weighted approximation theorem for literature test, with B as identity map. Apply the same C term-by-term, then take limit using variance continuity under function L² convergence and energy continuity under gradient L² convergence. Do not treat these convergence conclusions as new unproven inputs.
Step 6 compares sets of finite admissible constants, without requiring attainment of optimal values.

Step 7 still requires connecting the smooth test inequalities of the original and intrinsic measures: the existing test restriction does not increase energy, normal constant extension preserves energy, and intrinsic L² isometry preserves variance. Then apply step 6 to the intrinsic measure. Step 8 is the combination of this conclusion with existing `constant_eq_intrinsicAffineSmoothGradientRelaxation`.
Even in direct combination, this batch retains the proof body for Claude as per user request.

## Coordinates, Quantifiers, and Boundaries

`KLS.LiteratureHolds ν C` directly tests functions on ν, but `KLS.literatureConstant μ`'s definition already
takes `Probability.intrinsicMeasure μ`. Thus step 6 explicitly writes `⨅ C : {C : NNReal // KLS.LiteratureHolds ν C}, (C.1 : ENNReal)`, rather than incorrectly substituting it with `literatureConstant ν` and then re-entering intrinsic coordinates. No parallel constant definitions or aliases are added.

In steps 7 and 8, the type of m is `Measure (Probability.affineSupport μ).direction`, with the absolute continuity assumption explicitly applied to `intrinsicMeasure μ`. The original measure μ may be singular in the ambient space, e.g., supported on a line with a probability law; it cannot be secretly endowed with ambient Lebesgue absolute continuity.

Constant C includes zero; optimal values remain in ENNReal, allowing infinity and nonexistence of effective finite constants. Energy has no additional half-factor; zero-energy functions are included. Except for the more general pointwise conclusion in step 1, all proceed in finite-dimensional Borel second-countable complete real inner product spaces. Zero-dimensional and zero-dimensional affine supports are preserved.

No requirement for second moments, density lower bound, log-concavity, or raw/core agreement. Especially, step 8 is an explicit absolute continuity condition comparison, so it cannot be used to consider `thm:selected-literature-constant-equivalence`'s general log-concave version or Borell nodes as proven. Current KLS definition, Statement, and golden remain unmodified.

## Existing Tools and Proof Boundaries

- `Energy.Euclidean.LipschitzApproximation.ae_differentiableAt_of_locallyLipschitz` and `measurable_gradient`: a.e. differentiability and measurability of the canonical gradient.
- Within the same module `exists_smooth_weighted_L2_approximation`: take B as identity map; both function and gradient have explicit L² membership conditions and difference eLpNorm convergence; cannot rely solely on function value approximation.
- `MeasureTheory.memLp_two_iff_integrable_sq_norm`: conversion of gradient L² to square norm integrability, must retain its a.e. strong measurability premise.
- `FunctionalInequalities.L2.continuous_variance`, `variance_toLp`, and `ProbabilityTheory.ofReal_variance`: connect L² variance to pointwise extended/real variance. The latter must be used under the condition that the original function belongs to L²; cannot infer integrability from totalized real variance.
- `Energy.Euclidean.SmoothGradientTest.exists_intrinsic_restriction` and `exists_ambient_extension`, and `Probability.measurePreserving_reconstruct`: coordinate bridge.
  Do not use the merely measurable branch of `intrinsicMap` outside the support as global smooth extensions.

These names are verified against the currently pinned local source code. Gaps exist in local proof adaptation to existing KLS definitions. `tasks.json` thus refines the infrastructure of this node from `unchecked` to `missing`, with source file hash and specific gaps; existing approximation nodes are `available`. No mathematics classification or long-path status of any node has been altered.

Claude may add useful auxiliary lemmas, or adjust public interfaces upon encountering issues; if altering the mathematical scope, must add supplementary explanation and sync ledger, verifying that the original target remains covered. Do not introduce a cyclic premise such as "existence of required approximation," do not rewrite Definitions/golden to make the target easier, do not loosen axiomatic checks.
Certificates for this node shall be created and registered upon completion of future proofs; no tasks are sent, no commits or pushes are made in this batch.

## Local Evidence and Two Snapshots

The weighted approximation has passed formal local verification, with receipt `build/verification/20260906T142018.550602Z/report.json`, status passed, source SHA256 `1a8ab75311a665296ff29a7c1b1be2d3d427fdd615016b7246c7f868afb6aa6c`, HEAD `70ca1c19c4d207a31716c2e589c0b096521a5490`. 97 test cases, default builds, 26 definition golden checks, 102 axiom statement reports, and 61 locally replayed kernel modules have passed. This snapshot does not include the eight draft items in this batch.

In the certificate, the universally quantified premises whose binder names are unused in the conclusion were subsequently given anonymous binders, with linting warnings cleared; the premises remain intact, representing only variable naming cleanup, without altering the mathematical content. The final validation in this batch will cover this final certificate version.

This batch `lake build solutions.ThmSmoothLipschitzConstantEquivalence` has passed, 3094 jobs, eight expected placeholder warnings; the fully printed signature retains the above coordinates, Haar, absolutely continuous, and finite-dimensional conditional properties. Each of the eight declarations' transitive axioms should include `sorryAx`, and must not be treated as proof acceptance. Original declaration printouts and inspection outputs are located in the ignored directory `build/density-acceptance/`, and are not considered new sources of truth or golden references.

After this record is complete, a final run of `verify.py` is performed on the final working tree. The final receipt's source SHA256 and log indicate verification of seven certified nodes and elaboration of draft content in the default build; ordinary draft modules may contain placeholders. Full validation passing does not imply that the eight declarations have been proven. The final receipt result is not pre-written as passed, nor is the hash written back to the source code. Local kernel replay trusts third-party compiled imports; no isolated rebuilds, remote CI, or release processes were performed.
