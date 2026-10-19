# Section-variable scope review

This is readability maintenance for existing KLS, Letwin and BKL infrastructure, with no change
to paper coverage or certificate status. Mathematical ownership and imports are unchanged;
there are no new modules, public names, structures, aliases or bundled assumptions.

## Shared regular-source hypotheses

The four CEK owners
[`WeakDerivative`](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean),
[`WeakHessian`](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakHessian.lean),
[`Cutoff`](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Cutoff.lean) and
[`TraceStein`](../../formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean),
and Letwin's
[`RegularClass`](../../formalization/FunctionalInequalities/KLS/Letwin/RegularClass.lean)
share their regular-source binders within each file. Nineteen source-law theorem headers
use local `include` for the original nine premises. The chosen law stays explicit, the
dimension and source data retain their original implicitness and ordering, and generic
auxiliary lemmas do not inherit regular-source assumptions.

These are the same positive-dimensional, compact convex source laws with nonempty
interior, smooth uniformly convex potential and isotropic probability normalization.
No noncompact Letwin theorem is added.

## Repeated instance exclusions

[`Tilt/SquareIntegrable`](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean)
groups integral calculus and scalar L² results separately from the complete-space vector
average results. [`Cumulant/Basic`](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean)
separates Laplace calculus, third-moment identities and coordinate estimates from the
conditional Letwin application.
[`TensorEnergy`](../../formalization/FunctionalInequalities/Analysis/BakryEmery/TensorEnergy.lean)
groups coordinate-gradient identities, coordinate symmetry and tensor symmetrization.
Each named section shares exactly the previously repeated instance omissions and ends
before results requiring the stronger context. Additional theorem-local omissions remain
where the scope actually differs. These eight modules retain their existing linter settings.

## Anonymous instance premises and enabled checks

The owned library no longer directly disables `linter.unusedSectionVars`. The seventeen
previous suppressions in the fourteen modules below are removed. Compiler diagnostics
identified nineteen declarations with unused automatically included premises; the
suppression on `cumulant_compactPosterior` was unnecessary. The mathematical assumptions
remain in the interfaces, as anonymous theorem-header binders in their original order.
Five `unusedVariables` exceptions remain for the explicit `hK`, `hac`, `hρ` and two
`hu01` arguments; their names and proof bodies are retained. The earlier count of four
missed the independent Minkowski coarea inequality.

| Owner | Scope organization |
| --- | --- |
| [`Cumulant/MomentBound`](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/MomentBound.lean) | The sole theorem declares its full ambient context directly |
| [`Energy/Cheeger/Identification`](../../formalization/FunctionalInequalities/Energy/Cheeger/Identification.lean) | The sole intrinsic identification theorem declares its ambient context directly |
| [`BKL/CompactReduction`](../../formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean) | Operator helpers share the inner-product context; measure helpers share the normed-group context; each statement declares the retained remaining structure |
| [`BKL/Localization/Process/Integral`](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean) | The product almost-everywhere lemma declares its probability instance locally |
| [`Cheeger/DistanceCutoff`](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/DistanceCutoff.lean) | The estimate declares its second-countability and finite-dimensionality tail locally |
| [`Cheeger/Equality`](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Equality.lean) | The intrinsic comparison declares the ambient tail locally |
| [`Cheeger/MinkowskiContent`](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/MinkowskiContent.lean) | The coarea estimate declares finite dimensionality locally |
| [`Coarea/Isoperimetry`](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Isoperimetry.lean) | The sole theorem declares its full ambient context directly |
| [`Slice/Measurable`](../../formalization/FunctionalInequalities/KLS/Geometry/Slice/Measurable.lean) | The sole theorem declares its full ambient context directly |
| [`SmoothDomain/GaussGreen`](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/GaussGreen.lean) | The surface-measure local-finiteness theorem declares the ambient tail locally |
| [`SmoothDomain/RegularSuperlevel`](../../formalization/FunctionalInequalities/KLS/Geometry/SmoothDomain/RegularSuperlevel.lean) | Frontier geometry shares only the normed-group context; the Sard result declares the stronger retained premises |
| [`LogConcave/ConditionalFiber`](../../formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean) | The fiber theorem declares the ambient tail and its dependent laws together |
| [`Diffusion/Transport`](../../formalization/FunctionalInequalities/Probability/Diffusion/Transport.lean) | The linear transport theorem declares finite dimensionality locally |
| [`Posterior/LogPartition`](../../formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean) | The smoothness and log-Laplace results declare the ambient tail locally; the cumulant result needs no suppression |

A local `omit` removes the automatically inserted tail before the theorem reintroduces
those same anonymous binders. Moving the whole dependent tail, including laws where
necessary, retains parameter order and avoids duplicate measurable-space instances.
This is an interface-preserving organization of existing premises, not a weakening.

Lean's `include` accepts named variables in the pinned toolchain. It cannot select an
anonymous instance by its type. The direct header binders keep instances anonymous.
Compiler-generated hygiene identifiers can change when these binders move; comparison
erases only their macro-scope suffixes, retaining all public labels, binder kinds,
counts, order and exact type hashes. The full elaborated type/definition snapshots of
all 180 owned declarations are byte-identical, and all 108 authored bodies are unchanged.
The compiled values of these declarations, including 168 theorem proofs, also retain
the same structural hashes; the comparison baseline is bound to its source hashes.

## Further property and instance scopes

Eight further modules retain their existing owners, imports and namespaces. Sixteen theorem
headers share repeated property premises in their original telescope order. Each theorem
uses local `include`; no hypothesis is added to neighboring translation or geometric helpers.

| Owner | Scope organization |
| --- | --- |
| [`LogConcave/Covariance`](../../formalization/FunctionalInequalities/KLS/LogConcave/Covariance.lean) | Share the law and `hμ`; the ambient context no longer declares completeness that all four statements already omitted |
| [`LogConcave/ClosedForm`](../../formalization/FunctionalInequalities/KLS/LogConcave/ClosedForm.lean) | Share `hμ` within the five covariance-relaxation properties; translation remains independent; remove the completeness context already omitted by every statement |
| [`LogConcave/Borel`](../../formalization/FunctionalInequalities/KLS/LogConcave/Borel.lean) | Inner-measure properties and compact combinations have separate shared instance exclusions |
| [`Regular/Affine`](../../formalization/FunctionalInequalities/KLS/LogConcave/Regular/Affine.lean) | Share the regular-potential premises for the three affine-law statements; group the two inverse-map evaluations separately |
| [`Line/SharpHardy`](../../formalization/FunctionalInequalities/KLS/LogConcave/Line/SharpHardy.lean) | Clipped-test lemmas include their own premises directly instead of globally including six premises and repeatedly omitting most of them |
| [`GaussianSmoothing/Growth`](../../formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Growth.lean) | Centered factorizations and Laplace regularity share local exclusions; uniform derivative bounds retain their original stronger context |
| [`GaussianSmoothing/Hessian`](../../formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Hessian.lean) | Remove a duplicated ambient variable block and the completeness context already omitted throughout; explicitly retain the original universe name `u_2`; group posterior probability, score moments and second moments separately |
| [`WeightedGradient/Basic`](../../formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Basic.lean) | Share `hμ` only in the four intrinsic property lemmas, after the existing Haar measure and weight operator; the operator definition keeps its own premises |

The number of `omit` commands in these eight modules decreases from 72 to 20. The complete
elaborated type/definition snapshots of their 169 owned declarations, including generated
declarations, are unchanged. Public parameter labels, binder kinds and order are retained;
only anonymous compiler hygiene suffixes are normalized in the separate label comparison.
All 114 authored declaration bodies and all 169 compiled values, including 158 theorem proofs,
are unchanged. Strict compilation keeps both variable linters enabled. The full default build,
an explicit build of all eight owners, and an affected-declaration axiom audit pass.
This does not renew the earlier full local-verifier or kernel-replay receipts.

## Retained explicit-hypothesis exceptions

The five remaining sites were tested with narrow `variable` contexts and explicit
`include`, keeping the statements and authored proofs intact. In pinned Lean 4.33.0,
an unused explicitly included hypothesis still triggers `unusedSectionVars`. This
also occurs in a minimal example with `variable (h : True)`, `include h`, and
`theorem includeStandalone : True := by trivial`; using `include h in` has the same result.
Moving the premises therefore replaces one suppressed warning with another.
The existing theorem-local `unusedVariables` exceptions are retained; no new
`unusedSectionVars` suppression is introduced.

`omit` acts on section variables, not on declaration-header binders. Omitting an included
hypothesis removes that parameter from the exported theorem. Restating it in the header
restores the original `unusedVariables` warning. Removing these exceptions would require a
separate change to linter behavior, parameter labels or proofs; this review changes none of them.

| Owner and theorem | Retained hypothesis | Additional warning from the scoped trial |
| --- | --- | --- |
| [`Coarea/Isoperimetry`](../../formalization/FunctionalInequalities/KLS/Geometry/Coarea/Isoperimetry.lean), `lintegral_enorm_gradient_mul_eq_lintegral_levelSet` | `hK` | Anonymous `SecondCountableTopology V` |
| [`Cheeger/DistanceCutoff`](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/DistanceCutoff.lean), `lintegral_enorm_gradient_distanceCutoff_le` | `hac` | Anonymous `SecondCountableTopology V`, `FiniteDimensional ℝ V` and `m.IsAddHaarMeasure` |
| [`Cheeger/Equality`](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Equality.lean), `smoothConstant_mul_lintegral_min_superlevel_le` | `hu01` | None besides the included hypothesis |
| [`Cheeger/MinkowskiConstant`](../../formalization/FunctionalInequalities/KLS/Geometry/Cheeger/MinkowskiConstant.lean), `minkowskiConstant_mul_lintegral_min_superlevel_le` | `hu01` | None besides the included hypothesis |
| [`LogConcave/ConditionalFiber`](../../formalization/FunctionalInequalities/KLS/LogConcave/ConditionalFiber.lean), `ae_conditionalFiber_logConcave` | `hρ` | Anonymous `CompleteSpace E` |

All five source files are byte-identical to the saved baseline for this follow-up.
Strict compilation passes with both linters enabled globally and the existing local
exceptions. The failed scope trials and the minimal compiler reproduction are retained
under ignored `build/reviews/`; they do not change theorem or certificate status.

## Acceptance checks

Compare all elaborated declarations owned by each affected module, including private and
generated declarations: names, universes, binder explicitness/order and full types, plus
definition bodies. Compare every authored declaration body separately. For restored
checks, compile the affected sources with `-Dlinter.unusedSectionVars=true` and
`-DwarningAsError=true`; compile actual consumers and run a full library build when the
context has broad downstream use. Audit the affected declarations' transitive axioms.
Source evidence hashes are refreshed only after comparison with the saved dirty baseline.

The first eight-module batch has its full local-verifier receipt. The fourteen-module
batch has strict source compilation, a full build, exact interface/body comparisons and
an affected-declaration axiom audit; it does not renew the earlier full kernel-replay
receipt. No proof body, public API or module path changes, so this scope-only batch does
not require a new complete kernel replay under the classification workflow.

Exact source hashes and execution logs stay under ignored `build/reviews/`. The current
owners, comparison boundaries and checks above are available in a fresh clone without
local operational history. Earlier receipts retain their original snapshot scope.
