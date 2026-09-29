# Mathematical Object Namespace and Parameter Organization Migration

Baseline: `main`, `19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`, workspace starts clean.
User approves direct implementation; delivers local changes, without commit or push. Existing decisions/explorations remains unchanged.

## Pre-migration Checklist and Evidence

Complete declaration mapping see [machine-readable mapping](../api-migration/2026-09-08-name-map.json)].
`build/api-refactor/baseline/` preserves all 233 tracking files and SHA256;
`baseline-build.log` records the original default build passing (3349 jobs]), `baseline-golden.log`
confirms consistency between the original 26 declarations' golden and the baseline. `before-raw.json` preserves 1088 local declaration types and definitions expanded from 882 public declaration entry points; theorem proving is performed via compilation, axiom audit, and final kernel replay verification.
The original StatementSnapshot's pretty printer truncates internally on type length, so a non-truncated `Expr` representation is saved instead; lossless compressed files per declaration are located at `baseline-expressions/`. Printing truncation cannot be considered equivalent evidence.

## Objects and Ambient Spaces

- `Poincare.SmoothTest`: Global smoothness, L², and integrable square of gradient test constants.
- `Energy.SmoothGradient`: Ordinary gradient pre-energy and relaxation; `Intrinsic.energy` pulls back to the original L² space via intrinsic coordinates.
- `Energy.CovarianceGradient`: Covariance-weighted test `Test`, `Test.energy`, `preEnergy`, `relaxation`; `Intrinsic.energy` remains in the L² space of intrinsic laws. Corresponding constants appear in `Poincare.CovarianceGradient.Intrinsic`.
- `Energy.WeightedGradient`: External choice `B` of `B ∇`, `IsTest`, `operator`, and closure, without assuming B is a covariance factor.
- `Energy.LocalSlope`: Pointwise local slopes and square integrals; `Poincare.LocalSlope.Holds` on given coordinate laws, `Poincare.LocalSlope.Intrinsic.constant` first takes intrinsic measure.
- Probabilistic pushforward on `Probability`; L²'s `Translation`, `LinearIsometry`, `ContinuousLinearEquiv` respectively provide `pullback`, `pullbackInv`, and `pullbackEquiv`. Reuses Mathlib's `ProbabilityMeasure.map` and `Lp.compMeasurePreservingₗᵢ`, without establishing another general transport abstraction.

## Parameter Adjustment Checklist

The first stage only replaces declaration names, namespaces, and references; constructs the selected measure, operator, and reference Haar measure is kept explicit.
`WeightedGradient.IsTest.memLp` supports `hf.memLp`, two tests support `f.energy`, `f.toL2`.
Log-concave results retain property-proof calls in the form `hμ.theorem_name`. Any subsequent adjustments to section scope or redundant hypotheses
Must independently list and compare against actual elaborated parameters, and cannot be counted as pure renaming comparison.

## Mathematical Contract

The covariance factor only asserts `∃ B, ∀ v, ⟪Σ v,v⟫ = ‖B v‖²`, hence named `Covariance.exists_inner_eq_norm_sq`; it does not add any conclusions regarding square, self-adjointness, positivity, or uniqueness.
The direct ambient law's translation invariance yields `constant_translateLaw`, and the intrinsic measure is explicitly indicated in the intrinsic expression.
Differences in ordinary gradient versus covariance-weighted energy, ambient space versus intrinsic space, closed quadratic forms versus Dirichlet properties, zero-dimensional versus degenerate support, and distinction in infinite optimal constants are preserved. Stable node IDs, certificate entry points, and source tags remain unchanged.


## Final Interface Changes Reviewed

The complete list of actual parameter orders, visibility, and instance entries is in
[parameters.json](../api-migration/2026-09-08-parameters.json). Compare actual declarations from before migration `Expr`
and after migration `forallTelescope`; not inferred from `variable` text.
882 source code declaration entries within the library are merged into 881, of which 305 have parameter changes:

- 214 entries only remove redundant instances; 68 entries remove instances and adjust parameter ordering.
- 22 entries only adjust ordering. The usage of explicit mathematical input (probability laws, weights, reference measures, and proofs) remains unchanged.
- 1 entries are a merger of the real-valued second moment lemma and the general version:
  `ConditionalFiber.memLp_id_two_iff` and `memLp_id_two_iff'` are unified into
  `Probability.memLp_id_two_iff_lintegral_enorm_rpow_lt_top`.
  The real-valued specialization yields a Borel norm space carrier for any universe; the general version removes unnecessary Hilbert/finite-dimensional conditions.

Aside from this real-valued specialization, the number of public declaration universe parameters remains unchanged, and the visibility of non-instance parameters remains unchanged.
The two implicit parameters of `WeightedGradient.IsTest.smul` and `IsTest.weightedGradient_smul_ae` are adjusted from `… m g …` to `… g m …`; the complete parameter sequence (including instance ordering) is listed in the checklist.
All proof parameters derived from `LogConcave`, absolute continuity, finite moments, and integrability are retained.
Three certificate entry points (intrinsic absolute continuity, Borel density, closed covariance form) also remove redundant
`[CompleteSpace E]`; the finite-dimensional conditions remain, and the original use cases with completeness assumptions are still covered.
All other certificate entry point names and guards are preserved.

The new layered modules include `Probability.Transport`, `Probability.IntrinsicTranslation`,
`Probability.LocalDomination`, `Probability.Moments`, `L2.Transport`,
`Energy.CovarianceGradient.IntrinsicTranslation`, and `Poincare.CovarianceGradient.Transport`.
The covariance norm decomposition (including the intrinsic version) belongs to `Probability.CovarianceFactorization`.
The complete module migration and splitting are detailed in [module-map.json](../api-migration/2026-09-08-module-map.json)
and [module-splits.json](../api-migration/2026-09-08-module-splits.json). Old modules do not have forwarding wrappers.

All closing terms in the original 22 at `unusedSectionVars` are removed; the final default build does not issue such warnings.
WeightedGradient is grouped by differential, measurable test, and Haar/Rademacher; local measure domination is independent;
AffineSupport is grouped by geometric, closedness, full measure, and intrinsic coordinates; LipschitzApproximation separates the pure differentiability property of the kernel from Haar normalization. Local `omit` is retained when individual adjacent lemmas have weak assumptions, and the checker is always enabled. No new structural or typeclass with bundled environment assumptions.

## Semantic comparison results

[Audit overview](../api-migration/2026-09-08-review.json) and per-declaration records provide the following evidence:

1. **Pure naming phase**: 1088 local declarations have the same types and definition closures after alpha-renaming with explicit name mappings and variable bindings; all are identical, with no omissions, additions, or unexplained differences.
Independent stage mappings are preserved in `2026-09-08-renaming-stage-name-map.json`, avoiding re-interpretation of this phase using the final generalization mapping.
2. **Final source code**: 189 definitions/structures' bodies are identical after `.ilean` parsing and reference mapping. Among 882 source code signatures, 876 are identical; the remaining 6 are individually reviewed: second-order moment tensors are merged, intrinsic norm decompositions move explicit `μ` from the section into the theorem header, a completeness statement, and three finite-dimensional instances are moved from the section to their corresponding theorem headers. No modifications to formulas, test fields, energy normalization, or relaxation constructions are made.
3. **Final elaboration**: preserves 1085 current local declaration types and definition closures. In strict `Expr` comparison, 708 remain identical, while 375 change due to actual parameter adjustments (335), call adjustments depending on these interfaces (36), and compiler-generated proof renumbering (4). Additionally, 5 old generated proof auxiliary names no longer appear, and 3 new generated auxiliary names appear; all are `._proof_N` compiler artifacts, not omissions from public mathematical entry points. Two second-order moment entry points are merged into a single record. These interfaces cannot be generalized as merely "renamed" across the entire library.
4. **Statement golden**: The baseline 26 declarations initially pass verification against the original checkout, ultimately remaining 26 in number; roots, external trust boundaries, toolchain, and Lake dependencies remain locked (roots only under name mapping). Module ownership and same-type generated proof indices are aligned first; remaining 10 differences arise from removal of internal coordinate auxiliary definitions, redundant instances, and their calls; the quantifier count in `KLS.Conjecture` remains unchanged. See [golden-review.json](../api-migration/2026-09-08-golden-review.json).

Original `Expr` JSON and per-assertion lossless compression records in `build/api-refactor/`, including
`baseline-expressions.json`, `renamed-raw.json`, and `final-expressions.json`.
Assertion comparison tool used for verification, not replacing Lean kernel validation; theorem proofs are responsible by full build, axiom audit, and final kernel replay.

The infrastructure has 134 source hashes verified (82 repository source entries, 52 external dependency entries), with no baseline inconsistencies. Expand the source list based on the actual declared module ownership, then refresh 94 entries; do not first recalculate hashes before skipping difference review. 71 existing decisions/explorations are byte-for-byte identical.

## Acceptance and Final Receipt

Pre-acceptance completed: default `lake build` passed (3359 jobs); all 100 Python tests passed;
405 checks for the `#check_failure` old public names have all passed; Blueprint structure checks for 87 labels,
4 active routes, 0 errors, PDF/Web/checkdecls all passed. 37 PDF pages have been checked for full page thumbnails,
And magnify inspect the updated frontend, compare titles, and conditional-fiber certification boundary pages.
Default build adds `examples.ApiOrganization`, overriding `f.energy`, `f.toL2`, `hf.memLp`,
hμ.theorem name, any finite-dimensional carrier, zero-dimensional, zero weight and transport direction; existing degenerate support, infinite constant
Continue building with all certificate examples.

This record reviews and approves the current round of golden and infrastructure hash updates. The final execution from the root directory
`python3 research/verify.py`; the immutable runtime directory's `report.json` is the acceptance basis for the final build,
statement/axiom audit, and full current module kernel replay.
[`build/verification/latest.json`](../../build/verification/latest.json) points to this latest attempt.
This record is finalized prior to final verification; the receipt must match the final source code snapshot including this record and all control files.
No substitution of `git diff --check` for any semantic checks.

Intentionally retain stable ledger/Blueprint ID, historical spelling in certificate entry, Borel/Borell, L1/L2,
weighted, ae, compact support and boundary qualifiers. Blueprint's `C_P^can` and similar mathematical notations are still used as abbreviations for corresponding objects; public Lean API are named after mathematical objects and their ambient spaces.
This delivery is for local workspace only, without commit, push, or website publication; no new mathematical certification states added.
