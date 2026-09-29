# Comparison short names do not restate the full type

From the complete naming inventory, the user identified three covariance-relaxation comparisons
as still too long. This round shortens those and related Poincaré-frontend comparisons,
12 public theorems in total, without changing namespaces, modules, definitions, or parameter
interfaces. Continue from the verified local tree, with baseline snapshot
`192ddba6daa0f0d0f0bdc3fdab82bb5bc180414f1c3f4809c73f3cf4c4229684`, corresponding to
`build/verification/20260908T122939.817508Z/report.json`.
Branch remains `main`, HEAD `19cd996817d1c31c6fe46e949e19a51cb7cc5ae2`;
all prior uncommitted work is preserved as the baseline.

## Names and contracts

The complete map is [comparison-name-map.json](../api-migration/2026-09-08-comparison-name-map.json).
State the shared operation once in each short name; use comparison-object names sufficient
to distinguish them within the namespace. Types and documentation retain every premise and
exact equality; shortening names does not change mathematical contracts.

| namespace | Previous short name | Current short name |
| --- | --- | --- |
| `Energy.CovarianceGradient` | `relaxation_eq_lipschitzGradient_relaxation_of_covariance_eq_id` | `relaxation_eq_lipschitz` |
| Same as above | `relaxation_eq_sequentialRelaxation_ofLinearPMap` | `relaxation_eq_ofLinearPMap` |
| Same as above | `relaxation_le_opNorm_mul_lipschitzGradient_relaxation` | `relaxation_le_mul_lipschitz` |
| `Poincare.SmoothTest` | `holds_iff_smoothGradient_preEnergy` | `holds_iff_preEnergy` |
| Same as above | `holds_iff_ambient_smoothGradient_holds` | `holds_iff_ambient` |
| Same as above | `constant_eq_ambient_smoothGradient_constant` | `constant_eq_ambient` |
| Same as above | `holds_iff_intrinsic_smoothGradient_holds` | `holds_iff_intrinsic` |
| Same as above | `constant_eq_intrinsic_smoothGradient_constant` | `constant_eq_intrinsic` |
| Same as above | `constant_eq_lipschitzGradient_constant` | `constant_eq_lipschitz` |
| Same as above | `holds_iff_localSlope_holds` | `holds_iff_localSlope` |
| `Poincare.LipschitzGradient` | `holds_iff_localSlope_holds` | `holds_iff_localSlope` |
| `Poincare.SmoothGradient.Intrinsic` | `constant_eq_localSlope_constant_of_ac` | `constant_eq_localSlope` |

The first theorem still requires identity covariance, absolute continuity, and a null support
boundary. The second's right side remains sequential relaxation of the pre-energy constructed
by `PreEnergy.ofLinearPMap`, not the unrelaxed squared operator norm. The third still bounds
covariance relaxation by the covariance operator norm times Lipschitz relaxation, requiring
the latter finite at the point. Its name retains `mul` and does not imply coefficient-free
domination. Intrinsic optimal-constant comparison retains absolute continuity. Removing a
condition from a name does not remove it from the type.

## Semantic review

At entry, the entire source snapshot was checked against the previous passing receipt.
Current source and `.ilean` declarations/reference positions were saved to
`build/api-comparison-names/baseline/` and `ileans.json`. References are replaced using
resolved declaration identities, updating source, all consumers, guards, Blueprint anchors,
and guides. No aliases, wrappers, parameter generalization, removed assumptions, or disabled linters.

Library-wide source comparison covers 881 public signatures, 189 definition/structure bodies,
and 885 named declaration bodies including proofs; all agree after name mapping and format
normalization, without omissions or unexplained differences. Additionally, raw Lean Expr
types and definition closures of 132 local declarations reachable from the 12 affected
theorems agree after name mapping and binder alpha normalization; 291 external dependency
leaves are unchanged. Modules, universes, parameter order, explicitness, and dependencies are
unchanged. Anonymous instance parameters of the 12 renamed entries differ only in compiler
hygiene hashes; modules and local hygiene indices agree individually, and explicit parameter
names are unchanged. Raw differences and review are in
[comparison-name-review.json](../api-migration/2026-09-08-comparison-name-review.json).

All 26 existing statement golden checks pass; golden files and their existing decision are
unchanged. These theorems do not change that definition closure; renaming does not justify
unconditionally regenerating golden files. The 90 prior historical decisions, explorations,
and migration evidence files remain unchanged. Check 158 infrastructure source hashes against
the baseline, then refresh 13 hashes across 7 files based on source comparison. Paths,
assessments, and certification status stay unchanged. See the
[source review](../api-migration/2026-09-08-comparison-name-evidence.json).

## Acceptance

Pre-acceptance default build passes (3359 jobs); all 12 old names pass `#check_failure`,
and all 12 new names resolve. Existing certificates, property-proof calls, general
finite-dimensional and zero-dimensional applications still build. Blueprint PDF/Web/checkdecls
pass; the PDF remains 37 pages, with all rendered page content identical to the previously
reviewed version. The naming inventory is re-exported from current public declarations for
continued user review.

After finalizing this record, run root `python3 research/verify.py`, retaining all Python tests,
builds, statement snapshots, declaration/transitive-axiom audits, and kernel replay of all
current local modules. Final results are in `build/verification/<UTC timestamp>/report.json`,
with the latest attempt at `build/verification/latest.json`. The final receipt must match the
actual source including this record; `git diff --check` is only a formatting check.
No commit, push, or publication in this round.
