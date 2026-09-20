# Second independent-review closeout (2026-09-20)

The second independent review confirmed the filtered-module audit repair, unchanged semigroup
interfaces, and current certificate/proof-status statements. It found three remaining P3 issues.
This record corrects the earlier closeout claims without rewriting their dated evidence.

## R1 and R2: remaining ignore patterns

The root packaging rule `MANIFEST` is now `/MANIFEST`. The local `.git/info/exclude` rule
`output/` is now `/output/`, preserving root output artifacts without excluding nested Output
families. The latter is host-local Git metadata, not a tracked repository policy; other checkouts
may have different local/global excludes. The existing source-discovery gate continues to reject
production/audit Lean files omitted from their Git-aware snapshot.

The case-insensitive Git regression now includes Manifest and Output under the library, audit
and solution roots, with a local `/output/` exclusion. It also checks that root MANIFEST and
output artifacts remain ignored. Actual host `git check-ignore` checks confirm that the two
reported nested source paths are no longer excluded.

## R3: restore historical records, separate live navigation

The previous remediation changed five path occurrences in three dated design sections despite
claiming that dated records were unchanged. That claim was inaccurate. The tail of
`LEAN_DESIGN.md`, beginning with “Mathematical API organization (2026-09-08)”, is restored
byte-for-byte from `build/review-remediation/before/LEAN_DESIGN.md`. This restores the reviewed
pre-remediation history rather than imposing current paths on past records.

The current semantic boundary remains intact. A separate live path directory precedes the
historical records and maps the sixteen distinct relocated paths, including the remaining graph,
Sard, perimeter and smooth-domain paths. Deleted WIP references remain historical provenance.
No Lean declarations, proof bodies, certificate status or mathematical scope change.

## Verification scope

A successful receipt is not a universal no-sorry guarantee. Outside certificate import closures
and explicitly audited declaration sets, a new library sorry need not fail the existing gates;
kernel replay accepts sorryAx. The observed single intentional library hole is a current-source
finding, not an invariant enforced over every possible future declaration. Discovery checks cover
the production library and aggregate, solutions, examples and research/audits; scratch tooling
and third-party dependencies retain their documented separate scope.

The expanded ignore regression and history/link checks pass. The full verifier is run after all
tracked changes are finalized, producing a separate snapshot-bound receipt under build/verification.
The local exclude change is checked separately because that file is outside the source snapshot.
No commit, push, cache deletion or staging change is performed.
