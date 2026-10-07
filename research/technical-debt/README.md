# Formalization technical-debt register

Structural audit: **2026-09-20**, after the S0a layout cleanup. This is a worktree snapshot,
not a committed-revision certificate. No library source was changed by this audit.
The [classification workflow](../workflow.md) governs future remediation.

## Post-cleanup audit correction

The independent strict review found LD-010: the Bochner audit's one-dimensional normalization
check lost an implicit dependency, and the verifier did not compile research audit clients.
The [repair record](../decisions/2026-09-20-audit-coverage.md) documents the explicit import and
new snapshot-driven audit gate. Earlier successful receipts retain their original, narrower
scope; they do not establish that every research audit compiled.

## Independent-review follow-up

The [review remediation](../decisions/2026-09-20-review-remediation.md) fixes LD-011 (stale/orphan
artifacts available to research audits) and LD-012 (ignore rules silently hiding Lean families).
It also corrects the additional LD-001/002 current-navigation/status omissions and finishes the
LD-008 namespace syntax requirement. Earlier closure reports were incomplete on these points;
the original dated inventories remain evidence of what was checked then.

## Second independent-review closeout

The [closeout correction](../decisions/2026-09-20-review-closeout.md) resolves R1/R2 (the residual
MANIFEST and local output exclusions) and R3 (five unauthorized historical path rewrites).
Historical design text is restored; a separate live directory supplies current paths. The
previous “dated historical records are not rewritten” claim was inaccurate for those five
occurrences and is corrected by this append-only record. Existing no-sorry and discovery scope
boundaries remain explicit; these repairs do not expand mathematical certification.

## Third independent-review fixes

The third independent review found LD-013 (generic Energy modules reaching Energy declarations
only through a Poincare module) and LD-014 (one library module outside every gate scope), plus a
group of current-status and navigation defects that the earlier LD-001/002 closures had missed.
The [fix record](../decisions/2026-09-20-review-fixes.md) documents the declaration move, the
added audit client, the corrected live documents and the refreshed declaration locations. It also
corrects this review's own first reading of LD-013: the Poincare import of
`Energy/LocalSlope/Relaxation` is unused *by that module* but was load-bearing as a transitive
re-export, so removing it alone would have broken `Energy/Cheeger/Basic`.

## Scope and evidence

The scan covered **241 library modules**, **456 local import edges**, and **2,225 public
source declarations** reported by the available `.ilean` files. All 241 modules had `.ilean`
metadata. Declaration counts exclude private declarations and are not a count of all generated
Lean environment constants. Names and reference counts from build metadata are discovery aids;
flagged ownership questions were checked against source. An absence of library consumers does
not establish that an API is unused by audits, certificates or external clients.

The [module and declaration inventory](2026-09-20-layout-inventory.json) records source hashes,
imports, namespaces, direct library consumers, transitive import counts, declaration locations,
and screening signals. The [link inventory](2026-09-20-link-inventory.json) lists the 21 Markdown
files checked and every missing relative file target. It checks file existence, not remote URLs
or heading anchors. It includes one ignored local duplicate, identified below.

This is a whole-library structural scan with focused source review of flagged families, not a
new proof-correctness audit or an exhaustive judgment on every public name. It did not rebuild
the entire library, replay kernels, or renew a full-tree verification receipt. The only Lean
experiment was a strict compile of a temporary copy for LD-005.

First remediation: LD-001, LD-002 and LD-005 are resolved; see the
[batch record](2026-09-20-first-remediation.md) and its checks. The inventories above remain
the original audit snapshot. LD-009 was discovered during downstream validation.

Hausdorff remediation: LD-003 and LD-004 are resolved; see the
[placement decision](../decisions/2026-09-20-hausdorff-layout.md),
[source/declaration map](../api-migration/2026-09-20-hausdorff-layout-map.json) and
[checks](2026-09-20-hausdorff-checks.json). Historical audit counts below describe the original snapshot.

Interface remediation: LD-006, LD-007 and LD-009 are resolved; see the
[decision](../decisions/2026-09-20-interface-layout.md),
[migration map](../api-migration/2026-09-20-interface-layout-map.json) and
[checks](2026-09-20-interface-checks.json). LD-008 was subsequently completed in the final batch below.

Final remediation: LD-008 and LC-001/002 are resolved; LC-003/004 are reviewed accepted choices.
See the [decision](../decisions/2026-09-20-final-cleanup.md),
[migration map](../api-migration/2026-09-20-final-cleanup-map.json), and
[final checks](2026-09-20-final-checks.json). The final library has 252 modules and 2,225 public
source declarations. The original inventory and historical finding descriptions remain below.


## Findings and remediation status

Priorities mean remediation order, not mathematical severity: **P1** misleading current
navigation/status; **P2** ownership or dependency debt; **P3** naming consistency. “Open” means
confirmed evidence; the proposed destination still needs a scoped migration plan. No finding
below establishes a false theorem.

| ID | State | Priority | Finding | Recommended batch |
| --- | --- | --- | --- | --- |
| LD-001 | Resolved | P1 | 24 broken live README links and obsolete displayed paths | Documentation navigation |
| LD-002 | Resolved | P1 | Current source and overview prose retain obsolete Energy WIP status | Documentation status |
| LD-003 | Resolved | P2 | Generic normalized Hausdorff tools are owned by KLS | Geometry foundations, with LD-004 |
| LD-004 | Resolved | P2 | `Hausdorff/LevelSet` combines several independent mathematical roles | Geometry foundations, with LD-003 |
| LD-005 | Resolved | P2 | Generic local-slope relaxation imports log-concave absolute continuity unnecessarily | Small import cleanup |
| LD-006 | Resolved | P2 | Generic Poincare gradient comparison also owns a log-concave specialization | Poincare specialization boundary |
| LD-007 | Resolved | P2 | Closed weighted-gradient prerequisites are bundled with heat construction | Closed-gradient interface |
| LD-008 | Resolved | P3 | Older semigroup APIs and new domain APIs use inconsistent namespace organization | Explicit API migration |
| LD-009 | Resolved | P2 | Cheeger basics also own a log-concave specialization | With LD-006 specialization review |
| LD-010 | Resolved | P2 | Missing Bochner audit dependency and omitted research audit acceptance | Explicit import and automatic strict audit coverage; see repair record |
| LD-011 | Resolved | P1 | Audit clients can load stale or orphaned local artifacts | Full-scope build before audits; filtered search path and regression fixtures |
| LD-012 | Resolved | P3 | Packaging ignore rules hide Lean source families | Rooted ignore patterns and independent source-discovery gate |
| LD-013 | Resolved | P2 | Generic Energy modules obtain Energy declarations only through a Poincare module | Move the Energy-namespace lemma to its family; make the approximation import explicit |
| LD-014 | Resolved | P2 | `Analysis/Sard/Planar` is outside the certificate, audit and aggregate scopes | Add a research audit client with axiom reports |
| LD-015 | Resolved | P3 | Tilt, Bochner and Gaussian-smoothing families repeat the family term in flat basenames | Path-only family directories with a module map |

### LD-001 — navigation after migrations

Evidence: [Poincare README](../../formalization/FunctionalInequalities/Poincare/README.md)
lines 25 and 81 (2 broken links), [KLS README](../../formalization/FunctionalInequalities/KLS/README.md)
lines 52–222 (20), and [LogConcave README](../../formalization/FunctionalInequalities/KLS/LogConcave/README.md)
lines 13–14 (2). Exact occurrences are in the link inventory. Examples include `L2Energy.lean`,
`Geometry/RelativePerimeter.lean`, and `LogConcave/DensityBounds.lean`.
The [Energy README](../../formalization/FunctionalInequalities/Energy/README.md), line 21,
also displays obsolete flat paths such as `Cheeger.lean` and `Euclidean/SlopeRecovery.lean`.
Some Poincare link labels still display old paths even where targets were updated.

Repair live targets and labels using current modules and migration maps; verify the result by
relative-file checks and manual review of semantic destinations. Do not silently point an old
claim at a merely similarly named theorem. Two further missing links in the historical
[correction log](../proof-corrections-and-improvements.md), lines 141 and 156, are **not** included
in the 24 live defects. Preserve their chronology; add a provenance/migration reference if needed.

### LD-002 — obsolete completion prose

[LocalSlope/Relaxation](../../formalization/FunctionalInequalities/Energy/LocalSlope/Relaxation.lean),
lines 26–30, says the singular-law reverse comparison remains open in `Energy/WIP/Cheeger.lean`.
[Cheeger/Identification](../../formalization/FunctionalInequalities/Energy/Cheeger/Identification.lean),
lines 8–24, instead documents the completed comparison of the two slope relaxations for arbitrary
Borel laws, including `LocalSlope.relaxation_eq_asymptoticLipschitz`.
The [formalization overview](../../formalization/README.md), around lines 540–542, also points
to the deleted Energy WIP module. Its long status narrative mixes earlier “current” statements
with later parenthetical corrections (for example line 204).

Reconcile each live statement with its exact theorem. The initial audit checked the equality of
the two slope relaxations; remediation also checked the unconditional canonical smooth-energy
identity in the same Identification module. Both hold for finite-dimensional Borel probability
laws, including singular laws. Neither is raw-test agreement or a finite Poincare bound. Move or clearly label historical narrative; preserve dated
records. Acceptance requires source-level review of assumptions and normalization, not just
search-and-replace of “open”. A module saying a result is not proved **in that module** is not
by itself stale.

### LD-003 — normalized Hausdorff ownership

Four direct edges run from Analysis into KLS:

- `Analysis/Hausdorff/LevelSet` → `KLS/Geometry/Surface/Measure`.
- `Analysis/Lipschitz/Local` → `KLS/Geometry/Surface/Measure`.
- `Analysis/Vector/Slice/Hausdorff` → `KLS/Geometry/Surface/Measure`.
- `Analysis/Vector/Slice/Measurable` → `KLS/Geometry/Surface/Slicing`.

[Surface/Measure](../../formalization/FunctionalInequalities/Analysis/Hausdorff/Measure.lean),
lines 35–46, defines `unitBallVolume`, `hausdorffNormalized`, and `surfaceMeasure` for general
finite-dimensional inner-product spaces, without log-concavity. [Surface/Slicing](../../formalization/FunctionalInequalities/Analysis/Hausdorff/SurfaceSlicing.lean)
provides generic normalized wrappers but imports `SmoothDomain/Basic`; the latter also owns the
top-dimensional normalization theorem before its smooth-domain structure.

Plan a joint foundation extraction with LD-004, potentially into the existing
`Analysis/Hausdorff` family. The directory move and namespace change are separate decisions.
Acceptance: no generic normalization client needs the concrete KLS surface/smooth-domain layer;
all signatures and constants remain unchanged, including the zero-dimensional convention.
Recompile surface slicing, level sets, smooth domains and their downstream proof clients.

### LD-004 — LevelSet responsibility boundary

At the original audit, [Hausdorff/LevelSet](../../formalization/FunctionalInequalities/Analysis/Hausdorff/LevelSet.lean)
contained Prékopa–Leindler (line 230), volume combination/addition inequalities (247, 313),
isodiametry (414), volume/Hausdorff comparison (478), top-dimensional normalization (655),
and regular level-set charts and finiteness (734, 789). These roles, rather than its 816 lines,
are the reason to split. Direct consumers include graph area, rank-deficient exponent
obstruction, vector slice measurability and smooth-domain basics.

Separate the general volume inequalities, normalization, and level-set chart layers in dependency
order. Review together with LD-003 to avoid introducing a cycle. Acceptance: each client imports
the relevant layer, with unchanged mathematical scope and successful downstream validation.

### LD-005 — removable application import

[LocalSlope/Relaxation](../../formalization/FunctionalInequalities/Energy/LocalSlope/Relaxation.lean),
line 4, imports `KLS.LogConcave.Density.AbsoluteContinuity`; its own statements are generic.
No KLS constant use was found in its `.ilean` references. A temporary source copy with only
that import removed passed `lake env lean -DwarningAsError=true`. Production source is unchanged.

The static project import closure falls from **45 to 40** modules when this edge is removed:
`KLS.Definitions`, `KLS.LogConcave.Density.AbsoluteContinuity`, `KLS.LogConcave.Transport`,
`Probability.Domination.Averages`, and `Probability.Domination.Ball` disappear. This is a graph
measurement, not a measured build-time improvement. Before applying the change, compare elaborated
public signatures/definitions and check downstream clients for accidental transitive-import use.

### LD-006 — concrete wrapper in a generic module

[Poincare/LocalSlope/Gradient](../../formalization/FunctionalInequalities/Poincare/LocalSlope/Gradient.lean)
imports log-concave absolute continuity (line 3) for
`Intrinsic.constant_eq_iInf_gradient_of_logConcave` (line 93), alongside generic comparison
results such as `holds_iff_memLp_gradient` (line 35). This import has a real use, unlike LD-005.

Move the specialization to a suitable KLS log-concave comparison frontend while keeping generic
results independent. Review aggregate imports, audits and certificate anchors even though the
inventory reports no direct library consumers. Preserve public namespaces unless a separately
specified API migration is justified; validate both generic and log-concave clients.

### LD-007 — closure before semigroup generation

[HeatSemigroup/Basic](../../formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Basic.lean)
imports generated-semigroup machinery and defines `closedWeightedOperator` (line 53), its
closedness (60), and dense domain (66) before constructing `heatSemigroup` (74).
[HeatSemigroup/Energy](../../formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Energy.lean)
uses the closed operator and its energy identities, with no time evolution in its statements,
but reaches generation through Basic. Basic has 40 transitive project imports in this snapshot.

Extract the closure interface below heat construction; a `WeightedGradient` basic/closure pair
is a possible destination, subject to the family rule. This is a prerequisite to plan during
future closed-gradient work, not permission to create empty interface files. Preserve arbitrary
bounded `B`, the core/domain, and the energy normalization. Check generator, energy, and domain
clients; measure actual dependency reduction after extraction rather than predicting it here.

### LD-008 — semigroup API transition

Older APIs in `Analysis/Semigroup/Generated` remain in the broad `Analysis.Semigroup` namespace,
while S0a domain declarations use `Analysis.Semigroup.Generated`.
Older concrete `heatSemigroup_*` declarations in Basic/Markov sit in `KLS.LogConcave`, while new
domain declarations use `KLS.LogConcave.HeatSemigroup`. The narrow S0a cleanup deliberately left
older APIs intact, so discoverability and naming are currently inconsistent.

Plan a consumer-backed family migration, using the existing
[S0a migration map](../api-migration/2026-09-20-semigroup-layout-map.json) as provenance.
Avoid renaming merely to shorten spelling. Acceptance: an explicit old/new map, unchanged types,
parameter order and visibility, updated clients/metadata, and no compatibility aliases left behind.

### LD-009 — specialization in Cheeger basics

Found during LD-005 remediation: [Cheeger/Basic](../../formalization/FunctionalInequalities/Energy/Cheeger/Basic.lean)
contains the generic Cheeger definitions and absolutely-continuous comparison, followed by
`KLS.LogConcave.intrinsicSmooth_energy_eq_two_mul_cheeger` in its final namespace block.
The specialization uses `intrinsic_absolutelyContinuous`. Previously that dependency arrived
through LocalSlope/Relaxation; removing the generic module's import exposed it in a full build.
The first batch makes the dependency explicit without moving declarations.

Consider extracting this concrete wrapper into the existing KLS log-concave frontend together
with LD-006. Preserve namespaces and types unless separately mapped; inspect both sides for
cycles and update certificate/aggregate clients. Acceptance: generic Cheeger definitions and
comparisons no longer import log-concave density, while concrete clients retain the exact theorem.

### LD-013 — Energy declarations reached through a Poincare module

[Poincare/LipschitzGradient/Comparison](../../formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean)
owned `Energy.LocalSlope.energy_eq_integral_gradient`, whose two real consumers are
[Energy/Cheeger/Basic](../../formalization/FunctionalInequalities/Energy/Cheeger/Basic.lean) and
[KLS/LogConcave/WeightedGradient/Energy](../../formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Energy.lean).
`Energy/Cheeger/Basic` imports only `Energy/LocalSlope/Relaxation`, which in turn imported the
Poincare module without using any of its declarations, so both that lemma and
`LipschitzApproximation.exists_smooth_weighted_L2` reached the generic Energy layer as transitive
re-exports through `Poincare`. The project import closure of `Energy/LocalSlope/Relaxation` was 43
modules, 30 of which disappear once the edge is removed.

Resolved by moving the lemma into
[Energy/LocalSlope/Gradient](../../formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean),
beside the `energy_eq_lintegral_gradient` it rewrites with, dropping the unused Poincare import and
giving `Energy/Cheeger/Basic` an explicit `LipschitzApproximation.Approximation` import. The moved
theorem keeps its namespace, universe parameter, implicit type variable, hypothesis names,
parameter order and proof term; its `pp.all` signature and definition are byte-identical.
`Energy -> Poincare` direct edges fall from two to one, and the remaining one
(`Energy/SmoothGradient/NormalDirection`) has a real use.

### LD-014 — a library module outside every gate scope

`Analysis/Sard/Planar` had no consumer: not the root aggregate, no library, solution or example
module, and no research audit. Certificate import closures covered 174 of the 253 library modules,
audit import closures 225 and the aggregate closure 245; the union covered 252, and `Sard/Planar`
was the one module in none of them. Its public `sard_plane` and `volume_image_nonflat_eq_zero`
were consequently in no audited declaration closure, so only kernel replay — which accepts
`sorryAx` — saw them. An isolated Lake project experiment confirmed that a `sorry` placed there passes
the ledger token guard, the full-scope build and `leanchecker`.

Resolved by [research/audits/PlanarSardAudit.lean](../audits/PlanarSardAudit.lean), which restates
both theorems, records that the sharp `Analysis.sard` already covers the planar case, and prints
five standard-only axiom reports. This adds no certificate and changes no proof status.

### LD-015 — family terms in flat basenames (2026-10-07)

A basename scan after the 2026-10-07 BKL blocks found four tilt and four Bochner modules flat in
`Analysis/BakryEmery/` and four `GaussianSmoothing`-namespace modules flat in
`KLS/LogConcave/Density/`, against rule 1 of the family-directory convention; `TemperateIBP`
abbreviated `IntegrationByParts`. Resolved by a path-only move of 14 modules; see the
[decision](../decisions/2026-10-07-family-directories.md) and
[module map](../api-migration/2026-10-07-family-directories-map.json), which also list the
flagged prefixes reviewed and left in place. No declaration, statement or status changed.

## Reviewed candidates (original evidence and review questions)

| ID | Candidate | Evidence and required decision |
| --- | --- | --- |
| LC-001 | `Energy/Euclidean/LipschitzApproximation` role split | 1,028 lines, 73 public source declarations, seven direct library consumers. Gradient, measurability, kernel, Haar normalization and approximation sections serve distinct roles. Inspect minimal consumer needs before choosing a family split; preserve weighted integrability and approximation guarantees. |
| LC-002 | `KLS/LogConcave/Density/BorellRepresentation` role split | 880 lines, 40 public source declarations, five direct library consumers. Representative, moments, construction and intrinsic sections span several namespaces. Determine whether moments and construction can be separated without fragmenting the representation argument. |
| LC-003 | Formula-length names and redundant object prefixes | Three short declaration names have at least 65 characters; exact names and consumers are in the inventory. Two Gauss–Green names encode different support restrictions; one semigroup name encodes a generator-limit estimate. Preserve these distinctions. Review older `sequentialRelaxation_*` and flat graph APIs only with a concrete namespace/consumer plan. Length alone is not a rename criterion. |
| LC-004 | Helper visibility | Large files such as LipschitzApproximation and Graph/Implicit expose many source declarations. A zero external-library reference count does not establish privacy. Check aggregate, audit, ledger, example and external-client use before proposing any visibility reduction. |
| LC-005 | `Energy.LipschitzGradient.relaxation` defined under `Poincare/` | The definition and the five bridge theorems beside it live in `Poincare/LipschitzGradient/Comparison.lean` while carrying `Energy.*` namespaces. After LD-013 no Energy-layer module depends on them: the only consumers are that module's own bridges and `KLS/LogConcave/Isotropic`, which imports it anyway. The bridge theorems genuinely mix `Energy` and `Poincare` notions, so extracting only the definition would split a coherent bridge. Left in place; revisit if an Energy-layer consumer appears. |

## Reviewed signals that are not confirmed debt

- The local library import graph has **no cycles** and **no unresolved local module imports**.
- There are **no `X.lean` / `X/` collisions**. The two single-module directories,
  `Poincare/Euclidean` and `Poincare/LipschitzGradient`, are documented exceptions in the naming
  policy; they are not new findings.
- `Energy/Euclidean/Slope/Density` (1,202 lines), `Analysis/Graph/Area` (957), and
  `KLS/Geometry/Cheeger/Inequality` (811) were size-review signals. No split obligation follows
  from size alone. Similarly, the private helpers in `ConditionalFiber/EnergyComparison` do not
  constitute public-API debt merely because the file is substantial.
- `Poincare/README 2.md` is an old local duplicate explicitly ignored by `.git/info/exclude`.
  It is not tracked repository debt and was left untouched; its contents are not authoritative.
- Historical WIP paths in dated decisions and correction records are provenance, not live import
  failures. They must not be mass-rewritten to current paths.
- Cross-family edges are screening signals, not a universal forbidden-layer rule. Identification
  bridges may legitimately depend on both sides. No claim is made that all cross-family edges
  should be removed.

## Maintenance and completion

Keep IDs stable. Add new findings here with source evidence, mathematical responsibility,
consumer impact, proposed scope and an acceptance check. Distinguish **Open**, **Candidate**,
**Accepted exception**, and **Resolved**; record the reason and evidence when changing state.
A planned rename is not a completed migration. Resolve entries only after the actual change,
client/metadata updates and scope-appropriate verification, linking the resulting decision and
receipt. Preserve this dated inventory as a snapshot; take a new snapshot for a later audit.

No confirmed structural finding from this audit remains open. LC-001/002 are resolved,
LC-003/004/005 are accepted with the reasons in the final and fix decisions, and LD-013/014 are
resolved by the third-review fixes. This does not claim that all
possible future technical debt has been excluded, or change any proof-completion markers.
