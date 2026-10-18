# Independent downstream reuse and source-interface cleanup

Date: 2026-10-18. Baseline: `79fbe1afad6273224b47503cf4fb305890b6266a`, fully verified in
`build/verification/20261018T011543.378047Z/report.json`.
This is reuse and maintenance of existing Letwin/BKL, finite-tensorization and covariance infrastructure.
No existing theorem, proof, hypothesis, constant, normalization, dimension or certificate status is changed.

## Placement and actual consumers

- New clients stay in `examples/`: `MatrixIntegral`, `GeneratedSemigroup`, `FiniteProductCovariance`.
  They call mathematical owners and are registered in the existing `Examples` Lake target.
  They introduce no public library theorem or paper certificate.
- The matrix client retains an arbitrary real `C` and tests an indefinite matrix. Its identity-field
  case actually discharges the PSD bound, using the existing unbundled probability-measure class.
- The semigroup client exposed missing bounded-operator forms of existing pointwise properties.
  Extend `Analysis/Semigroup/Generated/Laws.lean` with `Generated.norm_operator_le_one` and
  `Generated.operator_add_time`. The closedness, density, real Hilbert and nonnegative-time
  hypotheses are unchanged; no new import, alias, rename or simp attribute is added.
  An additional `Generated.operator.congr_simp` is compiler-generated support, not a new authored interface.
- The product client keeps the smooth-test frontend. The `[1, 0, 4]` Gaussian variance family,
  a Dirac marginal and the empty product are exercised. Covariance translation is checked for
  this same product law without claiming equality of different energy frontends.

## Independent acceptance and caller friction

The first separate Lake project requires the remote Git repository at the full baseline SHA
and `subDir = "formalization"`. Its primary project modules start without compiled outputs and
are all freshly built. Pinned clean third-party checkouts and their compiled caches are copied
separately after slow Mathlib full-history Git transport is stopped; this trust boundary is explicit.
All paths used for the project are in the fixture, apart from the pinned toolchain. The initial
probe passes strict elaboration, four standard-axiom reports and 33 narrow-module kernel replays
(32 project modules plus its client), with 3,160 Lake jobs and no KLS/solution/example imports.

Later clients use a separate consumer. The proposed additive API is an explicit source overlay
on the baseline checkout, not an assertion that the unpublished changes occur in that Git commit.
The current examples require matching current interfaces. Each client batch has strict compilation,
standard-axiom and kernel checks, and its own acceptance before the next batch. Failed experiments
and transport/setup diagnostics remain preserved in the ignored output directory.

The measured caller friction leads to two small bounded-operator facts. The matrix and product
APIs need no library migration, extra assumptions or new abstraction. External package loading
requires no source-layout change.

## Source documentation and namespace openings

The semigroup-law, generator and HminusOne headers now describe mathematical purpose, retained
scope and entry points. Their route/controller narratives are preserved verbatim in the
[source-interface history](2026-10-18-source-interface-history.md).
The quoted HminusOne opening was already section-local. Remove duplicated file-level openings
and the compiler-confirmed unused `Filter`, `Topology`, `Set`, then open the mathematical owners
inside the existing namespace with shorter names. No import or namespace migration is performed.

For all 42 original declarations of these three modules, structural type/definition trees,
universe/binder information, theorem expression hashes and used constants match the accepted baseline.
The original proof text is retained. Only the two authored API properties and one generated support
are added. The two infrastructure evidence hashes in `research/tasks.json` are reassessed after
this comparison; mathematical classifications, assumptions, assessed states and gaps stay unchanged.

## Empty-directory cleanup

The only empty canonical source leaf was `KLS/LogConcave/HeatSemigroup/PoissonIterate`.
The existing 2026-10-07 per-paper map records its relocation to `KLS/BKL/PoissonIterate`, where all
8 Lean files remain. Remove only that truly empty directory with `rmdir`; no file bytes or Git
entries change. The canonical source tree has no remaining empty leaves at that check.

## Validation and delivery boundary

The scoped/full receipts, exact snapshots, source overlays and comparison scripts are kept in
`build/reusability/2026-10-18-downstream-and-examples/`. The final proposed tree needs the complete
local verifier plus current link, generated-progress and module-inventory checks. The original
real index/staging and all pre-existing dated records stay unchanged. Progress generation uses
an intended task-local index; generated blocks are not edited by hand. This work advances no
paper or certificate status and includes no new commit/push, remote CI or milestone tag.

## Previous handoff evidence and delivery text (verbatim)

The following block was superseded as a current-work description. Its receipts retain their own snapshots:

```text
## Verification evidence

The last frozen-source full receipt is `build/verification/20261017T182503.125701Z/report.json`:
297 gates, 282 strict audit clients and 864 local-module kernel replays. It audits every
project-local declaration, including `KLS.kls`, with no target exclusion. Known
[vendored holes](formalization/vendor/README.md#upstream-holes) remain outside the proved local dependency closures.

The layout receipt chain and cumulative checks are indexed by
`build/file-management/2026-10-17-other-families-optimization/COMPLETION.json` and its `REPORT.md`.
The final documentation review and staged-input comparison (including six corrected module
docstrings, with all bytes outside those headers unchanged) are retained under
`build/file-management/2026-10-18-final-docs-and-push/`.
These ignored local artifacts apply to their recorded snapshots. Documentation checks do not
renew the full Lean receipt; see [receipt scope](research/verification.md#receipts-and-trust-scope).

## Coordination and delivery

All proof API loops are idle; the original Claude session remains the canonical proof integrator.
The queued review follow-up is paused. Sealed failures and earlier controller records remain
historical evidence and do not override this handoff.

The user authorized final documentation cleanup, one commit and an ordinary branch push on
2026-10-18. This delivery preserves the accepted mathematics and excludes local editor configuration.
The [previous handoff](research/decisions/2026-10-18-pre-final-documentation-handoff.md) preserves the superseded detail verbatim.
```
