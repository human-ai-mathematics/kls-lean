# Remaining-family documentation correction (2026-10-17)

This is the first independently checked batch of the remaining-family maintenance review.
It changes current navigation and module documentation only. Published theorem scope,
constants, dimensions, proof declarations, certificates and paper coverage stay unchanged.

## Placement and corrections

- Extend the existing Poincare guide: the dimension-free KLS target is proved in
  [KLS/Target](../../formalization/FunctionalInequalities/KLS/Target.lean); energy identification
  alone still supplies no finite Poincare bound or raw-energy agreement.
- Repair thirteen current path references in the LogConcave guide, naming table and source
  module documentation using the existing filename/BKL migration maps. Historical records
  keep their original references.
- Describe the trace-energy, tensor and later algebra sections by responsibility rather than
  calling each one the final section.
- Clarify that the early CEK cutoff package differs from the later same-witness trace and
  weak Stein producers. The regular-class producer is separate from the Stein kernel interface;
  no global C2, gradient diffeomorphism or unrestricted-source construction is asserted.

Owner and destination: existing current guides and source module docstrings. Imports and public
API are unchanged. This is an extend-only documentation batch; no module split or move occurs.

## Validation and receipts

The batch compares every existing Lean source after removing comments, reviews current paths
and local links, checks generated navigation and progress freshness with a private Git index,
and preserves the original real staging and unrelated dirty tree. Prose alone does not require
a Lean rebuild. Checks and the scoped acceptance receipt are retained under
`build/file-management/2026-10-17-other-families-optimization/batch-00-docs/`.

The previous full verification receipt remains evidence for its original snapshot. This batch's
scoped acceptance does not renew that receipt or advance proof/certificate status.
