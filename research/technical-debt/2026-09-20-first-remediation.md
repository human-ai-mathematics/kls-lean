# First layout-debt remediation batch

Date: 2026-09-20. Scope: LD-001, LD-002 and LD-005. This batch precedes further proof work;
the larger ownership/API migrations remain separately tracked in the [register](README.md).

## Placement and interface plan

Keep local-slope relaxation in its existing generic Energy family. Remove only its unnecessary
log-concave absolute-continuity import. Put that import explicitly in the existing
`Energy/Cheeger/Basic` client, which actually uses the log-concave specialization. No module split,
new module, public rename, parameter change or proof edit belongs to this batch. Update current
navigation and completion prose against source; retain dated records and the original audit
inventories. Validate elaborated interfaces, downstream builds, links and evidence hashes.

## Changes

- Repaired all 24 missing live README targets from the audit, using the existing module migration
  maps. Updated stale displayed Poincare paths and Energy family paths in the same navigation.
  The two missing historical correction-log links remain historical references.
- Updated LocalSlope/Relaxation, the Energy and Poincare guides, and the formalization overview:
  `Cheeger/Identification` proves the canonical-energy identity for every finite-dimensional
  Borel probability law, including singular laws, and equality of the two slope relaxations.
  These claims concern relaxed energies, allow infinite values, and do not imply raw-test
  agreement or a Poincare bound. Dimension-free KLS remains open.
- Clearly labelled old overview and KLS WIP counts as historical. No dated decision, exploration
  or correction-log text was rewritten.
- Removed the KLS import from generic relaxation. Full downstream compilation exposed
  `Cheeger/Basic`'s existing reliance on the transitive import, so its genuine dependency is now
  explicit. The module's specialization ownership is separately recorded as LD-009.
- Refreshed the three evidence-hash occurrences for the two edited Lean files in
  `research/tasks.json`, after checking the old hashes against the saved dirty baseline.
  The standard verifier also detected an already-stale `research/naming.md` evidence hash from
  the preceding workflow edit. Its old hash matches the prior receipt; reviewing the change
  confirmed that the classification rules preserve mathematical scope, so this fourth evidence
  occurrence was refreshed too. Proof statuses, certificate registrations, theorem declarations
  and source paths are unchanged.

## Validation record

Detailed local artifacts are under `build/debt-batch1/` (ignored). The source baseline includes
tracked and untracked non-ignored files and the actual staged diff. The pre-change Cheeger
snapshot uses the copied modules from the prior verification receipt; its source hashes are
checked against this turn's baseline before use. No prior receipt is asserted to certify the
new working tree.

The completion summary is recorded in [batch checks](2026-09-20-first-remediation-checks.json).
The standard verifier's fresh receipt, when run, remains in `build/verification/`; it binds its
own snapshot and is distinct from remote CI. No commit or push is part of this batch.
