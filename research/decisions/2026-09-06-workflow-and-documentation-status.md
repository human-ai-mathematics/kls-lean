# Workflow policy and current documentation status

**Date:** 2026-09-06 (Asia/Shanghai). **Authorization:** the owner instructed
“将我提到的这一点写进交接文档，然后修改文档状态滞后的问题”, referring to the preceding policy
“后面我们除了大的推送其他的都不用CL”. Work is local on `main`.

## Workflow policy

`HANDOFF.md` now records the owner's wording: CL is reserved for large pushes. Routine work and
small pushes proceed without a CL workflow, with local checks appropriate to the change.
The mathematical statement-freeze and Lean-certification rules continue to apply.

## Documentation corrections

- `formalization/README.md` and the Poincare foundation guide now consistently record the
  ambient/intrinsic and legacy/relaxed comparisons as proved. The former still denied both
  comparisons in its proof-boundary paragraph; the latter still listed the old/new constant
  equality among unfinished theorems.
- The root README and Poincare guide distinguish the locally Lipschitz comparison's written
  analytic proof in Blueprint Appendix A from its pending API freeze and Lean formalization.
- `solutions/README.md` now records 27 foundation axiom guards, matching
  `solutions/FoundationAxiomAudit.lean`, instead of the earlier count of 22.
- The handoff's closing boundary now names the already certified frontend equalities and the
  specific literature comparison still awaiting Lean certification.

The current evidence is the six-node production ledger, the proved comparison modules and
certificates, and the 27 guarded declarations. Earlier decision and exploration records retain
their dated snapshots; this correction does not rewrite them.

## Validation and scope

This change updates five live Markdown guides and adds this record. Lean sources, certificate
files, axiom guards, the ledger, Blueprint TeX and route metadata, and CI configuration are
unchanged from the start of this edit. No commit or push is included.

Validation passed:

- Ledger checker: six proved/Lean nodes, zero errors.
- Blueprint checker: eight chapter files, 86 labels, four active routes, zero errors.
- Existing Python suite: all 63 tests passed.
- All 93 local Markdown links in the five updated guides and this record resolve.
- Source-hash comparison confirms that only the five intended existing Markdown files changed;
  the Lean sources, certification data, Blueprint sources, workflows, and existing history retain
  their pre-edit hashes. The foundation audit contains exactly 27 guards.
- `git diff --check` passed.

The successful Lean build and transitive axiom audit from the immediately preceding status
analysis are separate evidence; this Markdown edit adds no new proof claim.
