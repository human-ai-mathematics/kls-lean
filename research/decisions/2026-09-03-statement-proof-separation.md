# Statement and proof ownership in the Lean ledger

**Date:** 2026-09-03 (Asia/Shanghai)

## Decision

Use the lifecycle `drafted → frozen → proved`. Codex prepares candidate statements, encoding
decisions, documentation, and compilable Lean skeletons with `sorry`. Human review alone freezes
the public statements. A separate proof agent then replaces the placeholders while preserving
the frozen public signatures and ledger statement; objections return through a new exploration
entry for human resolution.

Keep `checked_by` mandatory and set it to JSON `null` for `drafted` and `frozen` nodes. Preserve
the existing `proved`/`checked_by: lean` pairing for completed certificates. All statuses must
have a node-specific artifact in the default Lake target. Only proved nodes undergo escape-token
checks, including `native_decide` and literal local imports. The checker validates current
metadata, not human approval or a historical transition sequence.

## Rationale

A passing Lean build verifies that draft signatures elaborate, but placeholders do not establish
their truth. Recording an explicit uncertified state keeps the existing linear-test certificate
meaningful while permitting new statement work in the same default build and CI workflow.
Following local imports prevents a thin entry point from masking an unfinished reusable lemma.

The tensorization artifact names the exact public declarations with `#check`, avoiding duplicate
statements or proof wrappers during the statement phase. It remains unproved. Before promotion
to `proved`, the proof phase must complete the imported statements and perform its mathematical
and axiom review as well as the three repository checks.

## Scope

The existing Poincaré and covariance definitions and proved linear-test node are unchanged.
Tensorization is `drafted`; this decision grants no statement freeze or proof certification.
