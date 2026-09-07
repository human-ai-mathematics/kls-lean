# Log-concavity module organization and documentation corrections

Date: 2026-09-07. The user requested correction of stale navigation/status documentation and
organization of the log-concavity files within KLS. This is a local source-layout change.

## Scope

The shared LogConcave predicate, local slope and literature constant definitions remain in
KLS/Definitions.lean. Four related modules move into KLS/LogConcave/. Declaration namespaces,
statements, proof bodies and existing draft obligations remain unchanged. Consumers migrate
directly, with no old-path forwarding files. Existing uncommitted work is preserved.

Paths below are relative to formalization/FunctionalInequalities/.

| Previous path | Current path |
| --- | --- |
| `KLS/LogConcave.lean` | `KLS/LogConcave/Transport.lean` |
| `KLS/LogConcaveBorel.lean` | `KLS/LogConcave/Borel.lean` |
| `KLS/LogConcaveDensity.lean` | `KLS/LogConcave/AbsoluteContinuity.lean` |
| `KLS/BorellRepresentation.lean` | `KLS/LogConcave/BorellRepresentation.lean` |

The name AbsoluteContinuity identifies the established conclusion without implying construction
of the Borell density representative. Transport identifies the geometric role of the former
LogConcave module. Definitions and representation statements are not split or strengthened.

## Documentation

The Poincare guide now describes the proved literature comparisons and their assumptions.
ConditionalFiber's module header now agrees with its six proved well-definedness contracts.
The root module and main guide explicitly include drafts in the aggregate. The main guide uses
a topic map covering every library subject and Dev, and links detailed subject guides instead
of repeating a partial full file tree. New KLS and LogConcave guides describe reading order,
module placement and exact proof boundaries. Existing dated decisions/explorations are retained.

## Validation

The pre-edit working-tree snapshot was compared with all 82 existing Lean files: all non-comment
content is identical after only the specified import substitutions. Infrastructure evidence
hashes are refreshed only for files changed by those imports, module-reference comments or the
ConditionalFiber header; each old hash was checked against the pre-edit source. The ledger's
status fields and statement baseline are unchanged. Run `python3 research/verify.py` for the
repository's structural, Python, Lake, statement, axiom and current-source kernel-replay gates;
immutable execution results are stored under build/verification/.
