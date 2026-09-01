# Issue 2 Stage 4B actor prompt

Produce a compiling Lean implementation of the eight spectral-bridge and extended covariance
declarations in the frozen Stage 4B specification.

## Context

Your workspace is a deliberately isolated autoformalization fixture with exactly fifteen entries:
`AGENTS.md`, `TASK.md`, the accepted Stage 1A, 1B, 2A, 2B, 3, and 4A source/compiled pairs, and
`CandidateStage4B.lean`.

Read the nine text files and do not inspect any compiled `.olean` dependency. `TASK.md` is the
complete frozen specification. The six accepted Lean sources and their toolchain-matched compiled
artifacts are read-only, human-accepted experimental dependencies. No repository source, existing
Issue 2 implementation, solution, certificate, review, ledger, oracle, or later-stage artifact is
available or needed.

## Required result

Edit only `CandidateStage4B.lean`. It must:

- import exactly `AcceptedStage4A`, with no second import;
- continue namespace `Issue2Autoformalization.Stage1A` without redeclaring accepted material;
- implement exactly the eight declarations displayed in `TASK.md`, in that order;
- preserve every displayed binder, declaration type, instance hypothesis, expression, attribute,
  and right-hand side;
- preserve the zero-dimensional convention and extended-value bounds; and
- compile with `lean CandidateStage4B.lean` at exit zero and with empty standard output and
  standard error.

After every edit, run exactly `lean CandidateStage4B.lean`. Use only actual Lean diagnostics to
repair proof terms or style findings until the command exits zero and its output is empty. A
warning or linter suggestion is a failed attempt even when Lean exits zero.

## Boundaries

- Work directly in this single actor session; do not spawn or delegate.
- Do not use collaboration, review, web, browser, plugin, MCP, or network tools.
- Do not access or name paths outside this workspace, inspect runtime/client state, credentials,
  transcripts, environment variables, or any `.olean`.
- Do not modify accepted artifacts or create, rename, or delete files.
- Do not use a proof or diagnostic escape hatch.
- Do not move finite-dimensional, nontrivial, or subsingleton instances into the ambient block or
  add probability, stronger moment, separability, or other assumptions.
- Do not change the import, namespace, API, or formalize Euclidean/Gaussian specialization, final
  Issue 2 assembly, or another later-layer result.
- Do not claim review, certification, production integration, or mathematical acceptance.

## Final response

When Lean exits zero with no diagnostic output, report only the clean compiler result, the eight
requested declaration names, whether any assumption beyond `TASK.md` was added (the required
answer is no), the number of compiler-feedback repair iterations, and any semantic or proof
uncertainty for the human reviewer. Then stop; compilation is not acceptance.
