# Issue 2 Stage 5 actor prompt

Produce a compiling Lean implementation of the three final-assembly theorems in the frozen Stage
5 specification.

## Context

Your workspace is a deliberately isolated autoformalization fixture with exactly seventeen
entries: `AGENTS.md`, `TASK.md`, the accepted Stage 1A, 1B, 2A, 2B, 3, 4A, and 4B
source/compiled pairs, and `CandidateStage5.lean`.

Read the ten text files and do not inspect any compiled `.olean` dependency. `TASK.md` is the
complete frozen specification. The seven accepted Lean sources and their toolchain-matched
compiled artifacts are read-only, human-accepted experimental dependencies. No repository
source, production implementation, solution, certificate, review, ledger file, oracle, or
later-stage artifact is available or needed.

## Required result

Edit only `CandidateStage5.lean`. It must:

- import exactly `AcceptedStage4B`, with no second import;
- continue namespace `Issue2Autoformalization.Stage1A` without redeclaring accepted material;
- implement exactly the three theorems displayed in `TASK.md`, in that order;
- preserve every displayed binder, declaration type, instance hypothesis, expression, and
  conclusion, including the strict-implicit `⦃f⦄` binder and the deliberate finite-dimensional
  probability hypotheses;
- add no attribute or definition; preserve the `D = 0` Euclidean boundary; and
- compile with `lean CandidateStage5.lean` at exit zero and with empty standard output and
  standard error.

After every edit, run exactly `lean CandidateStage5.lean`. Use only actual Lean diagnostics to
repair proof terms or style findings until the command exits zero and its output is empty. A
warning or linter suggestion is a failed attempt even when Lean exits zero.

## Boundaries

- Work directly in this single actor session; do not spawn or delegate.
- Do not use collaboration, review, web, browser, plugin, MCP, or network tools.
- Do not access or name paths outside this workspace, inspect runtime/client state, credentials,
  transcripts, environment variables, or any `.olean`.
- Do not modify accepted artifacts or create, rename, or delete files.
- Do not use a proof or diagnostic escape hatch.
- Do not remove the deliberately redundant finite-dimensional or probability instances, change
  the strict-implicit binder, add manual Euclidean instances, or exclude dimension zero.
- Do not change the import, namespace, API, or formalize a Gaussian formula, another KLS target,
  a production certificate binding, or any other result.
- Do not claim review, certification, production integration, or mathematical acceptance.

## Final response

When Lean exits zero with no diagnostic output, report only the clean compiler result, the three
requested theorem names, whether any assumption beyond `TASK.md` was added (the required answer
is no), the number of compiler-feedback repair iterations, and any semantic or proof uncertainty
for the human reviewer. Then stop; compilation is not acceptance.
