# Issue 2 Stage 2B actor prompt

Produce a compiling Lean implementation of the three linear-test analysis theorems in the frozen
Stage 2B specification.

## Context

Your workspace is a deliberately isolated autoformalization fixture. Its exact file entries are:

1. `AGENTS.md`;
2. `TASK.md`;
3. `AcceptedStage1A.lean`;
4. `AcceptedStage1A.olean`;
5. `AcceptedStage1B.lean`;
6. `AcceptedStage1B.olean`;
7. `AcceptedStage2A.lean`;
8. `AcceptedStage2A.olean`; and
9. `CandidateStage2B.lean`.

Read the six text files and do not inspect any compiled `.olean` dependency.

`TASK.md` is the complete frozen Stage 2B specification. The three accepted Lean sources and
their toolchain-matched compiled artifacts are read-only, human-accepted experimental
dependencies. No repository source, existing Issue 2 implementation, solution, certificate,
review, ledger, oracle, or later-stage artifact is available or needed.

## Required result

Edit only `CandidateStage2B.lean`. It must:

- import only `AcceptedStage2A`;
- continue namespace `Issue2Autoformalization.Stage1A` without redeclaring accepted material;
- implement exactly the three theorem declarations displayed in `TASK.md`;
- preserve every displayed binder, theorem type, hypothesis, and right-hand side;
- derive all three `IsAdmissible` fields from exactly the displayed probability and `MemLp id`
  hypotheses;
- add no unrequested public declaration, attribute, stronger assumption, or later-stage result;
  and
- compile with `lean CandidateStage2B.lean` at exit zero and with empty standard output and
  standard error.

After every edit, run exactly `lean CandidateStage2B.lean`. Use only actual Lean diagnostics to
repair imports, namespaces, types, binders, coercions, proof terms, or style findings until the
command exits zero and its output is empty. A warning or linter suggestion is a failed attempt even
when Lean exits zero. Do not report success based on inspection alone.

## Boundaries

- Work directly in this single actor session.
- Do not spawn a subagent, delegate, invoke collaboration, or act as a reviewer.
- Do not use web search, browser, plugins, MCP tools, or network commands.
- Do not access or name paths outside this workspace.
- Do not inspect Codex/Humanize client state, credentials, transcripts, or environment variables.
- Do not inspect any `.olean`, modify any accepted artifact, or create, rename, or delete files.
- Do not use `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `external`, `set_option`, `attribute`,
  or another proof/diagnostic escape hatch.
- Do not add stronger assumptions, change the required namespace or API, or formalize Stage 3 or
  any later layer.
- Do not create a proof dossier or claim review, certification, production integration, or
  mathematical acceptance.

## Final response

When Lean exits zero with no diagnostic output, inspect `CandidateStage2B.lean` once more. Report
only:

1. that `lean CandidateStage2B.lean` exited zero and emitted no diagnostics;
2. the three requested theorem names;
3. whether you added any assumption beyond `TASK.md` (the required answer is no);
4. the number of compiler-feedback repair iterations; and
5. any semantic or proof uncertainty that the human reviewer should examine.

Compilation is neither semantic acceptance nor proof certification. Stop after reporting; a human
reviewer makes the only accept/reject decision.
