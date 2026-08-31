# Issue 2 Stage 2A actor prompt

Produce a compiling Lean implementation of the five linear-test geometry declarations in the
frozen Stage 2A specification.

## Context

Your workspace is a deliberately isolated autoformalization fixture. Its exact file entries are:

1. `AGENTS.md`;
2. `TASK.md`;
3. `AcceptedStage1A.lean`;
4. `AcceptedStage1A.olean`;
5. `AcceptedStage1B.lean`;
6. `AcceptedStage1B.olean`; and
7. `CandidateStage2A.lean`.

Read the five text files and do not inspect either compiled `.olean` dependency.

`TASK.md` is the complete frozen Stage 2A specification. The two accepted Lean sources and their
toolchain-matched compiled artifacts are read-only, human-accepted experimental dependencies. No
repository source, existing Issue 2 implementation, solution, certificate, review, ledger,
oracle, or later-stage artifact is available or needed.

## Required result

Edit only `CandidateStage2A.lean`. It must:

- import only `AcceptedStage1B`;
- continue namespace `Issue2Autoformalization.Stage1A` without redeclaring accepted material;
- implement exactly the five declarations displayed in `TASK.md`;
- preserve every displayed binder, theorem type, inner-product argument order, and `@[simp]`
  attribute;
- use no measurable-space or measure-theoretic assumption;
- add no unrequested public declaration or later-stage result; and
- compile with `lean CandidateStage2A.lean` at exit zero and with empty standard output and
  standard error.

After every edit, run exactly `lean CandidateStage2A.lean`. Use only actual Lean diagnostics to
repair imports, namespaces, types, binders, coercions, proof terms, or style findings until the
command exits zero and its output is empty. A warning or linter suggestion is a failed attempt even
when Lean exits zero. Do not report success based on inspection alone.

## Boundaries

- Work directly in this single actor session.
- Do not spawn a subagent, delegate, invoke collaboration, or act as a reviewer.
- Do not use web search, browser, plugins, MCP tools, or network commands.
- Do not access or name paths outside this workspace.
- Do not inspect Codex/Humanize client state, credentials, transcripts, or environment variables.
- Do not modify either accepted source or compiled artifact, and do not create, rename, or delete
  files.
- Do not use `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `external`, `set_option`, `attribute`,
  or another proof/diagnostic escape hatch. The two requested inline `@[simp]` annotations are the
  only attributes allowed.
- Do not add stronger assumptions, change the required namespace or API, or formalize Stage 2B or
  any later layer.
- Do not create a proof dossier or claim review, certification, or mathematical acceptance.

## Final response

When Lean exits zero with no diagnostic output, inspect `CandidateStage2A.lean` once more. Report
only:

1. that `lean CandidateStage2A.lean` exited zero and emitted no diagnostics;
2. the five requested declaration names;
3. whether you added any assumption beyond `TASK.md` (the required answer is no);
4. the number of compiler-feedback repair iterations; and
5. any semantic or proof uncertainty that the human reviewer should examine.

Compilation is neither semantic acceptance nor proof certification. Stop after reporting; a human
reviewer makes the only accept/reject decision.
