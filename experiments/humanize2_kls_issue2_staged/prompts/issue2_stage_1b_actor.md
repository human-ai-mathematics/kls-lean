# Issue 2 Stage 1B actor prompt

Produce a compiling Lean implementation of the foundational lemmas and extended optimal Poincaré
constant in the frozen Stage 1B specification.

## Context

Your workspace is a deliberately isolated autoformalization fixture. Its exact file entries are:

1. `AGENTS.md`;
2. `TASK.md`;
3. `AcceptedStage1A.lean`;
4. `AcceptedStage1A.olean`; and
5. `CandidateStage1B.lean`.

Read the four text files and do not inspect or modify the compiled `.olean` dependency.

`TASK.md` is the complete frozen Stage 1B mathematical specification. `AcceptedStage1A.lean` and
its toolchain-matched `.olean` are a read-only, human-accepted experimental dependency. Its
explicit quantified-function binder in `HasPoincare` is intentional. No repository source,
existing Issue 2 implementation, solution, certificate, review, ledger, oracle, or later-stage
artifact is available or needed.

## Required result

Edit only `CandidateStage1B.lean`. It must:

- import only `AcceptedStage1A`;
- extend namespace `Issue2Autoformalization.Stage1A` without redeclaring its accepted definitions;
- implement exactly the declarations and theorem statements listed in `TASK.md`;
- copy the five frozen optimal-constant theorem headers from `TASK.md` literally, including every
  implicit binder and the universal-negation form of `optimalPoincareConstant_eq_top_iff`;
- retain the accepted Stage 1A assumptions and explicit `HasPoincare` binder;
- add no unrequested public mathematical declaration; and
- compile successfully with `lean CandidateStage1B.lean`, with no compiler or linter diagnostic on
  standard output or standard error.

After every edit, run exactly `lean CandidateStage1B.lean`. Use only actual Lean diagnostics to
repair imports, namespaces, types, binders, coercions, proof terms, or style findings until that
command exits zero and its output is empty. A warning or linter suggestion is a failed attempt even
when the exit code is zero. Do not report success based on inspection alone.

## Boundaries

- Work directly in this single actor session.
- Do not spawn a subagent, delegate, invoke collaboration, or act as a reviewer.
- Do not use web search, browser, plugins, MCP tools, or network commands.
- Do not access or name paths outside this workspace.
- Do not inspect Codex/Humanize client state, credentials, transcripts, or environment variables.
- Do not modify either accepted Stage 1A artifact or create, rename, or delete files.
- Do not use `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `external`, or a custom unsound escape
  hatch.
- Do not add stronger assumptions, alter accepted Stage 1A declarations, or formalize a later
  stage.
- Do not suppress a warning or linter with `set_option`, `attribute`, or another configuration
  escape; repair the underlying code.
- Do not replace any of the five frozen theorem types with a merely logically equivalent type or
  change an implicit binder to an explicit positional argument.
- Do not create a proof dossier or claim review/certification.

## Final response

When Lean exits zero with no diagnostic output, inspect `CandidateStage1B.lean` once more. Report
only:

1. that `lean CandidateStage1B.lean` exited zero and emitted no diagnostics;
2. the requested definition and theorem names produced;
3. whether you added any assumption beyond `TASK.md` (the required answer is no);
4. the number of compiler-feedback repair iterations; and
5. any semantic or proof uncertainty that the human reviewer should examine.

Compilation is neither semantic acceptance nor proof certification. Stop after reporting; a human
reviewer makes the only accept/reject decision.
